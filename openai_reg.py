import json
import os
import re
import sys
import time
import uuid
import math
import random
import string
import secrets
import hashlib
import base64
import threading
import argparse
from datetime import datetime, timezone, timedelta
from urllib.parse import urlparse, parse_qs, urlencode, quote
from dataclasses import dataclass
from typing import Any, Dict, Optional, List
import urllib.parse
import ssl
import urllib.request
import urllib.error
import imaplib
import email
import socket
from email.header import decode_header
from email.utils import parsedate_to_datetime

from curl_cffi import requests

# ==========================================
# Cloudflare Temp Email API
# ==========================================


def _load_dotenv(path: str = ".env") -> None:
    if not os.path.exists(path):
        return
    try:
        with open(path, "r", encoding="utf-8") as handle:
            for raw in handle:
                line = raw.strip()
                if not line or line.startswith("#") or "=" not in line:
                    continue
                key, value = line.split("=", 1)
                key = key.strip()
                if not key or key in os.environ:
                    continue
                value = value.strip()
                if len(value) >= 2 and value[0] == value[-1] and value[0] in {'"', "'"}:
                    value = value[1:-1]
                os.environ[key] = value
    except Exception:
        pass


_load_dotenv()

MAIL_DOMAIN = "mydomain.domain.com"
TOKEN_OUTPUT_DIR = os.getenv("TOKEN_OUTPUT_DIR", "").strip()
KEYS_DIR = os.getenv("KEYS_DIR", "keys").strip() or "keys"


def _ssl_verify() -> bool:
    flag = os.getenv("OPENAI_SSL_VERIFY", "1").strip().lower()
    return flag not in {"0", "false", "no", "off"}


def _skip_net_check() -> bool:
    flag = os.getenv("SKIP_NET_CHECK", "0").strip().lower()
    return flag in {"1", "true", "yes", "on"}


def get_email_and_token(proxies: Any = None) -> tuple:
    """生成随机前缀的自有域名邮箱"""
    prefix = ''.join(random.choices(string.ascii_lowercase + string.digits, k=10))
    email = f"{prefix}@{MAIL_DOMAIN}"
    return email, email



def _extract_otp_code(content: str) -> str:
    if not content:
        return ""
    patterns = [
        r"Your ChatGPT code is\s*(\d{6})",
        r"ChatGPT code is\s*(\d{6})",
        r"your verification code is\s*(\d{6})",
        r"verification code to continue:\s*(\d{6})",
        r"verification code[^0-9]{0,20}(\d{6})",
        r"(?:openai|chatgpt)[^0-9]{0,30}(?:code|otp)[^0-9]{0,20}(\d{6})",
        r"验证码[^0-9]{0,20}(\d{6})",
    ]
    for pattern in patterns:
        match = re.search(pattern, content, re.IGNORECASE | re.DOTALL)
        if match:
            return match.group(1)
    return ""


def _decode_header_value(value: str) -> str:
    if not value:
        return ""
    parts: List[str] = []
    try:
        for text, charset in decode_header(value):
            if isinstance(text, bytes):
                parts.append(text.decode(charset or "utf-8", errors="replace"))
            else:
                parts.append(text)
    except Exception:
        return value
    return "".join(parts)


def _message_to_text(msg: Any) -> str:
    chunks: List[str] = []
    for h in ("Subject", "From", "To", "Date"):
        chunks.append(_decode_header_value(msg.get(h, "")))

    if msg.is_multipart():
        for part in msg.walk():
            ctype = (part.get_content_type() or "").lower()
            if ctype not in {"text/plain", "text/html"}:
                continue
            payload = part.get_payload(decode=True)
            if payload is None:
                continue
            charset = part.get_content_charset() or "utf-8"
            chunks.append(payload.decode(charset, errors="replace"))
    else:
        payload = msg.get_payload(decode=True)
        if payload is not None:
            charset = msg.get_content_charset() or "utf-8"
            chunks.append(payload.decode(charset, errors="replace"))
        else:
            chunks.append(str(msg.get_payload() or ""))

    return "\n".join(filter(None, chunks))


def _env_int(name: str, default: int, minimum: Optional[int] = None) -> int:
    raw = os.getenv(name, str(default))
    try:
        value = int(str(raw).strip() or str(default))
    except (TypeError, ValueError):
        value = default
    if minimum is not None:
        value = max(minimum, value)
    return value


def _iter_imap_folders(imap_folder: str, imap_host: str) -> List[str]:
    folders: List[str] = []

    def add(folder_name: str) -> None:
        folder_name = (folder_name or "").strip()
        if folder_name and folder_name not in folders:
            folders.append(folder_name)

    add(imap_folder)
    add("INBOX")

    host = (imap_host or "").lower()
    if "gmail" in host or "googlemail" in host:
        add("[Gmail]/All Mail")
        add("[Google Mail]/All Mail")
        add("[Gmail]/Spam")
        add("[Google Mail]/Spam")

    extra = os.getenv("IMAP_EXTRA_FOLDERS", "").strip()
    if extra:
        for item in extra.split(","):
            add(item)

    return folders


def _imap_open_folder(imap: Any, folder_name: str) -> bool:
    try:
        status, _ = imap.select(f'"{folder_name}"')
        if status == "OK":
            return True
    except Exception:
        pass
    try:
        status, _ = imap.select(folder_name)
        return status == "OK"
    except Exception:
        return False


def _imap_search_ids(imap: Any, min_date_ts: Optional[float] = None) -> List[bytes]:
    since_str = ""
    if min_date_ts:
        try:
            since_dt = datetime.fromtimestamp(min_date_ts, timezone.utc)
            since_str = since_dt.strftime("%d-%b-%Y")
        except Exception:
            since_str = ""

    queries: List[tuple] = []
    if since_str:
        queries.extend(
            [
                ("UNSEEN", "SINCE", since_str),
                ("RECENT", "SINCE", since_str),
                ("ALL", "SINCE", since_str),
            ]
        )
    queries.extend(
        [
            ("UNSEEN",),
            ("RECENT",),
            ("ALL",),
        ]
    )
    seen: set = set()
    ordered: List[bytes] = []
    for query in queries:
        try:
            status, data = imap.search(None, *query)
        except Exception:
            continue
        if status != "OK" or not data or not data[0]:
            continue
        for msg_id in data[0].split():
            if msg_id not in seen:
                seen.add(msg_id)
                ordered.append(msg_id)
    # 按邮件序号排序，保证从最新邮件开始抓取
    def _msgid_key(v: bytes) -> int:
        try:
            return int(v)
        except Exception:
            return 0

    return sorted(ordered, key=_msgid_key)


def _looks_like_openai_otp(msg: Any, content: str) -> bool:
    subject = _decode_header_value(msg.get("Subject", "")).lower()
    sender = " ".join(
        [
            _decode_header_value(msg.get("From", "")),
            _decode_header_value(msg.get("Sender", "")),
            _decode_header_value(msg.get("Return-Path", "")),
        ]
    ).lower()
    merged = f"{subject}\n{sender}\n{content}".lower()
    keywords = (
        "chatgpt code",
        "your chatgpt code",
        "your verification code is",
        "verification code to continue",
        "openai",
        "chatgpt",
        "email verification",
    )
    return any(keyword in merged for keyword in keywords)


def _imap_fetch_otp(email_addr: str, min_date_ts: Optional[float] = None) -> str:
    imap_host = os.getenv("IMAP_HOST", "").strip()
    imap_user = os.getenv("IMAP_USER", "").strip() or email_addr
    imap_password = os.getenv("IMAP_PASSWORD", "").strip()
    imap_folder = os.getenv("IMAP_FOLDER", "INBOX").strip() or "INBOX"
    imap_ssl = os.getenv("IMAP_SSL", "1").strip().lower() not in {"0", "false", "no", "off"}
    imap_timeout = _env_int("IMAP_TIMEOUT_SECONDS", 180, minimum=15)
    imap_poll = _env_int("IMAP_POLL_SECONDS", 1, minimum=1)
    imap_lookback = _env_int("IMAP_LOOKBACK_SECONDS", 900, minimum=60)
    imap_connect_timeout = _env_int("IMAP_CONNECT_TIMEOUT_SECONDS", 20, minimum=5)
    imap_login_retries = _env_int("IMAP_LOGIN_RETRIES", 2, minimum=0)
    imap_fetch_limit = _env_int("IMAP_FETCH_LIMIT", 40, minimum=5)
    imap_debug = os.getenv("IMAP_DEBUG", "0").strip().lower() in {"1", "true", "yes", "on"}
    imap_strict_rcpt = os.getenv("IMAP_STRICT_RECIPIENT", "0").strip().lower() in {"1", "true", "yes", "on"}

    if not imap_host or not imap_password:
        print("[*] 未配置 IMAP_HOST / IMAP_PASSWORD，跳过自动收码")
        return ""

    default_port = 993 if imap_ssl else 143
    imap_port = int(os.getenv("IMAP_PORT", str(default_port)) or str(default_port))
    print(f"[*] 尝试 IMAP 自动收码: {imap_user}@{imap_host}:{imap_port} ({imap_folder})")
    start = time.time()
    checked_ids: set = set()

    hosts_to_try: List[str] = [imap_host]
    if imap_host.lower() in {"imap.gmail.com", "imap.googlemail.com"}:
        alt = "imap.googlemail.com" if imap_host.lower() == "imap.gmail.com" else "imap.gmail.com"
        hosts_to_try.append(alt)

    imap = None
    last_error: Optional[Exception] = None
    for host in hosts_to_try:
        for attempt in range(imap_login_retries + 1):
            try:
                if imap_ssl:
                    ctx = None if _ssl_verify() else ssl._create_unverified_context()
                    imap = imaplib.IMAP4_SSL(host, imap_port, ssl_context=ctx, timeout=imap_connect_timeout)
                else:
                    imap = imaplib.IMAP4(host, imap_port, timeout=imap_connect_timeout)

                imap.login(imap_user, imap_password)
                imap.select(imap_folder)
                last_error = None
                break
            except (imaplib.IMAP4.error, socket.timeout, TimeoutError, OSError) as e:
                last_error = e
                print(f"[Warn] IMAP 连接失败({host}) 第 {attempt + 1}/{imap_login_retries + 1} 次: {e}")
                try:
                    if imap is not None:
                        imap.logout()
                except Exception:
                    pass
                imap = None
                if attempt < imap_login_retries:
                    time.sleep(min(3, 1 + attempt))
        if imap is not None:
            break

    if imap is None:
        print(f"[Error] IMAP 连接失败: {last_error}")
        return ""

    try:
        folders = _iter_imap_folders(imap_folder, imap_host)
        while time.time() - start < imap_timeout:
            for folder_name in folders:
                if not _imap_open_folder(imap, folder_name):
                    continue
                ids = _imap_search_ids(imap, min_date_ts=min_date_ts)
                if imap_debug:
                    print(f"[*] IMAP 文件夹 {folder_name} 候选邮件数: {len(ids)}")
                for msg_id in reversed(ids[-imap_fetch_limit:]):
                    cache_key = (folder_name, msg_id)
                    if cache_key in checked_ids:
                        continue
                    checked_ids.add(cache_key)

                    f_status, f_data = imap.fetch(msg_id, "(BODY.PEEK[])")
                    if f_status != "OK" or not f_data:
                        continue

                    raw_bytes = b""
                    for row in f_data:
                        if isinstance(row, tuple) and len(row) > 1 and isinstance(row[1], bytes):
                            raw_bytes = row[1]
                            break
                    if not raw_bytes:
                        continue

                    msg = email.message_from_bytes(raw_bytes)

                    # 过滤过老邮件，减少误取历史验证码
                    try:
                        date_hdr = msg.get("Date", "")
                        dt = parsedate_to_datetime(date_hdr)
                        if dt is not None:
                            if dt.tzinfo is None:
                                dt = dt.replace(tzinfo=timezone.utc)
                            dt_utc = dt.astimezone(timezone.utc)
                            age_seconds = (datetime.now(timezone.utc) - dt_utc).total_seconds()
                            if age_seconds > imap_lookback:
                                continue
                            if min_date_ts is not None and dt_utc.timestamp() < (min_date_ts - 15):
                                if imap_debug:
                                    print(
                                        f"[*] 跳过触发发送前的旧邮件: {dt_utc.isoformat()} < "
                                        f"{datetime.fromtimestamp(min_date_ts, timezone.utc).isoformat()}"
                                    )
                                continue
                    except Exception:
                        pass

                    # 如果是 catch-all 邮箱，默认只作为弱过滤，避免因为转发导致 To 头变化而漏掉验证码
                    rcpt_hdr = " ".join(
                        [
                            _decode_header_value(msg.get("To", "")),
                            _decode_header_value(msg.get("Delivered-To", "")),
                            _decode_header_value(msg.get("X-Original-To", "")),
                            _decode_header_value(msg.get("Envelope-To", "")),
                        ]
                    ).lower()
                    if (
                        imap_strict_rcpt
                        and email_addr
                        and rcpt_hdr
                        and email_addr.lower() not in rcpt_hdr
                    ):
                        if imap_debug:
                            print(f"[*] 跳过收件人不匹配邮件: {rcpt_hdr[:120]}")
                        continue

                    content = _message_to_text(msg)
                    code = _extract_otp_code(content)
                    if not code:
                        continue
                    # IMAP 收码不能对“最近邮件”放宽为任意发件人，否则很容易误抓到其他服务的 6 位数字
                    if not _looks_like_openai_otp(msg, content):
                        if imap_debug:
                            subj = _decode_header_value(msg.get("Subject", ""))
                            print(f"[*] 跳过疑似非 OpenAI 验证码邮件: {subj[:120]}")
                        continue

                    print(f"[*] IMAP 自动获取验证码成功: {code} (folder={folder_name})")
                    return code

            time.sleep(imap_poll)
    finally:
        try:
            imap.logout()
        except Exception:
            pass

    print("[*] IMAP 超时，未自动获取到验证码")
    return ""


def get_oai_code(token: str, email: str, proxies: Any = None) -> str:
    """通过 GPTMail API 轮询获取 OpenAI 验证码"""
    headers = {"X-API-Key": GPTMAIL_API_KEY}
    print(f"[*] 正在等待邮箱 {email} 的验证码...", end="", flush=True)

    for _ in range(40):
        print(".", end="", flush=True)
        try:
            res = requests.get(
                f"{GPTMAIL_BASE}/api/emails",
                params={"email": email},
                headers=headers,
                proxies=proxies,
                impersonate="safari",
                verify=_ssl_verify(),
                timeout=15,
            )
            if res.status_code == 200:
                j = res.json()
                if j.get("success"):
                    emails_list = (j.get("data") or {}).get("emails", [])
                    if isinstance(emails_list, list) and emails_list:
                        # 尝试读取邮件详情获取完整内容
                        mail_id = emails_list[0].get("id", "")
                        content = ""
                        if mail_id:
                            detail_res = requests.get(
                                f"{GPTMAIL_BASE}/api/email/{mail_id}",
                                headers=headers,
                                proxies=proxies,
                                impersonate="safari",
                                verify=_ssl_verify(),
                                timeout=15,
                            )
                            if detail_res.status_code == 200:
                                detail = detail_res.json()
                                if detail.get("success"):
                                    d = detail.get("data") or {}
                                    content = "\n".join(filter(None, [
                                        str(d.get("subject") or ""),
                                        str(d.get("content") or ""),
                                        str(d.get("html_content") or ""),
                                    ]))
                        if not content:
                            # fallback: 用列表里的 subject
                            content = str(emails_list[0].get("subject") or "")
                        code = _extract_otp_code(content)
                        if code:
                            print(" 抓到啦! 验证码:", code)
                            return code
        except Exception:
            pass

        time.sleep(3)

    print(" 超时，未收到验证码")
    return ""


# ==========================================
# OAuth 授权与辅助函数
# ==========================================

AUTH_URL = "https://auth.openai.com/oauth/authorize"
TOKEN_URL = "https://auth.openai.com/oauth/token"
CLIENT_ID = "app_EMoamEEZ73f0CkXaXp7hrann"

DEFAULT_REDIRECT_URI = f"http://localhost:1455/auth/callback"
DEFAULT_SCOPE = "openid email profile offline_access"


def _b64url_no_pad(raw: bytes) -> str:
    return base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=")


def _sha256_b64url_no_pad(s: str) -> str:
    return _b64url_no_pad(hashlib.sha256(s.encode("ascii")).digest())


def _random_state(nbytes: int = 16) -> str:
    return secrets.token_urlsafe(nbytes)


def _pkce_verifier() -> str:
    return secrets.token_urlsafe(64)


def _parse_callback_url(callback_url: str) -> Dict[str, Any]:
    candidate = callback_url.strip()
    if not candidate:
        return {"code": "", "state": "", "error": "", "error_description": ""}

    if "://" not in candidate:
        if candidate.startswith("?"):
            candidate = f"http://localhost{candidate}"
        elif any(ch in candidate for ch in "/?#") or ":" in candidate:
            candidate = f"http://{candidate}"
        elif "=" in candidate:
            candidate = f"http://localhost/?{candidate}"

    parsed = urllib.parse.urlparse(candidate)
    query = urllib.parse.parse_qs(parsed.query, keep_blank_values=True)
    fragment = urllib.parse.parse_qs(parsed.fragment, keep_blank_values=True)

    for key, values in fragment.items():
        if key not in query or not query[key] or not (query[key][0] or "").strip():
            query[key] = values

    def get1(k: str) -> str:
        v = query.get(k, [""])
        return (v[0] or "").strip()

    code = get1("code")
    state = get1("state")
    error = get1("error")
    error_description = get1("error_description")

    if code and not state and "#" in code:
        code, state = code.split("#", 1)

    if not error and error_description:
        error, error_description = error_description, ""

    return {
        "code": code,
        "state": state,
        "error": error,
        "error_description": error_description,
    }


def _jwt_claims_no_verify(id_token: str) -> Dict[str, Any]:
    if not id_token or id_token.count(".") < 2:
        return {}
    payload_b64 = id_token.split(".")[1]
    pad = "=" * ((4 - (len(payload_b64) % 4)) % 4)
    try:
        payload = base64.urlsafe_b64decode((payload_b64 + pad).encode("ascii"))
        return json.loads(payload.decode("utf-8"))
    except Exception:
        return {}


def _decode_jwt_segment(seg: str) -> Dict[str, Any]:
    raw = (seg or "").strip()
    if not raw:
        return {}
    pad = "=" * ((4 - (len(raw) % 4)) % 4)
    try:
        decoded = base64.urlsafe_b64decode((raw + pad).encode("ascii"))
        return json.loads(decoded.decode("utf-8"))
    except Exception:
        return {}


def _to_int(v: Any) -> int:
    try:
        return int(v)
    except (TypeError, ValueError):
        return 0


def _post_form(url: str, data: Dict[str, str], timeout: int = 30) -> Dict[str, Any]:
    body = urllib.parse.urlencode(data).encode("utf-8")
    req = urllib.request.Request(
        url,
        data=body,
        method="POST",
        headers={
            "Content-Type": "application/x-www-form-urlencoded",
            "Accept": "application/json",
        },
    )
    try:
        context = None
        if not _ssl_verify():
            context = ssl._create_unverified_context()
        with urllib.request.urlopen(req, timeout=timeout, context=context) as resp:
            raw = resp.read()
            if resp.status != 200:
                raise RuntimeError(
                    f"token exchange failed: {resp.status}: {raw.decode('utf-8', 'replace')}"
                )
            return json.loads(raw.decode("utf-8"))
    except urllib.error.HTTPError as exc:
        raw = exc.read()
        raise RuntimeError(
            f"token exchange failed: {exc.code}: {raw.decode('utf-8', 'replace')}"
        ) from exc


def _post_with_retry(
    session: requests.Session,
    url: str,
    *,
    headers: Dict[str, Any],
    data: Any = None,
    json_body: Any = None,
    proxies: Any = None,
    timeout: int = 30,
    retries: int = 2,
) -> Any:
    last_error: Optional[Exception] = None
    for attempt in range(retries + 1):
        try:
            if json_body is not None:
                return session.post(
                    url,
                    headers=headers,
                    json=json_body,
                    proxies=proxies,
                    verify=_ssl_verify(),
                    timeout=timeout,
                )
            return session.post(
                url,
                headers=headers,
                data=data,
                proxies=proxies,
                verify=_ssl_verify(),
                timeout=timeout,
            )
        except Exception as e:
            last_error = e
            if attempt >= retries:
                break
            time.sleep(2 * (attempt + 1))
    if last_error:
        raise last_error
    raise RuntimeError("Request failed without exception")


@dataclass(frozen=True)
class OAuthStart:
    auth_url: str
    state: str
    code_verifier: str
    redirect_uri: str


def generate_oauth_url(
    *, redirect_uri: str = DEFAULT_REDIRECT_URI, scope: str = DEFAULT_SCOPE
) -> OAuthStart:
    state = _random_state()
    code_verifier = _pkce_verifier()
    code_challenge = _sha256_b64url_no_pad(code_verifier)

    params = {
        "client_id": CLIENT_ID,
        "response_type": "code",
        "redirect_uri": redirect_uri,
        "scope": scope,
        "state": state,
        "code_challenge": code_challenge,
        "code_challenge_method": "S256",
        "prompt": "login",
        "id_token_add_organizations": "true",
        "codex_cli_simplified_flow": "true",
    }
    auth_url = f"{AUTH_URL}?{urllib.parse.urlencode(params)}"
    return OAuthStart(
        auth_url=auth_url,
        state=state,
        code_verifier=code_verifier,
        redirect_uri=redirect_uri,
    )


def submit_callback_url(
    *,
    callback_url: str,
    expected_state: str,
    code_verifier: str,
    redirect_uri: str = DEFAULT_REDIRECT_URI,
) -> str:
    cb = _parse_callback_url(callback_url)
    if cb["error"]:
        desc = cb["error_description"]
        raise RuntimeError(f"oauth error: {cb['error']}: {desc}".strip())

    if not cb["code"]:
        raise ValueError("callback url missing ?code=")
    if not cb["state"]:
        raise ValueError("callback url missing ?state=")
    if cb["state"] != expected_state:
        raise ValueError("state mismatch")

    token_resp = _post_form(
        TOKEN_URL,
        {
            "grant_type": "authorization_code",
            "client_id": CLIENT_ID,
            "code": cb["code"],
            "redirect_uri": redirect_uri,
            "code_verifier": code_verifier,
        },
    )

    access_token = (token_resp.get("access_token") or "").strip()
    refresh_token = (token_resp.get("refresh_token") or "").strip()
    id_token = (token_resp.get("id_token") or "").strip()
    expires_in = _to_int(token_resp.get("expires_in"))

    claims = _jwt_claims_no_verify(id_token)
    email = str(claims.get("email") or "").strip()
    auth_claims = claims.get("https://api.openai.com/auth") or {}
    account_id = str(auth_claims.get("chatgpt_account_id") or "").strip()

    now = int(time.time())
    expired_rfc3339 = time.strftime(
        "%Y-%m-%dT%H:%M:%SZ", time.gmtime(now + max(expires_in, 0))
    )
    now_rfc3339 = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(now))

    config = {
        "id_token": id_token,
        "access_token": access_token,
        "refresh_token": refresh_token,
        "account_id": account_id,
        "last_refresh": now_rfc3339,
        "email": email,
        "type": "codex",
        "expired": expired_rfc3339,
    }

    return json.dumps(config, ensure_ascii=False, separators=(",", ":"))


# ==========================================
# 核心注册逻辑
# ==========================================


def _generate_password(length: int = 16) -> str:
    """生成符合 OpenAI 要求的随机强密码（大小写+数字+特殊字符）"""
    upper = random.choices(string.ascii_uppercase, k=2)
    lower = random.choices(string.ascii_lowercase, k=2)
    digits = random.choices(string.digits, k=2)
    specials = random.choices("!@#$%&*", k=2)
    rest_len = length - 8
    pool = string.ascii_letters + string.digits + "!@#$%&*"
    rest = random.choices(pool, k=rest_len)
    chars = upper + lower + digits + specials + rest
    random.shuffle(chars)
    return "".join(chars)


def _normalize_proxy_value(raw_proxy: str) -> str:
    proxy = (raw_proxy or "").strip()
    if not proxy:
        return ""
    if "://" not in proxy:
        proxy = f"http://{proxy}"
    return proxy


def _load_proxies_from_file(path: str) -> List[str]:
    if not path:
        return []
    if not os.path.exists(path):
        return []

    proxies: List[str] = []
    try:
        with open(path, "r", encoding="utf-8") as handle:
            for raw_line in handle:
                line = raw_line.strip()
                if not line or line.startswith("#"):
                    continue
                proxy = _normalize_proxy_value(line)
                if proxy:
                    proxies.append(proxy)
    except Exception as e:
        print(f"[Warn] 读取代理文件失败: {path}, err={e}")
    return proxies


def run(proxy: Optional[str]) -> tuple:
    proxies: Any = None
    if proxy:
        proxies = {"http": proxy, "https": proxy}

    s = requests.Session(proxies=proxies, impersonate="safari")

    if not _skip_net_check():
        try:
            trace = s.get(
                "https://cloudflare.com/cdn-cgi/trace",
                proxies=proxies,
                verify=_ssl_verify(),
                timeout=10,
            )
            trace = trace.text
            loc_re = re.search(r"^loc=(.+)$", trace, re.MULTILINE)
            loc = loc_re.group(1) if loc_re else None
            print(f"[*] 当前 IP 所在地: {loc}")
            if loc == "CN" or loc == "HK":
                raise RuntimeError("检查代理哦w - 所在地不支持")
        except Exception as e:
            print(f"[Error] 网络连接检查失败: {e}")
            return None, None

    email, dev_token = get_email_and_token(proxies)
    if not email or not dev_token:
        return None, None
    print(f"[*] 成功获取临时邮箱与授权: {email}")
    masked = dev_token[:8] + "..." if dev_token else ""
    print(f"[*] 临时邮箱 JWT: {masked}")

    oauth = generate_oauth_url()
    url = oauth.auth_url

    try:
        resp = s.get(url, proxies=proxies, verify=True, timeout=15)
        did = s.cookies.get("oai-did")
        print(f"[*] Device ID: {did}")

        signup_body = f'{{"username":{{"value":"{email}","kind":"email"}},"screen_hint":"signup"}}'
        sen_req_body = f'{{"p":"","id":"{did}","flow":"authorize_continue"}}'

        sen_resp = requests.post(
            "https://sentinel.openai.com/backend-api/sentinel/req",
            headers={
                "origin": "https://sentinel.openai.com",
                "referer": "https://sentinel.openai.com/backend-api/sentinel/frame.html?sv=20260219f9f6",
                "content-type": "text/plain;charset=UTF-8",
            },
            data=sen_req_body,
            proxies=proxies,
            impersonate="safari",
            verify=_ssl_verify(),
            timeout=15,
        )

        if sen_resp.status_code != 200:
            print(f"[Error] Sentinel 异常拦截，状态码: {sen_resp.status_code}")
            return None, None

        sen_token = sen_resp.json()["token"]
        sentinel = f'{{"p": "", "t": "", "c": "{sen_token}", "id": "{did}", "flow": "authorize_continue"}}'

        signup_resp = s.post(
            "https://auth.openai.com/api/accounts/authorize/continue",
            headers={
                "referer": "https://auth.openai.com/create-account",
                "accept": "application/json",
                "content-type": "application/json",
                "openai-sentinel-token": sentinel,
            },
            data=signup_body,
            proxies=proxies,
            verify=_ssl_verify(),
        )
        signup_status = signup_resp.status_code
        print(f"[*] 提交注册表单状态: {signup_status}")

        if signup_status == 403:
            print("[Error] 提交注册表单返回 403，中断本次运行，将在10秒后重试...")
            return "retry_403", None
        if signup_status != 200:
            print("[Error] 提交注册表单失败，跳过本次流程")
            print(signup_resp.text)
            return None, None

        # --- 密码注册流程（/user/register 接口）---
        password = _generate_password()
        register_body = json.dumps({"password": password, "username": email})
        print(f"[*] 生成随机密码: {password[:4]}****")

        pwd_resp = s.post(
            "https://auth.openai.com/api/accounts/user/register",
            headers={
                "referer": "https://auth.openai.com/create-account/password",
                "accept": "application/json",
                "content-type": "application/json",
                "openai-sentinel-token": sentinel,
            },
            data=register_body,
            proxies=proxies,
            verify=_ssl_verify(),
        )
        print(f"[*] 提交注册(密码)状态: {pwd_resp.status_code}")
        if pwd_resp.status_code != 200:
            print(pwd_resp.text)
            return None, None

        # 解析 /user/register 的响应，获取 continue_url
        try:
            register_json = pwd_resp.json()
            register_continue = register_json.get("continue_url", "")
            register_page = (register_json.get("page") or {}).get("type", "")
            print(f"[*] 注册响应 continue_url: {register_continue}")
            print(f"[*] 注册响应 page.type: {register_page}")
        except Exception:
            register_continue = ""
            register_page = ""
            print(f"[*] 注册响应(raw): {pwd_resp.text[:300]}")

        # 根据 continue_url 判断是否需要邮箱验证
        need_otp = "email-verification" in register_continue or "verify" in register_continue
        if not need_otp and register_page:
            need_otp = "verification" in register_page or "otp" in register_page

        if need_otp:
            print("[*] 需要邮箱验证，开始等待验证码...")
            otp_sent_at = time.time()

            # 先触发 OpenAI 发送 OTP
            if register_continue:
                otp_send_url = register_continue
                if not otp_send_url.startswith("http"):
                    otp_send_url = f"https://auth.openai.com{otp_send_url}"
                print(f"[*] 触发发送 OTP: {otp_send_url}")
                otp_send_resp = _post_with_retry(
                    s,
                    otp_send_url,
                    headers={
                        "referer": "https://auth.openai.com/create-account/password",
                        "accept": "application/json",
                        "content-type": "application/json",
                        "openai-sentinel-token": sentinel,
                    },
                    json_body={},
                    proxies=proxies,
                    timeout=30,
                    retries=2,
                )
                print(f"[*] OTP 发送状态: {otp_send_resp.status_code}")
                if otp_send_resp.status_code != 200:
                    print(otp_send_resp.text)
                else:
                    otp_sent_at = time.time()

            code = _imap_fetch_otp(email, min_date_ts=otp_sent_at)
            if not code:
                code = input("\n[*] 请输入收到的验证码: ").strip()
            if not code:
                print("[Error] 未输入验证码，跳过")
                return None, None

            print("[*] 开始校验验证码...")
            code_resp = _post_with_retry(
                s,
                "https://auth.openai.com/api/accounts/email-otp/validate",
                headers={
                    "referer": "https://auth.openai.com/email-verification",
                    "accept": "application/json",
                    "content-type": "application/json",
                    "openai-sentinel-token": sentinel,
                },
                json_body={"code": code},
                proxies=proxies,
                timeout=30,
                retries=2,
            )
            print(f"[*] 验证码校验状态: {code_resp.status_code}")
            if code_resp.status_code != 200:
                print(code_resp.text)
        else:
            print("[*] 密码注册无需邮箱验证，跳过 OTP 步骤")

        create_account_body = '{"name":"Neo","birthdate":"2000-02-20"}'
        print("[*] 开始创建账户...")
        create_account_resp = _post_with_retry(
            s,
            "https://auth.openai.com/api/accounts/create_account",
            headers={
                "referer": "https://auth.openai.com/about-you",
                "accept": "application/json",
                "content-type": "application/json",
            },
            data=create_account_body,
            proxies=proxies,
            timeout=30,
            retries=2,
        )
        create_account_status = create_account_resp.status_code
        print(f"[*] 账户创建状态: {create_account_status}")

        if create_account_status != 200:
            print(create_account_resp.text)
            return None, None

        auth_cookie = s.cookies.get("oai-client-auth-session")
        if not auth_cookie:
            print("[Error] 未能获取到授权 Cookie")
            return None, None

        auth_json = _decode_jwt_segment(auth_cookie.split(".")[0])
        workspaces = auth_json.get("workspaces") or []
        if not workspaces:
            print("[Error] 授权 Cookie 里没有 workspace 信息")
            return None, None
        workspace_id = str((workspaces[0] or {}).get("id") or "").strip()
        if not workspace_id:
            print("[Error] 无法解析 workspace_id")
            return None, None

        select_body = f'{{"workspace_id":"{workspace_id}"}}'
        print("[*] 开始选择 workspace...")
        select_resp = _post_with_retry(
            s,
            "https://auth.openai.com/api/accounts/workspace/select",
            headers={
                "referer": "https://auth.openai.com/sign-in-with-chatgpt/codex/consent",
                "content-type": "application/json",
            },
            data=select_body,
            proxies=proxies,
            timeout=30,
            retries=2,
        )

        if select_resp.status_code != 200:
            print(f"[Error] 选择 workspace 失败，状态码: {select_resp.status_code}")
            print(select_resp.text)
            return None, None

        continue_url = str((select_resp.json() or {}).get("continue_url") or "").strip()
        if not continue_url:
            print("[Error] workspace/select 响应里缺少 continue_url")
            return None, None

        current_url = continue_url
        for _ in range(6):
            final_resp = s.get(
                current_url,
                allow_redirects=False,
                proxies=proxies,
                verify=_ssl_verify(),
                timeout=15,
            )
            location = final_resp.headers.get("Location") or ""

            if final_resp.status_code not in [301, 302, 303, 307, 308]:
                break
            if not location:
                break

            next_url = urllib.parse.urljoin(current_url, location)
            if "code=" in next_url and "state=" in next_url:
                token_json = submit_callback_url(
                    callback_url=next_url,
                    code_verifier=oauth.code_verifier,
                    redirect_uri=oauth.redirect_uri,
                    expected_state=oauth.state,
                )
                return token_json, password
            current_url = next_url

        print("[Error] 未能在重定向链中捕获到最终 Callback URL")
        return None, None

    except Exception as e:
        print(f"[Error] 运行时发生错误: {e}")
        return None, None


def main() -> None:
    parser = argparse.ArgumentParser(description="OpenAI 自动注册脚本")
    parser.add_argument(
        "--proxy", default=None, help="代理地址，如 http://127.0.0.1:7890"
    )
    parser.add_argument(
        "--proxies-file",
        default="proxies.txt",
        help="代理列表文件路径（每行一个代理，支持 # 注释）",
    )
    parser.add_argument("--once", action="store_true", help="只运行一次")
    parser.add_argument("--sleep-min", type=int, default=5, help="循环模式最短等待秒数")
    parser.add_argument(
        "--sleep-max", type=int, default=30, help="循环模式最长等待秒数"
    )
    args = parser.parse_args()

    sleep_min = max(1, args.sleep_min)
    sleep_max = max(sleep_min, args.sleep_max)

    count = 0
    print("[Info] Yasal's Seamless OpenAI Auto-Registrar Started for ZJH")
    print()
    print("=" * 60)
    print("  🔥 本脚本由 gaojilingjuli 出品")
    print("  📺 YouTube: https://www.youtube.com/@gaojilingjuli")
    print("  ⭐ 觉得好用？订阅频道支持一下！更多好用工具持续更新中~")
    print("=" * 60)
    print()

    while True:
        count += 1
        print(
            f"\n[{datetime.now().strftime('%H:%M:%S')}] >>> 开始第 {count} 次注册流程 <<<"
        )

        try:
            selected_proxy = _normalize_proxy_value(args.proxy or "")
            if selected_proxy:
                print(f"[*] 使用命令行代理: {selected_proxy}")
            else:
                file_proxies = _load_proxies_from_file(args.proxies_file)
                if file_proxies:
                    selected_proxy = file_proxies[(count - 1) % len(file_proxies)]
                    print(
                        f"[*] 使用文件代理({args.proxies_file}) [{(count - 1) % len(file_proxies) + 1}/{len(file_proxies)}]: {selected_proxy}"
                    )
                else:
                    if args.proxies_file:
                        print(
                            f"[*] 未检测到可用文件代理({args.proxies_file})，将直连运行"
                        )

            token_json, password = run(selected_proxy or None)

            if token_json == "retry_403":
                print("[Info] 检测到 403 错误，等待10秒后重试...")
                time.sleep(10)
                continue

            if token_json:
                try:
                    t_data = json.loads(token_json)
                    fname_email = t_data.get("email", "unknown").replace("@", "_")
                    account_email = t_data.get("email", "")
                except Exception:
                    fname_email = "unknown"
                    account_email = ""

                file_name = f"token_{fname_email}_{int(time.time())}.json"
                if TOKEN_OUTPUT_DIR:
                    os.makedirs(TOKEN_OUTPUT_DIR, exist_ok=True)
                    file_name = os.path.join(TOKEN_OUTPUT_DIR, file_name)

                with open(file_name, "w", encoding="utf-8") as f:
                    f.write(token_json)

                print(f"[*] 成功! Token 已保存至: {file_name}")

                # 追加记录账号密码
                if account_email and password:
                    os.makedirs(KEYS_DIR, exist_ok=True)
                    accounts_file = os.path.join(KEYS_DIR, "accounts.txt")
                    with open(accounts_file, "a", encoding="utf-8") as af:
                        af.write(f"{account_email}----{password}\n")
                    print(f"[*] 账号密码已追加至: {accounts_file}")
            else:
                print("[-] 本次注册失败。")

        except Exception as e:
            print(f"[Error] 发生未捕获异常: {e}")

        if args.once:
            break

        wait_time = random.randint(sleep_min, sleep_max)
        print(f"[*] 休息 {wait_time} 秒...")
        time.sleep(wait_time)


if __name__ == "__main__":
    main()
