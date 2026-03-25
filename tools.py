import discord
from discord import app_commands
from discord.ext import commands, tasks
import keepa
import matplotlib.pyplot as plt
import numpy as np
import requests
from io import BytesIO
from datetime import datetime, timedelta, timezone
from PIL import Image
from pyzbar.pyzbar import decode
from dotenv import load_dotenv
import os
import json
import time
from sp_api.api import Products, CatalogItems
from sp_api.base import Marketplaces, SellingApiException
from decimal import Decimal, ROUND_HALF_UP
import logging
import urllib.parse
import csv
from watchdog.observers import Observer
from watchdog.events import FileSystemEventHandler
from discord.ui import Select, Modal, TextInput, Button, View
from discord import SelectOption, TextStyle, ButtonStyle, ChannelType
import random
import re
import asyncio
import threading
import aiohttp
import io
import fcntl
import pandas as pd
from pathlib import Path
from typing import Dict, List, Optional
import unicodedata
from difflib import SequenceMatcher
import sqlite3
import hashlib
from contextlib import closing

BASE_DIR = "/root/Tools-Bot"

# --- Keepa safety knobs ---
MAX_KEEPA_QUERIES = int(os.getenv("MAX_KEEPA_QUERIES", "200"))
TARGET_RESULTS = int(os.getenv("TARGET_RESULTS", "30"))
BATCH_SIZE = 5

# --- Qogita knobs ---
QOGITA_MAX_PER_RUN = 250
QOGITA_CACHE_TTL_H = 24

# Logging setup
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
    handlers=[logging.StreamHandler()]
)
logger = logging.getLogger(__name__)

# Directories
CACHE_DIR = os.path.join(BASE_DIR, "cache")
LOG_DIR = os.path.join(BASE_DIR, "logs")
TEMP_DIR = os.path.join(BASE_DIR, "temp")

os.makedirs(LOG_DIR, exist_ok=True)
os.makedirs(TEMP_DIR, exist_ok=True)
os.makedirs(CACHE_DIR, exist_ok=True)

# --- SQLite path ---
QOGITA_DB_PATH = os.path.join(BASE_DIR, "qogita_cache.db")

# File-based logging for detailed Keepa responses
KEEPA_LOG_FILE = os.path.join(LOG_DIR, f"keepa_responses_{datetime.now(timezone.utc).date().isoformat()}.log")
file_handler = logging.FileHandler(KEEPA_LOG_FILE)
file_handler.setLevel(logging.DEBUG)
file_handler.setFormatter(logging.Formatter("%(asctime)s - %(levelname)s - %(message)s"))
logging.getLogger().addHandler(file_handler)

# Load environment variables
load_dotenv()
KEEPA_API_KEY = os.getenv('KEEPA_API_KEY')
DISCORD_BOT_TOKEN = os.getenv('DISCORD_BOT_TOKEN')
GUILD_ID = 1264672155652587562
PAID_ROLE_ID = 1269034801567105248
WELCOME_CHANNEL_ID = 1269036878880047266
SP_API_CREDENTIALS = {
    "refresh_token": os.getenv("refresh_token"),
    "lwa_app_id": os.getenv("lwa_app_id"),
    "lwa_client_secret": os.getenv("lwa_client_secret"),
    "aws_access_key": os.getenv("aws_access_key"),
    "aws_secret_key": os.getenv("aws_secret_key"),
    "role_arn": os.getenv("role_arn")
}
EU_SP_API_CREDENTIALS = {
    "refresh_token": os.getenv("EU_REFRESH_TOKEN"),
    "lwa_app_id": os.getenv("EU_LWA_APP_ID"),
    "lwa_client_secret": os.getenv("EU_LWA_CLIENT_SECRET"),
    "aws_access_key": os.getenv("EU_AWS_ACCESS_KEY"),
    "aws_secret_key": os.getenv("EU_AWS_SECRET_KEY"),
    "role_arn": os.getenv("EU_ROLE_ARN")
}
MARKETPLACE_ID = os.getenv("marketplace_id", "A1F83G8C2ARO7P")
EU_MARKETPLACE_ID = os.getenv("EU_MARKETPLACE_ID", "A1F83G8C2ARO7P")
OFFER_CACHE_FILE = os.path.join(BASE_DIR, "offer_cache.json")
SEARCH_HISTORY_FILE = os.path.join(BASE_DIR, "search_history.json")
SEARCH_HISTORY_LOCK = threading.Lock()
QOGITA_EMAIL = os.getenv("QOGITA_EMAIL")
QOGITA_PASSWORD = os.getenv("QOGITA_PASSWORD")

# Validate environment variables
required_vars = {
    "QOGITA_EMAIL": QOGITA_EMAIL,
    "QOGITA_PASSWORD": QOGITA_PASSWORD,
    "DISCORD_BOT_TOKEN": DISCORD_BOT_TOKEN,
    "KEEPA_API_KEY": KEEPA_API_KEY
}
missing_vars = [k for k, v in required_vars.items() if not v]
if missing_vars:
    logging.error(f"Missing environment variables: {', '.join(missing_vars)}")
    raise ValueError(f"Missing environment variables: {', '.join(missing_vars)}")

logging.info(f"Loaded KEEPA_API_KEY ending in …{KEEPA_API_KEY[-5:]}")

# Qogita API settings
API_BASE_URL = "https://api.qogita.com"
HEADERS = None

# Global token state
current_token = None
token_expiry = None

# File paths for output and caching
TEMP_RESULTS_FILE = os.path.join(TEMP_DIR, f"temp_results_{datetime.now(timezone.utc).date().isoformat()}.json")
SKIPPED_PRODUCTS_FILE = os.path.join(TEMP_DIR, f"skipped_products_{datetime.now(timezone.utc).date().isoformat()}.json")

# Keepa UK domain constant
UK_DOMAIN_ID = 2


# --------------------------------------------------------------------------- #
# SQLite helpers (Qogita cache + skip reasons)                                #
# --------------------------------------------------------------------------- #
def init_db():
    try:
        with closing(sqlite3.connect(QOGITA_DB_PATH)) as conn:
            conn.execute("""
                CREATE TABLE IF NOT EXISTS variants (
                    fid TEXT PRIMARY KEY,
                    name TEXT,
                    slug TEXT,
                    image_url TEXT,
                    gtin TEXT,
                    brand TEXT,
                    category TEXT,
                    last_price REAL,
                    inventory INTEGER,
                    min_order_quantity INTEGER,
                    last_seen INTEGER
                )
            """)
            conn.execute("""
                CREATE TABLE IF NOT EXISTS search_cache (
                    criteria_key TEXT,
                    fid TEXT,
                    last_seen INTEGER,
                    PRIMARY KEY(criteria_key, fid)
                )
            """)
            conn.execute("""
                CREATE TABLE IF NOT EXISTS skips (
                    gtin TEXT PRIMARY KEY,
                    reason TEXT,
                    expiry INTEGER
                )
            """)
            conn.execute("""
                CREATE TABLE IF NOT EXISTS keyword_pingers (
                    user_id INTEGER NOT NULL,
                    keyword TEXT NOT NULL,
                    channel_id INTEGER NOT NULL,
                    created_at INTEGER NOT NULL,
                    PRIMARY KEY(user_id, keyword, channel_id)
                )
            """)
            conn.execute("CREATE INDEX IF NOT EXISTS idx_search_last_seen ON search_cache(last_seen)")
            conn.execute("CREATE INDEX IF NOT EXISTS idx_variants_last_seen ON variants(last_seen)")
            conn.execute("CREATE INDEX IF NOT EXISTS idx_keyword_channel ON keyword_pingers(channel_id)")
            conn.commit()
    except Exception as e:
        logging.error(f"Failed to init SQLite DB: {e}")


def now_epoch() -> int:
    return int(time.time())


def criteria_key_for(brand: str, max_price: Optional[float]) -> str:
    key = f"{(brand or '').strip().lower()}|{'' if max_price is None else round(float(max_price),2)}"
    return hashlib.sha256(key.encode()).hexdigest()


def cache_upsert_variant(v: dict):
    try:
        with closing(sqlite3.connect(QOGITA_DB_PATH)) as conn:
            conn.execute("""
                INSERT INTO variants (fid, name, slug, image_url, gtin, brand, category, last_price, inventory, min_order_quantity, last_seen)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(fid) DO UPDATE SET
                    name=excluded.name,
                    slug=excluded.slug,
                    image_url=excluded.image_url,
                    gtin=excluded.gtin,
                    brand=excluded.brand,
                    category=excluded.category,
                    last_price=excluded.last_price,
                    inventory=excluded.inventory,
                    min_order_quantity=excluded.min_order_quantity,
                    last_seen=excluded.last_seen
            """, (
                v.get("fid"), v.get("name"), v.get("slug"), v.get("image_url"),
                v.get("gtin"), v.get("brand"), v.get("category"),
                v.get("buy_price"), v.get("inventory_units"), v.get("min_order_quantity"),
                now_epoch()
            ))
            conn.commit()
    except Exception as e:
        logging.error(f"Failed to upsert variant {v.get('fid')}: {e}")


def cache_record_search(criteria_key: str, fid: str):
    try:
        with closing(sqlite3.connect(QOGITA_DB_PATH)) as conn:
            conn.execute("""
                INSERT INTO search_cache (criteria_key, fid, last_seen)
                VALUES (?, ?, ?)
                ON CONFLICT(criteria_key, fid) DO UPDATE SET
                    last_seen=excluded.last_seen
            """, (criteria_key, fid, now_epoch()))
            conn.commit()
    except Exception as e:
        logging.error(f"Failed to record search hit {fid} for {criteria_key}: {e}")


def load_cached_search(criteria_key: str, max_age_hours: int = QOGITA_CACHE_TTL_H) -> List[dict]:
    cutoff = now_epoch() - max_age_hours * 3600
    try:
        with closing(sqlite3.connect(QOGITA_DB_PATH)) as conn:
            rows = conn.execute("""
                SELECT v.fid, v.name, v.slug, v.image_url, v.gtin, v.brand, v.category,
                       v.last_price, v.inventory, v.min_order_quantity
                FROM search_cache sc
                JOIN variants v ON v.fid = sc.fid
                WHERE sc.criteria_key = ? AND sc.last_seen >= ?
                ORDER BY sc.last_seen DESC
            """, (criteria_key, cutoff)).fetchall()
        products = []
        for r in rows:
            fid, name, slug, image_url, gtin, brand, category, price, inventory, moq = r
            if not gtin:
                gtin = "N/A"
            products.append({
                "id": fid,
                "name": name,
                "product_url": f"https://www.qogita.com/products/{fid}/{slug}/",
                "image_url": image_url,
                "gtin": gtin,
                "brand": brand,
                "category": category,
                "buy_price": float(price) if price is not None else None,
                "inventory": f"{inventory or 0} units",
                "min_order_quantity": moq or 1
            })
        if products:
            logging.info(f"Loaded {len(products)} cached product(s) for criteria {criteria_key}")
        return products
    except Exception as e:
        logging.error(f"Failed to load cached search for {criteria_key}: {e}")
        return []


def save_skipped_product(gtin, reason):
    try:
        gtin = str(gtin)
        reason = str(reason)
        reason_l = reason.lower()

        seven_day_reasons = (
            "no uk asin",
            "no keepa data",
            "no valid asin",
            "no acceptable uk asin",
            "title mismatch",
            "title mismatch after gtin check",
            "no buy box price"
        )
        three_day_reasons = (
            "monthly sales",
            "profit",
            "roi",
            "sellers"
        )

        if any(s in reason_l for s in seven_day_reasons):
            expiry = now_epoch() + 7 * 24 * 3600
        elif any(s in reason_l for s in three_day_reasons):
            expiry = now_epoch() + 3 * 24 * 3600
        else:
            expiry = now_epoch() + 3 * 24 * 3600

        with closing(sqlite3.connect(QOGITA_DB_PATH)) as conn:
            conn.execute("""
                INSERT INTO skips (gtin, reason, expiry)
                VALUES (?, ?, ?)
                ON CONFLICT(gtin) DO UPDATE SET
                    reason=excluded.reason,
                    expiry=excluded.expiry
            """, (gtin, reason, expiry))
            conn.commit()
        logging.info(f"Saved skip for GTIN {gtin}: {reason} (until {datetime.fromtimestamp(expiry, tz=timezone.utc).isoformat()})")
    except Exception as e:
        logging.error(f"Failed to save skipped product GTIN {gtin}: {e}")


def check_skipped_product(gtin):
    try:
        gtin = str(gtin)
        with closing(sqlite3.connect(QOGITA_DB_PATH)) as conn:
            row = conn.execute("SELECT reason, expiry FROM skips WHERE gtin = ?", (gtin,)).fetchone()
            if not row:
                return None
            reason, expiry = row
            if expiry and expiry > now_epoch():
                return reason
            conn.execute("DELETE FROM skips WHERE gtin = ?", (gtin,))
            conn.commit()
            return None
    except Exception as e:
        logging.error(f"Failed to check skipped product GTIN {gtin}: {e}")
        return None


init_db()

KEYWORD_ALLOWED_CHANNEL_IDS = {
    1265414863384084490,
    1369779123949539458,
    1418877365005582367,
    1483178233095651539,
    1265414756206903400,
    1478084254687825980,
    1469846994641223784,
    1469847414738387191,
    1469847611451375780,
}

KEYWORD_ALLOWED_CATEGORY_IDS = {
    1265415271586201834,
    1428092841082486895,
    1280219378809311334,
}


# --------------------------------------------------------------------------- #
# helpers                                                                     #
# --------------------------------------------------------------------------- #
ALNUM = re.compile(r"[a-z0-9]+")
UNIT_MERGE = re.compile(r"(\d+)\s*([a-z]{1,4})")
VOL_RE = re.compile(r"\b(\d+(?:\.\d+)?)(ml|g|kg|l|oz)\b", re.I)
VARIANT_RE = re.compile(r"\b(pink|original|lemon|tuberose|bleach|ammonia)\b", re.I)


def normalize_title(title: str) -> List[str]:
    txt = unicodedata.normalize("NFKD", title).encode("ascii", "ignore").decode().lower()
    txt = UNIT_MERGE.sub(r"\1\2", txt)
    tokens = ALNUM.findall(txt)
    return tokens


def size_token(text: str) -> str:
    m = VOL_RE.search(text)
    return m.group(0).lower().replace(" ", "") if m else ""


def variant_token(text: str) -> str:
    m = VARIANT_RE.search(text)
    return m.group(0).lower() if m else ""


def normalize_keyword(keyword: str) -> str:
    return " ".join((keyword or "").strip().lower().split())


def save_keyword_pinger(user_id: int, keyword: str, channel_ids: List[int]) -> int:
    keyword = normalize_keyword(keyword)
    if not keyword or not channel_ids:
        return 0

    rows_written = 0
    try:
        with closing(sqlite3.connect(QOGITA_DB_PATH)) as conn:
            for channel_id in channel_ids:
                cursor = conn.execute("""
                    INSERT INTO keyword_pingers (user_id, keyword, channel_id, created_at)
                    VALUES (?, ?, ?, ?)
                    ON CONFLICT(user_id, keyword, channel_id) DO NOTHING
                """, (int(user_id), keyword, int(channel_id), now_epoch()))
                rows_written += cursor.rowcount
            conn.commit()
    except Exception as e:
        logger.error(f"Failed to save keyword pinger for user {user_id}: {e}")
    return rows_written


def get_keyword_pingers_for_channel(channel_id: int) -> List[tuple]:
    try:
        with closing(sqlite3.connect(QOGITA_DB_PATH)) as conn:
            return conn.execute("""
                SELECT user_id, keyword
                FROM keyword_pingers
                WHERE channel_id = ?
            """, (int(channel_id),)).fetchall()
    except Exception as e:
        logger.error(f"Failed to load keyword pingers for channel {channel_id}: {e}")
        return []


def _attrs_ok(q: Dict[str, str], k: Dict[str, str]) -> bool:
    q_size = q.get("size") or size_token(q.get("raw", ""))
    k_size = k.get("size") or size_token(k.get("raw", ""))
    if q_size and k_size and q_size != k_size:
        return False
    q_variant = variant_token(q.get("raw", ""))
    k_variant = variant_token(k.get("raw", ""))
    if q_variant and k_variant and q_variant != k_variant:
        return False
    return True


def normalize_brand(s: str) -> str:
    return " ".join(normalize_title(s or ""))


def brand_matches(user_brand: str, candidate_brand: str, candidate_name: str) -> bool:
    ub = normalize_brand(user_brand)
    cb = normalize_brand(candidate_brand)
    cn = " ".join(normalize_title(candidate_name))
    if not ub:
        return True
    if ub and (ub in cb or ub in cn):
        return True
    if SequenceMatcher(None, ub, cb).ratio() >= 0.72:
        return True
    return False


def slugify(text: str) -> str:
    text = (text or "").strip().lower()
    text = unicodedata.normalize("NFKD", text).encode("ascii", "ignore").decode()
    text = re.sub(r"[^a-z0-9]+", "-", text).strip("-")
    return text or "product"


# --------------------------------------------------------------------------- #
# choose the right Keepa product for a GTIN                                   #
# --------------------------------------------------------------------------- #
def select_keepa_product(gtin: str, qogita_title: str, keepa_products: List[Dict], qogita_brand: str = "") -> Optional[Dict]:
    if not gtin or not qogita_title or not keepa_products:
        logging.info(f"Invalid input for GTIN {gtin}: gtin={bool(gtin)}, title={bool(qogita_title)}, products={len(keepa_products)}")
        return None

    logging.info(f"Products for GTIN {gtin}: {[p.get('asin') for p in keepa_products]}")

    uk = [p for p in keepa_products if p.get("domainId") == UK_DOMAIN_ID]
    logging.info(f"UK products for GTIN {gtin}: {[p.get('asin') for p in uk]}")
    if not uk:
        logging.info("No UK products in Keepa response")
        return None

    exact_matches = [p for p in uk if gtin in p.get("eanList", [])]
    logging.info(f"Exact GTIN matches for {gtin}: {[p.get('asin') for p in exact_matches]}")
    if not exact_matches:
        logging.info("No exact GTIN matches in UK Keepa response")
        return None

    q_tokens = set(normalize_title(qogita_title))
    q_brand = qogita_brand.lower()
    candidates = []

    for p in exact_matches:
        title = p.get("title", "")
        bp = p.get("brand", "").lower()
        logging.info(f"Evaluating product: ASIN {p.get('asin')}, Title: {title}, Brand: {bp}")

        if q_brand and q_brand not in bp:
            logging.info(f"Skipping ASIN {p.get('asin')}: brand mismatch (qogita_brand={q_brand}, keepa_brand={bp})")
            continue

        k_tokens = set(normalize_title(title))
        overlap = (len(q_tokens & k_tokens) / len(q_tokens)) * 100 if q_tokens else 0

        if not _attrs_ok({"raw": qogita_title}, {"raw": title}):
            logging.info(f"Skipping ASIN {p.get('asin')}: attribute mismatch")
            continue

        if overlap < 50:
            logging.info(f"Skipping ASIN {p['asin']}: only {overlap:.0f}% title overlap")
            continue

        stats = p.get("stats", {})
        bb90 = stats.get("avg90", [0] * 19)[18] if isinstance(stats.get("avg90"), list) else 0
        has_data = bb90 > 0

        candidates.append((p, overlap, has_data, len(title)))
        logging.info(f"Added candidate: ASIN {p.get('asin')}, Overlap: {overlap:.2f}%, Has Data: {has_data}, Title Length: {len(title)}")

    if not candidates:
        logging.warning(f"No candidates for GTIN {gtin}")
        return None

    candidates.sort(key=lambda x: (-x[1], -int(x[2]), -x[3]))
    best = candidates[0][0]
    logging.info(f"Selected Keepa '{best['title']}' (ASIN {best['asin']}) with overlap {candidates[0][1]:.2f}%")
    return best


def save_temp_results(interaction_id, filtered_products, search_params):
    try:
        temp_entry = {
            "interaction_id": str(interaction_id),
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "products": filtered_products,
            "search_params": search_params
        }
        if os.path.exists(TEMP_RESULTS_FILE):
            file_stat = os.stat(TEMP_RESULTS_FILE)
            file_age_seconds = time.time() - file_stat.st_ctime
            if file_age_seconds > 4 * 60 * 60:
                logging.info(f"Deleting {TEMP_RESULTS_FILE} as it is older than 4 hours")
                os.remove(TEMP_RESULTS_FILE)

        mode = 'r+' if os.path.exists(TEMP_RESULTS_FILE) else 'w+'
        with open(TEMP_RESULTS_FILE, mode) as f:
            fcntl.flock(f.fileno(), fcntl.LOCK_EX)
            try:
                f.seek(0)
                existing_content = f.read()
                f.seek(0)
                f.truncate()
                if existing_content:
                    f.write(existing_content.rstrip(']') + ',\n' + json.dumps(temp_entry) + '\n]')
                else:
                    f.write('[\n' + json.dumps(temp_entry) + '\n]')
            finally:
                fcntl.flock(f.fileno(), fcntl.LOCK_UN)
        logging.info(f"Saved temporary results for interaction {interaction_id}")
    except Exception as e:
        logging.error(f"Failed to save temporary results for interaction {interaction_id}: {e}")


def load_temp_results(interaction_id):
    try:
        if not os.path.exists(TEMP_RESULTS_FILE):
            return None
        with open(TEMP_RESULTS_FILE, "r") as f:
            fcntl.flock(f.fileno(), fcntl.LOCK_SH)
            try:
                data = json.load(f)
                for entry in data:
                    if entry["interaction_id"] == str(interaction_id):
                        return entry["products"], entry["search_params"]
                return None
            finally:
                fcntl.flock(f.fileno(), fcntl.LOCK_UN)
    except Exception as e:
        logging.error(f"Failed to load temporary results for interaction {interaction_id}: {e}")
        return None


def delete_temp_results(interaction_id):
    try:
        if not os.path.exists(TEMP_RESULTS_FILE):
            return
        with open(TEMP_RESULTS_FILE, "r") as f:
            fcntl.flock(f.fileno(), fcntl.LOCK_EX)
            try:
                data = json.load(f)
                data = [entry for entry in data if entry["interaction_id"] != str(interaction_id)]
                with open(TEMP_RESULTS_FILE, "w") as f_out:
                    json.dump(data, f_out)
            finally:
                fcntl.flock(f.fileno(), fcntl.LOCK_UN)
        logging.info(f"Deleted temporary results for interaction {interaction_id}")
    except Exception as e:
        logging.error(f"Failed to delete temporary results for interaction {interaction_id}: {e}")


def convert_numpy_types(obj):
    if isinstance(obj, pd.DataFrame):
        return obj.to_dict(orient="records")
    if isinstance(obj, np.ndarray):
        return obj.tolist()
    if isinstance(obj, np.integer):
        return int(obj)
    if isinstance(obj, np.floating):
        return float(obj)
    if isinstance(obj, dict):
        return {key: convert_numpy_types(value) for key, value in obj.items()}
    if isinstance(obj, list):
        return [convert_numpy_types(item) for item in obj]
    return obj


async def get_access_token():
    url = f"{API_BASE_URL}/auth/login/"
    payload = {"email": QOGITA_EMAIL, "password": QOGITA_PASSWORD}
    headers = {
        "Accept": "application/json",
        "Content-Type": "application/json"
    }

    logging.debug(f"→ POST {url}")
    logging.debug(f"  Headers: {headers}")
    logging.debug(f"  Body:    {json.dumps(payload)}")

    async with aiohttp.ClientSession() as session:
        async with session.post(url, headers=headers, json=payload) as resp:
            body = await resp.text()
            logging.debug(f"← Status {resp.status}")
            logging.debug(f"← Body   {body!r}")

            if resp.status != 200:
                raise Exception(f"Auth failed ({resp.status}): {body}")

            data = json.loads(body)
            token = data.get("accessToken")
            exp_ms = data.get("accessExp")

            if not token or not exp_ms:
                raise Exception(f"Unexpected auth response: {data!r}")

            expiry = datetime.fromtimestamp(exp_ms / 1000, tz=timezone.utc)
            return token, expiry


async def initialize_token():
    global current_token, token_expiry, HEADERS
    logging.debug(f"QOGITA_EMAIL: '{QOGITA_EMAIL}'")
    logging.debug(f"QOGITA_PASSWORD: '***hidden***'")
    if not (QOGITA_EMAIL and QOGITA_PASSWORD):
        raise Exception("Missing Qogita credentials")
    current_token, token_expiry = await get_access_token()
    logging.info(f"Got Qogita token; expires at {token_expiry.isoformat()}")
    HEADERS = {
        "Accept": "application/json",
        "Authorization": f"Bearer {current_token}"
    }


class NextItemButton(discord.ui.Button):
    def __init__(self, products, current_index, total_products, interaction_id, brand, max_price, min_roi, min_profit, min_sellers, min_spm):
        super().__init__(label="Next Item", style=discord.ButtonStyle.primary)
        self.products = products
        self.current_index = current_index
        self.total_products = total_products
        self.interaction_id = interaction_id
        self.brand = brand
        self.max_price = max_price
        self.min_roi = min_roi
        self.min_profit = min_profit
        self.min_sellers = min_sellers
        self.min_spm = min_spm

    async def callback(self, interaction: discord.Interaction):
        await interaction.response.defer()
        if self.current_index < self.total_products - 1:
            self.current_index += 1
            embed = await create_embed(self.products[self.current_index], self.current_index, self.total_products)
            view = create_view(self.products, self.current_index, self.total_products, self.interaction_id, self.brand, self.max_price, self.min_roi, self.min_profit, self.min_sellers, self.min_spm)
            graph_bytes = await download_keepa_graph(self.products[self.current_index]["asin"])
            if graph_bytes:
                embed.set_image(url="attachment://keepa_graph.png")
                file = discord.File(fp=io.BytesIO(graph_bytes), filename="keepa_graph.png")
                try:
                    await interaction.edit_original_response(embed=embed, view=view, attachments=[file])
                except discord.HTTPException:
                    await interaction.followup.send(embed=embed, view=view, file=file, ephemeral=True)
            else:
                try:
                    await interaction.edit_original_response(embed=embed, view=view, attachments=[])
                except discord.HTTPException:
                    await interaction.followup.send(embed=embed, view=view, ephemeral=True)
        else:
            await interaction.edit_original_response(view=create_view(self.products, self.current_index, self.total_products, self.interaction_id, self.brand, self.max_price, self.min_roi, self.min_profit, self.min_sellers, self.min_spm))


class PreviousItemButton(discord.ui.Button):
    def __init__(self, products, current_index, total_products, interaction_id, brand, max_price, min_roi, min_profit, min_sellers, min_spm):
        super().__init__(label="Previous Item", style=discord.ButtonStyle.primary)
        self.products = products
        self.current_index = current_index
        self.total_products = total_products
        self.interaction_id = interaction_id
        self.brand = brand
        self.max_price = max_price
        self.min_roi = min_roi
        self.min_profit = min_profit
        self.min_sellers = min_sellers
        self.min_spm = min_spm

    async def callback(self, interaction: discord.Interaction):
        await interaction.response.defer()
        if self.current_index > 0:
            self.current_index -= 1
            embed = await create_embed(self.products[self.current_index], self.current_index, self.total_products)
            view = create_view(self.products, self.current_index, self.total_products, self.interaction_id, self.brand, self.max_price, self.min_roi, self.min_profit, self.min_sellers, self.min_spm)
            graph_bytes = await download_keepa_graph(self.products[self.current_index]["asin"])
            if graph_bytes:
                embed.set_image(url="attachment://keepa_graph.png")
                file = discord.File(fp=io.BytesIO(graph_bytes), filename="keepa_graph.png")
                try:
                    await interaction.edit_original_response(embed=embed, view=view, attachments=[file])
                except discord.HTTPException:
                    await interaction.followup.send(embed=embed, view=view, file=file, ephemeral=True)
            else:
                try:
                    await interaction.edit_original_response(embed=embed, view=view, attachments=[])
                except discord.HTTPException:
                    await interaction.followup.send(embed=embed, view=view, ephemeral=True)
        else:
            await interaction.edit_original_response(view=create_view(self.products, self.current_index, self.total_products, self.interaction_id, self.brand, self.max_price, self.min_roi, self.min_profit, self.min_sellers, self.min_spm))


class DismissButton(discord.ui.Button):
    def __init__(self, interaction_id):
        super().__init__(label="Dismiss Message", style=discord.ButtonStyle.danger)
        self.interaction_id = interaction_id

    async def callback(self, interaction: discord.Interaction):
        await interaction.response.defer()
        delete_temp_results(self.interaction_id)
        await interaction.edit_original_response(content="Results dismissed.", embed=None, view=None, attachments=[])


class DownloadResultsButton(discord.ui.Button):
    def __init__(self, interaction_id: int):
        super().__init__(label="Download Results (CSV)", style=discord.ButtonStyle.secondary, emoji="📥")
        self.interaction_id = interaction_id

    async def callback(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)

        loaded = load_temp_results(self.interaction_id)
        if not loaded:
            await interaction.followup.send(
                "Sorry — I couldn't find those results (they may have been dismissed or expired).",
                ephemeral=True
            )
            return

        products, _search_params = loaded

        fieldnames = [
            "name", "asin", "gtin", "brand", "category",
            "inventory", "min_order_quantity", "sellers", "est_sales", "sales_rank",
            "buy_price", "avg90_price", "profit", "roi",
            "product_url", "image_url"
        ]

        output = io.StringIO()
        writer = csv.DictWriter(output, fieldnames=fieldnames, extrasaction="ignore")
        writer.writeheader()
        for p in products:
            writer.writerow({
                "name": p.get("name"),
                "asin": p.get("asin"),
                "gtin": p.get("gtin"),
                "brand": p.get("brand"),
                "category": p.get("category"),
                "inventory": p.get("inventory"),
                "min_order_quantity": p.get("min_order_quantity"),
                "sellers": p.get("sellers"),
                "est_sales": p.get("est_sales"),
                "sales_rank": p.get("sales_rank"),
                "buy_price": p.get("buy_price"),
                "avg90_price": p.get("avg90_price"),
                "profit": p.get("profit"),
                "roi": p.get("roi"),
                "product_url": p.get("product_url"),
                "image_url": p.get("image_url"),
            })

        csv_bytes = output.getvalue().encode("utf-8-sig")
        file = discord.File(io.BytesIO(csv_bytes), filename=f"qogita_results_{self.interaction_id}.csv")
        await interaction.followup.send(content="Here’s your CSV 📄", file=file, ephemeral=True)


def create_view(products, current_index, total_products, interaction_id, brand, max_price, min_roi, min_profit, min_sellers, min_spm):
    view = discord.ui.View()
    if current_index > 0:
        view.add_item(PreviousItemButton(products, current_index, total_products, interaction_id, brand, max_price, min_roi, min_profit, min_sellers, min_spm))
    if current_index < total_products - 1:
        view.add_item(NextItemButton(products, current_index, total_products, interaction_id, brand, max_price, min_roi, min_profit, min_sellers, min_spm))
    view.add_item(DownloadResultsButton(interaction_id))
    view.add_item(DismissButton(interaction_id))
    return view


def calculate_profit_and_roi(buy_price, sale_price, fba_fee, referral_fee, shipping=0, vat_registered=True, closing_fee=0):
    try:
        buy_price = Decimal(str(buy_price)).quantize(Decimal('0.01'), ROUND_HALF_UP)
        sale_price = Decimal(str(sale_price)).quantize(Decimal('0.01'), ROUND_HALF_UP)
        fba_fee = Decimal(str(fba_fee)).quantize(Decimal('0.01'), ROUND_HALF_UP)
        referral_fee = Decimal(str(referral_fee)).quantize(Decimal('0.01'), ROUND_HALF_UP)
        shipping = Decimal(str(shipping)).quantize(Decimal('0.01'), ROUND_HALF_UP)
        closing_fee = Decimal(str(closing_fee)).quantize(Decimal('0.01'), ROUND_HALF_UP)

        total_buy_price = buy_price + shipping
        digital_services_tax = ((fba_fee + referral_fee) * Decimal('0.02')).quantize(Decimal('0.01'), ROUND_HALF_UP)
        total_fees = (fba_fee + referral_fee + digital_services_tax + closing_fee).quantize(Decimal('0.01'), ROUND_HALF_UP)
        vat_on_fees = (total_fees * Decimal('0.20')).quantize(Decimal('0.01'), ROUND_HALF_UP)

        vat_on_sale = (sale_price / Decimal('6')).quantize(Decimal('0.01'), ROUND_HALF_UP)
        vat_on_buy = (total_buy_price / Decimal('6')).quantize(Decimal('0.01'), ROUND_HALF_UP)
        net_vat_pay = (vat_on_sale - vat_on_buy - vat_on_fees).quantize(Decimal('0.01'), ROUND_HALF_UP)
        profit = (sale_price - total_buy_price - total_fees - vat_on_fees - net_vat_pay).quantize(Decimal('0.01'), ROUND_HALF_UP)
        roi = ((profit / total_buy_price) * Decimal('100')).quantize(Decimal('0.01')) if total_buy_price > 0 else Decimal('0')

        return float(profit), float(roi), float(vat_on_fees), float(digital_services_tax)
    except Exception as e:
        logging.error(f"Profit/ROI calculation failed: {e}")
        return 0.0, 0.0, 0.0, 0.0


async def download_keepa_graph(asin):
    url = (
        f"https://api.keepa.com/graphimage?key={KEEPA_API_KEY}&domain=2&asin={asin}"
        "&type=2&amazon=1&new=1&salesrank=1&bb=1&range=90&yzoom=1&width=500&height=200"
        "&cBackground=282830&cFont=ffffff&cAmazon=FFA500&cNew=8888dd&cSales=3a883a&cBB=ff00b4"
    )
    try:
        async with aiohttp.ClientSession() as session:
            async with session.get(url, timeout=10) as r:
                if r.status == 200:
                    logger.info(f"Successfully fetched graph for ASIN {asin}")
                    return await r.read()
                logger.error(f"Graph download failed for {asin}: Status {r.status}, Response: {await r.text()}")
                return None
    except Exception as e:
        logger.error(f"Graph download failed for {asin}: {e}")
        return None


async def create_embed(product, current_index, total_products):
    embed = discord.Embed(
        title=product["name"][:256],
        url=product["product_url"],
        color=0xFFFFFF,
        timestamp=datetime.now(timezone.utc)
    )
    embed.set_thumbnail(url=product["image_url"])
    embed.add_field(name="ASIN", value=f"`{product['asin']}` ❐", inline=True)
    embed.add_field(name="GTIN", value=product["gtin"], inline=True)
    embed.add_field(name="Item", value=f"{current_index + 1} of {total_products}", inline=True)
    embed.add_field(
        name="**Product Information**",
        value=(
            f"Brand: {product['brand']}\n"
            f"Category: {product['category']}\n"
            f"Inventory: {product['inventory']}\n"
            f"Min Order Qty: {product['min_order_quantity']}\n"
            f"Total Sellers: {product['sellers']}\n"
            f"Est. Sales: {product['est_sales']}"
        ),
        inline=False
    )
    embed.add_field(
        name="**Pricing Information**",
        value=(
            f"Buy: £{product['buy_price']:.2f}\n"
            f"90-Day Avg: £{product['avg90_price']:.2f}"
        ),
        inline=False
    )
    embed.add_field(
        name="**Profit & ROI**",
        value=f"Profit: £{product['profit']:.2f} | ROI: {product['roi']:.2f}%",
        inline=False
    )
    embed.add_field(
        name="**Links**",
        value=(
            f"[Keepa](https://keepa.com/#!product/2-{product['asin']}) | "
            f"[SellerAMP](https://sas.selleramp.com/sas/lookup?search_term={product['asin']}) | "
            f"[Google](https://www.google.com/search?q={urllib.parse.quote(product['name'])})"
        ),
        inline=False
    )
    embed.add_field(
        name="**Notes**",
        value="Always conduct your own research before making decisions.",
        inline=False
    )
    embed.set_footer(
        text="Mastermind Arbitrage",
        icon_url="https://cdn.discordapp.com/attachments/1266519400287174658/1268338281150419068/Copy_of_Mastermind.png"
    )
    return embed


async def fetch_products(brand: str, max_price: Optional[float], page_limit: int = 10, page_size: int = 50):
    async with aiohttp.ClientSession() as session:
        url = f"{API_BASE_URL}/variants/offers/search/"

        def base_params():
            p = [
                ("size", page_size),
                ("stock_availability", "in_stock"),
            ]
            if max_price is not None:
                p.append(("price_max", str(max_price)))
            return p

        crit_key = criteria_key_for(brand, max_price)
        products = []
        cached = load_cached_search(crit_key, QOGITA_CACHE_TTL_H)
        seen_fids = set()
        for item in cached:
            products.append(item)
            seen_fids.add(item["id"])
            if len(products) >= QOGITA_MAX_PER_RUN:
                break

        wanted = (brand or "").strip()
        page = 1
        while page <= page_limit and len(products) < QOGITA_MAX_PER_RUN:
            params = base_params() + [("page", page)]
            if wanted:
                params.append(("brand_name", wanted))
            logging.debug(f"→ GET {url} params={params}")
            async with session.get(url, headers=HEADERS, params=params) as resp:
                if resp.status != 200:
                    logging.debug(f"← Status {resp.status} {await resp.text()!r}")
                    break
                data = await resp.json()
                rows = data.get("results", []) or []
                if not rows:
                    break

                for v in rows:
                    if len(products) >= QOGITA_MAX_PER_RUN:
                        break
                    raw_price = v.get("minPrice")
                    try:
                        if raw_price is None:
                            continue
                        buy_price = float(raw_price)
                    except (TypeError, ValueError):
                        continue

                        name = v.get("name", "")
                    cand_brand = v.get("brandName", "")

                    if wanted and not brand_matches(wanted, cand_brand, name):
                        continue
                    if max_price is not None and buy_price > max_price:
                        continue

                    fid = v["fid"]
                    slug = v.get("slug") or slugify(name)

                    item = {
                        "id": fid,
                        "name": name,
                        "product_url": f"https://www.qogita.com/products/{fid}/{slug}/",
                        "image_url": v.get("imageUrl"),
                        "gtin": v.get("gtin", "N/A"),
                        "brand": cand_brand,
                        "category": v.get("categoryName"),
                        "buy_price": buy_price,
                        "inventory": f"{v.get('inventory', 0)} units",
                        "min_order_quantity": v.get("minOrderQuantity", 1)
                    }

                    cache_upsert_variant({
                        "fid": fid,
                        "name": name,
                        "slug": slug,
                        "image_url": v.get("imageUrl"),
                        "gtin": v.get("gtin"),
                        "brand": cand_brand,
                        "category": v.get("categoryName"),
                        "buy_price": buy_price,
                        "inventory_units": v.get("inventory", 0),
                        "min_order_quantity": v.get("minOrderQuantity", 1)
                    })
                    cache_record_search(crit_key, fid)

                    if fid not in seen_fids:
                        products.append(item)
                        seen_fids.add(fid)
            page += 1

        if len(products) < QOGITA_MAX_PER_RUN and wanted:
            page = 1
            while page <= page_limit and len(products) < QOGITA_MAX_PER_RUN:
                params = base_params() + [("page", page)]
                logging.debug(f"→ GET {url} (fallback) params={params}")
                async with session.get(url, headers=HEADERS, params=params) as resp:
                    if resp.status != 200:
                        logging.debug(f"← Status {resp.status} {await resp.text()!r}")
                        break
                    data = await resp.json()
                    rows = data.get("results", []) or []
                    if not rows:
                        break

                    for v in rows:
                        if len(products) >= QOGITA_MAX_PER_RUN:
                            break
                        raw_price = v.get("minPrice")
                        try:
                            if raw_price is None:
                                continue
                            buy_price = float(raw_price)
                        except (TypeError, ValueError):
                            continue

                        name = v.get("name", "")
                        cand_brand = v.get("brandName", "")

                        if not brand_matches(wanted, cand_brand, name):
                            continue
                        if max_price is not None and buy_price > max_price:
                            continue

                        fid = v["fid"]
                        slug = v.get("slug") or slugify(name)

                        item = {
                            "id": fid,
                            "name": name,
                            "product_url": f"https://www.qogita.com/products/{fid}/{slug}/",
                            "image_url": v.get("imageUrl"),
                            "gtin": v.get("gtin", "N/A"),
                            "brand": cand_brand,
                            "category": v.get("categoryName"),
                            "buy_price": buy_price,
                            "inventory": f"{v.get('inventory', 0)} units",
                            "min_order_quantity": v.get("minOrderQuantity", 1)
                        }

                        cache_upsert_variant({
                            "fid": fid,
                            "name": name,
                            "slug": slug,
                            "image_url": v.get("imageUrl"),
                            "gtin": v.get("gtin"),
                            "brand": cand_brand,
                            "category": v.get("categoryName"),
                            "buy_price": buy_price,
                            "inventory_units": v.get("inventory", 0),
                            "min_order_quantity": v.get("minOrderQuantity", 1)
                        })
                        cache_record_search(crit_key, fid)

                        if fid not in seen_fids:
                            products.append(item)
                            seen_fids.add(fid)
                page += 1

        products = products[:QOGITA_MAX_PER_RUN]

        logging.info(f"Retrieved {len(products)} products from Qogita (brand='{brand}', max_price={max_price}) [including cache]")
        return products


def cached_or_none(gtin):
    p = Path(os.path.join(CACHE_DIR, f"keepa_response_{gtin}.json"))
    if p.exists() and time.time() - p.stat().st_mtime < 4 * 3600:
        try:
            data = json.loads(p.read_text())
            logging.info(f"Cache hit for GTIN {gtin}: ASINs {[p.get('asin') for p in data]}")
            return data
        except Exception as e:
            logging.error(f"Failed to load cache for GTIN {gtin}: {e}")
            return None
    logging.info(f"No valid cache for GTIN {gtin}, fetching fresh response")
    return None


async def write_keepa_cache(gtin, response):
    try:
        with open(os.path.join(CACHE_DIR, f"keepa_response_{gtin}.json"), "w") as f:
            json.dump(convert_numpy_types(response), f, indent=2, default=str)
        logging.debug(f"Wrote Keepa response for GTIN {gtin} to cache")
    except Exception as e:
        logging.error(f"Failed to write Keepa cache for GTIN {gtin}: {e}")


def _sum_known_counts(stats):
    counts = []
    for idx in (11, 12, 13, 14):
        try:
            val = stats["current"][idx]
            if val >= 0:
                counts.append(val)
        except (IndexError, TypeError):
            pass
    return sum(counts)


async def filter_with_keepa(products, max_price, min_roi, min_profit, min_sellers, min_spm):
    filtered_products = []
    gtin_to_product: Dict[str, dict] = {}
    gtins_to_query: List[str] = []
    cached_responses: Dict[str, list] = {}
    all_responses: Dict[str, list] = {}

    for product in products:
        gtin = product.get("gtin")
        if not gtin or gtin == "N/A":
            logging.info(f"Skipping product {product.get('name')}: no valid GTIN")
            continue

        skip_reason = check_skipped_product(gtin)
        if skip_reason:
            logging.info(f"Skipping GTIN {gtin}: cached reason - {skip_reason}")
            continue

        prev = gtin_to_product.get(gtin)
        if prev and product["buy_price"] >= prev["buy_price"]:
            continue
        gtin_to_product[gtin] = product

    for gtin, product in gtin_to_product.items():
        cached = cached_or_none(gtin)
        if cached:
            cached_responses[gtin] = cached
        else:
            gtins_to_query.append(gtin)

    gtins_to_query.sort(key=lambda g: gtin_to_product[g]["buy_price"])

    if len(gtins_to_query) > MAX_KEEPA_QUERIES:
        logging.info(f"Capping Keepa queries from {len(gtins_to_query)} → {MAX_KEEPA_QUERIES}")
        gtins_to_query = gtins_to_query[:MAX_KEEPA_QUERIES]

    if not (gtins_to_query or cached_responses):
        return []

    keepa_api = await keepa.AsyncKeepa().create(KEEPA_API_KEY)
    await keepa_api.update_status()
    status = keepa_api.status
    tokens_per_min = status.get("refillRate", 60)
    logging.info(f"Tokens left: {status['tokensLeft']} · Refill rate: {tokens_per_min}/min")
    logging.info(f"Initial tokens: {keepa_api.tokens_left}")

    HTTP_TIMEOUT = 180
    MAX_RETRIES = 4
    RETRY_BACKOFF = 5
    batched_chunks = [gtins_to_query[i:i + BATCH_SIZE] for i in range(0, len(gtins_to_query), BATCH_SIZE)]

    sem = asyncio.Semaphore(3)

    async def fetch(chunk):
        async with sem:
            for attempt in range(MAX_RETRIES + 1):
                try:
                    start_time = time.time()
                    result = await asyncio.wait_for(keepa_api.query(
                        chunk,
                        stats=90,
                        domain="GB",
                        buybox=True,
                        product_code_is_asin=False,
                        history=False,
                        wait=True,
                    ), timeout=HTTP_TIMEOUT)
                    logging.info(f"Keepa query for chunk of {len(chunk)} GTINs succeeded in {time.time() - start_time:.2f}s")
                    return result
                except asyncio.TimeoutError:
                    if attempt == MAX_RETRIES:
                        logging.error(f"Keepa timed out after {attempt} retries (chunk len={len(chunk)})")
                        raise
                    logging.warning(f"Keepa timeout (chunk {len(chunk)} GTINs). Retrying {attempt + 1}/{MAX_RETRIES} …")
                    await asyncio.sleep(RETRY_BACKOFF * (attempt + 1))
                except Exception as e:
                    logging.error(f"Keepa query failed for chunk {len(chunk)} GTINs: {e}")
                    raise

    if batched_chunks:
        batch_results = await asyncio.gather(*[fetch(chunk) for chunk in batched_chunks], return_exceptions=True)
        for idx, result in enumerate(batch_results):
            if isinstance(result, Exception):
                logging.error(f"Batch {idx} (chunk len={len(batched_chunks[idx])}) failed permanently: {result}")
                for gtin in batched_chunks[idx]:
                    save_skipped_product(gtin, f"Batch timeout/error: {str(result)}")
                continue
    else:
        batch_results = []

    batch_idx = 0
    for chunk in batched_chunks:
        resp = batch_results[batch_idx]
        batch_idx += 1

        if isinstance(resp, Exception) or not resp:
            for code in chunk:
                logging.info(f"No Keepa data for GTIN {code} (batch error or empty)")
                save_skipped_product(str(code), "No Keepa data")
                continue

        by_gtin = {str(c): [] for c in chunk}
        for p in resp:
            for e in (p.get("eanList") or []):
                s = str(e)
                if s in by_gtin:
                    by_gtin[s].append(p)

        for code in chunk:
            code_str = str(code)
            prods = by_gtin.get(code_str, [])
            if not prods:
                logging.info(f"No Keepa data for GTIN {code_str}")
                save_skipped_product(code_str, "No Keepa data")
                continue

            all_responses[code_str] = prods
            await write_keepa_cache(code_str, prods)

    all_responses.update(cached_responses)

    for gtin, keepa_response in all_responses.items():
        product = gtin_to_product.get(gtin)
        if not product:
            continue

        try:
            products_list = keepa_response if isinstance(keepa_response, list) else [keepa_response]

            uk_products = [p for p in products_list if p.get("domainId") == UK_DOMAIN_ID]
            if not uk_products:
                logging.info(f"No UK product for GTIN {gtin}")
                save_skipped_product(gtin, "No UK ASIN")
                continue

            match = select_keepa_product(
                gtin,
                product["name"],
                uk_products,
                qogita_brand=product["brand"],
            )
            if match is None:
                logging.info(f"No acceptable UK ASIN for GTIN {gtin} (titles too different)")
                save_skipped_product(gtin, "Title mismatch after GTIN check")
                continue

            asin = match.get("asin")
            if not asin:
                logging.info(f"No valid ASIN for GTIN {gtin}")
                save_skipped_product(gtin, "No valid ASIN")
                continue

            logging.info(f"Selected ASIN {asin} for GTIN {gtin}")

            stats = match.get("stats")
            if not isinstance(stats, dict):
                logging.info(f"Invalid stats for ASIN {asin}: {type(stats)}")
                save_skipped_product(gtin, "Invalid stats")
                continue

            avg90 = stats.get("avg90", [])
            if isinstance(avg90, (list, tuple)) and len(avg90) > 18:
                bb90_cents = avg90[18]
            else:
                bb90_cents = 0
            if bb90_cents <= 0:
                logging.info(f"No 90-day Buy Box price for ASIN {asin}")
                save_skipped_product(gtin, "No Buy Box price")
                continue
            sell_price = bb90_cents / 100

            if sell_price < product["buy_price"]:
                logging.info(f"Skipping ASIN {asin}: sell price £{sell_price} < buy price £{product['buy_price']}")
                save_skipped_product(gtin, f"Sell price £{sell_price} < buy price £{product['buy_price']}")
                continue

            if max_price is not None and product["buy_price"] > max_price:
                logging.info(f"Skipping ASIN {asin}: buy price £{product['buy_price']} > max £{max_price}")
                save_skipped_product(gtin, f"Buy price £{product['buy_price']} > max £{max_price}")
                continue

            referral_pct = match.get("referralFeePercentage", 15)
            referral_fee = sell_price * referral_pct / 100
            fba_fees = match.get("fbaFees", {})
            fba_fee = fba_fees.get("pickAndPackFee", 0) / 100 if fba_fees else 3.0
            closing_fee = 0.50

            monthly_sold = match.get("monthlySold", 0)
            if min_spm is not None and monthly_sold < min_spm:
                logging.info(f"Skipping ASIN {asin}: monthly sales {monthly_sold} < {min_spm}")
                save_skipped_product(gtin, f"Monthly sales {monthly_sold} < {min_spm}")
                continue

            raw_sellers = stats.get("totalOfferCount", -1)
            if raw_sellers < 0:
                raw_sellers = _sum_known_counts(stats)
            sellers = max(raw_sellers, 0)
            if sellers < min_sellers:
                logging.info(f"Skipping ASIN {asin}: sellers {sellers} < {min_sellers}")
                save_skipped_product(gtin, f"Sellers {sellers} < {min_sellers}")
                continue

            profit, roi, _, _ = calculate_profit_and_roi(
                product["buy_price"], sell_price, fba_fee, referral_fee, shipping=0, vat_registered=True, closing_fee=closing_fee
            )

            if min_roi is not None and roi < min_roi:
                logging.info(f"Skipping ASIN {asin}: ROI {roi:.2f}% < {min_roi}%")
                save_skipped_product(gtin, f"ROI {roi:.2f}% < {min_roi}%")
                continue
            if min_profit is not None and profit < min_profit:
                logging.info(f"Skipping ASIN {asin}: profit £{profit:.2f} < £{min_profit}")
                save_skipped_product(gtin, f"Profit £{profit:.2f} < £{min_profit}")
                continue

            bsr_val = stats["current"][3]
            bsr = ("Unavailable" if bsr_val == -1 else f"{bsr_val // 1000}k" if bsr_val >= 1000 else str(bsr_val))
            sales_disp = (f"{monthly_sold // 1000}k+/mo" if monthly_sold >= 1000 else f"{monthly_sold:,}+/mo")

            filtered_products.append({
                **product,
                "asin": asin,
                "avg90_price": float(sell_price),
                "profit": float(profit),
                "roi": float(roi),
                "sellers": sellers,
                "est_sales": sales_disp,
                "sales_rank": bsr
            })
            logging.info(f"Added product {product['name']} (ASIN {asin}) to filtered products")

            if TARGET_RESULTS and len(filtered_products) >= TARGET_RESULTS:
                logging.info(f"Reached TARGET_RESULTS={TARGET_RESULTS}, stopping early.")
                break

        except Exception as e:
            logging.error(f"Error processing GTIN {gtin}: {e}")
            save_skipped_product(gtin, f"Error: {str(e)}")
            continue

    logging.info(f"Keepa tokens remaining: {keepa_api.tokens_left}")
    return filtered_products


class MastermindBot(commands.Bot):
    def __init__(self):
        intents = discord.Intents.default()
        intents.message_content = True
        intents.members = True
        super().__init__(command_prefix='!', intents=intents)

    async def setup_hook(self):
        guild = discord.Object(id=GUILD_ID)
        try:
            await self.tree.sync(guild=guild)
            synced = await self.tree.fetch_commands(guild=guild)
            logger.info(f"Synced {len(synced)} commands to {guild.id}")
            logger.info(f"Synced commands: {[cmd.name for cmd in synced]}")
        except Exception as e:
            logger.error(f"Failed to sync commands: {e}")
        self.cleanup_search_history.start()

    @tasks.loop(hours=24)
    async def cleanup_search_history(self):
        try:
            logger.info("Starting search history cleanup")
            history = load_search_history()
            seven_days_ago = datetime.now(timezone.utc) - timedelta(days=7)
            cleaned_history = [
                entry for entry in history
                if datetime.fromisoformat(entry["timestamp"]) > seven_days_ago
            ]
            if len(history) != len(cleaned_history):
                save_search_history(cleaned_history)
                logger.info(f"Cleaned up {len(history) - len(cleaned_history)} old search history entries")
            else:
                logger.info("No search history entries to clean up")
        except Exception as e:
            logger.error(f"Search history cleanup failed: {e}")

    @cleanup_search_history.before_loop
    async def before_cleanup(self):
        await self.wait_until_ready()


client = MastermindBot()

try:
    keepa_api = keepa.Keepa(KEEPA_API_KEY)
except Exception as e:
    logger.error(f"Failed to initialize Keepa API: {e}")
    exit(1)

try:
    products_api = Products(marketplace=Marketplaces.UK, credentials=SP_API_CREDENTIALS)
except Exception as e:
    logger.error(f"Failed to initialize SP-API Products client: {e}")
    exit(1)

try:
    eu_catalog_client = CatalogItems(credentials=EU_SP_API_CREDENTIALS, marketplace=Marketplaces.UK)
    eu_products_client = Products(credentials=EU_SP_API_CREDENTIALS, marketplace=Marketplaces.UK)
except Exception as e:
    logger.error(f"Failed to initialize SP-API EU clients: {e}")
    exit(1)

# CSV data structures
auto_ungate_brands = {}
ungate_brands = {}
true_stores = []
false_stores = []
store_invoices = {}

# Session data for interactive flows
user_session_data = {}


def load_search_history():
    try:
        with SEARCH_HISTORY_LOCK:
            if not os.path.exists(SEARCH_HISTORY_FILE):
                return []
            with open(SEARCH_HISTORY_FILE, 'r') as f:
                data = json.load(f)
                logger.info(f"Loaded {len(data)} search history entries")
                return data
    except Exception as e:
        logger.error(f"Failed to load search history: {e}")
        return []


def save_search_history(history):
    try:
        with SEARCH_HISTORY_LOCK:
            with open(SEARCH_HISTORY_FILE, 'w') as f:
                json.dump(history, f, indent=2)
            logger.info(f"Saved {len(history)} search history entries")
    except Exception as e:
        logger.error(f"Failed to save search history: {e}")


def add_search_entry(user_id, asin_or_ean, buy_price):
    try:
        history = load_search_history()
        entry = {
            "user_id": str(user_id),
            "asin_or_ean": asin_or_ean,
            "buy_price": buy_price,
            "timestamp": datetime.now(timezone.utc).isoformat()
        }
        history.append(entry)
        save_search_history(history)
        logger.info(f"Secretly added search entry for user {user_id}: {asin_or_ean}")
    except Exception as e:
        logger.error(f"Failed to add search entry for user {user_id}: {e}")


def estimate_fba_fees(buy_price, referral_fee_pct, root_category, fba_fee=3.00):
    buy_price = Decimal(str(buy_price)).quantize(Decimal('0.01'), ROUND_HALF_UP)
    referral_fee = buy_price * Decimal(str(referral_fee_pct)) / Decimal('100')
    fba_fee = Decimal(str(fba_fee)).quantize(Decimal('0.01'), ROUND_HALF_UP)
    closing_fee = Decimal('0.00')
    if root_category == 1025612:
        closing_fee = Decimal('0.50') if buy_price < Decimal('5.00') else Decimal('1.00')
    elif root_category in [110918, 110922, 110934, 110930]:
        closing_fee = Decimal('0.50')
    digital_services_tax = ((fba_fee + referral_fee) * Decimal('0.02')).quantize(Decimal('0.01'), ROUND_HALF_UP)
    total_fees = (fba_fee + referral_fee + closing_fee + digital_services_tax).quantize(Decimal('0.01'), ROUND_HALF_UP)
    vat_on_fees = (total_fees * Decimal('0.2')).quantize(Decimal('0.01'), ROUND_HALF_UP)
    return {
        'fba_fee': float(fba_fee),
        'referral_fee': float(referral_fee),
        'closing_fee': float(closing_fee),
        'digital_services_tax': float(digital_services_tax),
        'vat_on_fees': float(vat_on_fees),
        'total_fees': float(total_fees + vat_on_fees)
    }


def calculate_vat(incl):
    try:
        incl = Decimal(str(incl))
        non_vat_price = incl / Decimal('1.2')
        vat = incl - non_vat_price
        return vat.quantize(Decimal('0.01'), ROUND_HALF_UP), incl.quantize(Decimal('0.01'), ROUND_HALF_UP)
    except Exception as e:
        logger.error(f"VAT calculation failed: {e}")
        return Decimal('0.00'), Decimal('0.00')


def keepa_minutes_to_datetime(m):
    if isinstance(m, datetime):
        return m if m.tzinfo is not None else m.replace(tzinfo=timezone.utc)
    return datetime.fromtimestamp((int(m) + 21_564_000) * 60, tz=timezone.utc)


def download_avatar():
    url = "https://cdn.discordapp.com/attachments/1266519400287174658/1268338281150419068/Copy_of_Mastermind.png"
    try:
        r = requests.get(url, timeout=10)
        if r.status_code == 200:
            logger.info("Successfully downloaded webhook avatar")
            return r.content
        logger.error(f"Avatar download failed: Status {r.status_code}, Response: {r.text}")
        return None
    except Exception as e:
        logger.error(f"Avatar download failed: {e}")
        return None


def load_cache(cache_file):
    try:
        if not os.path.exists(cache_file):
            return {}
        with open(cache_file, 'r') as f:
            cache = json.load(f)
        current_time = time.time()
        valid_entries = {
            k: v for k, v in cache.items()
            if v.get("timestamp", 0) + 900 > current_time
        }
        logger.info(f"Loaded {len(valid_entries)} valid entries from {cache_file}")
        return valid_entries
    except Exception as e:
        logger.error(f"Failed to load cache {cache_file}: {e}")
        return {}


def save_cache(cache, cache_file):
    try:
        with open(cache_file, 'w') as f:
            json.dump(cache, f, indent=2)
        logger.info(f"Saved {len(cache)} entries to {cache_file}")
    except Exception as e:
        logger.error(f"Failed to save cache {cache_file}: {e}")


def serialize_sp_api_response(response):
    try:
        if not response:
            return None
        payload = response.payload
        return {
            "status": payload.get("status"),
            "Summary": {
                "LowestPrices": payload.get("Summary", {}).get("LowestPrices", []),
                "BuyBoxPrices": payload.get("Summary", {}).get("BuyBoxPrices", []),
                "NumberOfOffers": payload.get("Summary", {}).get("NumberOfOffers", []),
                "TotalOfferCount": payload.get("Summary", {}).get("TotalOfferCount", 0),
                "SalesRankings": payload.get("Summary", {}).get("SalesRankings", [])
            },
            "Offers": [
                {
                    "Shipping": o.get("Shipping", {}),
                    "ListingPrice": o.get("ListingPrice", {}),
                    "ShippingTime": o.get("ShippingTime", {}),
                    "SellerFeedbackRating": o.get("SellerFeedbackRating", {}),
                    "PrimeInformation": o.get("PrimeInformation", {}),
                    "SubCondition": o.get("SubCondition"),
                    "SellerId": o.get("SellerId"),
                    "IsFeaturedMerchant": o.get("IsFeaturedMerchant"),
                    "IsBuyBoxWinner": o.get("IsBuyBoxWinner"),
                    "IsFulfilledByAmazon": o.get("IsFulfilledByAmazon"),
                    "quantityDiscountPrices": o.get("quantityDiscountPrices", [])
                } for o in payload.get("Offers", [])
            ],
            "marketplaceId": payload.get("marketplaceId")
        }
    except Exception as e:
        logger.error(f"Failed to serialize SP-API response: {e}")
        return None


def deserialize_sp_api_response(data):
    class ResponseWrapper:
        def __init__(self, payload):
            self.payload = payload
    try:
        return ResponseWrapper(data) if data else None
    except Exception as e:
        logger.error(f"Failed to deserialize SP-API response: {e}")
        return None


def get_offers_with_retry(asin, retries=2, initial_delay=2, max_wait=20):
    global sp_api_request_count, sp_api_last_request_time
    cache = load_cache(OFFER_CACHE_FILE)
    cache_key = f"{asin}_Consumer"
    sp_api_request_count = 0
    sp_api_last_request_time = 0

    if cache_key in cache:
        logger.info(f"Cache hit for SP-API offers for ASIN {asin} (Consumer)")
        return deserialize_sp_api_response(cache[cache_key]["data"])

    total_wait = 0
    delay = initial_delay
    for attempt in range(retries):
        try:
            current_time = time.time()
            time_since_last = current_time - sp_api_last_request_time
            if time_since_last < 3:
                time.sleep(3 - time_since_last)
            logger.debug(f"Attempting SP-API request for ASIN {asin} (Consumer, attempt {attempt + 1}/{retries})")
            response = products_api.get_item_offers(
                asin=asin,
                item_condition='New',
                customer_type='Consumer',
                marketplace_id=MARKETPLACE_ID
            )
            logger.debug(f"SP-API request for ASIN {asin} (Consumer) succeeded")
            sp_api_request_count += 1
            sp_api_last_request_time = time.time()
            cache[cache_key] = {"data": serialize_sp_api_response(response), "timestamp": time.time()}
            save_cache(cache, OFFER_CACHE_FILE)
            time.sleep(3)
            return response
        except SellingApiException as e:
            if isinstance(e.args[0], list) and any(err.get("code") == "QuotaExceeded" for err in e.args[0]):
                if total_wait + delay > max_wait:
                    logger.error(f"Max wait time ({max_wait}s) exceeded for ASIN {asin} (Consumer)")
                    return None
                logger.warning(f"Quota exceeded for ASIN {asin} (Consumer), retrying in {delay}s")
                time.sleep(delay)
                total_wait += delay
                delay *= 2
            else:
                logger.error(f"SP-API request failed for ASIN {asin} (Consumer): {e}")
                return None
        except Exception as e:
            logger.error(f"Unexpected error for ASIN {asin} (Consumer): {e}")
            return None
    logger.error(f"Retries exhausted for ASIN {asin} (Consumer) after {total_wait}s")
    return None


def buybox_avg_90d(product, marketplace="GB"):
    bb_avg_90 = product["stats"]["avg90"][18] / 100 if product.get("stats") and product["stats"].get("avg90", [0] * 19)[18] > 0 else 0
    if bb_avg_90 > 0:
        return round(bb_avg_90, 2)

    bb_prices = product["data"].get("BUY_BOX_SHIPPING", [])
    bb_times = product["data"].get("BUY_BOX_SHIPPING_time", [])
    if not bb_prices:
        for legacy in ('NEW_FBA', 'BUY_BOX'):
            bb_prices = product["data"].get(legacy, [])
            bb_times = product["data"].get(f'{legacy}_time', [])
            if len(bb_prices) > 0:
                break

    cutoff = datetime.now(timezone.utc) - timedelta(days=90)
    clean = [
        price / 100
        for price, t in zip(bb_prices, bb_times)
        if price > 0 and keepa_minutes_to_datetime(t) >= cutoff
    ]
    return round(sum(clean) / len(clean), 2) if clean else None


async def fetch_product_data(code, is_asin=True):
    try:
        logger.debug(f"Querying Keepa for {code} (is_asin={is_asin})")
        products = keepa_api.query(code, product_code_is_asin=is_asin, stats=90, buybox=True, domain="GB")
        return products[0] if products else None
    except Exception as e:
        logger.error(f"Keepa API error for {code}: {str(e)}")
        return None


async def create_product_embed(product, code, buy_price, interaction):
    logger.info(f"Creating product embed for code {code}, user {interaction.user.id}")
    if not product:
        await interaction.followup.send(f"Product not found or invalid code: {code}", ephemeral=True)
        return

    asin = product.get('asin', code)
    raw_title = product.get('title') or f"Product {asin}"
    title = raw_title[:256]
    stats = product.get('stats') or {}
    sales_rank = stats.get('current', [0] * 19)[3] if stats else -1
    if sales_rank == -1:
        sales_data = product['data'].get('SALES', [])
        if len(sales_data) > 0:
            sales_rank = sales_data[-1]
    monthly_sold = product.get('monthlySold', stats.get('salesRankDrops30', 0) if stats else 0)
    avg90_price = buybox_avg_90d(product, "GB")
    fba_fees_block = product.get('fbaFees') or {}
    fba_fee_cents = fba_fees_block.get('pickAndPackFee') or 300
    fba_fee = fba_fee_cents / 100
    referral_fee_pct = product.get('referralFeePercentage') or 15.0
    root_category = product.get('rootCategory') or 0
    img_csv = product.get('imagesCSV') or ''
    img_url = f"https://m.media-amazon.com/images/I/{img_csv.split(',')[0]}.jpg" if img_csv else ""

    offer_response = get_offers_with_retry(asin)
    market_buy_box_price = -1
    total_offers = 0
    top_offers = []
    is_buy_box = False
    AMAZON_SELLER_IDS = {"A3P5ROKL5A1OLE", "A30DC7701CXIBH"}
    if offer_response:
        summary = offer_response.payload.get("Summary", {})
        total_offers = summary.get("TotalOfferCount", 0)
        offers = offer_response.payload.get("Offers", [])[:10]
        buy_box_prices = summary.get("BuyBoxPrices", [])
        lowest_price = None
        lowest_shipping = Decimal('0')
        selected_offer = None
        seller_id = None
        for bb in buy_box_prices:
            if bb.get("quantityTier", 1) == 1 and bb.get("condition") == "New":
                market_buy_box_price = Decimal(str(bb.get("ListingPrice", {}).get("Amount", -1)))
                is_buy_box = True
                break
        unique_offers = {}
        for o in offers:
            price = o.get("ListingPrice", {}).get("Amount", -1)
            if price <= 0 or o.get("SubCondition") != "new":
                continue
            seller_id = o.get("SellerId", "")
            is_fba = o.get("IsFulfilledByAmazon", False)
            is_buy_box_winner = o.get("IsBuyBoxWinner", False)
            key = (seller_id, price, is_fba)
            if key not in unique_offers:
                unique_offers[key] = o
        sorted_offers = sorted(unique_offers.values(), key=lambda x: x.get("ListingPrice", {}).get("Amount", float('inf')))
        for o in sorted_offers[:5]:
            price = o.get("ListingPrice", {}).get("Amount", -1)
            is_fba = o.get("IsFulfilledByAmazon", False)
            seller_type = "Amazon" if o.get("SellerId", "") in AMAZON_SELLER_IDS else "FBA" if is_fba else "FBM"
            fulfillment = "FBA" if is_fba else "FBM"
            top_offers.append(f"{seller_type} ({fulfillment}): £{price:.2f}")
        if not top_offers:
            top_offers = ["N/A"]
        if not is_buy_box:
            for o in sorted_offers:
                price = o.get("ListingPrice", {}).get("Amount", -1)
                shipping = Decimal(str(o.get("Shipping", {}).get("Amount", 0)))
                if price > 0:
                    total_price = Decimal(str(price)) + shipping
                    if lowest_price is None or total_price < lowest_price:
                        lowest_price = total_price
                        lowest_shipping = shipping
                        selected_offer = o
                        seller_id = o.get("SellerId", "")
            if lowest_price is not None and market_buy_box_price == -1:
                market_buy_box_price = lowest_price - lowest_shipping
                is_buy_box = selected_offer.get("IsBuyBoxWinner", False)
    if not top_offers:
        total_offers = len(product.get('liveOffersOrder', [])) if product.get('liveOffersOrder') is not None else 0
        top_offers = ["N/A"]

    bsr = "Unavailable" if sales_rank == -1 else f"{sales_rank // 1000}k" if sales_rank >= 1000 else str(sales_rank)
    est_sales = f"{monthly_sold // 1000}k+/mo" if monthly_sold >= 1000 else f"{monthly_sold:,}+/mo"

    fees_buy_box = estimate_fba_fees(market_buy_box_price, referral_fee_pct, root_category, fba_fee) if market_buy_box_price > 0 else {
        'fba_fee': 0.0, 'referral_fee': 0.0, 'closing_fee': 0.0, 'digital_services_tax': 0.0, 'vat_on_fees': 0.0, 'total_fees': 0.0
    }
    fees_avg = estimate_fba_fees(avg90_price, referral_fee_pct, root_category, fba_fee) if avg90_price else {
        'fba_fee': 0.0, 'referral_fee': 0.0, 'closing_fee': 0.0, 'digital_services_tax': 0.0, 'vat_on_fees': 0.0, 'total_fees': 0.0
    }

    profit_vat_current = profit_non_vat_current = roi_vat_current = roi_non_vat_current = 0.0
    profit_vat_avg = profit_non_vat_avg = roi_vat_avg = roi_non_vat_avg = 0.0
    if buy_price is not None:
        vat, vat_incl = calculate_vat(buy_price)
        if market_buy_box_price > 0:
            profit_vat_current, roi_vat_current, _, _ = calculate_profit_and_roi(
                buy_price=buy_price, sale_price=market_buy_box_price, fba_fee=fees_buy_box['fba_fee'],
                referral_fee=fees_buy_box['referral_fee'], shipping=0, vat_registered=True, closing_fee=fees_buy_box['closing_fee']
            )
            profit_non_vat_current, roi_non_vat_current, _, _ = calculate_profit_and_roi(
                buy_price=buy_price, sale_price=market_buy_box_price, fba_fee=fees_buy_box['fba_fee'],
                referral_fee=fees_buy_box['referral_fee'], shipping=0, vat_registered=False, closing_fee=fees_buy_box['closing_fee']
            )
        if avg90_price:
            profit_vat_avg, roi_vat_avg, _, _ = calculate_profit_and_roi(
                buy_price=buy_price, sale_price=avg90_price, fba_fee=fees_avg['fba_fee'],
                referral_fee=fees_avg['referral_fee'], shipping=0, vat_registered=True, closing_fee=fees_avg['closing_fee']
            )
            profit_non_vat_avg, roi_non_vat_avg, _, _ = calculate_profit_and_roi(
                buy_price=buy_price, sale_price=avg90_price, fba_fee=fees_avg['fba_fee'],
                referral_fee=fees_avg['referral_fee'], shipping=0, vat_registered=False, closing_fee=fees_avg['closing_fee']
            )

    embed = discord.Embed(
        title=title,
        color=discord.Color.blue(),
        url=f"https://www.amazon.co.uk/dp/{asin}"
    )
    embed.add_field(
        name="ASIN/EAN",
        value=f"`{asin}` ❐",
        inline=True
    )
    embed.add_field(
        name="**Product Information**",
        value=(
            f"Sales Rank: {bsr}\n"
            f"Est. Sales: {est_sales}\n"
            f"Total Sellers: {total_offers}"
        ),
        inline=False
    )
    pricing_info = f"Buy Box Price: £{market_buy_box_price:.2f}" if market_buy_box_price > 0 else "Buy Box Price: N/A"
    pricing_info += f"\n90-Day Avg: £{avg90_price:.2f}" if avg90_price else "\n90-Day Avg: N/A"
    if buy_price is not None:
        pricing_info += f"\nBuy Price: £{buy_price:.2f}"
    embed.add_field(
        name="**Pricing Information**",
        value=pricing_info,
        inline=False
    )
    fees_info = (
        f"FBA: £{fees_buy_box['fba_fee']:.2f}\n"
        f"Referral: £{fees_buy_box['referral_fee']:.2f}\n"
        + (f"Closing: £{fees_buy_box['closing_fee']:.2f}\n" if fees_buy_box['closing_fee'] > 0 else "")
        + f"Digital Services: £{fees_buy_box['digital_services_tax']:.2f}\n"
        f"VAT on Fees: £{fees_buy_box['vat_on_fees']:.2f}\n"
        f"Total: £{fees_buy_box['total_fees']:.2f}"
    ) if fees_buy_box['total_fees'] > 0 else "N/A"
    embed.add_field(
        name="**Fees (Buy Box)**",
        value=fees_info,
        inline=False
    )
    if buy_price is not None:
        embed.add_field(
            name="**Profit & ROI**",
            value=(
                f"Buy Box Price (VAT): £{profit_vat_current:.2f} | ROI: {roi_vat_current:.2f}%\n"
                f"Buy Box Price (Non-VAT): £{profit_non_vat_current:.2f} | ROI: {roi_non_vat_current:.2f}%\n"
                f"90-Day Avg (VAT): £{profit_vat_avg:.2f} | ROI: {roi_vat_avg:.2f}%\n"
                f"90-Day Avg (Non-VAT): £{profit_non_vat_avg:.2f} | ROI: {roi_non_vat_avg:.2f}%"
            ) if (market_buy_box_price > 0 or avg90_price) else "N/A",
            inline=False
        )
    embed.add_field(
        name="**Offers**",
        value=f"Offers: {total_offers}\nTop 5 Offers:\n" + "\n".join(top_offers) if top_offers else "Offers: 0\nTop 5 Offers: N/A",
        inline=False
    )
    embed.add_field(
        name="**Links**",
        value=(
            f"[Keepa](https://keepa.com/#!product/2-{asin}) | "
            f"[Google](https://www.google.com/search?q={urllib.parse.quote(title)})"
        ),
        inline=False
    )
    embed.set_thumbnail(url=img_url)
    embed.set_footer(
        text="Mastermind Arbitrage",
        icon_url="https://cdn.discordapp.com/attachments/1266519400287174658/1268338281150419068/Copy_of_Mastermind.png"
    )
    embed.timestamp = datetime.now(timezone.utc)

    graph = await download_keepa_graph(asin)
    graph_file = discord.File(BytesIO(graph), filename="keepa_graph.png") if graph else None
    if graph_file:
        embed.set_image(url="attachment://keepa_graph.png")

    try:
        if graph_file:
            await interaction.followup.send(embed=embed, file=graph_file, ephemeral=True)
        else:
            await interaction.followup.send(embed=embed, ephemeral=True)
        logger.info(f"Product embed sent successfully for code {code}, user {interaction.user.id}")
    except Exception as e:
        logger.error(f"Failed to send product embed for code {code}, user {interaction.user.id}: {e}")
        await interaction.followup.send(f"Failed to send product embed: {e}", ephemeral=True)


def load_csv(file_path, target, is_array=False, callback=None):
    try:
        temp_data = [] if is_array else {}
        with open(file_path, 'r', encoding='utf-8') as f:
            reader = csv.DictReader(f)
            for row in reader:
                if is_array:
                    temp_data.append(row['storeName'].lower())
                else:
                    temp_data[row['brandName'].lower()] = {'link': row['link']}
        if is_array:
            target.clear()
            target.extend(temp_data)
            if callback:
                callback()
        else:
            target.clear()
            target.update(temp_data)
        logger.info(f"{file_path} reloaded")
    except Exception as e:
        logger.error(f"Failed to load {file_path}: {e}")


def update_store_invoices():
    store_invoices.clear()
    for store in true_stores:
        store_invoices[store] = True
    for store in false_stores:
        store_invoices[store] = False
    logger.info("Store invoices updated")


load_csv(os.path.join(BASE_DIR, 'trueStores.csv'), true_stores, is_array=True, callback=update_store_invoices)
load_csv(os.path.join(BASE_DIR, 'falseStores.csv'), false_stores, is_array=True, callback=update_store_invoices)
load_csv(os.path.join(BASE_DIR, 'autoUngateBrands.csv'), auto_ungate_brands)
load_csv(os.path.join(BASE_DIR, 'ungateBrands.csv'), ungate_brands)


class CSVWatcher(FileSystemEventHandler):
    def __init__(self, file_path, target, is_array=False, callback=None):
        self.file_path = file_path
        self.target = target
        self.is_array = is_array
        self.callback = callback

    def on_modified(self, event):
        if event.src_path == self.file_path and not event.is_directory:
            logger.info(f"{self.file_path} changed, reloading...")
            load_csv(self.file_path, self.target, self.is_array, self.callback)


observer = Observer()
observer.schedule(CSVWatcher(os.path.join(BASE_DIR, 'trueStores.csv'), true_stores, is_array=True, callback=update_store_invoices), path=BASE_DIR)
observer.schedule(CSVWatcher(os.path.join(BASE_DIR, 'falseStores.csv'), false_stores, is_array=True, callback=update_store_invoices), path=BASE_DIR)
observer.schedule(CSVWatcher(os.path.join(BASE_DIR, 'autoUngateBrands.csv'), auto_ungate_brands), path=BASE_DIR)
observer.schedule(CSVWatcher(os.path.join(BASE_DIR, 'ungateBrands.csv'), ungate_brands), path=BASE_DIR)
observer.start()


async def get_ma_webhook(channel):
    logger.info(f"Attempting to get or create webhook for channel {channel.id} ({channel.name})")
    if not hasattr(client, '_ma_webhooks'):
        client._ma_webhooks = {}
    if channel.id in client._ma_webhooks:
        logger.info(f"Using cached webhook for channel {channel.id}")
        return client._ma_webhooks[channel.id]

    try:
        webhooks = await channel.webhooks()
        webhook = next((w for w in webhooks if w.name == "Mastermind Arbitrage"), None)
        if not webhook:
            avatar_data = download_avatar()
            webhook = await channel.create_webhook(
                name="Mastermind Arbitrage",
                avatar=avatar_data
            )
            logger.info(f"Created MA webhook in #{channel.name} ({channel.id})")
        client._ma_webhooks[channel.id] = webhook
        return webhook
    except Exception as e:
        logger.error(f"Failed to get or create webhook for channel {channel.id}: {e}")
        return None


def capitalize(s):
    return s[0].upper() + s[1:] if s else s


async def get_exchange_rate():
    try:
        async with aiohttp.ClientSession() as session:
            async with session.get('https://api.exchangerate-api.com/v4/latest/EUR') as response:
                if response.status == 200:
                    data = await response.json()
                    rate = data.get('rates', {}).get('GBP')
                    if rate:
                        logger.info(f"Fetched EUR-to-GBP rate: {rate}")
                        return rate
                    logger.warning("GBP rate not found in API response")
                    return EUR_TO_GBP_FALLBACK
                logger.warning(f"Exchange rate API returned status {response.status}")
                return EUR_TO_GBP_FALLBACK
    except Exception as e:
        logger.error(f"Failed to fetch exchange rate: {e}", exc_info=True)
        return EUR_TO_GBP_FALLBACK


async def validate_identifier(identifier):
    if not identifier or not isinstance(identifier, str):
        logger.error("Identifier is empty or not a string")
        return False
    identifier = identifier.strip()
    if len(identifier) == 10 and re.match(r'^[A-Z0-9]{10}$', identifier):
        logger.info(f"Valid ASIN: {identifier}")
        return True
    logger.error(f"Invalid ASIN format: {identifier}")
    return False


async def resolve_asin(identifier: str) -> str | None:
    if not await validate_identifier(identifier):
        return None

    identifier = identifier.strip().upper()
    logger.info(f"Resolving identifier: {identifier}")
    logger.info(f"Returning ASIN: {identifier}")
    return identifier


async def get_product_details(asin):
    try:
        response = eu_catalog_client.get_catalog_item(
            asin,
            marketplaceIds=[EU_MARKETPLACE_ID],
            includedData=['summaries', 'images']
        )
        logger.info(f"Product details response: {response.payload}")
        item = response.payload
        title = item.get('summaries', [{}])[0].get('itemName', 'Unknown Title')
        images = item.get('images', [{}])[0].get('images', [])
        image_url = images[0].get('link') if images else None
        logger.info(f"Got title: {title}, image: {image_url}")
        return title, image_url
    except Exception as e:
        logger.error(f"Error fetching product details: {e}", exc_info=True)
        return "Unknown Title", None


async def _fetch_price_once(asin, mp_id, retries=3, initial_delay=2, max_wait=20):
    total_wait = 0
    delay = initial_delay
    for attempt in range(retries):
        try:
            response = eu_products_client.get_competitive_pricing_for_asins(
                [asin],
                MarketplaceId=mp_id,
                ShipToCountryCode="GB",
                CustomerType="Business",
                ItemCondition="New"
            )
            prices = (
                response.payload[0]
                .get("Product", {})
                .get("CompetitivePricing", {})
                .get("CompetitivePrices", [])
            )
            if not prices:
                logger.debug(f"No new condition prices found for {mp_id} (attempt {attempt + 1}/{retries})")
                return None

            cheapest = None
            for price in prices:
                if price.get("condition") != "New":
                    logger.debug(f"Skipping non-new price for {mp_id}: {price}")
                    continue
                landed_price = price.get("Price", {}).get("LandedPrice", {}).get("Amount")
                if landed_price is None:
                    logger.debug(f"Skipping invalid price for {mp_id}: {price}")
                    continue
                if cheapest is None or landed_price < cheapest["Price"]["LandedPrice"]["Amount"]:
                    cheapest = price

            if cheapest:
                logger.debug(f"Cheapest new price for {mp_id} (attempt {attempt + 1}/{retries}): {cheapest}")
                return cheapest
            logger.debug(f"No valid new condition price found for {mp_id} (attempt {attempt + 1}/{retries})")
            return None
        except SellingApiException as e:
            if isinstance(e.args[0], list) and any(err.get("code") == "QuotaExceeded" for err in e.args[0]):
                if total_wait + delay > max_wait:
                    logger.error(f"Max wait time ({max_wait}s) exceeded for ASIN {asin} ({mp_id})")
                    return None
                logger.warning(f"Quota exceeded for ASIN {asin} ({mp_id}), retrying in {delay}s")
                await asyncio.sleep(delay)
                total_wait += delay
                delay *= 2
            else:
                logger.error(f"Error fetching price for {mp_id}: {e}", exc_info=True)
                return None
        except Exception as e:
            logger.error(f"Unexpected error fetching price for {mp_id}: {e}", exc_info=True)
            return None
    logger.error(f"Retries exhausted for ASIN {asin} ({mp_id}) after {total_wait}s")
    return None


async def get_prices(asin):
    prices = {}
    marketplace_ids = [EU_MARKETPLACE_ID] + [info['id'] for info in EU_MARKETPLACES.values()]
    logger.info(f"Fetching prices for ASIN {asin} in marketplaces: {marketplace_ids}")

    eur_to_gbp = await get_exchange_rate()

    for mp_id in marketplace_ids:
        try:
            info = await _fetch_price_once(asin, mp_id)

            if info is None:
                logger.info(f"No new Business offer deliverable to GB for marketplace {mp_id}")
                await asyncio.sleep(2)
                continue

            landed = info["Price"]["LandedPrice"]
            shipping = info["Price"]["Shipping"]["Amount"]
            amount = landed["Amount"]
            currency = landed["CurrencyCode"]

            orig_amount, orig_currency = amount, currency

            if currency == "EUR":
                amount *= eur_to_gbp
                shipping *= eur_to_gbp
                currency = "GBP"
            elif currency == "SEK":
                amount *= SEK_TO_GBP
                shipping *= SEK_TO_GBP
                currency = "GBP"

            prices[mp_id] = {
                "landed_price": round(amount, 2),
                "shipping_price": round(shipping, 2),
                "currency": currency,
                "original_amount": round(orig_amount, 2),
                "original_currency": orig_currency
            }
            logger.info(f"Price for {mp_id}: {orig_currency}{orig_amount:.2f} (£{amount:.2f}), Shipping: £{shipping:.2f}")
            await asyncio.sleep(2)

        except Exception as e:
            logger.warning(f"Pricing lookup failed for {mp_id}: {e}", exc_info=True)
            await asyncio.sleep(2)
            continue

    return prices


EUR_TO_GBP_FALLBACK = 0.85
SEK_TO_GBP = 0.075

EU_MARKETPLACES = {
    'DE': {'id': 'A1PA6795UKMFR9', 'name': 'Germany', 'flag': '🇩🇪', 'domain': 'www.amazon.de'},
    'FR': {'id': 'A13V1IB3VIYZZH', 'name': 'France', 'flag': '🇫🇷', 'domain': 'www.amazon.fr'},
    'IT': {'id': 'APJ6JRA9NG5V4', 'name': 'Italy', 'flag': '🇮🇹', 'domain': 'www.amazon.it'},
    'ES': {'id': 'A1RKKUPIHCS9HS', 'name': 'Spain', 'flag': '🇪🇸', 'domain': 'www.amazon.es'}
}


@client.tree.command(name="search", description="Search Amazon product by ASIN or EAN and optional buy price", guild=discord.Object(id=GUILD_ID))
@app_commands.describe(asin_or_ean="Enter the ASIN or EAN", buy_price="Enter your buy price in GBP (optional)")
async def search(interaction: discord.Interaction, asin_or_ean: str, buy_price: float = None):
    logger.info(f"Search command triggered by user {interaction.user.id} with ASIN/EAN {asin_or_ean}")
    add_search_entry(interaction.user.id, asin_or_ean, buy_price)
    await interaction.response.defer(ephemeral=True)
    is_asin = len(asin_or_ean) == 10 and asin_or_ean.startswith('B')
    product = await fetch_product_data(asin_or_ean, is_asin)
    await create_product_embed(product, asin_or_ean, buy_price, interaction)


@client.tree.command(name="scan", description="Scan a barcode image to get Amazon product details and optional buy price", guild=discord.Object(id=GUILD_ID))
@app_commands.describe(image="Upload an image of the barcode (UPC/EAN)", buy_price="Enter your buy price in GBP (optional)")
async def scan(interaction: discord.Interaction, image: discord.Attachment, buy_price: float = None):
    logger.info(f"Scan command triggered by user {interaction.user.id}")
    await interaction.response.defer(ephemeral=True)
    try:
        image_data = await image.read()
        img = Image.open(BytesIO(image_data))
        barcodes = decode(img)
        if not barcodes:
            await interaction.followup.send("No barcode detected in the image. Please upload a clearer image.", ephemeral=True)
            return
        barcode = max(barcodes, key=lambda b: len(b.data.decode('utf-8')) if b.data.isdigit() and len(b.data.decode('utf-8')) in [12, 13] else 0).data.decode('utf-8')
        if not (barcode.isdigit() and len(barcode) in [12, 13]):
            await interaction.followup.send("No valid EAN/UPC barcode detected. Please ensure the EAN is at the bottom.", ephemeral=True)
            return
        product = await fetch_product_data(barcode, is_asin=False)
        await create_product_embed(product, barcode, buy_price, interaction)
    except Exception as e:
        logger.error(f"Error processing scan for user {interaction.user.id}: {e}")
        await interaction.followup.send(f"Error processing image: {str(e)}", ephemeral=True)


@client.tree.command(name="ungate", description="Check if a brand is auto-ungated or provides a link to ungate it", guild=discord.Object(id=GUILD_ID))
@app_commands.describe(brand="Name of the brand")
async def ungate(interaction: discord.Interaction, brand: str):
    logger.info(f"Ungate command triggered by user {interaction.user.id} with brand {brand}")
    await interaction.response.defer(ephemeral=True)
    brand = brand.lower()
    if brand in auto_ungate_brands:
        await interaction.followup.send(
            f"{capitalize(brand)} is auto-ungated. Use the ASIN {auto_ungate_brands[brand]['link']} to ungate.",
            ephemeral=True
        )
    elif brand in ungate_brands:
        await interaction.followup.send(
            f"{capitalize(brand)} is not auto-ungated. You can ungate it here: {ungate_brands[brand]['link']}",
            ephemeral=True
        )
    else:
        server_id = "1264672155652587562"
        channel_id = "1266520487375278111"
        await interaction.followup.send(
            f"We don't have an ungate for this brand. [Submit an ungate request](https://discord.com/channels/{server_id}/{channel_id}).",
            ephemeral=True
        )


@client.tree.command(name="invoice", description="Check if a store provides an invoice", guild=discord.Object(id=GUILD_ID))
@app_commands.describe(store="Name of the store")
async def invoice(interaction: discord.Interaction, store: str):
    logger.info(f"Invoice command triggered by user {interaction.user.id} with store {store}")
    await interaction.response.defer(ephemeral=True)
    store = store.lower()
    if store in store_invoices:
        await interaction.followup.send(
            f"{capitalize(store)} {'supplies an invoice.' if store_invoices[store] else 'does not provide an invoice.'}",
            ephemeral=True
        )
    else:
        server_id = "1264672155652587562"
        channel_id = "1266520487375278111"
        await interaction.followup.send(
            f"Store not in our list. [Submit a request](https://discord.com/channels/{server_id}/{channel_id}).",
            ephemeral=True
        )


@client.tree.command(name="embed", description="Manage embeds", guild=discord.Object(id=GUILD_ID))
@app_commands.describe(action="Choose an action: create a lead or post embed")
@app_commands.choices(action=[
    app_commands.Choice(name="lead", value="lead"),
    app_commands.Choice(name="post", value="post")
])
async def embed(interaction: discord.Interaction, action: str):
    logger.info(f"Embed command triggered by user {interaction.user.id} with action {action}")
    await interaction.response.defer(ephemeral=True)

    allowed_role_ids = {
        "lead": {
            "1264672155652587562", "1266690776742629499", "1266690883634597909",
            "1266690966341947402", "1373636997364711555"
        },
        "post": {
            "1264672155652587562", "1265421527671767153", "1266690776742629499",
            "1266690883634597909", "1266690966341947402", "1266690966341947402", "1373636997364711555",
            "1332084573701673014", "1266691088970944634", "1426959824234745926", "1426959372562731118", "1426958982974799933"
        }
    }

    user_roles = {str(role.id) for role in interaction.user.roles}
    logger.debug(f"user roles = {user_roles}")
    logger.debug(f"allowed = {allowed_role_ids[action]}")
    if not user_roles & allowed_role_ids[action]:
        logger.info(f"User {interaction.user.id} lacks permission for {action}")
        await interaction.followup.send("You don't have permission to use this command.", ephemeral=True)
        return

    user_session_data[interaction.user.id] = {
        "subcommand": action,
        "step": "selecting_roles",
        "selected_roles": [],
        "selected_categories": [],
        "selected_channels": [],
        "embeds": []
    }
    logger.info(f"Initialized session for user {interaction.user.id}: {user_session_data[interaction.user.id]}")

    roles = [
        SelectOption(label=role.name, value=str(role.id))
        for role in interaction.guild.roles
        if str(role.id) in allowed_role_ids[action]
    ]
    roles.sort(key=lambda x: x.label)

    class RoleSelect(Select):
        def __init__(self):
            super().__init__(placeholder="Select roles to mention", min_values=0, max_values=len(roles), options=roles)

        async def callback(self, interaction: discord.Interaction):
            logger.info(f"RoleSelect callback triggered for user {interaction.user.id}, selected: {self.values}")
            data = user_session_data.get(interaction.user.id)
            if not data:
                logger.error(f"Session data missing for user {interaction.user.id} in RoleSelect")
                await interaction.response.send_message("Session expired.", ephemeral=True)
                return
            data["selected_roles"] = self.values
            data["step"] = "selecting_categories"
            user_session_data[interaction.user.id] = data
            logger.debug(f"Updated session for user {interaction.user.id}: {data}")

            allowed_category_ids = {"1265414598836621353", "1373642167351906314", "1265415271586201834", "1420837786864455723", "1426612060913008732"} if action == "lead" else None
            categories = [
                SelectOption(label=channel.name, value=str(channel.id))
                for channel in interaction.guild.channels
                if channel.type == ChannelType.category and (not allowed_category_ids or str(channel.id) in allowed_category_ids)
            ]
            categories.sort(key=lambda x: x.label)

            if not categories:
                logger.error(f"No categories found for user {interaction.user.id}")
                del user_session_data[interaction.user.id]
                await interaction.response.send_message("No categories found.", ephemeral=True)
                return

            class CategorySelect(Select):
                def __init__(self):
                    super().__init__(placeholder="Select categories", min_values=1, max_values=len(categories), options=categories)

                async def callback(self, interaction: discord.Interaction):
                    logger.info(f"CategorySelect callback triggered for user {interaction.user.id}, selected: {self.values}")
                    data = user_session_data.get(interaction.user.id)
                    if not data:
                        logger.error(f"Session data missing for user {interaction.user.id} in CategorySelect")
                        await interaction.response.send_message("Session expired.", ephemeral=True)
                        return
                    data["selected_categories"] = self.values
                    data["step"] = "selecting_channels"
                    user_session_data[interaction.user.id] = data
                    logger.debug(f"Updated session for user {interaction.user.id}: {data}")

                    channels = [
                        SelectOption(label=channel.name, value=str(channel.id))
                        for channel in interaction.guild.channels
                        if (channel.type in (ChannelType.text, ChannelType.news) and
                            channel.category_id and str(channel.category_id) in data["selected_categories"])
                    ]
                    channels.sort(key=lambda x: x.label)

                    if not channels:
                        logger.error(f"No text channels found in selected categories for user {interaction.user.id}")
                        del user_session_data[interaction.user.id]
                        await interaction.response.send_message("No text channels found in selected categories.", ephemeral=True)
                        return

                    class ChannelSelect(Select):
                        def __init__(self):
                            super().__init__(placeholder="Select channels", min_values=1, max_values=len(channels), options=channels)

                        async def callback(self, interaction: discord.Interaction):
                            logger.info(f"ChannelSelect callback triggered for user {interaction.user.id}, selected: {self.values}")
                            data = user_session_data.get(interaction.user.id)
                            if not data:
                                logger.error(f"Session data missing for user {interaction.user.id} in ChannelSelect")
                                await interaction.response.send_message("Session expired.", ephemeral=True)
                                return
                            data["selected_channels"] = self.values
                            data["step"] = "modal"
                            user_session_data[interaction.user.id] = data
                            logger.debug(f"Updated session for user {interaction.user.id}: {data}")

                            modal = Modal(title="Create Lead Embed" if action == "lead" else "Create Post Embed")
                            if action == "lead":
                                modal.add_item(TextInput(label="Product Link", custom_id="product_link", style=TextStyle.short, required=True))
                                modal.add_item(TextInput(label="ASIN", custom_id="asin", style=TextStyle.short, required=True))
                                modal.add_item(TextInput(label="TopCashback (optional)", custom_id="topcashback", style=TextStyle.short, required=False))
                                modal.add_item(TextInput(label="Notes (optional)", custom_id="notes", style=TextStyle.paragraph, required=False))
                                modal.add_item(TextInput(label="Image URL (optional)", custom_id="image_url", style=TextStyle.short, required=False))
                            else:
                                modal.add_item(TextInput(label="Title", custom_id="title", style=TextStyle.short, required=False))
                                modal.add_item(TextInput(label="Content", custom_id="content", style=TextStyle.paragraph, required=True))
                                modal.add_item(TextInput(label="Image URL (optional)", custom_id="image_url", style=TextStyle.short, required=False))

                            async def on_submit(modal_interaction: discord.Interaction):
                                logger.info(f"Modal submission triggered for user {modal_interaction.user.id}, data: {modal_interaction.data}")
                                data = user_session_data.get(modal_interaction.user.id)
                                if not data:
                                    logger.error(f"Session data missing for user {modal_interaction.user.id} in on_submit")
                                    await modal_interaction.response.send_message("Session expired.", ephemeral=True)
                                    return

                                try:
                                    embed = discord.Embed()
                                    embed.set_footer(
                                        text="Mastermind Arbitrage - Smart Moves for Greater Gains",
                                        icon_url="https://cdn.discordapp.com/attachments/1266519400287174658/1268338281150419068/Copy_of_Mastermind.png"
                                    )

                                    if data["subcommand"] == "lead":
                                        product_link = modal_interaction.data['components'][0]['components'][0]['value']
                                        asin = modal_interaction.data['components'][1]['components'][0]['value']
                                        topcashback = modal_interaction.data['components'][2]['components'][0]['value']
                                        notes = modal_interaction.data['components'][3]['components'][0]['value']
                                        image_url = modal_interaction.data['components'][4]['components'][0]['value']
                                        if len(product_link) > 2000 or len(asin) > 2000 or len(topcashback) > 2000 or len(notes) > 2000 or len(image_url) > 2000:
                                            logger.error(f"Invalid input length for user {modal_interaction.user.id}")
                                            await modal_interaction.response.send_message("Input fields must be under 2000 characters.", ephemeral=True)
                                            return
                                        embed.description = product_link
                                        embed.add_field(name="ASIN", value=asin)
                                        if topcashback:
                                            embed.add_field(name="TopCashback", value=topcashback)
                                        if notes:
                                            embed.add_field(name="Notes", value=notes)
                                        if image_url:
                                            embed.set_image(url=image_url)
                                    else:
                                        title = modal_interaction.data['components'][0]['components'][0]['value']
                                        content = modal_interaction.data['components'][1]['components'][0]['value']
                                        image_url = modal_interaction.data['components'][2]['components'][0]['value']
                                        if len(title) > 256 or len(content) > 2000 or len(image_url) > 2000:
                                            logger.error(f"Invalid input length for user {modal_interaction.user.id}")
                                            await modal_interaction.response.send_message("Title must be under 256 characters, content and image URL under 2000 characters.", ephemeral=True)
                                            return
                                        if title:
                                            embed.title = title
                                        embed.description = content
                                        if image_url:
                                            embed.set_image(url=image_url)

                                    data.setdefault("embeds", []).append(embed)
                                    user_session_data[modal_interaction.user.id] = data
                                    logger.debug(f"Updated session after modal for user {modal_interaction.user.id}: {data}")

                                    class EmbedButtons(View):
                                        @discord.ui.button(label=f"Add Another {'Lead' if data['subcommand'] == 'lead' else 'Post'}", style=ButtonStyle.primary, custom_id="add_another_embed")
                                        async def add_another(self, interaction: discord.Interaction, button: Button):
                                            logger.info(f"Add Another button triggered for user {interaction.user.id}")
                                            data = user_session_data.get(interaction.user.id)
                                            if not data:
                                                logger.error(f"Session data missing for user {interaction.user.id} in add_another")
                                                await interaction.response.send_message("Session expired.", ephemeral=True)
                                                return

                                            modal = Modal(title="Create Lead Embed" if data["subcommand"] == "lead" else "Create Post Embed")
                                            if data["subcommand"] == "lead":
                                                modal.add_item(TextInput(label="Product Link", custom_id="product_link", style=TextStyle.short, required=True))
                                                modal.add_item(TextInput(label="ASIN", custom_id="asin", style=TextStyle.short, required=True))
                                                modal.add_item(TextInput(label="TopCashback (optional)", custom_id="topcashback", style=TextStyle.short, required=False))
                                                modal.add_item(TextInput(label="Notes (optional)", custom_id="notes", style=TextStyle.paragraph, required=False))
                                                modal.add_item(TextInput(label="Image URL (optional)", custom_id="image_url", style=TextStyle.short, required=False))
                                            else:
                                                modal.add_item(TextInput(label="Title", custom_id="title", style=TextStyle.short, required=False))
                                                modal.add_item(TextInput(label="Content", custom_id="content", style=TextStyle.paragraph, required=True))
                                                modal.add_item(TextInput(label="Image URL (optional)", custom_id="image_url", style=TextStyle.short, required=False))
                                            modal.on_submit = on_submit
                                            logger.info(f"Sending add_another modal for user {interaction.user.id}")
                                            await interaction.response.send_modal(modal)
                                            return

                                        @discord.ui.button(label="Finish", style=ButtonStyle.success, custom_id="finish_embeds")
                                        async def finish(self, interaction: discord.Interaction, button: Button):
                                            logger.info(f"Finish button triggered for user {interaction.user.id}")
                                            data = user_session_data.get(interaction.user.id)
                                            if not data:
                                                logger.error(f"Session data missing for user {interaction.user.id} in finish")
                                                await interaction.response.send_message("Session expired.", ephemeral=True)
                                                return

                                            mention = " ".join(
                                                "@everyone" if rid == str(interaction.guild.id) else f"<@&{rid}>"
                                                for rid in data["selected_roles"]
                                            ) or None
                                            logger.debug(f"Mention string for user {interaction.user.id}: {mention}")

                                            sent_count = 0
                                            for ch_id in data["selected_channels"]:
                                                logger.info(f"Attempting to send embed to channel {ch_id} for user {interaction.user.id}")
                                                channel = interaction.guild.get_channel(int(ch_id))
                                                if not channel:
                                                    logger.error(f"Channel {ch_id} not found")
                                                    continue
                                                permissions = channel.permissions_for(interaction.guild.me)
                                                if not permissions.send_messages or not permissions.embed_links:
                                                    logger.error(f"Bot lacks permissions (send_messages: {permissions.send_messages}, embed_links: {permissions.embed_links}) in channel {ch_id}")
                                                    continue
                                                webhook = await get_ma_webhook(channel)
                                                if not webhook:
                                                    logger.error(f"Failed to get webhook for channel {ch_id}")
                                                    continue
                                                for embed in data["embeds"]:
                                                    try:
                                                        logger.info(f"Sending embed to channel {ch_id}")
                                                        await webhook.send(
                                                            content=mention,
                                                            embed=embed,
                                                            username="Mastermind Arbitrage",
                                                            avatar_url="https://cdn.discordapp.com/attachments/1266519400287174658/1268338281150419068/Copy_of_Mastermind.png"
                                                        )
                                                        logger.info(f"Embed sent successfully to channel {ch_id}")
                                                        sent_count += 1
                                                    except Exception as e:
                                                        logger.error(f"Failed to send embed to channel {ch_id}: {e}")

                                            del user_session_data[interaction.user.id]
                                            logger.info(f"Session cleared for user {interaction.user.id}")
                                            if sent_count > 0:
                                                await interaction.response.send_message(
                                                    f"Successfully posted **{sent_count}** embed(s) to {len(data['selected_channels'])} channel(s)!",
                                                    ephemeral=True
                                                )
                                            else:
                                                await interaction.response.send_message(
                                                    "Failed to post embeds. Check bot permissions or logs for details.",
                                                    ephemeral=True
                                                )
                                            return

                                    await modal_interaction.response.send_message(
                                        f"You have created **{len(data['embeds'])}** embed. Add another or finish?",
                                        view=EmbedButtons(),
                                        ephemeral=True
                                    )
                                    logger.info(f"Sent embed creation confirmation to user {modal_interaction.user.id}")
                                except Exception as e:
                                    logger.exception(f"Modal submission failed for user {modal_interaction.user.id}: {e}")
                                    await modal_interaction.response.send_message(
                                        "Something went wrong while processing your submission.", ephemeral=True
                                    )

                            modal.on_submit = on_submit
                            logger.info(f"Sending modal for user {interaction.user.id}, action: {action}")
                            await interaction.response.send_modal(modal)
                            return

                    view = View()
                    view.add_item(ChannelSelect())
                    await interaction.response.send_message("Select channels from chosen categories:", view=view, ephemeral=True)
                    logger.info(f"Sent channel select to user {interaction.user.id}")
                    return

            view = View()
            view.add_item(CategorySelect())
            await interaction.response.send_message("Select categories:", view=view, ephemeral=True)
            logger.info(f"Sent category select to user {interaction.user.id}")
            return

    view = View()
    view.add_item(RoleSelect())
    await interaction.followup.send("Select roles to mention:", view=view, ephemeral=True)
    logger.info(f"Sent role select to user {interaction.user.id}")


eu_group = app_commands.Group(name="eu", description="Commands for EU price comparisons")


@eu_group.command(name="compare", description="Compare Amazon Business prices across EU marketplaces for a UK ASIN")
@app_commands.describe(
    asin="ASIN of the product",
    threshold="Percentage threshold for cheaper prices (e.g., 10 for 10%)"
)
async def compare(interaction: discord.Interaction, asin: str, threshold: int):
    await interaction.response.defer(ephemeral=True)
    logger.info(f"Received /eu compare command with ASIN: {asin}, threshold: {threshold}")

    asin = await resolve_asin(asin)
    if not asin:
        logger.error("Failed to resolve ASIN")
        await interaction.followup.send("Invalid ASIN or product not found in UK marketplace. Please check the input and try again.")
        return

    title, image_url = await get_product_details(asin)
    prices = await get_prices(asin)

    uk_price = prices.get(EU_MARKETPLACE_ID, {}).get('landed_price')
    if not uk_price:
        logger.error("Failed to fetch UK price")
        await interaction.followup.send("Could not fetch UK price for this product.")
        return

    cheaper_markets = []
    for code, info in EU_MARKETPLACES.items():
        market_price = prices.get(info['id'], {}).get('landed_price')
        shipping_price = prices.get(info['id'], {}).get('shipping_price', 0)
        original_amount = prices.get(info['id'], {}).get('original_amount')
        original_currency = prices.get(info['id'], {}).get('original_currency')
        if market_price and market_price < uk_price:
            savings_percent = ((uk_price - market_price) / uk_price) * 100
            if savings_percent >= threshold:
                cheaper_markets.append({
                    'name': info['name'],
                    'flag': info['flag'],
                    'price': market_price,
                    'shipping_price': shipping_price,
                    'savings': savings_percent,
                    'original_amount': original_amount,
                    'original_currency': original_currency,
                    'link': f"https://{info['domain']}/dp/{asin}"
                })
                logger.info(f"Cheaper market: {info['name']} - {original_currency}{original_amount:.2f} (£{market_price:.2f}), {savings_percent:.1f}% cheaper")

    embed = discord.Embed(
        title=title[:256],
        url=f"https://www.amazon.co.uk/dp/{asin}",
        color=discord.Color.blue(),
        timestamp=datetime.now(timezone.utc)
    )
    embed.set_thumbnail(url=image_url)
    embed.add_field(name="Threshold", value=f"{threshold}%", inline=False)
    embed.add_field(name="ASIN", value=f"`{asin}` ❐", inline=True)
    embed.add_field(name="UK Price 🇬🇧", value=f"£{uk_price:.2f}", inline=False)

    if cheaper_markets:
        value = ""
        for market in cheaper_markets:
            price_str = f"{market['original_currency']} {market['original_amount']:.2f} (£{market['price']:.2f}) - {market['savings']:.1f}% cheaper"
            value += f"{market['flag']} {market['name']}: {price_str}\n"
            if market['shipping_price'] > 0:
                value += f"- Shipping: £{market['shipping_price']:.2f}\n"
            value += f"- [View on Amazon {market['name']}]({market['link']})\n\n"
        embed.add_field(name="Cheaper EU Marketplaces", value=value, inline=False)
    else:
        embed.add_field(
            name="Cheaper EU Marketplaces",
            value="No EU marketplaces found with prices cheaper than the UK meeting the threshold.",
            inline=False
        )

    embed.set_footer(
        text="Mastermind Arbitrage",
        icon_url="https://cdn.discordapp.com/attachments/1266519400287174658/1268338281150419068/Copy_of_Mastermind.png"
    )

    await interaction.followup.send(embed=embed, ephemeral=True)
    logger.info("Sent embed response")


client.tree.add_command(eu_group, guild=discord.Object(id=GUILD_ID))


@client.tree.command(name="qogita", description="Search Qogita products with Keepa filtering", guild=discord.Object(id=GUILD_ID))
@app_commands.describe(
    brand="Brand name (e.g., Nivea)",
    max_price="Maximum price (default: 100.0)",
    min_roi="Minimum ROI percentage (optional)",
    min_profit="Minimum profit in GBP (optional)",
    min_sellers="Minimum number of sellers (default: 1, set 0 to ignore)",
    min_spm="Minimum sales per month (optional)"
)
async def qogita(interaction: discord.Interaction, brand: str, max_price: float = 100.0, min_roi: float = None, min_profit: float = None, min_sellers: int = 1, min_spm: int = None):
    global token_expiry
    if not HEADERS or datetime.now(timezone.utc) >= token_expiry - timedelta(seconds=30):
        await initialize_token()

    await interaction.response.send_message("Hunting for profitable deals. This may take a few minutes.", ephemeral=True)
    logging.info(f"Executing /qogita command: brand={brand}, max_price={max_price}, min_roi={min_roi}, min_profit={min_profit}, min_sellers={min_sellers}, min_spm={min_spm}")
    products = await fetch_products(brand, max_price)
    if not products:
        logging.info("No Qogita products found matching the criteria")
        await interaction.followup.send("No Qogita products found matching the criteria.", ephemeral=True)
        return

    filtered_products = await filter_with_keepa(products, max_price, min_roi, min_profit, min_sellers, min_spm)
    if not filtered_products:
        logging.info("No products matched the Keepa criteria")
        await interaction.followup.send("No products matched the Keepa criteria.", ephemeral=True)
        return

    logging.info(f"Found {len(filtered_products)} products after filtering")
    search_params = {
        "brand": brand,
        "max_price": max_price,
        "min_roi": min_roi,
        "min_profit": min_profit,
        "min_sellers": min_sellers,
        "min_spm": min_spm
    }
    save_temp_results(interaction.id, filtered_products, search_params)

    embed = await create_embed(filtered_products[0], 0, len(filtered_products))
    view = create_view(filtered_products, 0, len(filtered_products), interaction.id, brand, max_price, min_roi, min_profit, min_sellers, min_spm)
    graph_bytes = await download_keepa_graph(filtered_products[0]["asin"])
    if graph_bytes:
        embed.set_image(url="attachment://keepa_graph.png")
        file = discord.File(fp=io.BytesIO(graph_bytes), filename="keepa_graph.png")
        await interaction.followup.send(embed=embed, view=view, file=file, ephemeral=True)
    else:
        await interaction.followup.send(embed=embed, view=view, ephemeral=True)


keyword_group = app_commands.Group(name="keyword", description="Keyword alert commands")


class KeywordChannelSelect(discord.ui.ChannelSelect):
    def __init__(self, parent_view: "KeywordChannelPickerView"):
        super().__init__(
            placeholder="Select one or more channels…",
            min_values=1,
            max_values=min(25, len(parent_view.allowed_channel_ids)),
            channel_types=[ChannelType.text, ChannelType.news]
        )
        self.parent_view = parent_view

    async def callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.parent_view.owner_id:
            await interaction.response.send_message("Only the command author can use this selector.", ephemeral=True)
            return

        picked_channels = [c.id for c in self.values if c.id in self.parent_view.allowed_channel_ids]
        if not picked_channels:
            await interaction.response.send_message("Please select at least one allowed channel.", ephemeral=True)
            return

        inserted = save_keyword_pinger(self.parent_view.owner_id, self.parent_view.keyword, picked_channels)
        channel_mentions = ", ".join(f"<#{cid}>" for cid in picked_channels)
        await interaction.response.edit_message(
            content=(
                f"Keyword alert saved for `{self.parent_view.keyword}` in {len(picked_channels)} channel(s): {channel_mentions}\n"
                f"New subscriptions added: **{inserted}**"
            ),
            view=None
        )
        self.parent_view.stop()


class KeywordChannelPickerView(View):
    def __init__(self, owner_id: int, keyword: str, allowed_channel_ids: set[int]):
        super().__init__(timeout=120)
        self.owner_id = owner_id
        self.keyword = keyword
        self.allowed_channel_ids = allowed_channel_ids
        self.add_item(KeywordChannelSelect(self))

    async def on_timeout(self):
        self.stop()


def collect_allowed_keyword_channels(guild: discord.Guild) -> Dict[int, discord.abc.GuildChannel]:
    allowed_channels: Dict[int, discord.abc.GuildChannel] = {}

    for channel_id in KEYWORD_ALLOWED_CHANNEL_IDS:
        channel = guild.get_channel(channel_id)
        if channel and isinstance(channel, (discord.TextChannel, discord.Thread, discord.VoiceChannel, discord.ForumChannel)):
            if isinstance(channel, discord.TextChannel):
                allowed_channels[channel.id] = channel

    for category_id in KEYWORD_ALLOWED_CATEGORY_IDS:
        category = guild.get_channel(category_id)
        if isinstance(category, discord.CategoryChannel):
            for channel in category.channels:
                if isinstance(channel, discord.TextChannel):
                    allowed_channels[channel.id] = channel

    return allowed_channels


@keyword_group.command(name="pinger", description="Get DM alerts when your keyword appears.")
@app_commands.describe(keyword="Word or phrase to watch for")
async def keyword_pinger(interaction: discord.Interaction, keyword: str):
    normalized = normalize_keyword(keyword)
    if not normalized:
        await interaction.response.send_message("Please provide a valid keyword.", ephemeral=True)
        return

    if not interaction.guild:
        await interaction.response.send_message("This command can only be used inside the server.", ephemeral=True)
        return

    allowed_channels = collect_allowed_keyword_channels(interaction.guild)
    if not allowed_channels:
        await interaction.response.send_message("No allowed channels are currently available.", ephemeral=True)
        return

    view = KeywordChannelPickerView(interaction.user.id, normalized, set(allowed_channels.keys()))
    await interaction.response.send_message(
        f"Keyword: `{normalized}`\nSelect one or more channels to monitor.",
        view=view,
        ephemeral=True
    )


client.tree.add_command(keyword_group, guild=discord.Object(id=GUILD_ID))


async def process_keyword_pingers(message: discord.Message):
    if not message.guild or not isinstance(message.channel, discord.TextChannel):
        return

    text = (message.content or "").lower()
    if not text:
        return

    subscriptions = get_keyword_pingers_for_channel(message.channel.id)
    if not subscriptions:
        return

    matches_by_user: Dict[int, List[str]] = {}
    for user_id, keyword in subscriptions:
        if not keyword:
            continue
        if str(message.author.id) == str(user_id):
            continue
        if keyword in text:
            matches_by_user.setdefault(int(user_id), []).append(keyword)

    for user_id, matched_keywords in matches_by_user.items():
        try:
            user = client.get_user(user_id) or await client.fetch_user(user_id)
            if not user:
                continue

            deduped = sorted(set(matched_keywords))
            jump_link = message.jump_url
            keyword_list = ", ".join(f"`{k}`" for k in deduped)
            await user.send(
                f"🔔 Your keyword alert matched in **#{message.channel.name}**.\n"
                f"Keywords: {keyword_list}\n"
                f"Author: {message.author.mention}\n"
                f"Message: {jump_link}"
            )
        except Exception as e:
            logger.error(f"Failed sending keyword alert DM to {user_id}: {e}")


@client.event
async def on_ready():
    logger.info(f'Logged in as {client.user}')
    await initialize_token()


@client.event
async def on_member_join(member):
    if not any(r.id == PAID_ROLE_ID for r in member.roles):
        return
    logger.info(f"Member {member.id} joined the server")
    channel = member.guild.get_channel(WELCOME_CHANNEL_ID)
    if not channel:
        logger.error("Welcome channel 1269036878880047266 not found")
        return

    welcomes = [
        f"Welcome to Mastermind Arbitrage, <@{member.id}>! Glad to have you with us.",
        f"<@{member.id}> just joined the server. Let the flips begin!",
        f"Welcome to the hustle, <@{member.id}>!",
        f"Glad you're here, <@{member.id}>—time to make some moves.",
        f"Welcome to the squad, <@{member.id}>! Let's get sourcing.",
        f"<@{member.id}> just landed. Time to flip some deals!",
        f"<@{member.id}> joined. The resale grind just got stronger.",
        f"Big welcome to <@{member.id}>! Let's make smart moves.",
        f"<@{member.id}> is here! Let the arbitrage begin.",
        f"Another mastermind in the making—welcome, <@{member.id}>!"
    ]
    random_welcome = welcomes[random.randint(0, len(welcomes) - 1)]

    try:
        await channel.send(random_welcome)
        logger.info(f"Welcome message sent for member {member.id}")
    except Exception as e:
        logger.error(f"Failed to send welcome message for member {member.id}: {e}")

URL_RE = re.compile(r'https?://\S+', re.I)

AUTO_ROLE_PING_ID = 1428129348531126302
AUTO_ROLE_PING_CHANNELS = {
    1486052019138727946,
    1486053282290995311,
    1486054064201400432,
    1486126809203343531,
    1486054429319758027,
    1486054532558622931,
    1486054596878012436,
    1486054660061007954,
    1486054755573829672,
    1486054861819871412,
    1486054962390896862,
}

AUTO_ROLE_PING_TEXT = f"<@&{AUTO_ROLE_PING_ID}>"

# Track webhook message IDs we've already handled
_handled_webhook_ping_message_ids = set()
_handled_webhook_ping_lock = asyncio.Lock()


async def _ping_auto_role_only(channel: discord.TextChannel):
    await channel.send(
        AUTO_ROLE_PING_TEXT,
        allowed_mentions=discord.AllowedMentions(
            roles=True,
            users=False,
            everyone=False
        )
    )


@client.event
async def on_message(message: discord.Message):
    # Never react to our own bot messages
    if client.user and message.author.id == client.user.id:
        return

    # Keyword pinger checks run for all text channels in the guild
    try:
        await process_keyword_pingers(message)
    except Exception as e:
        logger.error(f"Keyword pinger processing failed for message {message.id}: {e}")

    # Only care about the configured channels
    if message.channel.id not in AUTO_ROLE_PING_CHANNELS:
        return

    # Only care about webhook messages
    if not message.webhook_id:
        return

    # Never react to the ping message itself
    if (message.content or "").strip() == AUTO_ROLE_PING_TEXT:
        return

    async with _handled_webhook_ping_lock:
        # If we've already handled this exact webhook message, do nothing
        if message.id in _handled_webhook_ping_message_ids:
            return

        _handled_webhook_ping_message_ids.add(message.id)

        # Keep memory from growing forever
        if len(_handled_webhook_ping_message_ids) > 10000:
            _handled_webhook_ping_message_ids.clear()
            _handled_webhook_ping_message_ids.add(message.id)

    try:
        await _ping_auto_role_only(message.channel)
    except Exception as e:
        logger.error(f"Failed to process webhook ping for message {message.id}: {e}")


client.run(DISCORD_BOT_TOKEN)
