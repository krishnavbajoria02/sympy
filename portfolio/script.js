const GITHUB_USERNAME = "krishnavbajoria02";

function setYear() {
  const yearEl = document.getElementById("year");
  if (yearEl) yearEl.textContent = new Date().getFullYear();
}

async function fetchJson(url) {
  const response = await fetch(url, {
    headers: { "Accept": "application/vnd.github+json" },
  });
  if (!response.ok) {
    throw new Error(`Request failed: ${response.status}`);
  }
  return response.json();
}

function formatDate(iso) {
  const date = new Date(iso);
  return date.toLocaleDateString(undefined, { year: "numeric", month: "short", day: "numeric" });
}

function createPrCard(pr) {
  const el = document.createElement("article");
  el.className = "card";

  const state = pr.state === "closed" && pr.pull_request_merged_at ? "merged" : pr.state;
  const number = `#${pr.number}`;

  el.innerHTML = `
    <h3>${pr.title}</h3>
    <p>${pr.repository_url?.includes("SeedSigner/seedsigner") ? "SeedSigner" : ""}</p>
    <div class="card__meta">
      <span class="badge">${state}</span>
      <span>Opened ${formatDate(pr.created_at)}</span>
      <span>${number}</span>
    </div>
    <div class="card__links">
      <a class="btn secondary" target="_blank" rel="noreferrer" href="${pr.html_url}">View PR</a>
    </div>
  `;
  return el;
}

async function fetchSeedSignerPRs() {
  const container = document.getElementById("seedsigner-prs");
  if (!container) return;

  const loading = document.createElement("div");
  loading.className = "card";
  loading.innerHTML = "Loading SeedSigner PRs...";
  container.appendChild(loading);

  try {
    const query = `repo:SeedSigner/seedsigner is:pr author:${GITHUB_USERNAME}`;
    const url = `https://api.github.com/search/issues?q=${encodeURIComponent(query)}&sort=created&order=desc&per_page=8`;
    const data = await fetchJson(url);

    container.innerHTML = "";
    if (!data.items || data.items.length === 0) {
      const empty = document.createElement("div");
      empty.className = "card";
      empty.innerHTML = "No PRs found yet — check back soon.";
      container.appendChild(empty);
      return;
    }

    data.items.forEach((item) => {
      const card = createPrCard(item);
      container.appendChild(card);
    });
  } catch (err) {
    container.innerHTML = "";
    const error = document.createElement("div");
    error.className = "card";
    error.innerHTML = "Unable to load PRs (rate limit or network). Use the button above to view on GitHub.";
    container.appendChild(error);
    console.error(err);
  }
}

function initSmoothScroll() {
  document.querySelectorAll('a[href^="#"]').forEach((anchor) => {
    anchor.addEventListener("click", function (e) {
      const targetId = this.getAttribute("href");
      if (!targetId || targetId === "#") return;
      const target = document.querySelector(targetId);
      if (!target) return;
      e.preventDefault();
      target.scrollIntoView({ behavior: "smooth" });
    });
  });
}

window.addEventListener("DOMContentLoaded", () => {
  setYear();
  initSmoothScroll();
  fetchSeedSignerPRs();
});

