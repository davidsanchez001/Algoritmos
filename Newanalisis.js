class AnalisisGrafos {
  constructor() {
    this.nodes = new Set()
    this.adj = {} 
    this.revAdj = {} 
    this.edgeCount = 0
    this.inDegree = {} 
    this.outDegree = {} 
    this.pagerankScores = null
    this.community = {} 
  }

  cargarAristasFromArray(edges) {
    this._reset()
    for (const e of edges) {
      const a = Number(e.fromNodeId)
      const b = Number(e.toNodeId)
      if (Number.isNaN(a) || Number.isNaN(b)) continue
      this.nodes.add(a)
      this.nodes.add(b)
      if (!this.adj[a]) this.adj[a] = []
      this.adj[a].push(b)
      if (!this.revAdj[b]) this.revAdj[b] = []
      this.revAdj[b].push(a)
      this.edgeCount++
    }
    for (const n of this.nodes) {
      if (!this.adj[n]) this.adj[n] = []
      if (!this.revAdj[n]) this.revAdj[n] = []
    }
    this._calcularGradosEnCarga()
  }

  _calcularGradosEnCarga() {
    this.inDegree = {}
    this.outDegree = {}
    for (const n of this.nodes) {
      this.inDegree[n] = this.revAdj[n] ? this.revAdj[n].length : 0
      this.outDegree[n] = this.adj[n] ? this.adj[n].length : 0
    }
  }

  obtenerTopInfluencers(k = 10) {
    const arr = Array.from(this.nodes).map(n => ({ node: n, in: this.inDegree[n] || 0 }))
    arr.sort((a,b) => b.in - a.in)
    return arr.slice(0, k)
  }

  bfs(start) {
    const s = Number(start)
    if (Number.isNaN(s) || !this.nodes.has(s)) return {dist: {}, pred: {}}
    const dist = {}
    const pred = {}
    const q = []
    for (const n of this.nodes) dist[n] = Infinity
    dist[s] = 0
    q.push(s)
    while (q.length) {
      const u = q.shift()
      const neighbors = this.adj[u] || []
      for (const v of neighbors) {
        if (dist[v] === Infinity) {
          dist[v] = dist[u] + 1
          pred[v] = u
          q.push(v)
        }
      }
    }
    return {dist, pred}
  }

  dfs(start) {
    const s = Number(start)
    if (Number.isNaN(s) || !this.nodes.has(s)) return {visited: new Set()}
    const stack = [s]
    const visited = new Set()
    while (stack.length) {
      const u = stack.pop()
      if (visited.has(u)) continue
      visited.add(u)
      const neighbors = (this.adj[u] || []).concat(this.revAdj[u] || [])
      for (const v of neighbors) if (!visited.has(v)) stack.push(v)
    }
    return {visited}
  }

  calcularPagerank({d = 0.85, maxIter = 50, tol = 1e-6} = {}) {
    const nodes = Array.from(this.nodes)
    const N = nodes.length
    if (N === 0) return {}
    const idx = {}
    nodes.forEach((n,i) => idx[n] = i)
    let pr = new Array(N).fill(1 / N)
    const outDeg = nodes.map(n => (this.outDegree[n] || 0))
    for (let iter = 0; iter < maxIter; iter++) {
      const newPr = new Array(N).fill((1 - d) / N)
      let diff = 0
      for (let i = 0; i < N; i++) {
        const u = nodes[i]
        const neighbors = this.adj[u] || []
        if (neighbors.length === 0) {
          for (let j = 0; j < N; j++) newPr[j] += d * pr[i] / N
        } else {
          const share = d * pr[i] / neighbors.length
          for (const v of neighbors) {
            newPr[idx[v]] += share
          }
        }
      }
      for (let i = 0; i < N; i++) diff += Math.abs(newPr[i] - pr[i])
      pr = newPr
      if (diff < tol) break
    }
    const out = {}
    nodes.forEach((n,i) => out[n] = pr[i])
    this.pagerankScores = out
    return out
  }

  aproximarBetweenness({sampleSize = 100} = {}) {
    const nodesArr = Array.from(this.nodes)
    const n = nodesArr.length
    if (n === 0) return {}
    if (sampleSize > n) sampleSize = n
    const sources = nodesArr.slice(0, sampleSize)
    const CB = {}
    for (const v of nodesArr) CB[v] = 0
    for (const s of sources) {
      const S = []
      const P = {} 
      const sigma = {}
      const dist = {}
      const Q = []
      for (const v of nodesArr) {
        P[v] = []
        sigma[v] = 0
        dist[v] = -1
      }
      sigma[s] = 1
      dist[s] = 0
      Q.push(s)
      while (Q.length) {
        const v = Q.shift()
        S.push(v)
        for (const w of this.adj[v] || []) {
          if (dist[w] < 0) {
            dist[w] = dist[v] + 1
            Q.push(w)
          }
          if (dist[w] === dist[v] + 1) {
            sigma[w] += sigma[v]
            P[w].push(v)
          }
        }
      }
      const delta = {}
      for (const v of nodesArr) delta[v] = 0
      while (S.length) {
        const w = S.pop()
        for (const v of P[w]) {
          delta[v] += (sigma[v] / sigma[w]) * (1 + delta[w])
        }
        if (w !== s) CB[w] += delta[w]
      }
    }
    return CB
  }

  labelPropagation({maxIter = 50} = {}) {
    const nodes = Array.from(this.nodes)
    const label = {}
    nodes.forEach(n => label[n] = n) 
    let changed = true
    let iter = 0
    while (changed && iter < maxIter) {
      changed = false
      iter++
      for (const n of nodes) {
        const neigh = (this.adj[n] || []).concat(this.revAdj[n] || [])
        if (neigh.length === 0) continue
        const counts = {}
        for (const v of neigh) counts[label[v]] = (counts[label[v]] || 0) + 1
        let best = null, bestCount = -1
        for (const lab in counts) {
          const cnt = counts[lab]
          if (cnt > bestCount || (cnt === bestCount && Number(lab) < Number(best))) {
            best = lab
            bestCount = cnt
          }
        }
        if (best != null && label[n] != best) {
          label[n] = Number(best)
          changed = true
        }
      }
    }
    const map = {}
    let next = 0
    for (const n of nodes) {
      const lab = label[n]
      if (!(lab in map)) map[lab] = next++
      this.community[n] = map[lab]
    }
    return this.community
  }

  ejecutarAnalisisCompleto({edges = [], pagerankOpts = {}, betweennessSample = 100, communities = {}} = {}) {
    this.cargarAristasFromArray(edges)
    const basicas = {
      nodesCount: this.nodes.size,
      edgesCount: this.edgeCount
    }
    const grados = {
      inDegree: this.inDegree,
      outDegree: this.outDegree,
      topInfluencers: this.obtenerTopInfluencers(10)
    }
    const pr = this.calcularPagerank(pagerankOpts)
    const bet = this.aproximarBetweenness({sampleSize: betweennessSample})
    const comm = this.labelPropagation(communities)
    const resultados = {
      basicas,
      grados,
      pagerank: pr,
      betweenness: bet,
      comunidades: comm
    }
    return resultados
  }

  _reset() {
    this.nodes = new Set()
    this.adj = {}
    this.revAdj = {}
    this.edgeCount = 0
    this.inDegree = {}
    this.outDegree = {}
    this.pagerankScores = null
    this.community = {}
  }
}

if (typeof window !== "undefined") {
  window.AnalisisGrafos = AnalisisGrafos
}
if (typeof module !== "undefined" && module.exports) {
  module.exports = AnalisisGrafos
}
