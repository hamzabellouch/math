import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound72
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2304 : keyMomentRows (2304 : Fin 2886) =
    keyMomentRow2304 := by decide +kernel

theorem keyMomentRowsAt2305 : keyMomentRows (2305 : Fin 2886) =
    keyMomentRow2305 := by decide +kernel

theorem keyMomentRowsAt2306 : keyMomentRows (2306 : Fin 2886) =
    keyMomentRow2306 := by decide +kernel

theorem keyMomentRowsAt2307 : keyMomentRows (2307 : Fin 2886) =
    keyMomentRow2307 := by decide +kernel

theorem keyMomentRowsAt2308 : keyMomentRows (2308 : Fin 2886) =
    keyMomentRow2308 := by decide +kernel

theorem keyMomentRowsAt2309 : keyMomentRows (2309 : Fin 2886) =
    keyMomentRow2309 := by decide +kernel

theorem keyMomentRowsAt2310 : keyMomentRows (2310 : Fin 2886) =
    keyMomentRow2310 := by decide +kernel

theorem keyMomentRowsAt2311 : keyMomentRows (2311 : Fin 2886) =
    keyMomentRow2311 := by decide +kernel

theorem keyMomentRowsAt2312 : keyMomentRows (2312 : Fin 2886) =
    keyMomentRow2312 := by decide +kernel

theorem keyMomentRowsAt2313 : keyMomentRows (2313 : Fin 2886) =
    keyMomentRow2313 := by decide +kernel

theorem keyMomentRowsAt2314 : keyMomentRows (2314 : Fin 2886) =
    keyMomentRow2314 := by decide +kernel

theorem keyMomentRowsAt2315 : keyMomentRows (2315 : Fin 2886) =
    keyMomentRow2315 := by decide +kernel

theorem keyMomentRowsAt2316 : keyMomentRows (2316 : Fin 2886) =
    keyMomentRow2316 := by decide +kernel

theorem keyMomentRowsAt2317 : keyMomentRows (2317 : Fin 2886) =
    keyMomentRow2317 := by decide +kernel

theorem keyMomentRowsAt2318 : keyMomentRows (2318 : Fin 2886) =
    keyMomentRow2318 := by decide +kernel

theorem keyMomentRowsAt2319 : keyMomentRows (2319 : Fin 2886) =
    keyMomentRow2319 := by decide +kernel

theorem keyMomentRowsAt2320 : keyMomentRows (2320 : Fin 2886) =
    keyMomentRow2320 := by decide +kernel

theorem keyMomentRowsAt2321 : keyMomentRows (2321 : Fin 2886) =
    keyMomentRow2321 := by decide +kernel

theorem keyMomentRowsAt2322 : keyMomentRows (2322 : Fin 2886) =
    keyMomentRow2322 := by decide +kernel

theorem keyMomentRowsAt2323 : keyMomentRows (2323 : Fin 2886) =
    keyMomentRow2323 := by decide +kernel

theorem keyMomentRowsAt2324 : keyMomentRows (2324 : Fin 2886) =
    keyMomentRow2324 := by decide +kernel

theorem keyMomentRowsAt2325 : keyMomentRows (2325 : Fin 2886) =
    keyMomentRow2325 := by decide +kernel

theorem keyMomentRowsAt2326 : keyMomentRows (2326 : Fin 2886) =
    keyMomentRow2326 := by decide +kernel

theorem keyMomentRowsAt2327 : keyMomentRows (2327 : Fin 2886) =
    keyMomentRow2327 := by decide +kernel

theorem keyMomentRowsAt2328 : keyMomentRows (2328 : Fin 2886) =
    keyMomentRow2328 := by decide +kernel

theorem keyMomentRowsAt2329 : keyMomentRows (2329 : Fin 2886) =
    keyMomentRow2329 := by decide +kernel

theorem keyMomentRowsAt2330 : keyMomentRows (2330 : Fin 2886) =
    keyMomentRow2330 := by decide +kernel

theorem keyMomentRowsAt2331 : keyMomentRows (2331 : Fin 2886) =
    keyMomentRow2331 := by decide +kernel

theorem keyMomentRowsAt2332 : keyMomentRows (2332 : Fin 2886) =
    keyMomentRow2332 := by decide +kernel

theorem keyMomentRowsAt2333 : keyMomentRows (2333 : Fin 2886) =
    keyMomentRow2333 := by decide +kernel

theorem keyMomentRowsAt2334 : keyMomentRows (2334 : Fin 2886) =
    keyMomentRow2334 := by decide +kernel

theorem keyMomentRowsAt2335 : keyMomentRows (2335 : Fin 2886) =
    keyMomentRow2335 := by decide +kernel

theorem keyMomentChunkSound72 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 72) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2304 ∨ k.val = 2305 ∨ k.val = 2306 ∨ k.val = 2307 ∨ k.val = 2308 ∨ k.val = 2309 ∨ k.val = 2310 ∨ k.val = 2311 ∨ k.val = 2312 ∨ k.val = 2313 ∨ k.val = 2314 ∨ k.val = 2315 ∨ k.val = 2316 ∨ k.val = 2317 ∨ k.val = 2318 ∨ k.val = 2319 ∨ k.val = 2320 ∨ k.val = 2321 ∨ k.val = 2322 ∨ k.val = 2323 ∨ k.val = 2324 ∨ k.val = 2325 ∨ k.val = 2326 ∨ k.val = 2327 ∨ k.val = 2328 ∨ k.val = 2329 ∨ k.val = 2330 ∨ k.val = 2331 ∨ k.val = 2332 ∨ k.val = 2333 ∨ k.val = 2334 ∨ k.val = 2335 := by omega
  rcases heq with h2304 | h2305 | h2306 | h2307 | h2308 | h2309 | h2310 | h2311 | h2312 | h2313 | h2314 | h2315 | h2316 | h2317 | h2318 | h2319 | h2320 | h2321 | h2322 | h2323 | h2324 | h2325 | h2326 | h2327 | h2328 | h2329 | h2330 | h2331 | h2332 | h2333 | h2334 | h2335
  · have he : k = (2304 : Fin 2886) := Fin.ext h2304
    subst k
    rw [keyMomentRowsAt2304]
    exact keyMoment2304 B hB
  · have he : k = (2305 : Fin 2886) := Fin.ext h2305
    subst k
    rw [keyMomentRowsAt2305]
    exact keyMoment2305 B hB
  · have he : k = (2306 : Fin 2886) := Fin.ext h2306
    subst k
    rw [keyMomentRowsAt2306]
    exact keyMoment2306 B hB
  · have he : k = (2307 : Fin 2886) := Fin.ext h2307
    subst k
    rw [keyMomentRowsAt2307]
    exact keyMoment2307 B hB
  · have he : k = (2308 : Fin 2886) := Fin.ext h2308
    subst k
    rw [keyMomentRowsAt2308]
    exact keyMoment2308 B hB
  · have he : k = (2309 : Fin 2886) := Fin.ext h2309
    subst k
    rw [keyMomentRowsAt2309]
    exact keyMoment2309 B hB
  · have he : k = (2310 : Fin 2886) := Fin.ext h2310
    subst k
    rw [keyMomentRowsAt2310]
    exact keyMoment2310 B hB
  · have he : k = (2311 : Fin 2886) := Fin.ext h2311
    subst k
    rw [keyMomentRowsAt2311]
    exact keyMoment2311 B hB
  · have he : k = (2312 : Fin 2886) := Fin.ext h2312
    subst k
    rw [keyMomentRowsAt2312]
    exact keyMoment2312 B hB
  · have he : k = (2313 : Fin 2886) := Fin.ext h2313
    subst k
    rw [keyMomentRowsAt2313]
    exact keyMoment2313 B hB
  · have he : k = (2314 : Fin 2886) := Fin.ext h2314
    subst k
    rw [keyMomentRowsAt2314]
    exact keyMoment2314 B hB
  · have he : k = (2315 : Fin 2886) := Fin.ext h2315
    subst k
    rw [keyMomentRowsAt2315]
    exact keyMoment2315 B hB
  · have he : k = (2316 : Fin 2886) := Fin.ext h2316
    subst k
    rw [keyMomentRowsAt2316]
    exact keyMoment2316 B hB
  · have he : k = (2317 : Fin 2886) := Fin.ext h2317
    subst k
    rw [keyMomentRowsAt2317]
    exact keyMoment2317 B hB
  · have he : k = (2318 : Fin 2886) := Fin.ext h2318
    subst k
    rw [keyMomentRowsAt2318]
    exact keyMoment2318 B hB
  · have he : k = (2319 : Fin 2886) := Fin.ext h2319
    subst k
    rw [keyMomentRowsAt2319]
    exact keyMoment2319 B hB
  · have he : k = (2320 : Fin 2886) := Fin.ext h2320
    subst k
    rw [keyMomentRowsAt2320]
    exact keyMoment2320 B hB
  · have he : k = (2321 : Fin 2886) := Fin.ext h2321
    subst k
    rw [keyMomentRowsAt2321]
    exact keyMoment2321 B hB
  · have he : k = (2322 : Fin 2886) := Fin.ext h2322
    subst k
    rw [keyMomentRowsAt2322]
    exact keyMoment2322 B hB
  · have he : k = (2323 : Fin 2886) := Fin.ext h2323
    subst k
    rw [keyMomentRowsAt2323]
    exact keyMoment2323 B hB
  · have he : k = (2324 : Fin 2886) := Fin.ext h2324
    subst k
    rw [keyMomentRowsAt2324]
    exact keyMoment2324 B hB
  · have he : k = (2325 : Fin 2886) := Fin.ext h2325
    subst k
    rw [keyMomentRowsAt2325]
    exact keyMoment2325 B hB
  · have he : k = (2326 : Fin 2886) := Fin.ext h2326
    subst k
    rw [keyMomentRowsAt2326]
    exact keyMoment2326 B hB
  · have he : k = (2327 : Fin 2886) := Fin.ext h2327
    subst k
    rw [keyMomentRowsAt2327]
    exact keyMoment2327 B hB
  · have he : k = (2328 : Fin 2886) := Fin.ext h2328
    subst k
    rw [keyMomentRowsAt2328]
    exact keyMoment2328 B hB
  · have he : k = (2329 : Fin 2886) := Fin.ext h2329
    subst k
    rw [keyMomentRowsAt2329]
    exact keyMoment2329 B hB
  · have he : k = (2330 : Fin 2886) := Fin.ext h2330
    subst k
    rw [keyMomentRowsAt2330]
    exact keyMoment2330 B hB
  · have he : k = (2331 : Fin 2886) := Fin.ext h2331
    subst k
    rw [keyMomentRowsAt2331]
    exact keyMoment2331 B hB
  · have he : k = (2332 : Fin 2886) := Fin.ext h2332
    subst k
    rw [keyMomentRowsAt2332]
    exact keyMoment2332 B hB
  · have he : k = (2333 : Fin 2886) := Fin.ext h2333
    subst k
    rw [keyMomentRowsAt2333]
    exact keyMoment2333 B hB
  · have he : k = (2334 : Fin 2886) := Fin.ext h2334
    subst k
    rw [keyMomentRowsAt2334]
    exact keyMoment2334 B hB
  · have he : k = (2335 : Fin 2886) := Fin.ext h2335
    subst k
    rw [keyMomentRowsAt2335]
    exact keyMoment2335 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
