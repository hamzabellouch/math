import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound71
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2272 : keyMomentRows (2272 : Fin 2886) =
    keyMomentRow2272 := by decide +kernel

theorem keyMomentRowsAt2273 : keyMomentRows (2273 : Fin 2886) =
    keyMomentRow2273 := by decide +kernel

theorem keyMomentRowsAt2274 : keyMomentRows (2274 : Fin 2886) =
    keyMomentRow2274 := by decide +kernel

theorem keyMomentRowsAt2275 : keyMomentRows (2275 : Fin 2886) =
    keyMomentRow2275 := by decide +kernel

theorem keyMomentRowsAt2276 : keyMomentRows (2276 : Fin 2886) =
    keyMomentRow2276 := by decide +kernel

theorem keyMomentRowsAt2277 : keyMomentRows (2277 : Fin 2886) =
    keyMomentRow2277 := by decide +kernel

theorem keyMomentRowsAt2278 : keyMomentRows (2278 : Fin 2886) =
    keyMomentRow2278 := by decide +kernel

theorem keyMomentRowsAt2279 : keyMomentRows (2279 : Fin 2886) =
    keyMomentRow2279 := by decide +kernel

theorem keyMomentRowsAt2280 : keyMomentRows (2280 : Fin 2886) =
    keyMomentRow2280 := by decide +kernel

theorem keyMomentRowsAt2281 : keyMomentRows (2281 : Fin 2886) =
    keyMomentRow2281 := by decide +kernel

theorem keyMomentRowsAt2282 : keyMomentRows (2282 : Fin 2886) =
    keyMomentRow2282 := by decide +kernel

theorem keyMomentRowsAt2283 : keyMomentRows (2283 : Fin 2886) =
    keyMomentRow2283 := by decide +kernel

theorem keyMomentRowsAt2284 : keyMomentRows (2284 : Fin 2886) =
    keyMomentRow2284 := by decide +kernel

theorem keyMomentRowsAt2285 : keyMomentRows (2285 : Fin 2886) =
    keyMomentRow2285 := by decide +kernel

theorem keyMomentRowsAt2286 : keyMomentRows (2286 : Fin 2886) =
    keyMomentRow2286 := by decide +kernel

theorem keyMomentRowsAt2287 : keyMomentRows (2287 : Fin 2886) =
    keyMomentRow2287 := by decide +kernel

theorem keyMomentRowsAt2288 : keyMomentRows (2288 : Fin 2886) =
    keyMomentRow2288 := by decide +kernel

theorem keyMomentRowsAt2289 : keyMomentRows (2289 : Fin 2886) =
    keyMomentRow2289 := by decide +kernel

theorem keyMomentRowsAt2290 : keyMomentRows (2290 : Fin 2886) =
    keyMomentRow2290 := by decide +kernel

theorem keyMomentRowsAt2291 : keyMomentRows (2291 : Fin 2886) =
    keyMomentRow2291 := by decide +kernel

theorem keyMomentRowsAt2292 : keyMomentRows (2292 : Fin 2886) =
    keyMomentRow2292 := by decide +kernel

theorem keyMomentRowsAt2293 : keyMomentRows (2293 : Fin 2886) =
    keyMomentRow2293 := by decide +kernel

theorem keyMomentRowsAt2294 : keyMomentRows (2294 : Fin 2886) =
    keyMomentRow2294 := by decide +kernel

theorem keyMomentRowsAt2295 : keyMomentRows (2295 : Fin 2886) =
    keyMomentRow2295 := by decide +kernel

theorem keyMomentRowsAt2296 : keyMomentRows (2296 : Fin 2886) =
    keyMomentRow2296 := by decide +kernel

theorem keyMomentRowsAt2297 : keyMomentRows (2297 : Fin 2886) =
    keyMomentRow2297 := by decide +kernel

theorem keyMomentRowsAt2298 : keyMomentRows (2298 : Fin 2886) =
    keyMomentRow2298 := by decide +kernel

theorem keyMomentRowsAt2299 : keyMomentRows (2299 : Fin 2886) =
    keyMomentRow2299 := by decide +kernel

theorem keyMomentRowsAt2300 : keyMomentRows (2300 : Fin 2886) =
    keyMomentRow2300 := by decide +kernel

theorem keyMomentRowsAt2301 : keyMomentRows (2301 : Fin 2886) =
    keyMomentRow2301 := by decide +kernel

theorem keyMomentRowsAt2302 : keyMomentRows (2302 : Fin 2886) =
    keyMomentRow2302 := by decide +kernel

theorem keyMomentRowsAt2303 : keyMomentRows (2303 : Fin 2886) =
    keyMomentRow2303 := by decide +kernel

theorem keyMomentChunkSound71 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 71) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2272 ∨ k.val = 2273 ∨ k.val = 2274 ∨ k.val = 2275 ∨ k.val = 2276 ∨ k.val = 2277 ∨ k.val = 2278 ∨ k.val = 2279 ∨ k.val = 2280 ∨ k.val = 2281 ∨ k.val = 2282 ∨ k.val = 2283 ∨ k.val = 2284 ∨ k.val = 2285 ∨ k.val = 2286 ∨ k.val = 2287 ∨ k.val = 2288 ∨ k.val = 2289 ∨ k.val = 2290 ∨ k.val = 2291 ∨ k.val = 2292 ∨ k.val = 2293 ∨ k.val = 2294 ∨ k.val = 2295 ∨ k.val = 2296 ∨ k.val = 2297 ∨ k.val = 2298 ∨ k.val = 2299 ∨ k.val = 2300 ∨ k.val = 2301 ∨ k.val = 2302 ∨ k.val = 2303 := by omega
  rcases heq with h2272 | h2273 | h2274 | h2275 | h2276 | h2277 | h2278 | h2279 | h2280 | h2281 | h2282 | h2283 | h2284 | h2285 | h2286 | h2287 | h2288 | h2289 | h2290 | h2291 | h2292 | h2293 | h2294 | h2295 | h2296 | h2297 | h2298 | h2299 | h2300 | h2301 | h2302 | h2303
  · have he : k = (2272 : Fin 2886) := Fin.ext h2272
    subst k
    rw [keyMomentRowsAt2272]
    exact keyMoment2272 B hB
  · have he : k = (2273 : Fin 2886) := Fin.ext h2273
    subst k
    rw [keyMomentRowsAt2273]
    exact keyMoment2273 B hB
  · have he : k = (2274 : Fin 2886) := Fin.ext h2274
    subst k
    rw [keyMomentRowsAt2274]
    exact keyMoment2274 B hB
  · have he : k = (2275 : Fin 2886) := Fin.ext h2275
    subst k
    rw [keyMomentRowsAt2275]
    exact keyMoment2275 B hB
  · have he : k = (2276 : Fin 2886) := Fin.ext h2276
    subst k
    rw [keyMomentRowsAt2276]
    exact keyMoment2276 B hB
  · have he : k = (2277 : Fin 2886) := Fin.ext h2277
    subst k
    rw [keyMomentRowsAt2277]
    exact keyMoment2277 B hB
  · have he : k = (2278 : Fin 2886) := Fin.ext h2278
    subst k
    rw [keyMomentRowsAt2278]
    exact keyMoment2278 B hB
  · have he : k = (2279 : Fin 2886) := Fin.ext h2279
    subst k
    rw [keyMomentRowsAt2279]
    exact keyMoment2279 B hB
  · have he : k = (2280 : Fin 2886) := Fin.ext h2280
    subst k
    rw [keyMomentRowsAt2280]
    exact keyMoment2280 B hB
  · have he : k = (2281 : Fin 2886) := Fin.ext h2281
    subst k
    rw [keyMomentRowsAt2281]
    exact keyMoment2281 B hB
  · have he : k = (2282 : Fin 2886) := Fin.ext h2282
    subst k
    rw [keyMomentRowsAt2282]
    exact keyMoment2282 B hB
  · have he : k = (2283 : Fin 2886) := Fin.ext h2283
    subst k
    rw [keyMomentRowsAt2283]
    exact keyMoment2283 B hB
  · have he : k = (2284 : Fin 2886) := Fin.ext h2284
    subst k
    rw [keyMomentRowsAt2284]
    exact keyMoment2284 B hB
  · have he : k = (2285 : Fin 2886) := Fin.ext h2285
    subst k
    rw [keyMomentRowsAt2285]
    exact keyMoment2285 B hB
  · have he : k = (2286 : Fin 2886) := Fin.ext h2286
    subst k
    rw [keyMomentRowsAt2286]
    exact keyMoment2286 B hB
  · have he : k = (2287 : Fin 2886) := Fin.ext h2287
    subst k
    rw [keyMomentRowsAt2287]
    exact keyMoment2287 B hB
  · have he : k = (2288 : Fin 2886) := Fin.ext h2288
    subst k
    rw [keyMomentRowsAt2288]
    exact keyMoment2288 B hB
  · have he : k = (2289 : Fin 2886) := Fin.ext h2289
    subst k
    rw [keyMomentRowsAt2289]
    exact keyMoment2289 B hB
  · have he : k = (2290 : Fin 2886) := Fin.ext h2290
    subst k
    rw [keyMomentRowsAt2290]
    exact keyMoment2290 B hB
  · have he : k = (2291 : Fin 2886) := Fin.ext h2291
    subst k
    rw [keyMomentRowsAt2291]
    exact keyMoment2291 B hB
  · have he : k = (2292 : Fin 2886) := Fin.ext h2292
    subst k
    rw [keyMomentRowsAt2292]
    exact keyMoment2292 B hB
  · have he : k = (2293 : Fin 2886) := Fin.ext h2293
    subst k
    rw [keyMomentRowsAt2293]
    exact keyMoment2293 B hB
  · have he : k = (2294 : Fin 2886) := Fin.ext h2294
    subst k
    rw [keyMomentRowsAt2294]
    exact keyMoment2294 B hB
  · have he : k = (2295 : Fin 2886) := Fin.ext h2295
    subst k
    rw [keyMomentRowsAt2295]
    exact keyMoment2295 B hB
  · have he : k = (2296 : Fin 2886) := Fin.ext h2296
    subst k
    rw [keyMomentRowsAt2296]
    exact keyMoment2296 B hB
  · have he : k = (2297 : Fin 2886) := Fin.ext h2297
    subst k
    rw [keyMomentRowsAt2297]
    exact keyMoment2297 B hB
  · have he : k = (2298 : Fin 2886) := Fin.ext h2298
    subst k
    rw [keyMomentRowsAt2298]
    exact keyMoment2298 B hB
  · have he : k = (2299 : Fin 2886) := Fin.ext h2299
    subst k
    rw [keyMomentRowsAt2299]
    exact keyMoment2299 B hB
  · have he : k = (2300 : Fin 2886) := Fin.ext h2300
    subst k
    rw [keyMomentRowsAt2300]
    exact keyMoment2300 B hB
  · have he : k = (2301 : Fin 2886) := Fin.ext h2301
    subst k
    rw [keyMomentRowsAt2301]
    exact keyMoment2301 B hB
  · have he : k = (2302 : Fin 2886) := Fin.ext h2302
    subst k
    rw [keyMomentRowsAt2302]
    exact keyMoment2302 B hB
  · have he : k = (2303 : Fin 2886) := Fin.ext h2303
    subst k
    rw [keyMomentRowsAt2303]
    exact keyMoment2303 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
