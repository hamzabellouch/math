import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound73
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2336 : keyMomentRows (2336 : Fin 2886) =
    keyMomentRow2336 := by decide +kernel

theorem keyMomentRowsAt2337 : keyMomentRows (2337 : Fin 2886) =
    keyMomentRow2337 := by decide +kernel

theorem keyMomentRowsAt2338 : keyMomentRows (2338 : Fin 2886) =
    keyMomentRow2338 := by decide +kernel

theorem keyMomentRowsAt2339 : keyMomentRows (2339 : Fin 2886) =
    keyMomentRow2339 := by decide +kernel

theorem keyMomentRowsAt2340 : keyMomentRows (2340 : Fin 2886) =
    keyMomentRow2340 := by decide +kernel

theorem keyMomentRowsAt2341 : keyMomentRows (2341 : Fin 2886) =
    keyMomentRow2341 := by decide +kernel

theorem keyMomentRowsAt2342 : keyMomentRows (2342 : Fin 2886) =
    keyMomentRow2342 := by decide +kernel

theorem keyMomentRowsAt2343 : keyMomentRows (2343 : Fin 2886) =
    keyMomentRow2343 := by decide +kernel

theorem keyMomentRowsAt2344 : keyMomentRows (2344 : Fin 2886) =
    keyMomentRow2344 := by decide +kernel

theorem keyMomentRowsAt2345 : keyMomentRows (2345 : Fin 2886) =
    keyMomentRow2345 := by decide +kernel

theorem keyMomentRowsAt2346 : keyMomentRows (2346 : Fin 2886) =
    keyMomentRow2346 := by decide +kernel

theorem keyMomentRowsAt2347 : keyMomentRows (2347 : Fin 2886) =
    keyMomentRow2347 := by decide +kernel

theorem keyMomentRowsAt2348 : keyMomentRows (2348 : Fin 2886) =
    keyMomentRow2348 := by decide +kernel

theorem keyMomentRowsAt2349 : keyMomentRows (2349 : Fin 2886) =
    keyMomentRow2349 := by decide +kernel

theorem keyMomentRowsAt2350 : keyMomentRows (2350 : Fin 2886) =
    keyMomentRow2350 := by decide +kernel

theorem keyMomentRowsAt2351 : keyMomentRows (2351 : Fin 2886) =
    keyMomentRow2351 := by decide +kernel

theorem keyMomentRowsAt2352 : keyMomentRows (2352 : Fin 2886) =
    keyMomentRow2352 := by decide +kernel

theorem keyMomentRowsAt2353 : keyMomentRows (2353 : Fin 2886) =
    keyMomentRow2353 := by decide +kernel

theorem keyMomentRowsAt2354 : keyMomentRows (2354 : Fin 2886) =
    keyMomentRow2354 := by decide +kernel

theorem keyMomentRowsAt2355 : keyMomentRows (2355 : Fin 2886) =
    keyMomentRow2355 := by decide +kernel

theorem keyMomentRowsAt2356 : keyMomentRows (2356 : Fin 2886) =
    keyMomentRow2356 := by decide +kernel

theorem keyMomentRowsAt2357 : keyMomentRows (2357 : Fin 2886) =
    keyMomentRow2357 := by decide +kernel

theorem keyMomentRowsAt2358 : keyMomentRows (2358 : Fin 2886) =
    keyMomentRow2358 := by decide +kernel

theorem keyMomentRowsAt2359 : keyMomentRows (2359 : Fin 2886) =
    keyMomentRow2359 := by decide +kernel

theorem keyMomentRowsAt2360 : keyMomentRows (2360 : Fin 2886) =
    keyMomentRow2360 := by decide +kernel

theorem keyMomentRowsAt2361 : keyMomentRows (2361 : Fin 2886) =
    keyMomentRow2361 := by decide +kernel

theorem keyMomentRowsAt2362 : keyMomentRows (2362 : Fin 2886) =
    keyMomentRow2362 := by decide +kernel

theorem keyMomentRowsAt2363 : keyMomentRows (2363 : Fin 2886) =
    keyMomentRow2363 := by decide +kernel

theorem keyMomentRowsAt2364 : keyMomentRows (2364 : Fin 2886) =
    keyMomentRow2364 := by decide +kernel

theorem keyMomentRowsAt2365 : keyMomentRows (2365 : Fin 2886) =
    keyMomentRow2365 := by decide +kernel

theorem keyMomentRowsAt2366 : keyMomentRows (2366 : Fin 2886) =
    keyMomentRow2366 := by decide +kernel

theorem keyMomentRowsAt2367 : keyMomentRows (2367 : Fin 2886) =
    keyMomentRow2367 := by decide +kernel

theorem keyMomentChunkSound73 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 73) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2336 ∨ k.val = 2337 ∨ k.val = 2338 ∨ k.val = 2339 ∨ k.val = 2340 ∨ k.val = 2341 ∨ k.val = 2342 ∨ k.val = 2343 ∨ k.val = 2344 ∨ k.val = 2345 ∨ k.val = 2346 ∨ k.val = 2347 ∨ k.val = 2348 ∨ k.val = 2349 ∨ k.val = 2350 ∨ k.val = 2351 ∨ k.val = 2352 ∨ k.val = 2353 ∨ k.val = 2354 ∨ k.val = 2355 ∨ k.val = 2356 ∨ k.val = 2357 ∨ k.val = 2358 ∨ k.val = 2359 ∨ k.val = 2360 ∨ k.val = 2361 ∨ k.val = 2362 ∨ k.val = 2363 ∨ k.val = 2364 ∨ k.val = 2365 ∨ k.val = 2366 ∨ k.val = 2367 := by omega
  rcases heq with h2336 | h2337 | h2338 | h2339 | h2340 | h2341 | h2342 | h2343 | h2344 | h2345 | h2346 | h2347 | h2348 | h2349 | h2350 | h2351 | h2352 | h2353 | h2354 | h2355 | h2356 | h2357 | h2358 | h2359 | h2360 | h2361 | h2362 | h2363 | h2364 | h2365 | h2366 | h2367
  · have he : k = (2336 : Fin 2886) := Fin.ext h2336
    subst k
    rw [keyMomentRowsAt2336]
    exact keyMoment2336 B hB
  · have he : k = (2337 : Fin 2886) := Fin.ext h2337
    subst k
    rw [keyMomentRowsAt2337]
    exact keyMoment2337 B hB
  · have he : k = (2338 : Fin 2886) := Fin.ext h2338
    subst k
    rw [keyMomentRowsAt2338]
    exact keyMoment2338 B hB
  · have he : k = (2339 : Fin 2886) := Fin.ext h2339
    subst k
    rw [keyMomentRowsAt2339]
    exact keyMoment2339 B hB
  · have he : k = (2340 : Fin 2886) := Fin.ext h2340
    subst k
    rw [keyMomentRowsAt2340]
    exact keyMoment2340 B hB
  · have he : k = (2341 : Fin 2886) := Fin.ext h2341
    subst k
    rw [keyMomentRowsAt2341]
    exact keyMoment2341 B hB
  · have he : k = (2342 : Fin 2886) := Fin.ext h2342
    subst k
    rw [keyMomentRowsAt2342]
    exact keyMoment2342 B hB
  · have he : k = (2343 : Fin 2886) := Fin.ext h2343
    subst k
    rw [keyMomentRowsAt2343]
    exact keyMoment2343 B hB
  · have he : k = (2344 : Fin 2886) := Fin.ext h2344
    subst k
    rw [keyMomentRowsAt2344]
    exact keyMoment2344 B hB
  · have he : k = (2345 : Fin 2886) := Fin.ext h2345
    subst k
    rw [keyMomentRowsAt2345]
    exact keyMoment2345 B hB
  · have he : k = (2346 : Fin 2886) := Fin.ext h2346
    subst k
    rw [keyMomentRowsAt2346]
    exact keyMoment2346 B hB
  · have he : k = (2347 : Fin 2886) := Fin.ext h2347
    subst k
    rw [keyMomentRowsAt2347]
    exact keyMoment2347 B hB
  · have he : k = (2348 : Fin 2886) := Fin.ext h2348
    subst k
    rw [keyMomentRowsAt2348]
    exact keyMoment2348 B hB
  · have he : k = (2349 : Fin 2886) := Fin.ext h2349
    subst k
    rw [keyMomentRowsAt2349]
    exact keyMoment2349 B hB
  · have he : k = (2350 : Fin 2886) := Fin.ext h2350
    subst k
    rw [keyMomentRowsAt2350]
    exact keyMoment2350 B hB
  · have he : k = (2351 : Fin 2886) := Fin.ext h2351
    subst k
    rw [keyMomentRowsAt2351]
    exact keyMoment2351 B hB
  · have he : k = (2352 : Fin 2886) := Fin.ext h2352
    subst k
    rw [keyMomentRowsAt2352]
    exact keyMoment2352 B hB
  · have he : k = (2353 : Fin 2886) := Fin.ext h2353
    subst k
    rw [keyMomentRowsAt2353]
    exact keyMoment2353 B hB
  · have he : k = (2354 : Fin 2886) := Fin.ext h2354
    subst k
    rw [keyMomentRowsAt2354]
    exact keyMoment2354 B hB
  · have he : k = (2355 : Fin 2886) := Fin.ext h2355
    subst k
    rw [keyMomentRowsAt2355]
    exact keyMoment2355 B hB
  · have he : k = (2356 : Fin 2886) := Fin.ext h2356
    subst k
    rw [keyMomentRowsAt2356]
    exact keyMoment2356 B hB
  · have he : k = (2357 : Fin 2886) := Fin.ext h2357
    subst k
    rw [keyMomentRowsAt2357]
    exact keyMoment2357 B hB
  · have he : k = (2358 : Fin 2886) := Fin.ext h2358
    subst k
    rw [keyMomentRowsAt2358]
    exact keyMoment2358 B hB
  · have he : k = (2359 : Fin 2886) := Fin.ext h2359
    subst k
    rw [keyMomentRowsAt2359]
    exact keyMoment2359 B hB
  · have he : k = (2360 : Fin 2886) := Fin.ext h2360
    subst k
    rw [keyMomentRowsAt2360]
    exact keyMoment2360 B hB
  · have he : k = (2361 : Fin 2886) := Fin.ext h2361
    subst k
    rw [keyMomentRowsAt2361]
    exact keyMoment2361 B hB
  · have he : k = (2362 : Fin 2886) := Fin.ext h2362
    subst k
    rw [keyMomentRowsAt2362]
    exact keyMoment2362 B hB
  · have he : k = (2363 : Fin 2886) := Fin.ext h2363
    subst k
    rw [keyMomentRowsAt2363]
    exact keyMoment2363 B hB
  · have he : k = (2364 : Fin 2886) := Fin.ext h2364
    subst k
    rw [keyMomentRowsAt2364]
    exact keyMoment2364 B hB
  · have he : k = (2365 : Fin 2886) := Fin.ext h2365
    subst k
    rw [keyMomentRowsAt2365]
    exact keyMoment2365 B hB
  · have he : k = (2366 : Fin 2886) := Fin.ext h2366
    subst k
    rw [keyMomentRowsAt2366]
    exact keyMoment2366 B hB
  · have he : k = (2367 : Fin 2886) := Fin.ext h2367
    subst k
    rw [keyMomentRowsAt2367]
    exact keyMoment2367 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
