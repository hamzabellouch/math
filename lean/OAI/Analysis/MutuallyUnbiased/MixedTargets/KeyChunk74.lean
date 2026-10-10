import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound74
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2368 : keyMomentRows (2368 : Fin 2886) =
    keyMomentRow2368 := by decide +kernel

theorem keyMomentRowsAt2369 : keyMomentRows (2369 : Fin 2886) =
    keyMomentRow2369 := by decide +kernel

theorem keyMomentRowsAt2370 : keyMomentRows (2370 : Fin 2886) =
    keyMomentRow2370 := by decide +kernel

theorem keyMomentRowsAt2371 : keyMomentRows (2371 : Fin 2886) =
    keyMomentRow2371 := by decide +kernel

theorem keyMomentRowsAt2372 : keyMomentRows (2372 : Fin 2886) =
    keyMomentRow2372 := by decide +kernel

theorem keyMomentRowsAt2373 : keyMomentRows (2373 : Fin 2886) =
    keyMomentRow2373 := by decide +kernel

theorem keyMomentRowsAt2374 : keyMomentRows (2374 : Fin 2886) =
    keyMomentRow2374 := by decide +kernel

theorem keyMomentRowsAt2375 : keyMomentRows (2375 : Fin 2886) =
    keyMomentRow2375 := by decide +kernel

theorem keyMomentRowsAt2376 : keyMomentRows (2376 : Fin 2886) =
    keyMomentRow2376 := by decide +kernel

theorem keyMomentRowsAt2377 : keyMomentRows (2377 : Fin 2886) =
    keyMomentRow2377 := by decide +kernel

theorem keyMomentRowsAt2378 : keyMomentRows (2378 : Fin 2886) =
    keyMomentRow2378 := by decide +kernel

theorem keyMomentRowsAt2379 : keyMomentRows (2379 : Fin 2886) =
    keyMomentRow2379 := by decide +kernel

theorem keyMomentRowsAt2380 : keyMomentRows (2380 : Fin 2886) =
    keyMomentRow2380 := by decide +kernel

theorem keyMomentRowsAt2381 : keyMomentRows (2381 : Fin 2886) =
    keyMomentRow2381 := by decide +kernel

theorem keyMomentRowsAt2382 : keyMomentRows (2382 : Fin 2886) =
    keyMomentRow2382 := by decide +kernel

theorem keyMomentRowsAt2383 : keyMomentRows (2383 : Fin 2886) =
    keyMomentRow2383 := by decide +kernel

theorem keyMomentRowsAt2384 : keyMomentRows (2384 : Fin 2886) =
    keyMomentRow2384 := by decide +kernel

theorem keyMomentRowsAt2385 : keyMomentRows (2385 : Fin 2886) =
    keyMomentRow2385 := by decide +kernel

theorem keyMomentRowsAt2386 : keyMomentRows (2386 : Fin 2886) =
    keyMomentRow2386 := by decide +kernel

theorem keyMomentRowsAt2387 : keyMomentRows (2387 : Fin 2886) =
    keyMomentRow2387 := by decide +kernel

theorem keyMomentRowsAt2388 : keyMomentRows (2388 : Fin 2886) =
    keyMomentRow2388 := by decide +kernel

theorem keyMomentRowsAt2389 : keyMomentRows (2389 : Fin 2886) =
    keyMomentRow2389 := by decide +kernel

theorem keyMomentRowsAt2390 : keyMomentRows (2390 : Fin 2886) =
    keyMomentRow2390 := by decide +kernel

theorem keyMomentRowsAt2391 : keyMomentRows (2391 : Fin 2886) =
    keyMomentRow2391 := by decide +kernel

theorem keyMomentRowsAt2392 : keyMomentRows (2392 : Fin 2886) =
    keyMomentRow2392 := by decide +kernel

theorem keyMomentRowsAt2393 : keyMomentRows (2393 : Fin 2886) =
    keyMomentRow2393 := by decide +kernel

theorem keyMomentRowsAt2394 : keyMomentRows (2394 : Fin 2886) =
    keyMomentRow2394 := by decide +kernel

theorem keyMomentRowsAt2395 : keyMomentRows (2395 : Fin 2886) =
    keyMomentRow2395 := by decide +kernel

theorem keyMomentRowsAt2396 : keyMomentRows (2396 : Fin 2886) =
    keyMomentRow2396 := by decide +kernel

theorem keyMomentRowsAt2397 : keyMomentRows (2397 : Fin 2886) =
    keyMomentRow2397 := by decide +kernel

theorem keyMomentRowsAt2398 : keyMomentRows (2398 : Fin 2886) =
    keyMomentRow2398 := by decide +kernel

theorem keyMomentRowsAt2399 : keyMomentRows (2399 : Fin 2886) =
    keyMomentRow2399 := by decide +kernel

theorem keyMomentChunkSound74 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 74) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2368 ∨ k.val = 2369 ∨ k.val = 2370 ∨ k.val = 2371 ∨ k.val = 2372 ∨ k.val = 2373 ∨ k.val = 2374 ∨ k.val = 2375 ∨ k.val = 2376 ∨ k.val = 2377 ∨ k.val = 2378 ∨ k.val = 2379 ∨ k.val = 2380 ∨ k.val = 2381 ∨ k.val = 2382 ∨ k.val = 2383 ∨ k.val = 2384 ∨ k.val = 2385 ∨ k.val = 2386 ∨ k.val = 2387 ∨ k.val = 2388 ∨ k.val = 2389 ∨ k.val = 2390 ∨ k.val = 2391 ∨ k.val = 2392 ∨ k.val = 2393 ∨ k.val = 2394 ∨ k.val = 2395 ∨ k.val = 2396 ∨ k.val = 2397 ∨ k.val = 2398 ∨ k.val = 2399 := by omega
  rcases heq with h2368 | h2369 | h2370 | h2371 | h2372 | h2373 | h2374 | h2375 | h2376 | h2377 | h2378 | h2379 | h2380 | h2381 | h2382 | h2383 | h2384 | h2385 | h2386 | h2387 | h2388 | h2389 | h2390 | h2391 | h2392 | h2393 | h2394 | h2395 | h2396 | h2397 | h2398 | h2399
  · have he : k = (2368 : Fin 2886) := Fin.ext h2368
    subst k
    rw [keyMomentRowsAt2368]
    exact keyMoment2368 B hB
  · have he : k = (2369 : Fin 2886) := Fin.ext h2369
    subst k
    rw [keyMomentRowsAt2369]
    exact keyMoment2369 B hB
  · have he : k = (2370 : Fin 2886) := Fin.ext h2370
    subst k
    rw [keyMomentRowsAt2370]
    exact keyMoment2370 B hB
  · have he : k = (2371 : Fin 2886) := Fin.ext h2371
    subst k
    rw [keyMomentRowsAt2371]
    exact keyMoment2371 B hB
  · have he : k = (2372 : Fin 2886) := Fin.ext h2372
    subst k
    rw [keyMomentRowsAt2372]
    exact keyMoment2372 B hB
  · have he : k = (2373 : Fin 2886) := Fin.ext h2373
    subst k
    rw [keyMomentRowsAt2373]
    exact keyMoment2373 B hB
  · have he : k = (2374 : Fin 2886) := Fin.ext h2374
    subst k
    rw [keyMomentRowsAt2374]
    exact keyMoment2374 B hB
  · have he : k = (2375 : Fin 2886) := Fin.ext h2375
    subst k
    rw [keyMomentRowsAt2375]
    exact keyMoment2375 B hB
  · have he : k = (2376 : Fin 2886) := Fin.ext h2376
    subst k
    rw [keyMomentRowsAt2376]
    exact keyMoment2376 B hB
  · have he : k = (2377 : Fin 2886) := Fin.ext h2377
    subst k
    rw [keyMomentRowsAt2377]
    exact keyMoment2377 B hB
  · have he : k = (2378 : Fin 2886) := Fin.ext h2378
    subst k
    rw [keyMomentRowsAt2378]
    exact keyMoment2378 B hB
  · have he : k = (2379 : Fin 2886) := Fin.ext h2379
    subst k
    rw [keyMomentRowsAt2379]
    exact keyMoment2379 B hB
  · have he : k = (2380 : Fin 2886) := Fin.ext h2380
    subst k
    rw [keyMomentRowsAt2380]
    exact keyMoment2380 B hB
  · have he : k = (2381 : Fin 2886) := Fin.ext h2381
    subst k
    rw [keyMomentRowsAt2381]
    exact keyMoment2381 B hB
  · have he : k = (2382 : Fin 2886) := Fin.ext h2382
    subst k
    rw [keyMomentRowsAt2382]
    exact keyMoment2382 B hB
  · have he : k = (2383 : Fin 2886) := Fin.ext h2383
    subst k
    rw [keyMomentRowsAt2383]
    exact keyMoment2383 B hB
  · have he : k = (2384 : Fin 2886) := Fin.ext h2384
    subst k
    rw [keyMomentRowsAt2384]
    exact keyMoment2384 B hB
  · have he : k = (2385 : Fin 2886) := Fin.ext h2385
    subst k
    rw [keyMomentRowsAt2385]
    exact keyMoment2385 B hB
  · have he : k = (2386 : Fin 2886) := Fin.ext h2386
    subst k
    rw [keyMomentRowsAt2386]
    exact keyMoment2386 B hB
  · have he : k = (2387 : Fin 2886) := Fin.ext h2387
    subst k
    rw [keyMomentRowsAt2387]
    exact keyMoment2387 B hB
  · have he : k = (2388 : Fin 2886) := Fin.ext h2388
    subst k
    rw [keyMomentRowsAt2388]
    exact keyMoment2388 B hB
  · have he : k = (2389 : Fin 2886) := Fin.ext h2389
    subst k
    rw [keyMomentRowsAt2389]
    exact keyMoment2389 B hB
  · have he : k = (2390 : Fin 2886) := Fin.ext h2390
    subst k
    rw [keyMomentRowsAt2390]
    exact keyMoment2390 B hB
  · have he : k = (2391 : Fin 2886) := Fin.ext h2391
    subst k
    rw [keyMomentRowsAt2391]
    exact keyMoment2391 B hB
  · have he : k = (2392 : Fin 2886) := Fin.ext h2392
    subst k
    rw [keyMomentRowsAt2392]
    exact keyMoment2392 B hB
  · have he : k = (2393 : Fin 2886) := Fin.ext h2393
    subst k
    rw [keyMomentRowsAt2393]
    exact keyMoment2393 B hB
  · have he : k = (2394 : Fin 2886) := Fin.ext h2394
    subst k
    rw [keyMomentRowsAt2394]
    exact keyMoment2394 B hB
  · have he : k = (2395 : Fin 2886) := Fin.ext h2395
    subst k
    rw [keyMomentRowsAt2395]
    exact keyMoment2395 B hB
  · have he : k = (2396 : Fin 2886) := Fin.ext h2396
    subst k
    rw [keyMomentRowsAt2396]
    exact keyMoment2396 B hB
  · have he : k = (2397 : Fin 2886) := Fin.ext h2397
    subst k
    rw [keyMomentRowsAt2397]
    exact keyMoment2397 B hB
  · have he : k = (2398 : Fin 2886) := Fin.ext h2398
    subst k
    rw [keyMomentRowsAt2398]
    exact keyMoment2398 B hB
  · have he : k = (2399 : Fin 2886) := Fin.ext h2399
    subst k
    rw [keyMomentRowsAt2399]
    exact keyMoment2399 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
