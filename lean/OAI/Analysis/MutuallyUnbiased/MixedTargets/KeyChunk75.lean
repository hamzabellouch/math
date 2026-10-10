import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound75
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2400 : keyMomentRows (2400 : Fin 2886) =
    keyMomentRow2400 := by decide +kernel

theorem keyMomentRowsAt2401 : keyMomentRows (2401 : Fin 2886) =
    keyMomentRow2401 := by decide +kernel

theorem keyMomentRowsAt2402 : keyMomentRows (2402 : Fin 2886) =
    keyMomentRow2402 := by decide +kernel

theorem keyMomentRowsAt2403 : keyMomentRows (2403 : Fin 2886) =
    keyMomentRow2403 := by decide +kernel

theorem keyMomentRowsAt2404 : keyMomentRows (2404 : Fin 2886) =
    keyMomentRow2404 := by decide +kernel

theorem keyMomentRowsAt2405 : keyMomentRows (2405 : Fin 2886) =
    keyMomentRow2405 := by decide +kernel

theorem keyMomentRowsAt2406 : keyMomentRows (2406 : Fin 2886) =
    keyMomentRow2406 := by decide +kernel

theorem keyMomentRowsAt2407 : keyMomentRows (2407 : Fin 2886) =
    keyMomentRow2407 := by decide +kernel

theorem keyMomentRowsAt2408 : keyMomentRows (2408 : Fin 2886) =
    keyMomentRow2408 := by decide +kernel

theorem keyMomentRowsAt2409 : keyMomentRows (2409 : Fin 2886) =
    keyMomentRow2409 := by decide +kernel

theorem keyMomentRowsAt2410 : keyMomentRows (2410 : Fin 2886) =
    keyMomentRow2410 := by decide +kernel

theorem keyMomentRowsAt2411 : keyMomentRows (2411 : Fin 2886) =
    keyMomentRow2411 := by decide +kernel

theorem keyMomentRowsAt2412 : keyMomentRows (2412 : Fin 2886) =
    keyMomentRow2412 := by decide +kernel

theorem keyMomentRowsAt2413 : keyMomentRows (2413 : Fin 2886) =
    keyMomentRow2413 := by decide +kernel

theorem keyMomentRowsAt2414 : keyMomentRows (2414 : Fin 2886) =
    keyMomentRow2414 := by decide +kernel

theorem keyMomentRowsAt2415 : keyMomentRows (2415 : Fin 2886) =
    keyMomentRow2415 := by decide +kernel

theorem keyMomentRowsAt2416 : keyMomentRows (2416 : Fin 2886) =
    keyMomentRow2416 := by decide +kernel

theorem keyMomentRowsAt2417 : keyMomentRows (2417 : Fin 2886) =
    keyMomentRow2417 := by decide +kernel

theorem keyMomentRowsAt2418 : keyMomentRows (2418 : Fin 2886) =
    keyMomentRow2418 := by decide +kernel

theorem keyMomentRowsAt2419 : keyMomentRows (2419 : Fin 2886) =
    keyMomentRow2419 := by decide +kernel

theorem keyMomentRowsAt2420 : keyMomentRows (2420 : Fin 2886) =
    keyMomentRow2420 := by decide +kernel

theorem keyMomentRowsAt2421 : keyMomentRows (2421 : Fin 2886) =
    keyMomentRow2421 := by decide +kernel

theorem keyMomentRowsAt2422 : keyMomentRows (2422 : Fin 2886) =
    keyMomentRow2422 := by decide +kernel

theorem keyMomentRowsAt2423 : keyMomentRows (2423 : Fin 2886) =
    keyMomentRow2423 := by decide +kernel

theorem keyMomentRowsAt2424 : keyMomentRows (2424 : Fin 2886) =
    keyMomentRow2424 := by decide +kernel

theorem keyMomentRowsAt2425 : keyMomentRows (2425 : Fin 2886) =
    keyMomentRow2425 := by decide +kernel

theorem keyMomentRowsAt2426 : keyMomentRows (2426 : Fin 2886) =
    keyMomentRow2426 := by decide +kernel

theorem keyMomentRowsAt2427 : keyMomentRows (2427 : Fin 2886) =
    keyMomentRow2427 := by decide +kernel

theorem keyMomentRowsAt2428 : keyMomentRows (2428 : Fin 2886) =
    keyMomentRow2428 := by decide +kernel

theorem keyMomentRowsAt2429 : keyMomentRows (2429 : Fin 2886) =
    keyMomentRow2429 := by decide +kernel

theorem keyMomentRowsAt2430 : keyMomentRows (2430 : Fin 2886) =
    keyMomentRow2430 := by decide +kernel

theorem keyMomentRowsAt2431 : keyMomentRows (2431 : Fin 2886) =
    keyMomentRow2431 := by decide +kernel

theorem keyMomentChunkSound75 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 75) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2400 ∨ k.val = 2401 ∨ k.val = 2402 ∨ k.val = 2403 ∨ k.val = 2404 ∨ k.val = 2405 ∨ k.val = 2406 ∨ k.val = 2407 ∨ k.val = 2408 ∨ k.val = 2409 ∨ k.val = 2410 ∨ k.val = 2411 ∨ k.val = 2412 ∨ k.val = 2413 ∨ k.val = 2414 ∨ k.val = 2415 ∨ k.val = 2416 ∨ k.val = 2417 ∨ k.val = 2418 ∨ k.val = 2419 ∨ k.val = 2420 ∨ k.val = 2421 ∨ k.val = 2422 ∨ k.val = 2423 ∨ k.val = 2424 ∨ k.val = 2425 ∨ k.val = 2426 ∨ k.val = 2427 ∨ k.val = 2428 ∨ k.val = 2429 ∨ k.val = 2430 ∨ k.val = 2431 := by omega
  rcases heq with h2400 | h2401 | h2402 | h2403 | h2404 | h2405 | h2406 | h2407 | h2408 | h2409 | h2410 | h2411 | h2412 | h2413 | h2414 | h2415 | h2416 | h2417 | h2418 | h2419 | h2420 | h2421 | h2422 | h2423 | h2424 | h2425 | h2426 | h2427 | h2428 | h2429 | h2430 | h2431
  · have he : k = (2400 : Fin 2886) := Fin.ext h2400
    subst k
    rw [keyMomentRowsAt2400]
    exact keyMoment2400 B hB
  · have he : k = (2401 : Fin 2886) := Fin.ext h2401
    subst k
    rw [keyMomentRowsAt2401]
    exact keyMoment2401 B hB
  · have he : k = (2402 : Fin 2886) := Fin.ext h2402
    subst k
    rw [keyMomentRowsAt2402]
    exact keyMoment2402 B hB
  · have he : k = (2403 : Fin 2886) := Fin.ext h2403
    subst k
    rw [keyMomentRowsAt2403]
    exact keyMoment2403 B hB
  · have he : k = (2404 : Fin 2886) := Fin.ext h2404
    subst k
    rw [keyMomentRowsAt2404]
    exact keyMoment2404 B hB
  · have he : k = (2405 : Fin 2886) := Fin.ext h2405
    subst k
    rw [keyMomentRowsAt2405]
    exact keyMoment2405 B hB
  · have he : k = (2406 : Fin 2886) := Fin.ext h2406
    subst k
    rw [keyMomentRowsAt2406]
    exact keyMoment2406 B hB
  · have he : k = (2407 : Fin 2886) := Fin.ext h2407
    subst k
    rw [keyMomentRowsAt2407]
    exact keyMoment2407 B hB
  · have he : k = (2408 : Fin 2886) := Fin.ext h2408
    subst k
    rw [keyMomentRowsAt2408]
    exact keyMoment2408 B hB
  · have he : k = (2409 : Fin 2886) := Fin.ext h2409
    subst k
    rw [keyMomentRowsAt2409]
    exact keyMoment2409 B hB
  · have he : k = (2410 : Fin 2886) := Fin.ext h2410
    subst k
    rw [keyMomentRowsAt2410]
    exact keyMoment2410 B hB
  · have he : k = (2411 : Fin 2886) := Fin.ext h2411
    subst k
    rw [keyMomentRowsAt2411]
    exact keyMoment2411 B hB
  · have he : k = (2412 : Fin 2886) := Fin.ext h2412
    subst k
    rw [keyMomentRowsAt2412]
    exact keyMoment2412 B hB
  · have he : k = (2413 : Fin 2886) := Fin.ext h2413
    subst k
    rw [keyMomentRowsAt2413]
    exact keyMoment2413 B hB
  · have he : k = (2414 : Fin 2886) := Fin.ext h2414
    subst k
    rw [keyMomentRowsAt2414]
    exact keyMoment2414 B hB
  · have he : k = (2415 : Fin 2886) := Fin.ext h2415
    subst k
    rw [keyMomentRowsAt2415]
    exact keyMoment2415 B hB
  · have he : k = (2416 : Fin 2886) := Fin.ext h2416
    subst k
    rw [keyMomentRowsAt2416]
    exact keyMoment2416 B hB
  · have he : k = (2417 : Fin 2886) := Fin.ext h2417
    subst k
    rw [keyMomentRowsAt2417]
    exact keyMoment2417 B hB
  · have he : k = (2418 : Fin 2886) := Fin.ext h2418
    subst k
    rw [keyMomentRowsAt2418]
    exact keyMoment2418 B hB
  · have he : k = (2419 : Fin 2886) := Fin.ext h2419
    subst k
    rw [keyMomentRowsAt2419]
    exact keyMoment2419 B hB
  · have he : k = (2420 : Fin 2886) := Fin.ext h2420
    subst k
    rw [keyMomentRowsAt2420]
    exact keyMoment2420 B hB
  · have he : k = (2421 : Fin 2886) := Fin.ext h2421
    subst k
    rw [keyMomentRowsAt2421]
    exact keyMoment2421 B hB
  · have he : k = (2422 : Fin 2886) := Fin.ext h2422
    subst k
    rw [keyMomentRowsAt2422]
    exact keyMoment2422 B hB
  · have he : k = (2423 : Fin 2886) := Fin.ext h2423
    subst k
    rw [keyMomentRowsAt2423]
    exact keyMoment2423 B hB
  · have he : k = (2424 : Fin 2886) := Fin.ext h2424
    subst k
    rw [keyMomentRowsAt2424]
    exact keyMoment2424 B hB
  · have he : k = (2425 : Fin 2886) := Fin.ext h2425
    subst k
    rw [keyMomentRowsAt2425]
    exact keyMoment2425 B hB
  · have he : k = (2426 : Fin 2886) := Fin.ext h2426
    subst k
    rw [keyMomentRowsAt2426]
    exact keyMoment2426 B hB
  · have he : k = (2427 : Fin 2886) := Fin.ext h2427
    subst k
    rw [keyMomentRowsAt2427]
    exact keyMoment2427 B hB
  · have he : k = (2428 : Fin 2886) := Fin.ext h2428
    subst k
    rw [keyMomentRowsAt2428]
    exact keyMoment2428 B hB
  · have he : k = (2429 : Fin 2886) := Fin.ext h2429
    subst k
    rw [keyMomentRowsAt2429]
    exact keyMoment2429 B hB
  · have he : k = (2430 : Fin 2886) := Fin.ext h2430
    subst k
    rw [keyMomentRowsAt2430]
    exact keyMoment2430 B hB
  · have he : k = (2431 : Fin 2886) := Fin.ext h2431
    subst k
    rw [keyMomentRowsAt2431]
    exact keyMoment2431 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
