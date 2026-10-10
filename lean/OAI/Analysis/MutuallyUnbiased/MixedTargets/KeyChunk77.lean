import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound77
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2464 : keyMomentRows (2464 : Fin 2886) =
    keyMomentRow2464 := by decide +kernel

theorem keyMomentRowsAt2465 : keyMomentRows (2465 : Fin 2886) =
    keyMomentRow2465 := by decide +kernel

theorem keyMomentRowsAt2466 : keyMomentRows (2466 : Fin 2886) =
    keyMomentRow2466 := by decide +kernel

theorem keyMomentRowsAt2467 : keyMomentRows (2467 : Fin 2886) =
    keyMomentRow2467 := by decide +kernel

theorem keyMomentRowsAt2468 : keyMomentRows (2468 : Fin 2886) =
    keyMomentRow2468 := by decide +kernel

theorem keyMomentRowsAt2469 : keyMomentRows (2469 : Fin 2886) =
    keyMomentRow2469 := by decide +kernel

theorem keyMomentRowsAt2470 : keyMomentRows (2470 : Fin 2886) =
    keyMomentRow2470 := by decide +kernel

theorem keyMomentRowsAt2471 : keyMomentRows (2471 : Fin 2886) =
    keyMomentRow2471 := by decide +kernel

theorem keyMomentRowsAt2472 : keyMomentRows (2472 : Fin 2886) =
    keyMomentRow2472 := by decide +kernel

theorem keyMomentRowsAt2473 : keyMomentRows (2473 : Fin 2886) =
    keyMomentRow2473 := by decide +kernel

theorem keyMomentRowsAt2474 : keyMomentRows (2474 : Fin 2886) =
    keyMomentRow2474 := by decide +kernel

theorem keyMomentRowsAt2475 : keyMomentRows (2475 : Fin 2886) =
    keyMomentRow2475 := by decide +kernel

theorem keyMomentRowsAt2476 : keyMomentRows (2476 : Fin 2886) =
    keyMomentRow2476 := by decide +kernel

theorem keyMomentRowsAt2477 : keyMomentRows (2477 : Fin 2886) =
    keyMomentRow2477 := by decide +kernel

theorem keyMomentRowsAt2478 : keyMomentRows (2478 : Fin 2886) =
    keyMomentRow2478 := by decide +kernel

theorem keyMomentRowsAt2479 : keyMomentRows (2479 : Fin 2886) =
    keyMomentRow2479 := by decide +kernel

theorem keyMomentRowsAt2480 : keyMomentRows (2480 : Fin 2886) =
    keyMomentRow2480 := by decide +kernel

theorem keyMomentRowsAt2481 : keyMomentRows (2481 : Fin 2886) =
    keyMomentRow2481 := by decide +kernel

theorem keyMomentRowsAt2482 : keyMomentRows (2482 : Fin 2886) =
    keyMomentRow2482 := by decide +kernel

theorem keyMomentRowsAt2483 : keyMomentRows (2483 : Fin 2886) =
    keyMomentRow2483 := by decide +kernel

theorem keyMomentRowsAt2484 : keyMomentRows (2484 : Fin 2886) =
    keyMomentRow2484 := by decide +kernel

theorem keyMomentRowsAt2485 : keyMomentRows (2485 : Fin 2886) =
    keyMomentRow2485 := by decide +kernel

theorem keyMomentRowsAt2486 : keyMomentRows (2486 : Fin 2886) =
    keyMomentRow2486 := by decide +kernel

theorem keyMomentRowsAt2487 : keyMomentRows (2487 : Fin 2886) =
    keyMomentRow2487 := by decide +kernel

theorem keyMomentRowsAt2488 : keyMomentRows (2488 : Fin 2886) =
    keyMomentRow2488 := by decide +kernel

theorem keyMomentRowsAt2489 : keyMomentRows (2489 : Fin 2886) =
    keyMomentRow2489 := by decide +kernel

theorem keyMomentRowsAt2490 : keyMomentRows (2490 : Fin 2886) =
    keyMomentRow2490 := by decide +kernel

theorem keyMomentRowsAt2491 : keyMomentRows (2491 : Fin 2886) =
    keyMomentRow2491 := by decide +kernel

theorem keyMomentRowsAt2492 : keyMomentRows (2492 : Fin 2886) =
    keyMomentRow2492 := by decide +kernel

theorem keyMomentRowsAt2493 : keyMomentRows (2493 : Fin 2886) =
    keyMomentRow2493 := by decide +kernel

theorem keyMomentRowsAt2494 : keyMomentRows (2494 : Fin 2886) =
    keyMomentRow2494 := by decide +kernel

theorem keyMomentRowsAt2495 : keyMomentRows (2495 : Fin 2886) =
    keyMomentRow2495 := by decide +kernel

theorem keyMomentChunkSound77 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 77) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2464 ∨ k.val = 2465 ∨ k.val = 2466 ∨ k.val = 2467 ∨ k.val = 2468 ∨ k.val = 2469 ∨ k.val = 2470 ∨ k.val = 2471 ∨ k.val = 2472 ∨ k.val = 2473 ∨ k.val = 2474 ∨ k.val = 2475 ∨ k.val = 2476 ∨ k.val = 2477 ∨ k.val = 2478 ∨ k.val = 2479 ∨ k.val = 2480 ∨ k.val = 2481 ∨ k.val = 2482 ∨ k.val = 2483 ∨ k.val = 2484 ∨ k.val = 2485 ∨ k.val = 2486 ∨ k.val = 2487 ∨ k.val = 2488 ∨ k.val = 2489 ∨ k.val = 2490 ∨ k.val = 2491 ∨ k.val = 2492 ∨ k.val = 2493 ∨ k.val = 2494 ∨ k.val = 2495 := by omega
  rcases heq with h2464 | h2465 | h2466 | h2467 | h2468 | h2469 | h2470 | h2471 | h2472 | h2473 | h2474 | h2475 | h2476 | h2477 | h2478 | h2479 | h2480 | h2481 | h2482 | h2483 | h2484 | h2485 | h2486 | h2487 | h2488 | h2489 | h2490 | h2491 | h2492 | h2493 | h2494 | h2495
  · have he : k = (2464 : Fin 2886) := Fin.ext h2464
    subst k
    rw [keyMomentRowsAt2464]
    exact keyMoment2464 B hB
  · have he : k = (2465 : Fin 2886) := Fin.ext h2465
    subst k
    rw [keyMomentRowsAt2465]
    exact keyMoment2465 B hB
  · have he : k = (2466 : Fin 2886) := Fin.ext h2466
    subst k
    rw [keyMomentRowsAt2466]
    exact keyMoment2466 B hB
  · have he : k = (2467 : Fin 2886) := Fin.ext h2467
    subst k
    rw [keyMomentRowsAt2467]
    exact keyMoment2467 B hB
  · have he : k = (2468 : Fin 2886) := Fin.ext h2468
    subst k
    rw [keyMomentRowsAt2468]
    exact keyMoment2468 B hB
  · have he : k = (2469 : Fin 2886) := Fin.ext h2469
    subst k
    rw [keyMomentRowsAt2469]
    exact keyMoment2469 B hB
  · have he : k = (2470 : Fin 2886) := Fin.ext h2470
    subst k
    rw [keyMomentRowsAt2470]
    exact keyMoment2470 B hB
  · have he : k = (2471 : Fin 2886) := Fin.ext h2471
    subst k
    rw [keyMomentRowsAt2471]
    exact keyMoment2471 B hB
  · have he : k = (2472 : Fin 2886) := Fin.ext h2472
    subst k
    rw [keyMomentRowsAt2472]
    exact keyMoment2472 B hB
  · have he : k = (2473 : Fin 2886) := Fin.ext h2473
    subst k
    rw [keyMomentRowsAt2473]
    exact keyMoment2473 B hB
  · have he : k = (2474 : Fin 2886) := Fin.ext h2474
    subst k
    rw [keyMomentRowsAt2474]
    exact keyMoment2474 B hB
  · have he : k = (2475 : Fin 2886) := Fin.ext h2475
    subst k
    rw [keyMomentRowsAt2475]
    exact keyMoment2475 B hB
  · have he : k = (2476 : Fin 2886) := Fin.ext h2476
    subst k
    rw [keyMomentRowsAt2476]
    exact keyMoment2476 B hB
  · have he : k = (2477 : Fin 2886) := Fin.ext h2477
    subst k
    rw [keyMomentRowsAt2477]
    exact keyMoment2477 B hB
  · have he : k = (2478 : Fin 2886) := Fin.ext h2478
    subst k
    rw [keyMomentRowsAt2478]
    exact keyMoment2478 B hB
  · have he : k = (2479 : Fin 2886) := Fin.ext h2479
    subst k
    rw [keyMomentRowsAt2479]
    exact keyMoment2479 B hB
  · have he : k = (2480 : Fin 2886) := Fin.ext h2480
    subst k
    rw [keyMomentRowsAt2480]
    exact keyMoment2480 B hB
  · have he : k = (2481 : Fin 2886) := Fin.ext h2481
    subst k
    rw [keyMomentRowsAt2481]
    exact keyMoment2481 B hB
  · have he : k = (2482 : Fin 2886) := Fin.ext h2482
    subst k
    rw [keyMomentRowsAt2482]
    exact keyMoment2482 B hB
  · have he : k = (2483 : Fin 2886) := Fin.ext h2483
    subst k
    rw [keyMomentRowsAt2483]
    exact keyMoment2483 B hB
  · have he : k = (2484 : Fin 2886) := Fin.ext h2484
    subst k
    rw [keyMomentRowsAt2484]
    exact keyMoment2484 B hB
  · have he : k = (2485 : Fin 2886) := Fin.ext h2485
    subst k
    rw [keyMomentRowsAt2485]
    exact keyMoment2485 B hB
  · have he : k = (2486 : Fin 2886) := Fin.ext h2486
    subst k
    rw [keyMomentRowsAt2486]
    exact keyMoment2486 B hB
  · have he : k = (2487 : Fin 2886) := Fin.ext h2487
    subst k
    rw [keyMomentRowsAt2487]
    exact keyMoment2487 B hB
  · have he : k = (2488 : Fin 2886) := Fin.ext h2488
    subst k
    rw [keyMomentRowsAt2488]
    exact keyMoment2488 B hB
  · have he : k = (2489 : Fin 2886) := Fin.ext h2489
    subst k
    rw [keyMomentRowsAt2489]
    exact keyMoment2489 B hB
  · have he : k = (2490 : Fin 2886) := Fin.ext h2490
    subst k
    rw [keyMomentRowsAt2490]
    exact keyMoment2490 B hB
  · have he : k = (2491 : Fin 2886) := Fin.ext h2491
    subst k
    rw [keyMomentRowsAt2491]
    exact keyMoment2491 B hB
  · have he : k = (2492 : Fin 2886) := Fin.ext h2492
    subst k
    rw [keyMomentRowsAt2492]
    exact keyMoment2492 B hB
  · have he : k = (2493 : Fin 2886) := Fin.ext h2493
    subst k
    rw [keyMomentRowsAt2493]
    exact keyMoment2493 B hB
  · have he : k = (2494 : Fin 2886) := Fin.ext h2494
    subst k
    rw [keyMomentRowsAt2494]
    exact keyMoment2494 B hB
  · have he : k = (2495 : Fin 2886) := Fin.ext h2495
    subst k
    rw [keyMomentRowsAt2495]
    exact keyMoment2495 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
