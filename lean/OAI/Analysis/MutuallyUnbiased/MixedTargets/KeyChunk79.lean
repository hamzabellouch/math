import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound79
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2528 : keyMomentRows (2528 : Fin 2886) =
    keyMomentRow2528 := by decide +kernel

theorem keyMomentRowsAt2529 : keyMomentRows (2529 : Fin 2886) =
    keyMomentRow2529 := by decide +kernel

theorem keyMomentRowsAt2530 : keyMomentRows (2530 : Fin 2886) =
    keyMomentRow2530 := by decide +kernel

theorem keyMomentRowsAt2531 : keyMomentRows (2531 : Fin 2886) =
    keyMomentRow2531 := by decide +kernel

theorem keyMomentRowsAt2532 : keyMomentRows (2532 : Fin 2886) =
    keyMomentRow2532 := by decide +kernel

theorem keyMomentRowsAt2533 : keyMomentRows (2533 : Fin 2886) =
    keyMomentRow2533 := by decide +kernel

theorem keyMomentRowsAt2534 : keyMomentRows (2534 : Fin 2886) =
    keyMomentRow2534 := by decide +kernel

theorem keyMomentRowsAt2535 : keyMomentRows (2535 : Fin 2886) =
    keyMomentRow2535 := by decide +kernel

theorem keyMomentRowsAt2536 : keyMomentRows (2536 : Fin 2886) =
    keyMomentRow2536 := by decide +kernel

theorem keyMomentRowsAt2537 : keyMomentRows (2537 : Fin 2886) =
    keyMomentRow2537 := by decide +kernel

theorem keyMomentRowsAt2538 : keyMomentRows (2538 : Fin 2886) =
    keyMomentRow2538 := by decide +kernel

theorem keyMomentRowsAt2539 : keyMomentRows (2539 : Fin 2886) =
    keyMomentRow2539 := by decide +kernel

theorem keyMomentRowsAt2540 : keyMomentRows (2540 : Fin 2886) =
    keyMomentRow2540 := by decide +kernel

theorem keyMomentRowsAt2541 : keyMomentRows (2541 : Fin 2886) =
    keyMomentRow2541 := by decide +kernel

theorem keyMomentRowsAt2542 : keyMomentRows (2542 : Fin 2886) =
    keyMomentRow2542 := by decide +kernel

theorem keyMomentRowsAt2543 : keyMomentRows (2543 : Fin 2886) =
    keyMomentRow2543 := by decide +kernel

theorem keyMomentRowsAt2544 : keyMomentRows (2544 : Fin 2886) =
    keyMomentRow2544 := by decide +kernel

theorem keyMomentRowsAt2545 : keyMomentRows (2545 : Fin 2886) =
    keyMomentRow2545 := by decide +kernel

theorem keyMomentRowsAt2546 : keyMomentRows (2546 : Fin 2886) =
    keyMomentRow2546 := by decide +kernel

theorem keyMomentRowsAt2547 : keyMomentRows (2547 : Fin 2886) =
    keyMomentRow2547 := by decide +kernel

theorem keyMomentRowsAt2548 : keyMomentRows (2548 : Fin 2886) =
    keyMomentRow2548 := by decide +kernel

theorem keyMomentRowsAt2549 : keyMomentRows (2549 : Fin 2886) =
    keyMomentRow2549 := by decide +kernel

theorem keyMomentRowsAt2550 : keyMomentRows (2550 : Fin 2886) =
    keyMomentRow2550 := by decide +kernel

theorem keyMomentRowsAt2551 : keyMomentRows (2551 : Fin 2886) =
    keyMomentRow2551 := by decide +kernel

theorem keyMomentRowsAt2552 : keyMomentRows (2552 : Fin 2886) =
    keyMomentRow2552 := by decide +kernel

theorem keyMomentRowsAt2553 : keyMomentRows (2553 : Fin 2886) =
    keyMomentRow2553 := by decide +kernel

theorem keyMomentRowsAt2554 : keyMomentRows (2554 : Fin 2886) =
    keyMomentRow2554 := by decide +kernel

theorem keyMomentRowsAt2555 : keyMomentRows (2555 : Fin 2886) =
    keyMomentRow2555 := by decide +kernel

theorem keyMomentRowsAt2556 : keyMomentRows (2556 : Fin 2886) =
    keyMomentRow2556 := by decide +kernel

theorem keyMomentRowsAt2557 : keyMomentRows (2557 : Fin 2886) =
    keyMomentRow2557 := by decide +kernel

theorem keyMomentRowsAt2558 : keyMomentRows (2558 : Fin 2886) =
    keyMomentRow2558 := by decide +kernel

theorem keyMomentRowsAt2559 : keyMomentRows (2559 : Fin 2886) =
    keyMomentRow2559 := by decide +kernel

theorem keyMomentChunkSound79 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 79) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2528 ∨ k.val = 2529 ∨ k.val = 2530 ∨ k.val = 2531 ∨ k.val = 2532 ∨ k.val = 2533 ∨ k.val = 2534 ∨ k.val = 2535 ∨ k.val = 2536 ∨ k.val = 2537 ∨ k.val = 2538 ∨ k.val = 2539 ∨ k.val = 2540 ∨ k.val = 2541 ∨ k.val = 2542 ∨ k.val = 2543 ∨ k.val = 2544 ∨ k.val = 2545 ∨ k.val = 2546 ∨ k.val = 2547 ∨ k.val = 2548 ∨ k.val = 2549 ∨ k.val = 2550 ∨ k.val = 2551 ∨ k.val = 2552 ∨ k.val = 2553 ∨ k.val = 2554 ∨ k.val = 2555 ∨ k.val = 2556 ∨ k.val = 2557 ∨ k.val = 2558 ∨ k.val = 2559 := by omega
  rcases heq with h2528 | h2529 | h2530 | h2531 | h2532 | h2533 | h2534 | h2535 | h2536 | h2537 | h2538 | h2539 | h2540 | h2541 | h2542 | h2543 | h2544 | h2545 | h2546 | h2547 | h2548 | h2549 | h2550 | h2551 | h2552 | h2553 | h2554 | h2555 | h2556 | h2557 | h2558 | h2559
  · have he : k = (2528 : Fin 2886) := Fin.ext h2528
    subst k
    rw [keyMomentRowsAt2528]
    exact keyMoment2528 B hB
  · have he : k = (2529 : Fin 2886) := Fin.ext h2529
    subst k
    rw [keyMomentRowsAt2529]
    exact keyMoment2529 B hB
  · have he : k = (2530 : Fin 2886) := Fin.ext h2530
    subst k
    rw [keyMomentRowsAt2530]
    exact keyMoment2530 B hB
  · have he : k = (2531 : Fin 2886) := Fin.ext h2531
    subst k
    rw [keyMomentRowsAt2531]
    exact keyMoment2531 B hB
  · have he : k = (2532 : Fin 2886) := Fin.ext h2532
    subst k
    rw [keyMomentRowsAt2532]
    exact keyMoment2532 B hB
  · have he : k = (2533 : Fin 2886) := Fin.ext h2533
    subst k
    rw [keyMomentRowsAt2533]
    exact keyMoment2533 B hB
  · have he : k = (2534 : Fin 2886) := Fin.ext h2534
    subst k
    rw [keyMomentRowsAt2534]
    exact keyMoment2534 B hB
  · have he : k = (2535 : Fin 2886) := Fin.ext h2535
    subst k
    rw [keyMomentRowsAt2535]
    exact keyMoment2535 B hB
  · have he : k = (2536 : Fin 2886) := Fin.ext h2536
    subst k
    rw [keyMomentRowsAt2536]
    exact keyMoment2536 B hB
  · have he : k = (2537 : Fin 2886) := Fin.ext h2537
    subst k
    rw [keyMomentRowsAt2537]
    exact keyMoment2537 B hB
  · have he : k = (2538 : Fin 2886) := Fin.ext h2538
    subst k
    rw [keyMomentRowsAt2538]
    exact keyMoment2538 B hB
  · have he : k = (2539 : Fin 2886) := Fin.ext h2539
    subst k
    rw [keyMomentRowsAt2539]
    exact keyMoment2539 B hB
  · have he : k = (2540 : Fin 2886) := Fin.ext h2540
    subst k
    rw [keyMomentRowsAt2540]
    exact keyMoment2540 B hB
  · have he : k = (2541 : Fin 2886) := Fin.ext h2541
    subst k
    rw [keyMomentRowsAt2541]
    exact keyMoment2541 B hB
  · have he : k = (2542 : Fin 2886) := Fin.ext h2542
    subst k
    rw [keyMomentRowsAt2542]
    exact keyMoment2542 B hB
  · have he : k = (2543 : Fin 2886) := Fin.ext h2543
    subst k
    rw [keyMomentRowsAt2543]
    exact keyMoment2543 B hB
  · have he : k = (2544 : Fin 2886) := Fin.ext h2544
    subst k
    rw [keyMomentRowsAt2544]
    exact keyMoment2544 B hB
  · have he : k = (2545 : Fin 2886) := Fin.ext h2545
    subst k
    rw [keyMomentRowsAt2545]
    exact keyMoment2545 B hB
  · have he : k = (2546 : Fin 2886) := Fin.ext h2546
    subst k
    rw [keyMomentRowsAt2546]
    exact keyMoment2546 B hB
  · have he : k = (2547 : Fin 2886) := Fin.ext h2547
    subst k
    rw [keyMomentRowsAt2547]
    exact keyMoment2547 B hB
  · have he : k = (2548 : Fin 2886) := Fin.ext h2548
    subst k
    rw [keyMomentRowsAt2548]
    exact keyMoment2548 B hB
  · have he : k = (2549 : Fin 2886) := Fin.ext h2549
    subst k
    rw [keyMomentRowsAt2549]
    exact keyMoment2549 B hB
  · have he : k = (2550 : Fin 2886) := Fin.ext h2550
    subst k
    rw [keyMomentRowsAt2550]
    exact keyMoment2550 B hB
  · have he : k = (2551 : Fin 2886) := Fin.ext h2551
    subst k
    rw [keyMomentRowsAt2551]
    exact keyMoment2551 B hB
  · have he : k = (2552 : Fin 2886) := Fin.ext h2552
    subst k
    rw [keyMomentRowsAt2552]
    exact keyMoment2552 B hB
  · have he : k = (2553 : Fin 2886) := Fin.ext h2553
    subst k
    rw [keyMomentRowsAt2553]
    exact keyMoment2553 B hB
  · have he : k = (2554 : Fin 2886) := Fin.ext h2554
    subst k
    rw [keyMomentRowsAt2554]
    exact keyMoment2554 B hB
  · have he : k = (2555 : Fin 2886) := Fin.ext h2555
    subst k
    rw [keyMomentRowsAt2555]
    exact keyMoment2555 B hB
  · have he : k = (2556 : Fin 2886) := Fin.ext h2556
    subst k
    rw [keyMomentRowsAt2556]
    exact keyMoment2556 B hB
  · have he : k = (2557 : Fin 2886) := Fin.ext h2557
    subst k
    rw [keyMomentRowsAt2557]
    exact keyMoment2557 B hB
  · have he : k = (2558 : Fin 2886) := Fin.ext h2558
    subst k
    rw [keyMomentRowsAt2558]
    exact keyMoment2558 B hB
  · have he : k = (2559 : Fin 2886) := Fin.ext h2559
    subst k
    rw [keyMomentRowsAt2559]
    exact keyMoment2559 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
