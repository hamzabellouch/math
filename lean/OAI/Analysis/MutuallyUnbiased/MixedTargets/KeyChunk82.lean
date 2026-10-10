import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound82
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2624 : keyMomentRows (2624 : Fin 2886) =
    keyMomentRow2624 := by decide +kernel

theorem keyMomentRowsAt2625 : keyMomentRows (2625 : Fin 2886) =
    keyMomentRow2625 := by decide +kernel

theorem keyMomentRowsAt2626 : keyMomentRows (2626 : Fin 2886) =
    keyMomentRow2626 := by decide +kernel

theorem keyMomentRowsAt2627 : keyMomentRows (2627 : Fin 2886) =
    keyMomentRow2627 := by decide +kernel

theorem keyMomentRowsAt2628 : keyMomentRows (2628 : Fin 2886) =
    keyMomentRow2628 := by decide +kernel

theorem keyMomentRowsAt2629 : keyMomentRows (2629 : Fin 2886) =
    keyMomentRow2629 := by decide +kernel

theorem keyMomentRowsAt2630 : keyMomentRows (2630 : Fin 2886) =
    keyMomentRow2630 := by decide +kernel

theorem keyMomentRowsAt2631 : keyMomentRows (2631 : Fin 2886) =
    keyMomentRow2631 := by decide +kernel

theorem keyMomentRowsAt2632 : keyMomentRows (2632 : Fin 2886) =
    keyMomentRow2632 := by decide +kernel

theorem keyMomentRowsAt2633 : keyMomentRows (2633 : Fin 2886) =
    keyMomentRow2633 := by decide +kernel

theorem keyMomentRowsAt2634 : keyMomentRows (2634 : Fin 2886) =
    keyMomentRow2634 := by decide +kernel

theorem keyMomentRowsAt2635 : keyMomentRows (2635 : Fin 2886) =
    keyMomentRow2635 := by decide +kernel

theorem keyMomentRowsAt2636 : keyMomentRows (2636 : Fin 2886) =
    keyMomentRow2636 := by decide +kernel

theorem keyMomentRowsAt2637 : keyMomentRows (2637 : Fin 2886) =
    keyMomentRow2637 := by decide +kernel

theorem keyMomentRowsAt2638 : keyMomentRows (2638 : Fin 2886) =
    keyMomentRow2638 := by decide +kernel

theorem keyMomentRowsAt2639 : keyMomentRows (2639 : Fin 2886) =
    keyMomentRow2639 := by decide +kernel

theorem keyMomentRowsAt2640 : keyMomentRows (2640 : Fin 2886) =
    keyMomentRow2640 := by decide +kernel

theorem keyMomentRowsAt2641 : keyMomentRows (2641 : Fin 2886) =
    keyMomentRow2641 := by decide +kernel

theorem keyMomentRowsAt2642 : keyMomentRows (2642 : Fin 2886) =
    keyMomentRow2642 := by decide +kernel

theorem keyMomentRowsAt2643 : keyMomentRows (2643 : Fin 2886) =
    keyMomentRow2643 := by decide +kernel

theorem keyMomentRowsAt2644 : keyMomentRows (2644 : Fin 2886) =
    keyMomentRow2644 := by decide +kernel

theorem keyMomentRowsAt2645 : keyMomentRows (2645 : Fin 2886) =
    keyMomentRow2645 := by decide +kernel

theorem keyMomentRowsAt2646 : keyMomentRows (2646 : Fin 2886) =
    keyMomentRow2646 := by decide +kernel

theorem keyMomentRowsAt2647 : keyMomentRows (2647 : Fin 2886) =
    keyMomentRow2647 := by decide +kernel

theorem keyMomentRowsAt2648 : keyMomentRows (2648 : Fin 2886) =
    keyMomentRow2648 := by decide +kernel

theorem keyMomentRowsAt2649 : keyMomentRows (2649 : Fin 2886) =
    keyMomentRow2649 := by decide +kernel

theorem keyMomentRowsAt2650 : keyMomentRows (2650 : Fin 2886) =
    keyMomentRow2650 := by decide +kernel

theorem keyMomentRowsAt2651 : keyMomentRows (2651 : Fin 2886) =
    keyMomentRow2651 := by decide +kernel

theorem keyMomentRowsAt2652 : keyMomentRows (2652 : Fin 2886) =
    keyMomentRow2652 := by decide +kernel

theorem keyMomentRowsAt2653 : keyMomentRows (2653 : Fin 2886) =
    keyMomentRow2653 := by decide +kernel

theorem keyMomentRowsAt2654 : keyMomentRows (2654 : Fin 2886) =
    keyMomentRow2654 := by decide +kernel

theorem keyMomentRowsAt2655 : keyMomentRows (2655 : Fin 2886) =
    keyMomentRow2655 := by decide +kernel

theorem keyMomentChunkSound82 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 82) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2624 ∨ k.val = 2625 ∨ k.val = 2626 ∨ k.val = 2627 ∨ k.val = 2628 ∨ k.val = 2629 ∨ k.val = 2630 ∨ k.val = 2631 ∨ k.val = 2632 ∨ k.val = 2633 ∨ k.val = 2634 ∨ k.val = 2635 ∨ k.val = 2636 ∨ k.val = 2637 ∨ k.val = 2638 ∨ k.val = 2639 ∨ k.val = 2640 ∨ k.val = 2641 ∨ k.val = 2642 ∨ k.val = 2643 ∨ k.val = 2644 ∨ k.val = 2645 ∨ k.val = 2646 ∨ k.val = 2647 ∨ k.val = 2648 ∨ k.val = 2649 ∨ k.val = 2650 ∨ k.val = 2651 ∨ k.val = 2652 ∨ k.val = 2653 ∨ k.val = 2654 ∨ k.val = 2655 := by omega
  rcases heq with h2624 | h2625 | h2626 | h2627 | h2628 | h2629 | h2630 | h2631 | h2632 | h2633 | h2634 | h2635 | h2636 | h2637 | h2638 | h2639 | h2640 | h2641 | h2642 | h2643 | h2644 | h2645 | h2646 | h2647 | h2648 | h2649 | h2650 | h2651 | h2652 | h2653 | h2654 | h2655
  · have he : k = (2624 : Fin 2886) := Fin.ext h2624
    subst k
    rw [keyMomentRowsAt2624]
    exact keyMoment2624 B hB
  · have he : k = (2625 : Fin 2886) := Fin.ext h2625
    subst k
    rw [keyMomentRowsAt2625]
    exact keyMoment2625 B hB
  · have he : k = (2626 : Fin 2886) := Fin.ext h2626
    subst k
    rw [keyMomentRowsAt2626]
    exact keyMoment2626 B hB
  · have he : k = (2627 : Fin 2886) := Fin.ext h2627
    subst k
    rw [keyMomentRowsAt2627]
    exact keyMoment2627 B hB
  · have he : k = (2628 : Fin 2886) := Fin.ext h2628
    subst k
    rw [keyMomentRowsAt2628]
    exact keyMoment2628 B hB
  · have he : k = (2629 : Fin 2886) := Fin.ext h2629
    subst k
    rw [keyMomentRowsAt2629]
    exact keyMoment2629 B hB
  · have he : k = (2630 : Fin 2886) := Fin.ext h2630
    subst k
    rw [keyMomentRowsAt2630]
    exact keyMoment2630 B hB
  · have he : k = (2631 : Fin 2886) := Fin.ext h2631
    subst k
    rw [keyMomentRowsAt2631]
    exact keyMoment2631 B hB
  · have he : k = (2632 : Fin 2886) := Fin.ext h2632
    subst k
    rw [keyMomentRowsAt2632]
    exact keyMoment2632 B hB
  · have he : k = (2633 : Fin 2886) := Fin.ext h2633
    subst k
    rw [keyMomentRowsAt2633]
    exact keyMoment2633 B hB
  · have he : k = (2634 : Fin 2886) := Fin.ext h2634
    subst k
    rw [keyMomentRowsAt2634]
    exact keyMoment2634 B hB
  · have he : k = (2635 : Fin 2886) := Fin.ext h2635
    subst k
    rw [keyMomentRowsAt2635]
    exact keyMoment2635 B hB
  · have he : k = (2636 : Fin 2886) := Fin.ext h2636
    subst k
    rw [keyMomentRowsAt2636]
    exact keyMoment2636 B hB
  · have he : k = (2637 : Fin 2886) := Fin.ext h2637
    subst k
    rw [keyMomentRowsAt2637]
    exact keyMoment2637 B hB
  · have he : k = (2638 : Fin 2886) := Fin.ext h2638
    subst k
    rw [keyMomentRowsAt2638]
    exact keyMoment2638 B hB
  · have he : k = (2639 : Fin 2886) := Fin.ext h2639
    subst k
    rw [keyMomentRowsAt2639]
    exact keyMoment2639 B hB
  · have he : k = (2640 : Fin 2886) := Fin.ext h2640
    subst k
    rw [keyMomentRowsAt2640]
    exact keyMoment2640 B hB
  · have he : k = (2641 : Fin 2886) := Fin.ext h2641
    subst k
    rw [keyMomentRowsAt2641]
    exact keyMoment2641 B hB
  · have he : k = (2642 : Fin 2886) := Fin.ext h2642
    subst k
    rw [keyMomentRowsAt2642]
    exact keyMoment2642 B hB
  · have he : k = (2643 : Fin 2886) := Fin.ext h2643
    subst k
    rw [keyMomentRowsAt2643]
    exact keyMoment2643 B hB
  · have he : k = (2644 : Fin 2886) := Fin.ext h2644
    subst k
    rw [keyMomentRowsAt2644]
    exact keyMoment2644 B hB
  · have he : k = (2645 : Fin 2886) := Fin.ext h2645
    subst k
    rw [keyMomentRowsAt2645]
    exact keyMoment2645 B hB
  · have he : k = (2646 : Fin 2886) := Fin.ext h2646
    subst k
    rw [keyMomentRowsAt2646]
    exact keyMoment2646 B hB
  · have he : k = (2647 : Fin 2886) := Fin.ext h2647
    subst k
    rw [keyMomentRowsAt2647]
    exact keyMoment2647 B hB
  · have he : k = (2648 : Fin 2886) := Fin.ext h2648
    subst k
    rw [keyMomentRowsAt2648]
    exact keyMoment2648 B hB
  · have he : k = (2649 : Fin 2886) := Fin.ext h2649
    subst k
    rw [keyMomentRowsAt2649]
    exact keyMoment2649 B hB
  · have he : k = (2650 : Fin 2886) := Fin.ext h2650
    subst k
    rw [keyMomentRowsAt2650]
    exact keyMoment2650 B hB
  · have he : k = (2651 : Fin 2886) := Fin.ext h2651
    subst k
    rw [keyMomentRowsAt2651]
    exact keyMoment2651 B hB
  · have he : k = (2652 : Fin 2886) := Fin.ext h2652
    subst k
    rw [keyMomentRowsAt2652]
    exact keyMoment2652 B hB
  · have he : k = (2653 : Fin 2886) := Fin.ext h2653
    subst k
    rw [keyMomentRowsAt2653]
    exact keyMoment2653 B hB
  · have he : k = (2654 : Fin 2886) := Fin.ext h2654
    subst k
    rw [keyMomentRowsAt2654]
    exact keyMoment2654 B hB
  · have he : k = (2655 : Fin 2886) := Fin.ext h2655
    subst k
    rw [keyMomentRowsAt2655]
    exact keyMoment2655 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
