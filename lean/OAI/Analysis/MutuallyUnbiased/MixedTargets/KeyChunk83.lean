import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound83
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2656 : keyMomentRows (2656 : Fin 2886) =
    keyMomentRow2656 := by decide +kernel

theorem keyMomentRowsAt2657 : keyMomentRows (2657 : Fin 2886) =
    keyMomentRow2657 := by decide +kernel

theorem keyMomentRowsAt2658 : keyMomentRows (2658 : Fin 2886) =
    keyMomentRow2658 := by decide +kernel

theorem keyMomentRowsAt2659 : keyMomentRows (2659 : Fin 2886) =
    keyMomentRow2659 := by decide +kernel

theorem keyMomentRowsAt2660 : keyMomentRows (2660 : Fin 2886) =
    keyMomentRow2660 := by decide +kernel

theorem keyMomentRowsAt2661 : keyMomentRows (2661 : Fin 2886) =
    keyMomentRow2661 := by decide +kernel

theorem keyMomentRowsAt2662 : keyMomentRows (2662 : Fin 2886) =
    keyMomentRow2662 := by decide +kernel

theorem keyMomentRowsAt2663 : keyMomentRows (2663 : Fin 2886) =
    keyMomentRow2663 := by decide +kernel

theorem keyMomentRowsAt2664 : keyMomentRows (2664 : Fin 2886) =
    keyMomentRow2664 := by decide +kernel

theorem keyMomentRowsAt2665 : keyMomentRows (2665 : Fin 2886) =
    keyMomentRow2665 := by decide +kernel

theorem keyMomentRowsAt2666 : keyMomentRows (2666 : Fin 2886) =
    keyMomentRow2666 := by decide +kernel

theorem keyMomentRowsAt2667 : keyMomentRows (2667 : Fin 2886) =
    keyMomentRow2667 := by decide +kernel

theorem keyMomentRowsAt2668 : keyMomentRows (2668 : Fin 2886) =
    keyMomentRow2668 := by decide +kernel

theorem keyMomentRowsAt2669 : keyMomentRows (2669 : Fin 2886) =
    keyMomentRow2669 := by decide +kernel

theorem keyMomentRowsAt2670 : keyMomentRows (2670 : Fin 2886) =
    keyMomentRow2670 := by decide +kernel

theorem keyMomentRowsAt2671 : keyMomentRows (2671 : Fin 2886) =
    keyMomentRow2671 := by decide +kernel

theorem keyMomentRowsAt2672 : keyMomentRows (2672 : Fin 2886) =
    keyMomentRow2672 := by decide +kernel

theorem keyMomentRowsAt2673 : keyMomentRows (2673 : Fin 2886) =
    keyMomentRow2673 := by decide +kernel

theorem keyMomentRowsAt2674 : keyMomentRows (2674 : Fin 2886) =
    keyMomentRow2674 := by decide +kernel

theorem keyMomentRowsAt2675 : keyMomentRows (2675 : Fin 2886) =
    keyMomentRow2675 := by decide +kernel

theorem keyMomentRowsAt2676 : keyMomentRows (2676 : Fin 2886) =
    keyMomentRow2676 := by decide +kernel

theorem keyMomentRowsAt2677 : keyMomentRows (2677 : Fin 2886) =
    keyMomentRow2677 := by decide +kernel

theorem keyMomentRowsAt2678 : keyMomentRows (2678 : Fin 2886) =
    keyMomentRow2678 := by decide +kernel

theorem keyMomentRowsAt2679 : keyMomentRows (2679 : Fin 2886) =
    keyMomentRow2679 := by decide +kernel

theorem keyMomentRowsAt2680 : keyMomentRows (2680 : Fin 2886) =
    keyMomentRow2680 := by decide +kernel

theorem keyMomentRowsAt2681 : keyMomentRows (2681 : Fin 2886) =
    keyMomentRow2681 := by decide +kernel

theorem keyMomentRowsAt2682 : keyMomentRows (2682 : Fin 2886) =
    keyMomentRow2682 := by decide +kernel

theorem keyMomentRowsAt2683 : keyMomentRows (2683 : Fin 2886) =
    keyMomentRow2683 := by decide +kernel

theorem keyMomentRowsAt2684 : keyMomentRows (2684 : Fin 2886) =
    keyMomentRow2684 := by decide +kernel

theorem keyMomentRowsAt2685 : keyMomentRows (2685 : Fin 2886) =
    keyMomentRow2685 := by decide +kernel

theorem keyMomentRowsAt2686 : keyMomentRows (2686 : Fin 2886) =
    keyMomentRow2686 := by decide +kernel

theorem keyMomentRowsAt2687 : keyMomentRows (2687 : Fin 2886) =
    keyMomentRow2687 := by decide +kernel

theorem keyMomentChunkSound83 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 83) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2656 ∨ k.val = 2657 ∨ k.val = 2658 ∨ k.val = 2659 ∨ k.val = 2660 ∨ k.val = 2661 ∨ k.val = 2662 ∨ k.val = 2663 ∨ k.val = 2664 ∨ k.val = 2665 ∨ k.val = 2666 ∨ k.val = 2667 ∨ k.val = 2668 ∨ k.val = 2669 ∨ k.val = 2670 ∨ k.val = 2671 ∨ k.val = 2672 ∨ k.val = 2673 ∨ k.val = 2674 ∨ k.val = 2675 ∨ k.val = 2676 ∨ k.val = 2677 ∨ k.val = 2678 ∨ k.val = 2679 ∨ k.val = 2680 ∨ k.val = 2681 ∨ k.val = 2682 ∨ k.val = 2683 ∨ k.val = 2684 ∨ k.val = 2685 ∨ k.val = 2686 ∨ k.val = 2687 := by omega
  rcases heq with h2656 | h2657 | h2658 | h2659 | h2660 | h2661 | h2662 | h2663 | h2664 | h2665 | h2666 | h2667 | h2668 | h2669 | h2670 | h2671 | h2672 | h2673 | h2674 | h2675 | h2676 | h2677 | h2678 | h2679 | h2680 | h2681 | h2682 | h2683 | h2684 | h2685 | h2686 | h2687
  · have he : k = (2656 : Fin 2886) := Fin.ext h2656
    subst k
    rw [keyMomentRowsAt2656]
    exact keyMoment2656 B hB
  · have he : k = (2657 : Fin 2886) := Fin.ext h2657
    subst k
    rw [keyMomentRowsAt2657]
    exact keyMoment2657 B hB
  · have he : k = (2658 : Fin 2886) := Fin.ext h2658
    subst k
    rw [keyMomentRowsAt2658]
    exact keyMoment2658 B hB
  · have he : k = (2659 : Fin 2886) := Fin.ext h2659
    subst k
    rw [keyMomentRowsAt2659]
    exact keyMoment2659 B hB
  · have he : k = (2660 : Fin 2886) := Fin.ext h2660
    subst k
    rw [keyMomentRowsAt2660]
    exact keyMoment2660 B hB
  · have he : k = (2661 : Fin 2886) := Fin.ext h2661
    subst k
    rw [keyMomentRowsAt2661]
    exact keyMoment2661 B hB
  · have he : k = (2662 : Fin 2886) := Fin.ext h2662
    subst k
    rw [keyMomentRowsAt2662]
    exact keyMoment2662 B hB
  · have he : k = (2663 : Fin 2886) := Fin.ext h2663
    subst k
    rw [keyMomentRowsAt2663]
    exact keyMoment2663 B hB
  · have he : k = (2664 : Fin 2886) := Fin.ext h2664
    subst k
    rw [keyMomentRowsAt2664]
    exact keyMoment2664 B hB
  · have he : k = (2665 : Fin 2886) := Fin.ext h2665
    subst k
    rw [keyMomentRowsAt2665]
    exact keyMoment2665 B hB
  · have he : k = (2666 : Fin 2886) := Fin.ext h2666
    subst k
    rw [keyMomentRowsAt2666]
    exact keyMoment2666 B hB
  · have he : k = (2667 : Fin 2886) := Fin.ext h2667
    subst k
    rw [keyMomentRowsAt2667]
    exact keyMoment2667 B hB
  · have he : k = (2668 : Fin 2886) := Fin.ext h2668
    subst k
    rw [keyMomentRowsAt2668]
    exact keyMoment2668 B hB
  · have he : k = (2669 : Fin 2886) := Fin.ext h2669
    subst k
    rw [keyMomentRowsAt2669]
    exact keyMoment2669 B hB
  · have he : k = (2670 : Fin 2886) := Fin.ext h2670
    subst k
    rw [keyMomentRowsAt2670]
    exact keyMoment2670 B hB
  · have he : k = (2671 : Fin 2886) := Fin.ext h2671
    subst k
    rw [keyMomentRowsAt2671]
    exact keyMoment2671 B hB
  · have he : k = (2672 : Fin 2886) := Fin.ext h2672
    subst k
    rw [keyMomentRowsAt2672]
    exact keyMoment2672 B hB
  · have he : k = (2673 : Fin 2886) := Fin.ext h2673
    subst k
    rw [keyMomentRowsAt2673]
    exact keyMoment2673 B hB
  · have he : k = (2674 : Fin 2886) := Fin.ext h2674
    subst k
    rw [keyMomentRowsAt2674]
    exact keyMoment2674 B hB
  · have he : k = (2675 : Fin 2886) := Fin.ext h2675
    subst k
    rw [keyMomentRowsAt2675]
    exact keyMoment2675 B hB
  · have he : k = (2676 : Fin 2886) := Fin.ext h2676
    subst k
    rw [keyMomentRowsAt2676]
    exact keyMoment2676 B hB
  · have he : k = (2677 : Fin 2886) := Fin.ext h2677
    subst k
    rw [keyMomentRowsAt2677]
    exact keyMoment2677 B hB
  · have he : k = (2678 : Fin 2886) := Fin.ext h2678
    subst k
    rw [keyMomentRowsAt2678]
    exact keyMoment2678 B hB
  · have he : k = (2679 : Fin 2886) := Fin.ext h2679
    subst k
    rw [keyMomentRowsAt2679]
    exact keyMoment2679 B hB
  · have he : k = (2680 : Fin 2886) := Fin.ext h2680
    subst k
    rw [keyMomentRowsAt2680]
    exact keyMoment2680 B hB
  · have he : k = (2681 : Fin 2886) := Fin.ext h2681
    subst k
    rw [keyMomentRowsAt2681]
    exact keyMoment2681 B hB
  · have he : k = (2682 : Fin 2886) := Fin.ext h2682
    subst k
    rw [keyMomentRowsAt2682]
    exact keyMoment2682 B hB
  · have he : k = (2683 : Fin 2886) := Fin.ext h2683
    subst k
    rw [keyMomentRowsAt2683]
    exact keyMoment2683 B hB
  · have he : k = (2684 : Fin 2886) := Fin.ext h2684
    subst k
    rw [keyMomentRowsAt2684]
    exact keyMoment2684 B hB
  · have he : k = (2685 : Fin 2886) := Fin.ext h2685
    subst k
    rw [keyMomentRowsAt2685]
    exact keyMoment2685 B hB
  · have he : k = (2686 : Fin 2886) := Fin.ext h2686
    subst k
    rw [keyMomentRowsAt2686]
    exact keyMoment2686 B hB
  · have he : k = (2687 : Fin 2886) := Fin.ext h2687
    subst k
    rw [keyMomentRowsAt2687]
    exact keyMoment2687 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
