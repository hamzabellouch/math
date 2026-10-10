import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound84
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2688 : keyMomentRows (2688 : Fin 2886) =
    keyMomentRow2688 := by decide +kernel

theorem keyMomentRowsAt2689 : keyMomentRows (2689 : Fin 2886) =
    keyMomentRow2689 := by decide +kernel

theorem keyMomentRowsAt2690 : keyMomentRows (2690 : Fin 2886) =
    keyMomentRow2690 := by decide +kernel

theorem keyMomentRowsAt2691 : keyMomentRows (2691 : Fin 2886) =
    keyMomentRow2691 := by decide +kernel

theorem keyMomentRowsAt2692 : keyMomentRows (2692 : Fin 2886) =
    keyMomentRow2692 := by decide +kernel

theorem keyMomentRowsAt2693 : keyMomentRows (2693 : Fin 2886) =
    keyMomentRow2693 := by decide +kernel

theorem keyMomentRowsAt2694 : keyMomentRows (2694 : Fin 2886) =
    keyMomentRow2694 := by decide +kernel

theorem keyMomentRowsAt2695 : keyMomentRows (2695 : Fin 2886) =
    keyMomentRow2695 := by decide +kernel

theorem keyMomentRowsAt2696 : keyMomentRows (2696 : Fin 2886) =
    keyMomentRow2696 := by decide +kernel

theorem keyMomentRowsAt2697 : keyMomentRows (2697 : Fin 2886) =
    keyMomentRow2697 := by decide +kernel

theorem keyMomentRowsAt2698 : keyMomentRows (2698 : Fin 2886) =
    keyMomentRow2698 := by decide +kernel

theorem keyMomentRowsAt2699 : keyMomentRows (2699 : Fin 2886) =
    keyMomentRow2699 := by decide +kernel

theorem keyMomentRowsAt2700 : keyMomentRows (2700 : Fin 2886) =
    keyMomentRow2700 := by decide +kernel

theorem keyMomentRowsAt2701 : keyMomentRows (2701 : Fin 2886) =
    keyMomentRow2701 := by decide +kernel

theorem keyMomentRowsAt2702 : keyMomentRows (2702 : Fin 2886) =
    keyMomentRow2702 := by decide +kernel

theorem keyMomentRowsAt2703 : keyMomentRows (2703 : Fin 2886) =
    keyMomentRow2703 := by decide +kernel

theorem keyMomentRowsAt2704 : keyMomentRows (2704 : Fin 2886) =
    keyMomentRow2704 := by decide +kernel

theorem keyMomentRowsAt2705 : keyMomentRows (2705 : Fin 2886) =
    keyMomentRow2705 := by decide +kernel

theorem keyMomentRowsAt2706 : keyMomentRows (2706 : Fin 2886) =
    keyMomentRow2706 := by decide +kernel

theorem keyMomentRowsAt2707 : keyMomentRows (2707 : Fin 2886) =
    keyMomentRow2707 := by decide +kernel

theorem keyMomentRowsAt2708 : keyMomentRows (2708 : Fin 2886) =
    keyMomentRow2708 := by decide +kernel

theorem keyMomentRowsAt2709 : keyMomentRows (2709 : Fin 2886) =
    keyMomentRow2709 := by decide +kernel

theorem keyMomentRowsAt2710 : keyMomentRows (2710 : Fin 2886) =
    keyMomentRow2710 := by decide +kernel

theorem keyMomentRowsAt2711 : keyMomentRows (2711 : Fin 2886) =
    keyMomentRow2711 := by decide +kernel

theorem keyMomentRowsAt2712 : keyMomentRows (2712 : Fin 2886) =
    keyMomentRow2712 := by decide +kernel

theorem keyMomentRowsAt2713 : keyMomentRows (2713 : Fin 2886) =
    keyMomentRow2713 := by decide +kernel

theorem keyMomentRowsAt2714 : keyMomentRows (2714 : Fin 2886) =
    keyMomentRow2714 := by decide +kernel

theorem keyMomentRowsAt2715 : keyMomentRows (2715 : Fin 2886) =
    keyMomentRow2715 := by decide +kernel

theorem keyMomentRowsAt2716 : keyMomentRows (2716 : Fin 2886) =
    keyMomentRow2716 := by decide +kernel

theorem keyMomentRowsAt2717 : keyMomentRows (2717 : Fin 2886) =
    keyMomentRow2717 := by decide +kernel

theorem keyMomentRowsAt2718 : keyMomentRows (2718 : Fin 2886) =
    keyMomentRow2718 := by decide +kernel

theorem keyMomentRowsAt2719 : keyMomentRows (2719 : Fin 2886) =
    keyMomentRow2719 := by decide +kernel

theorem keyMomentChunkSound84 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 84) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2688 ∨ k.val = 2689 ∨ k.val = 2690 ∨ k.val = 2691 ∨ k.val = 2692 ∨ k.val = 2693 ∨ k.val = 2694 ∨ k.val = 2695 ∨ k.val = 2696 ∨ k.val = 2697 ∨ k.val = 2698 ∨ k.val = 2699 ∨ k.val = 2700 ∨ k.val = 2701 ∨ k.val = 2702 ∨ k.val = 2703 ∨ k.val = 2704 ∨ k.val = 2705 ∨ k.val = 2706 ∨ k.val = 2707 ∨ k.val = 2708 ∨ k.val = 2709 ∨ k.val = 2710 ∨ k.val = 2711 ∨ k.val = 2712 ∨ k.val = 2713 ∨ k.val = 2714 ∨ k.val = 2715 ∨ k.val = 2716 ∨ k.val = 2717 ∨ k.val = 2718 ∨ k.val = 2719 := by omega
  rcases heq with h2688 | h2689 | h2690 | h2691 | h2692 | h2693 | h2694 | h2695 | h2696 | h2697 | h2698 | h2699 | h2700 | h2701 | h2702 | h2703 | h2704 | h2705 | h2706 | h2707 | h2708 | h2709 | h2710 | h2711 | h2712 | h2713 | h2714 | h2715 | h2716 | h2717 | h2718 | h2719
  · have he : k = (2688 : Fin 2886) := Fin.ext h2688
    subst k
    rw [keyMomentRowsAt2688]
    exact keyMoment2688 B hB
  · have he : k = (2689 : Fin 2886) := Fin.ext h2689
    subst k
    rw [keyMomentRowsAt2689]
    exact keyMoment2689 B hB
  · have he : k = (2690 : Fin 2886) := Fin.ext h2690
    subst k
    rw [keyMomentRowsAt2690]
    exact keyMoment2690 B hB
  · have he : k = (2691 : Fin 2886) := Fin.ext h2691
    subst k
    rw [keyMomentRowsAt2691]
    exact keyMoment2691 B hB
  · have he : k = (2692 : Fin 2886) := Fin.ext h2692
    subst k
    rw [keyMomentRowsAt2692]
    exact keyMoment2692 B hB
  · have he : k = (2693 : Fin 2886) := Fin.ext h2693
    subst k
    rw [keyMomentRowsAt2693]
    exact keyMoment2693 B hB
  · have he : k = (2694 : Fin 2886) := Fin.ext h2694
    subst k
    rw [keyMomentRowsAt2694]
    exact keyMoment2694 B hB
  · have he : k = (2695 : Fin 2886) := Fin.ext h2695
    subst k
    rw [keyMomentRowsAt2695]
    exact keyMoment2695 B hB
  · have he : k = (2696 : Fin 2886) := Fin.ext h2696
    subst k
    rw [keyMomentRowsAt2696]
    exact keyMoment2696 B hB
  · have he : k = (2697 : Fin 2886) := Fin.ext h2697
    subst k
    rw [keyMomentRowsAt2697]
    exact keyMoment2697 B hB
  · have he : k = (2698 : Fin 2886) := Fin.ext h2698
    subst k
    rw [keyMomentRowsAt2698]
    exact keyMoment2698 B hB
  · have he : k = (2699 : Fin 2886) := Fin.ext h2699
    subst k
    rw [keyMomentRowsAt2699]
    exact keyMoment2699 B hB
  · have he : k = (2700 : Fin 2886) := Fin.ext h2700
    subst k
    rw [keyMomentRowsAt2700]
    exact keyMoment2700 B hB
  · have he : k = (2701 : Fin 2886) := Fin.ext h2701
    subst k
    rw [keyMomentRowsAt2701]
    exact keyMoment2701 B hB
  · have he : k = (2702 : Fin 2886) := Fin.ext h2702
    subst k
    rw [keyMomentRowsAt2702]
    exact keyMoment2702 B hB
  · have he : k = (2703 : Fin 2886) := Fin.ext h2703
    subst k
    rw [keyMomentRowsAt2703]
    exact keyMoment2703 B hB
  · have he : k = (2704 : Fin 2886) := Fin.ext h2704
    subst k
    rw [keyMomentRowsAt2704]
    exact keyMoment2704 B hB
  · have he : k = (2705 : Fin 2886) := Fin.ext h2705
    subst k
    rw [keyMomentRowsAt2705]
    exact keyMoment2705 B hB
  · have he : k = (2706 : Fin 2886) := Fin.ext h2706
    subst k
    rw [keyMomentRowsAt2706]
    exact keyMoment2706 B hB
  · have he : k = (2707 : Fin 2886) := Fin.ext h2707
    subst k
    rw [keyMomentRowsAt2707]
    exact keyMoment2707 B hB
  · have he : k = (2708 : Fin 2886) := Fin.ext h2708
    subst k
    rw [keyMomentRowsAt2708]
    exact keyMoment2708 B hB
  · have he : k = (2709 : Fin 2886) := Fin.ext h2709
    subst k
    rw [keyMomentRowsAt2709]
    exact keyMoment2709 B hB
  · have he : k = (2710 : Fin 2886) := Fin.ext h2710
    subst k
    rw [keyMomentRowsAt2710]
    exact keyMoment2710 B hB
  · have he : k = (2711 : Fin 2886) := Fin.ext h2711
    subst k
    rw [keyMomentRowsAt2711]
    exact keyMoment2711 B hB
  · have he : k = (2712 : Fin 2886) := Fin.ext h2712
    subst k
    rw [keyMomentRowsAt2712]
    exact keyMoment2712 B hB
  · have he : k = (2713 : Fin 2886) := Fin.ext h2713
    subst k
    rw [keyMomentRowsAt2713]
    exact keyMoment2713 B hB
  · have he : k = (2714 : Fin 2886) := Fin.ext h2714
    subst k
    rw [keyMomentRowsAt2714]
    exact keyMoment2714 B hB
  · have he : k = (2715 : Fin 2886) := Fin.ext h2715
    subst k
    rw [keyMomentRowsAt2715]
    exact keyMoment2715 B hB
  · have he : k = (2716 : Fin 2886) := Fin.ext h2716
    subst k
    rw [keyMomentRowsAt2716]
    exact keyMoment2716 B hB
  · have he : k = (2717 : Fin 2886) := Fin.ext h2717
    subst k
    rw [keyMomentRowsAt2717]
    exact keyMoment2717 B hB
  · have he : k = (2718 : Fin 2886) := Fin.ext h2718
    subst k
    rw [keyMomentRowsAt2718]
    exact keyMoment2718 B hB
  · have he : k = (2719 : Fin 2886) := Fin.ext h2719
    subst k
    rw [keyMomentRowsAt2719]
    exact keyMoment2719 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
