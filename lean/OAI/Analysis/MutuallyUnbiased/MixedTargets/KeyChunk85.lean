import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound85
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2720 : keyMomentRows (2720 : Fin 2886) =
    keyMomentRow2720 := by decide +kernel

theorem keyMomentRowsAt2721 : keyMomentRows (2721 : Fin 2886) =
    keyMomentRow2721 := by decide +kernel

theorem keyMomentRowsAt2722 : keyMomentRows (2722 : Fin 2886) =
    keyMomentRow2722 := by decide +kernel

theorem keyMomentRowsAt2723 : keyMomentRows (2723 : Fin 2886) =
    keyMomentRow2723 := by decide +kernel

theorem keyMomentRowsAt2724 : keyMomentRows (2724 : Fin 2886) =
    keyMomentRow2724 := by decide +kernel

theorem keyMomentRowsAt2725 : keyMomentRows (2725 : Fin 2886) =
    keyMomentRow2725 := by decide +kernel

theorem keyMomentRowsAt2726 : keyMomentRows (2726 : Fin 2886) =
    keyMomentRow2726 := by decide +kernel

theorem keyMomentRowsAt2727 : keyMomentRows (2727 : Fin 2886) =
    keyMomentRow2727 := by decide +kernel

theorem keyMomentRowsAt2728 : keyMomentRows (2728 : Fin 2886) =
    keyMomentRow2728 := by decide +kernel

theorem keyMomentRowsAt2729 : keyMomentRows (2729 : Fin 2886) =
    keyMomentRow2729 := by decide +kernel

theorem keyMomentRowsAt2730 : keyMomentRows (2730 : Fin 2886) =
    keyMomentRow2730 := by decide +kernel

theorem keyMomentRowsAt2731 : keyMomentRows (2731 : Fin 2886) =
    keyMomentRow2731 := by decide +kernel

theorem keyMomentRowsAt2732 : keyMomentRows (2732 : Fin 2886) =
    keyMomentRow2732 := by decide +kernel

theorem keyMomentRowsAt2733 : keyMomentRows (2733 : Fin 2886) =
    keyMomentRow2733 := by decide +kernel

theorem keyMomentRowsAt2734 : keyMomentRows (2734 : Fin 2886) =
    keyMomentRow2734 := by decide +kernel

theorem keyMomentRowsAt2735 : keyMomentRows (2735 : Fin 2886) =
    keyMomentRow2735 := by decide +kernel

theorem keyMomentRowsAt2736 : keyMomentRows (2736 : Fin 2886) =
    keyMomentRow2736 := by decide +kernel

theorem keyMomentRowsAt2737 : keyMomentRows (2737 : Fin 2886) =
    keyMomentRow2737 := by decide +kernel

theorem keyMomentRowsAt2738 : keyMomentRows (2738 : Fin 2886) =
    keyMomentRow2738 := by decide +kernel

theorem keyMomentRowsAt2739 : keyMomentRows (2739 : Fin 2886) =
    keyMomentRow2739 := by decide +kernel

theorem keyMomentRowsAt2740 : keyMomentRows (2740 : Fin 2886) =
    keyMomentRow2740 := by decide +kernel

theorem keyMomentRowsAt2741 : keyMomentRows (2741 : Fin 2886) =
    keyMomentRow2741 := by decide +kernel

theorem keyMomentRowsAt2742 : keyMomentRows (2742 : Fin 2886) =
    keyMomentRow2742 := by decide +kernel

theorem keyMomentRowsAt2743 : keyMomentRows (2743 : Fin 2886) =
    keyMomentRow2743 := by decide +kernel

theorem keyMomentRowsAt2744 : keyMomentRows (2744 : Fin 2886) =
    keyMomentRow2744 := by decide +kernel

theorem keyMomentRowsAt2745 : keyMomentRows (2745 : Fin 2886) =
    keyMomentRow2745 := by decide +kernel

theorem keyMomentRowsAt2746 : keyMomentRows (2746 : Fin 2886) =
    keyMomentRow2746 := by decide +kernel

theorem keyMomentRowsAt2747 : keyMomentRows (2747 : Fin 2886) =
    keyMomentRow2747 := by decide +kernel

theorem keyMomentRowsAt2748 : keyMomentRows (2748 : Fin 2886) =
    keyMomentRow2748 := by decide +kernel

theorem keyMomentRowsAt2749 : keyMomentRows (2749 : Fin 2886) =
    keyMomentRow2749 := by decide +kernel

theorem keyMomentRowsAt2750 : keyMomentRows (2750 : Fin 2886) =
    keyMomentRow2750 := by decide +kernel

theorem keyMomentRowsAt2751 : keyMomentRows (2751 : Fin 2886) =
    keyMomentRow2751 := by decide +kernel

theorem keyMomentChunkSound85 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 85) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2720 ∨ k.val = 2721 ∨ k.val = 2722 ∨ k.val = 2723 ∨ k.val = 2724 ∨ k.val = 2725 ∨ k.val = 2726 ∨ k.val = 2727 ∨ k.val = 2728 ∨ k.val = 2729 ∨ k.val = 2730 ∨ k.val = 2731 ∨ k.val = 2732 ∨ k.val = 2733 ∨ k.val = 2734 ∨ k.val = 2735 ∨ k.val = 2736 ∨ k.val = 2737 ∨ k.val = 2738 ∨ k.val = 2739 ∨ k.val = 2740 ∨ k.val = 2741 ∨ k.val = 2742 ∨ k.val = 2743 ∨ k.val = 2744 ∨ k.val = 2745 ∨ k.val = 2746 ∨ k.val = 2747 ∨ k.val = 2748 ∨ k.val = 2749 ∨ k.val = 2750 ∨ k.val = 2751 := by omega
  rcases heq with h2720 | h2721 | h2722 | h2723 | h2724 | h2725 | h2726 | h2727 | h2728 | h2729 | h2730 | h2731 | h2732 | h2733 | h2734 | h2735 | h2736 | h2737 | h2738 | h2739 | h2740 | h2741 | h2742 | h2743 | h2744 | h2745 | h2746 | h2747 | h2748 | h2749 | h2750 | h2751
  · have he : k = (2720 : Fin 2886) := Fin.ext h2720
    subst k
    rw [keyMomentRowsAt2720]
    exact keyMoment2720 B hB
  · have he : k = (2721 : Fin 2886) := Fin.ext h2721
    subst k
    rw [keyMomentRowsAt2721]
    exact keyMoment2721 B hB
  · have he : k = (2722 : Fin 2886) := Fin.ext h2722
    subst k
    rw [keyMomentRowsAt2722]
    exact keyMoment2722 B hB
  · have he : k = (2723 : Fin 2886) := Fin.ext h2723
    subst k
    rw [keyMomentRowsAt2723]
    exact keyMoment2723 B hB
  · have he : k = (2724 : Fin 2886) := Fin.ext h2724
    subst k
    rw [keyMomentRowsAt2724]
    exact keyMoment2724 B hB
  · have he : k = (2725 : Fin 2886) := Fin.ext h2725
    subst k
    rw [keyMomentRowsAt2725]
    exact keyMoment2725 B hB
  · have he : k = (2726 : Fin 2886) := Fin.ext h2726
    subst k
    rw [keyMomentRowsAt2726]
    exact keyMoment2726 B hB
  · have he : k = (2727 : Fin 2886) := Fin.ext h2727
    subst k
    rw [keyMomentRowsAt2727]
    exact keyMoment2727 B hB
  · have he : k = (2728 : Fin 2886) := Fin.ext h2728
    subst k
    rw [keyMomentRowsAt2728]
    exact keyMoment2728 B hB
  · have he : k = (2729 : Fin 2886) := Fin.ext h2729
    subst k
    rw [keyMomentRowsAt2729]
    exact keyMoment2729 B hB
  · have he : k = (2730 : Fin 2886) := Fin.ext h2730
    subst k
    rw [keyMomentRowsAt2730]
    exact keyMoment2730 B hB
  · have he : k = (2731 : Fin 2886) := Fin.ext h2731
    subst k
    rw [keyMomentRowsAt2731]
    exact keyMoment2731 B hB
  · have he : k = (2732 : Fin 2886) := Fin.ext h2732
    subst k
    rw [keyMomentRowsAt2732]
    exact keyMoment2732 B hB
  · have he : k = (2733 : Fin 2886) := Fin.ext h2733
    subst k
    rw [keyMomentRowsAt2733]
    exact keyMoment2733 B hB
  · have he : k = (2734 : Fin 2886) := Fin.ext h2734
    subst k
    rw [keyMomentRowsAt2734]
    exact keyMoment2734 B hB
  · have he : k = (2735 : Fin 2886) := Fin.ext h2735
    subst k
    rw [keyMomentRowsAt2735]
    exact keyMoment2735 B hB
  · have he : k = (2736 : Fin 2886) := Fin.ext h2736
    subst k
    rw [keyMomentRowsAt2736]
    exact keyMoment2736 B hB
  · have he : k = (2737 : Fin 2886) := Fin.ext h2737
    subst k
    rw [keyMomentRowsAt2737]
    exact keyMoment2737 B hB
  · have he : k = (2738 : Fin 2886) := Fin.ext h2738
    subst k
    rw [keyMomentRowsAt2738]
    exact keyMoment2738 B hB
  · have he : k = (2739 : Fin 2886) := Fin.ext h2739
    subst k
    rw [keyMomentRowsAt2739]
    exact keyMoment2739 B hB
  · have he : k = (2740 : Fin 2886) := Fin.ext h2740
    subst k
    rw [keyMomentRowsAt2740]
    exact keyMoment2740 B hB
  · have he : k = (2741 : Fin 2886) := Fin.ext h2741
    subst k
    rw [keyMomentRowsAt2741]
    exact keyMoment2741 B hB
  · have he : k = (2742 : Fin 2886) := Fin.ext h2742
    subst k
    rw [keyMomentRowsAt2742]
    exact keyMoment2742 B hB
  · have he : k = (2743 : Fin 2886) := Fin.ext h2743
    subst k
    rw [keyMomentRowsAt2743]
    exact keyMoment2743 B hB
  · have he : k = (2744 : Fin 2886) := Fin.ext h2744
    subst k
    rw [keyMomentRowsAt2744]
    exact keyMoment2744 B hB
  · have he : k = (2745 : Fin 2886) := Fin.ext h2745
    subst k
    rw [keyMomentRowsAt2745]
    exact keyMoment2745 B hB
  · have he : k = (2746 : Fin 2886) := Fin.ext h2746
    subst k
    rw [keyMomentRowsAt2746]
    exact keyMoment2746 B hB
  · have he : k = (2747 : Fin 2886) := Fin.ext h2747
    subst k
    rw [keyMomentRowsAt2747]
    exact keyMoment2747 B hB
  · have he : k = (2748 : Fin 2886) := Fin.ext h2748
    subst k
    rw [keyMomentRowsAt2748]
    exact keyMoment2748 B hB
  · have he : k = (2749 : Fin 2886) := Fin.ext h2749
    subst k
    rw [keyMomentRowsAt2749]
    exact keyMoment2749 B hB
  · have he : k = (2750 : Fin 2886) := Fin.ext h2750
    subst k
    rw [keyMomentRowsAt2750]
    exact keyMoment2750 B hB
  · have he : k = (2751 : Fin 2886) := Fin.ext h2751
    subst k
    rw [keyMomentRowsAt2751]
    exact keyMoment2751 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
