import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound86
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2752 : keyMomentRows (2752 : Fin 2886) =
    keyMomentRow2752 := by decide +kernel

theorem keyMomentRowsAt2753 : keyMomentRows (2753 : Fin 2886) =
    keyMomentRow2753 := by decide +kernel

theorem keyMomentRowsAt2754 : keyMomentRows (2754 : Fin 2886) =
    keyMomentRow2754 := by decide +kernel

theorem keyMomentRowsAt2755 : keyMomentRows (2755 : Fin 2886) =
    keyMomentRow2755 := by decide +kernel

theorem keyMomentRowsAt2756 : keyMomentRows (2756 : Fin 2886) =
    keyMomentRow2756 := by decide +kernel

theorem keyMomentRowsAt2757 : keyMomentRows (2757 : Fin 2886) =
    keyMomentRow2757 := by decide +kernel

theorem keyMomentRowsAt2758 : keyMomentRows (2758 : Fin 2886) =
    keyMomentRow2758 := by decide +kernel

theorem keyMomentRowsAt2759 : keyMomentRows (2759 : Fin 2886) =
    keyMomentRow2759 := by decide +kernel

theorem keyMomentRowsAt2760 : keyMomentRows (2760 : Fin 2886) =
    keyMomentRow2760 := by decide +kernel

theorem keyMomentRowsAt2761 : keyMomentRows (2761 : Fin 2886) =
    keyMomentRow2761 := by decide +kernel

theorem keyMomentRowsAt2762 : keyMomentRows (2762 : Fin 2886) =
    keyMomentRow2762 := by decide +kernel

theorem keyMomentRowsAt2763 : keyMomentRows (2763 : Fin 2886) =
    keyMomentRow2763 := by decide +kernel

theorem keyMomentRowsAt2764 : keyMomentRows (2764 : Fin 2886) =
    keyMomentRow2764 := by decide +kernel

theorem keyMomentRowsAt2765 : keyMomentRows (2765 : Fin 2886) =
    keyMomentRow2765 := by decide +kernel

theorem keyMomentRowsAt2766 : keyMomentRows (2766 : Fin 2886) =
    keyMomentRow2766 := by decide +kernel

theorem keyMomentRowsAt2767 : keyMomentRows (2767 : Fin 2886) =
    keyMomentRow2767 := by decide +kernel

theorem keyMomentRowsAt2768 : keyMomentRows (2768 : Fin 2886) =
    keyMomentRow2768 := by decide +kernel

theorem keyMomentRowsAt2769 : keyMomentRows (2769 : Fin 2886) =
    keyMomentRow2769 := by decide +kernel

theorem keyMomentRowsAt2770 : keyMomentRows (2770 : Fin 2886) =
    keyMomentRow2770 := by decide +kernel

theorem keyMomentRowsAt2771 : keyMomentRows (2771 : Fin 2886) =
    keyMomentRow2771 := by decide +kernel

theorem keyMomentRowsAt2772 : keyMomentRows (2772 : Fin 2886) =
    keyMomentRow2772 := by decide +kernel

theorem keyMomentRowsAt2773 : keyMomentRows (2773 : Fin 2886) =
    keyMomentRow2773 := by decide +kernel

theorem keyMomentRowsAt2774 : keyMomentRows (2774 : Fin 2886) =
    keyMomentRow2774 := by decide +kernel

theorem keyMomentRowsAt2775 : keyMomentRows (2775 : Fin 2886) =
    keyMomentRow2775 := by decide +kernel

theorem keyMomentRowsAt2776 : keyMomentRows (2776 : Fin 2886) =
    keyMomentRow2776 := by decide +kernel

theorem keyMomentRowsAt2777 : keyMomentRows (2777 : Fin 2886) =
    keyMomentRow2777 := by decide +kernel

theorem keyMomentRowsAt2778 : keyMomentRows (2778 : Fin 2886) =
    keyMomentRow2778 := by decide +kernel

theorem keyMomentRowsAt2779 : keyMomentRows (2779 : Fin 2886) =
    keyMomentRow2779 := by decide +kernel

theorem keyMomentRowsAt2780 : keyMomentRows (2780 : Fin 2886) =
    keyMomentRow2780 := by decide +kernel

theorem keyMomentRowsAt2781 : keyMomentRows (2781 : Fin 2886) =
    keyMomentRow2781 := by decide +kernel

theorem keyMomentRowsAt2782 : keyMomentRows (2782 : Fin 2886) =
    keyMomentRow2782 := by decide +kernel

theorem keyMomentRowsAt2783 : keyMomentRows (2783 : Fin 2886) =
    keyMomentRow2783 := by decide +kernel

theorem keyMomentChunkSound86 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 86) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2752 ∨ k.val = 2753 ∨ k.val = 2754 ∨ k.val = 2755 ∨ k.val = 2756 ∨ k.val = 2757 ∨ k.val = 2758 ∨ k.val = 2759 ∨ k.val = 2760 ∨ k.val = 2761 ∨ k.val = 2762 ∨ k.val = 2763 ∨ k.val = 2764 ∨ k.val = 2765 ∨ k.val = 2766 ∨ k.val = 2767 ∨ k.val = 2768 ∨ k.val = 2769 ∨ k.val = 2770 ∨ k.val = 2771 ∨ k.val = 2772 ∨ k.val = 2773 ∨ k.val = 2774 ∨ k.val = 2775 ∨ k.val = 2776 ∨ k.val = 2777 ∨ k.val = 2778 ∨ k.val = 2779 ∨ k.val = 2780 ∨ k.val = 2781 ∨ k.val = 2782 ∨ k.val = 2783 := by omega
  rcases heq with h2752 | h2753 | h2754 | h2755 | h2756 | h2757 | h2758 | h2759 | h2760 | h2761 | h2762 | h2763 | h2764 | h2765 | h2766 | h2767 | h2768 | h2769 | h2770 | h2771 | h2772 | h2773 | h2774 | h2775 | h2776 | h2777 | h2778 | h2779 | h2780 | h2781 | h2782 | h2783
  · have he : k = (2752 : Fin 2886) := Fin.ext h2752
    subst k
    rw [keyMomentRowsAt2752]
    exact keyMoment2752 B hB
  · have he : k = (2753 : Fin 2886) := Fin.ext h2753
    subst k
    rw [keyMomentRowsAt2753]
    exact keyMoment2753 B hB
  · have he : k = (2754 : Fin 2886) := Fin.ext h2754
    subst k
    rw [keyMomentRowsAt2754]
    exact keyMoment2754 B hB
  · have he : k = (2755 : Fin 2886) := Fin.ext h2755
    subst k
    rw [keyMomentRowsAt2755]
    exact keyMoment2755 B hB
  · have he : k = (2756 : Fin 2886) := Fin.ext h2756
    subst k
    rw [keyMomentRowsAt2756]
    exact keyMoment2756 B hB
  · have he : k = (2757 : Fin 2886) := Fin.ext h2757
    subst k
    rw [keyMomentRowsAt2757]
    exact keyMoment2757 B hB
  · have he : k = (2758 : Fin 2886) := Fin.ext h2758
    subst k
    rw [keyMomentRowsAt2758]
    exact keyMoment2758 B hB
  · have he : k = (2759 : Fin 2886) := Fin.ext h2759
    subst k
    rw [keyMomentRowsAt2759]
    exact keyMoment2759 B hB
  · have he : k = (2760 : Fin 2886) := Fin.ext h2760
    subst k
    rw [keyMomentRowsAt2760]
    exact keyMoment2760 B hB
  · have he : k = (2761 : Fin 2886) := Fin.ext h2761
    subst k
    rw [keyMomentRowsAt2761]
    exact keyMoment2761 B hB
  · have he : k = (2762 : Fin 2886) := Fin.ext h2762
    subst k
    rw [keyMomentRowsAt2762]
    exact keyMoment2762 B hB
  · have he : k = (2763 : Fin 2886) := Fin.ext h2763
    subst k
    rw [keyMomentRowsAt2763]
    exact keyMoment2763 B hB
  · have he : k = (2764 : Fin 2886) := Fin.ext h2764
    subst k
    rw [keyMomentRowsAt2764]
    exact keyMoment2764 B hB
  · have he : k = (2765 : Fin 2886) := Fin.ext h2765
    subst k
    rw [keyMomentRowsAt2765]
    exact keyMoment2765 B hB
  · have he : k = (2766 : Fin 2886) := Fin.ext h2766
    subst k
    rw [keyMomentRowsAt2766]
    exact keyMoment2766 B hB
  · have he : k = (2767 : Fin 2886) := Fin.ext h2767
    subst k
    rw [keyMomentRowsAt2767]
    exact keyMoment2767 B hB
  · have he : k = (2768 : Fin 2886) := Fin.ext h2768
    subst k
    rw [keyMomentRowsAt2768]
    exact keyMoment2768 B hB
  · have he : k = (2769 : Fin 2886) := Fin.ext h2769
    subst k
    rw [keyMomentRowsAt2769]
    exact keyMoment2769 B hB
  · have he : k = (2770 : Fin 2886) := Fin.ext h2770
    subst k
    rw [keyMomentRowsAt2770]
    exact keyMoment2770 B hB
  · have he : k = (2771 : Fin 2886) := Fin.ext h2771
    subst k
    rw [keyMomentRowsAt2771]
    exact keyMoment2771 B hB
  · have he : k = (2772 : Fin 2886) := Fin.ext h2772
    subst k
    rw [keyMomentRowsAt2772]
    exact keyMoment2772 B hB
  · have he : k = (2773 : Fin 2886) := Fin.ext h2773
    subst k
    rw [keyMomentRowsAt2773]
    exact keyMoment2773 B hB
  · have he : k = (2774 : Fin 2886) := Fin.ext h2774
    subst k
    rw [keyMomentRowsAt2774]
    exact keyMoment2774 B hB
  · have he : k = (2775 : Fin 2886) := Fin.ext h2775
    subst k
    rw [keyMomentRowsAt2775]
    exact keyMoment2775 B hB
  · have he : k = (2776 : Fin 2886) := Fin.ext h2776
    subst k
    rw [keyMomentRowsAt2776]
    exact keyMoment2776 B hB
  · have he : k = (2777 : Fin 2886) := Fin.ext h2777
    subst k
    rw [keyMomentRowsAt2777]
    exact keyMoment2777 B hB
  · have he : k = (2778 : Fin 2886) := Fin.ext h2778
    subst k
    rw [keyMomentRowsAt2778]
    exact keyMoment2778 B hB
  · have he : k = (2779 : Fin 2886) := Fin.ext h2779
    subst k
    rw [keyMomentRowsAt2779]
    exact keyMoment2779 B hB
  · have he : k = (2780 : Fin 2886) := Fin.ext h2780
    subst k
    rw [keyMomentRowsAt2780]
    exact keyMoment2780 B hB
  · have he : k = (2781 : Fin 2886) := Fin.ext h2781
    subst k
    rw [keyMomentRowsAt2781]
    exact keyMoment2781 B hB
  · have he : k = (2782 : Fin 2886) := Fin.ext h2782
    subst k
    rw [keyMomentRowsAt2782]
    exact keyMoment2782 B hB
  · have he : k = (2783 : Fin 2886) := Fin.ext h2783
    subst k
    rw [keyMomentRowsAt2783]
    exact keyMoment2783 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
