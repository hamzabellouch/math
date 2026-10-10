import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound88
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2816 : keyMomentRows (2816 : Fin 2886) =
    keyMomentRow2816 := by decide +kernel

theorem keyMomentRowsAt2817 : keyMomentRows (2817 : Fin 2886) =
    keyMomentRow2817 := by decide +kernel

theorem keyMomentRowsAt2818 : keyMomentRows (2818 : Fin 2886) =
    keyMomentRow2818 := by decide +kernel

theorem keyMomentRowsAt2819 : keyMomentRows (2819 : Fin 2886) =
    keyMomentRow2819 := by decide +kernel

theorem keyMomentRowsAt2820 : keyMomentRows (2820 : Fin 2886) =
    keyMomentRow2820 := by decide +kernel

theorem keyMomentRowsAt2821 : keyMomentRows (2821 : Fin 2886) =
    keyMomentRow2821 := by decide +kernel

theorem keyMomentRowsAt2822 : keyMomentRows (2822 : Fin 2886) =
    keyMomentRow2822 := by decide +kernel

theorem keyMomentRowsAt2823 : keyMomentRows (2823 : Fin 2886) =
    keyMomentRow2823 := by decide +kernel

theorem keyMomentRowsAt2824 : keyMomentRows (2824 : Fin 2886) =
    keyMomentRow2824 := by decide +kernel

theorem keyMomentRowsAt2825 : keyMomentRows (2825 : Fin 2886) =
    keyMomentRow2825 := by decide +kernel

theorem keyMomentRowsAt2826 : keyMomentRows (2826 : Fin 2886) =
    keyMomentRow2826 := by decide +kernel

theorem keyMomentRowsAt2827 : keyMomentRows (2827 : Fin 2886) =
    keyMomentRow2827 := by decide +kernel

theorem keyMomentRowsAt2828 : keyMomentRows (2828 : Fin 2886) =
    keyMomentRow2828 := by decide +kernel

theorem keyMomentRowsAt2829 : keyMomentRows (2829 : Fin 2886) =
    keyMomentRow2829 := by decide +kernel

theorem keyMomentRowsAt2830 : keyMomentRows (2830 : Fin 2886) =
    keyMomentRow2830 := by decide +kernel

theorem keyMomentRowsAt2831 : keyMomentRows (2831 : Fin 2886) =
    keyMomentRow2831 := by decide +kernel

theorem keyMomentRowsAt2832 : keyMomentRows (2832 : Fin 2886) =
    keyMomentRow2832 := by decide +kernel

theorem keyMomentRowsAt2833 : keyMomentRows (2833 : Fin 2886) =
    keyMomentRow2833 := by decide +kernel

theorem keyMomentRowsAt2834 : keyMomentRows (2834 : Fin 2886) =
    keyMomentRow2834 := by decide +kernel

theorem keyMomentRowsAt2835 : keyMomentRows (2835 : Fin 2886) =
    keyMomentRow2835 := by decide +kernel

theorem keyMomentRowsAt2836 : keyMomentRows (2836 : Fin 2886) =
    keyMomentRow2836 := by decide +kernel

theorem keyMomentRowsAt2837 : keyMomentRows (2837 : Fin 2886) =
    keyMomentRow2837 := by decide +kernel

theorem keyMomentRowsAt2838 : keyMomentRows (2838 : Fin 2886) =
    keyMomentRow2838 := by decide +kernel

theorem keyMomentRowsAt2839 : keyMomentRows (2839 : Fin 2886) =
    keyMomentRow2839 := by decide +kernel

theorem keyMomentRowsAt2840 : keyMomentRows (2840 : Fin 2886) =
    keyMomentRow2840 := by decide +kernel

theorem keyMomentRowsAt2841 : keyMomentRows (2841 : Fin 2886) =
    keyMomentRow2841 := by decide +kernel

theorem keyMomentRowsAt2842 : keyMomentRows (2842 : Fin 2886) =
    keyMomentRow2842 := by decide +kernel

theorem keyMomentRowsAt2843 : keyMomentRows (2843 : Fin 2886) =
    keyMomentRow2843 := by decide +kernel

theorem keyMomentRowsAt2844 : keyMomentRows (2844 : Fin 2886) =
    keyMomentRow2844 := by decide +kernel

theorem keyMomentRowsAt2845 : keyMomentRows (2845 : Fin 2886) =
    keyMomentRow2845 := by decide +kernel

theorem keyMomentRowsAt2846 : keyMomentRows (2846 : Fin 2886) =
    keyMomentRow2846 := by decide +kernel

theorem keyMomentRowsAt2847 : keyMomentRows (2847 : Fin 2886) =
    keyMomentRow2847 := by decide +kernel

theorem keyMomentChunkSound88 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 88) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2816 ∨ k.val = 2817 ∨ k.val = 2818 ∨ k.val = 2819 ∨ k.val = 2820 ∨ k.val = 2821 ∨ k.val = 2822 ∨ k.val = 2823 ∨ k.val = 2824 ∨ k.val = 2825 ∨ k.val = 2826 ∨ k.val = 2827 ∨ k.val = 2828 ∨ k.val = 2829 ∨ k.val = 2830 ∨ k.val = 2831 ∨ k.val = 2832 ∨ k.val = 2833 ∨ k.val = 2834 ∨ k.val = 2835 ∨ k.val = 2836 ∨ k.val = 2837 ∨ k.val = 2838 ∨ k.val = 2839 ∨ k.val = 2840 ∨ k.val = 2841 ∨ k.val = 2842 ∨ k.val = 2843 ∨ k.val = 2844 ∨ k.val = 2845 ∨ k.val = 2846 ∨ k.val = 2847 := by omega
  rcases heq with h2816 | h2817 | h2818 | h2819 | h2820 | h2821 | h2822 | h2823 | h2824 | h2825 | h2826 | h2827 | h2828 | h2829 | h2830 | h2831 | h2832 | h2833 | h2834 | h2835 | h2836 | h2837 | h2838 | h2839 | h2840 | h2841 | h2842 | h2843 | h2844 | h2845 | h2846 | h2847
  · have he : k = (2816 : Fin 2886) := Fin.ext h2816
    subst k
    rw [keyMomentRowsAt2816]
    exact keyMoment2816 B hB
  · have he : k = (2817 : Fin 2886) := Fin.ext h2817
    subst k
    rw [keyMomentRowsAt2817]
    exact keyMoment2817 B hB
  · have he : k = (2818 : Fin 2886) := Fin.ext h2818
    subst k
    rw [keyMomentRowsAt2818]
    exact keyMoment2818 B hB
  · have he : k = (2819 : Fin 2886) := Fin.ext h2819
    subst k
    rw [keyMomentRowsAt2819]
    exact keyMoment2819 B hB
  · have he : k = (2820 : Fin 2886) := Fin.ext h2820
    subst k
    rw [keyMomentRowsAt2820]
    exact keyMoment2820 B hB
  · have he : k = (2821 : Fin 2886) := Fin.ext h2821
    subst k
    rw [keyMomentRowsAt2821]
    exact keyMoment2821 B hB
  · have he : k = (2822 : Fin 2886) := Fin.ext h2822
    subst k
    rw [keyMomentRowsAt2822]
    exact keyMoment2822 B hB
  · have he : k = (2823 : Fin 2886) := Fin.ext h2823
    subst k
    rw [keyMomentRowsAt2823]
    exact keyMoment2823 B hB
  · have he : k = (2824 : Fin 2886) := Fin.ext h2824
    subst k
    rw [keyMomentRowsAt2824]
    exact keyMoment2824 B hB
  · have he : k = (2825 : Fin 2886) := Fin.ext h2825
    subst k
    rw [keyMomentRowsAt2825]
    exact keyMoment2825 B hB
  · have he : k = (2826 : Fin 2886) := Fin.ext h2826
    subst k
    rw [keyMomentRowsAt2826]
    exact keyMoment2826 B hB
  · have he : k = (2827 : Fin 2886) := Fin.ext h2827
    subst k
    rw [keyMomentRowsAt2827]
    exact keyMoment2827 B hB
  · have he : k = (2828 : Fin 2886) := Fin.ext h2828
    subst k
    rw [keyMomentRowsAt2828]
    exact keyMoment2828 B hB
  · have he : k = (2829 : Fin 2886) := Fin.ext h2829
    subst k
    rw [keyMomentRowsAt2829]
    exact keyMoment2829 B hB
  · have he : k = (2830 : Fin 2886) := Fin.ext h2830
    subst k
    rw [keyMomentRowsAt2830]
    exact keyMoment2830 B hB
  · have he : k = (2831 : Fin 2886) := Fin.ext h2831
    subst k
    rw [keyMomentRowsAt2831]
    exact keyMoment2831 B hB
  · have he : k = (2832 : Fin 2886) := Fin.ext h2832
    subst k
    rw [keyMomentRowsAt2832]
    exact keyMoment2832 B hB
  · have he : k = (2833 : Fin 2886) := Fin.ext h2833
    subst k
    rw [keyMomentRowsAt2833]
    exact keyMoment2833 B hB
  · have he : k = (2834 : Fin 2886) := Fin.ext h2834
    subst k
    rw [keyMomentRowsAt2834]
    exact keyMoment2834 B hB
  · have he : k = (2835 : Fin 2886) := Fin.ext h2835
    subst k
    rw [keyMomentRowsAt2835]
    exact keyMoment2835 B hB
  · have he : k = (2836 : Fin 2886) := Fin.ext h2836
    subst k
    rw [keyMomentRowsAt2836]
    exact keyMoment2836 B hB
  · have he : k = (2837 : Fin 2886) := Fin.ext h2837
    subst k
    rw [keyMomentRowsAt2837]
    exact keyMoment2837 B hB
  · have he : k = (2838 : Fin 2886) := Fin.ext h2838
    subst k
    rw [keyMomentRowsAt2838]
    exact keyMoment2838 B hB
  · have he : k = (2839 : Fin 2886) := Fin.ext h2839
    subst k
    rw [keyMomentRowsAt2839]
    exact keyMoment2839 B hB
  · have he : k = (2840 : Fin 2886) := Fin.ext h2840
    subst k
    rw [keyMomentRowsAt2840]
    exact keyMoment2840 B hB
  · have he : k = (2841 : Fin 2886) := Fin.ext h2841
    subst k
    rw [keyMomentRowsAt2841]
    exact keyMoment2841 B hB
  · have he : k = (2842 : Fin 2886) := Fin.ext h2842
    subst k
    rw [keyMomentRowsAt2842]
    exact keyMoment2842 B hB
  · have he : k = (2843 : Fin 2886) := Fin.ext h2843
    subst k
    rw [keyMomentRowsAt2843]
    exact keyMoment2843 B hB
  · have he : k = (2844 : Fin 2886) := Fin.ext h2844
    subst k
    rw [keyMomentRowsAt2844]
    exact keyMoment2844 B hB
  · have he : k = (2845 : Fin 2886) := Fin.ext h2845
    subst k
    rw [keyMomentRowsAt2845]
    exact keyMoment2845 B hB
  · have he : k = (2846 : Fin 2886) := Fin.ext h2846
    subst k
    rw [keyMomentRowsAt2846]
    exact keyMoment2846 B hB
  · have he : k = (2847 : Fin 2886) := Fin.ext h2847
    subst k
    rw [keyMomentRowsAt2847]
    exact keyMoment2847 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
