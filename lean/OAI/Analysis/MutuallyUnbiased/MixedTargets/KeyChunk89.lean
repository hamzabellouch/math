import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound89
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2848 : keyMomentRows (2848 : Fin 2886) =
    keyMomentRow2848 := by decide +kernel

theorem keyMomentRowsAt2849 : keyMomentRows (2849 : Fin 2886) =
    keyMomentRow2849 := by decide +kernel

theorem keyMomentRowsAt2850 : keyMomentRows (2850 : Fin 2886) =
    keyMomentRow2850 := by decide +kernel

theorem keyMomentRowsAt2851 : keyMomentRows (2851 : Fin 2886) =
    keyMomentRow2851 := by decide +kernel

theorem keyMomentRowsAt2852 : keyMomentRows (2852 : Fin 2886) =
    keyMomentRow2852 := by decide +kernel

theorem keyMomentRowsAt2853 : keyMomentRows (2853 : Fin 2886) =
    keyMomentRow2853 := by decide +kernel

theorem keyMomentRowsAt2854 : keyMomentRows (2854 : Fin 2886) =
    keyMomentRow2854 := by decide +kernel

theorem keyMomentRowsAt2855 : keyMomentRows (2855 : Fin 2886) =
    keyMomentRow2855 := by decide +kernel

theorem keyMomentRowsAt2856 : keyMomentRows (2856 : Fin 2886) =
    keyMomentRow2856 := by decide +kernel

theorem keyMomentRowsAt2857 : keyMomentRows (2857 : Fin 2886) =
    keyMomentRow2857 := by decide +kernel

theorem keyMomentRowsAt2858 : keyMomentRows (2858 : Fin 2886) =
    keyMomentRow2858 := by decide +kernel

theorem keyMomentRowsAt2859 : keyMomentRows (2859 : Fin 2886) =
    keyMomentRow2859 := by decide +kernel

theorem keyMomentRowsAt2860 : keyMomentRows (2860 : Fin 2886) =
    keyMomentRow2860 := by decide +kernel

theorem keyMomentRowsAt2861 : keyMomentRows (2861 : Fin 2886) =
    keyMomentRow2861 := by decide +kernel

theorem keyMomentRowsAt2862 : keyMomentRows (2862 : Fin 2886) =
    keyMomentRow2862 := by decide +kernel

theorem keyMomentRowsAt2863 : keyMomentRows (2863 : Fin 2886) =
    keyMomentRow2863 := by decide +kernel

theorem keyMomentRowsAt2864 : keyMomentRows (2864 : Fin 2886) =
    keyMomentRow2864 := by decide +kernel

theorem keyMomentRowsAt2865 : keyMomentRows (2865 : Fin 2886) =
    keyMomentRow2865 := by decide +kernel

theorem keyMomentRowsAt2866 : keyMomentRows (2866 : Fin 2886) =
    keyMomentRow2866 := by decide +kernel

theorem keyMomentRowsAt2867 : keyMomentRows (2867 : Fin 2886) =
    keyMomentRow2867 := by decide +kernel

theorem keyMomentRowsAt2868 : keyMomentRows (2868 : Fin 2886) =
    keyMomentRow2868 := by decide +kernel

theorem keyMomentRowsAt2869 : keyMomentRows (2869 : Fin 2886) =
    keyMomentRow2869 := by decide +kernel

theorem keyMomentRowsAt2870 : keyMomentRows (2870 : Fin 2886) =
    keyMomentRow2870 := by decide +kernel

theorem keyMomentRowsAt2871 : keyMomentRows (2871 : Fin 2886) =
    keyMomentRow2871 := by decide +kernel

theorem keyMomentRowsAt2872 : keyMomentRows (2872 : Fin 2886) =
    keyMomentRow2872 := by decide +kernel

theorem keyMomentRowsAt2873 : keyMomentRows (2873 : Fin 2886) =
    keyMomentRow2873 := by decide +kernel

theorem keyMomentRowsAt2874 : keyMomentRows (2874 : Fin 2886) =
    keyMomentRow2874 := by decide +kernel

theorem keyMomentRowsAt2875 : keyMomentRows (2875 : Fin 2886) =
    keyMomentRow2875 := by decide +kernel

theorem keyMomentRowsAt2876 : keyMomentRows (2876 : Fin 2886) =
    keyMomentRow2876 := by decide +kernel

theorem keyMomentRowsAt2877 : keyMomentRows (2877 : Fin 2886) =
    keyMomentRow2877 := by decide +kernel

theorem keyMomentRowsAt2878 : keyMomentRows (2878 : Fin 2886) =
    keyMomentRow2878 := by decide +kernel

theorem keyMomentRowsAt2879 : keyMomentRows (2879 : Fin 2886) =
    keyMomentRow2879 := by decide +kernel

theorem keyMomentChunkSound89 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 89) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2848 ∨ k.val = 2849 ∨ k.val = 2850 ∨ k.val = 2851 ∨ k.val = 2852 ∨ k.val = 2853 ∨ k.val = 2854 ∨ k.val = 2855 ∨ k.val = 2856 ∨ k.val = 2857 ∨ k.val = 2858 ∨ k.val = 2859 ∨ k.val = 2860 ∨ k.val = 2861 ∨ k.val = 2862 ∨ k.val = 2863 ∨ k.val = 2864 ∨ k.val = 2865 ∨ k.val = 2866 ∨ k.val = 2867 ∨ k.val = 2868 ∨ k.val = 2869 ∨ k.val = 2870 ∨ k.val = 2871 ∨ k.val = 2872 ∨ k.val = 2873 ∨ k.val = 2874 ∨ k.val = 2875 ∨ k.val = 2876 ∨ k.val = 2877 ∨ k.val = 2878 ∨ k.val = 2879 := by omega
  rcases heq with h2848 | h2849 | h2850 | h2851 | h2852 | h2853 | h2854 | h2855 | h2856 | h2857 | h2858 | h2859 | h2860 | h2861 | h2862 | h2863 | h2864 | h2865 | h2866 | h2867 | h2868 | h2869 | h2870 | h2871 | h2872 | h2873 | h2874 | h2875 | h2876 | h2877 | h2878 | h2879
  · have he : k = (2848 : Fin 2886) := Fin.ext h2848
    subst k
    rw [keyMomentRowsAt2848]
    exact keyMoment2848 B hB
  · have he : k = (2849 : Fin 2886) := Fin.ext h2849
    subst k
    rw [keyMomentRowsAt2849]
    exact keyMoment2849 B hB
  · have he : k = (2850 : Fin 2886) := Fin.ext h2850
    subst k
    rw [keyMomentRowsAt2850]
    exact keyMoment2850 B hB
  · have he : k = (2851 : Fin 2886) := Fin.ext h2851
    subst k
    rw [keyMomentRowsAt2851]
    exact keyMoment2851 B hB
  · have he : k = (2852 : Fin 2886) := Fin.ext h2852
    subst k
    rw [keyMomentRowsAt2852]
    exact keyMoment2852 B hB
  · have he : k = (2853 : Fin 2886) := Fin.ext h2853
    subst k
    rw [keyMomentRowsAt2853]
    exact keyMoment2853 B hB
  · have he : k = (2854 : Fin 2886) := Fin.ext h2854
    subst k
    rw [keyMomentRowsAt2854]
    exact keyMoment2854 B hB
  · have he : k = (2855 : Fin 2886) := Fin.ext h2855
    subst k
    rw [keyMomentRowsAt2855]
    exact keyMoment2855 B hB
  · have he : k = (2856 : Fin 2886) := Fin.ext h2856
    subst k
    rw [keyMomentRowsAt2856]
    exact keyMoment2856 B hB
  · have he : k = (2857 : Fin 2886) := Fin.ext h2857
    subst k
    rw [keyMomentRowsAt2857]
    exact keyMoment2857 B hB
  · have he : k = (2858 : Fin 2886) := Fin.ext h2858
    subst k
    rw [keyMomentRowsAt2858]
    exact keyMoment2858 B hB
  · have he : k = (2859 : Fin 2886) := Fin.ext h2859
    subst k
    rw [keyMomentRowsAt2859]
    exact keyMoment2859 B hB
  · have he : k = (2860 : Fin 2886) := Fin.ext h2860
    subst k
    rw [keyMomentRowsAt2860]
    exact keyMoment2860 B hB
  · have he : k = (2861 : Fin 2886) := Fin.ext h2861
    subst k
    rw [keyMomentRowsAt2861]
    exact keyMoment2861 B hB
  · have he : k = (2862 : Fin 2886) := Fin.ext h2862
    subst k
    rw [keyMomentRowsAt2862]
    exact keyMoment2862 B hB
  · have he : k = (2863 : Fin 2886) := Fin.ext h2863
    subst k
    rw [keyMomentRowsAt2863]
    exact keyMoment2863 B hB
  · have he : k = (2864 : Fin 2886) := Fin.ext h2864
    subst k
    rw [keyMomentRowsAt2864]
    exact keyMoment2864 B hB
  · have he : k = (2865 : Fin 2886) := Fin.ext h2865
    subst k
    rw [keyMomentRowsAt2865]
    exact keyMoment2865 B hB
  · have he : k = (2866 : Fin 2886) := Fin.ext h2866
    subst k
    rw [keyMomentRowsAt2866]
    exact keyMoment2866 B hB
  · have he : k = (2867 : Fin 2886) := Fin.ext h2867
    subst k
    rw [keyMomentRowsAt2867]
    exact keyMoment2867 B hB
  · have he : k = (2868 : Fin 2886) := Fin.ext h2868
    subst k
    rw [keyMomentRowsAt2868]
    exact keyMoment2868 B hB
  · have he : k = (2869 : Fin 2886) := Fin.ext h2869
    subst k
    rw [keyMomentRowsAt2869]
    exact keyMoment2869 B hB
  · have he : k = (2870 : Fin 2886) := Fin.ext h2870
    subst k
    rw [keyMomentRowsAt2870]
    exact keyMoment2870 B hB
  · have he : k = (2871 : Fin 2886) := Fin.ext h2871
    subst k
    rw [keyMomentRowsAt2871]
    exact keyMoment2871 B hB
  · have he : k = (2872 : Fin 2886) := Fin.ext h2872
    subst k
    rw [keyMomentRowsAt2872]
    exact keyMoment2872 B hB
  · have he : k = (2873 : Fin 2886) := Fin.ext h2873
    subst k
    rw [keyMomentRowsAt2873]
    exact keyMoment2873 B hB
  · have he : k = (2874 : Fin 2886) := Fin.ext h2874
    subst k
    rw [keyMomentRowsAt2874]
    exact keyMoment2874 B hB
  · have he : k = (2875 : Fin 2886) := Fin.ext h2875
    subst k
    rw [keyMomentRowsAt2875]
    exact keyMoment2875 B hB
  · have he : k = (2876 : Fin 2886) := Fin.ext h2876
    subst k
    rw [keyMomentRowsAt2876]
    exact keyMoment2876 B hB
  · have he : k = (2877 : Fin 2886) := Fin.ext h2877
    subst k
    rw [keyMomentRowsAt2877]
    exact keyMoment2877 B hB
  · have he : k = (2878 : Fin 2886) := Fin.ext h2878
    subst k
    rw [keyMomentRowsAt2878]
    exact keyMoment2878 B hB
  · have he : k = (2879 : Fin 2886) := Fin.ext h2879
    subst k
    rw [keyMomentRowsAt2879]
    exact keyMoment2879 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
