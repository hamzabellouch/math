import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound27
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt864 : keyMomentRows (864 : Fin 2886) =
    keyMomentRow864 := by decide +kernel

theorem keyMomentRowsAt865 : keyMomentRows (865 : Fin 2886) =
    keyMomentRow865 := by decide +kernel

theorem keyMomentRowsAt866 : keyMomentRows (866 : Fin 2886) =
    keyMomentRow866 := by decide +kernel

theorem keyMomentRowsAt867 : keyMomentRows (867 : Fin 2886) =
    keyMomentRow867 := by decide +kernel

theorem keyMomentRowsAt868 : keyMomentRows (868 : Fin 2886) =
    keyMomentRow868 := by decide +kernel

theorem keyMomentRowsAt869 : keyMomentRows (869 : Fin 2886) =
    keyMomentRow869 := by decide +kernel

theorem keyMomentRowsAt870 : keyMomentRows (870 : Fin 2886) =
    keyMomentRow870 := by decide +kernel

theorem keyMomentRowsAt871 : keyMomentRows (871 : Fin 2886) =
    keyMomentRow871 := by decide +kernel

theorem keyMomentRowsAt872 : keyMomentRows (872 : Fin 2886) =
    keyMomentRow872 := by decide +kernel

theorem keyMomentRowsAt873 : keyMomentRows (873 : Fin 2886) =
    keyMomentRow873 := by decide +kernel

theorem keyMomentRowsAt874 : keyMomentRows (874 : Fin 2886) =
    keyMomentRow874 := by decide +kernel

theorem keyMomentRowsAt875 : keyMomentRows (875 : Fin 2886) =
    keyMomentRow875 := by decide +kernel

theorem keyMomentRowsAt876 : keyMomentRows (876 : Fin 2886) =
    keyMomentRow876 := by decide +kernel

theorem keyMomentRowsAt877 : keyMomentRows (877 : Fin 2886) =
    keyMomentRow877 := by decide +kernel

theorem keyMomentRowsAt878 : keyMomentRows (878 : Fin 2886) =
    keyMomentRow878 := by decide +kernel

theorem keyMomentRowsAt879 : keyMomentRows (879 : Fin 2886) =
    keyMomentRow879 := by decide +kernel

theorem keyMomentRowsAt880 : keyMomentRows (880 : Fin 2886) =
    keyMomentRow880 := by decide +kernel

theorem keyMomentRowsAt881 : keyMomentRows (881 : Fin 2886) =
    keyMomentRow881 := by decide +kernel

theorem keyMomentRowsAt882 : keyMomentRows (882 : Fin 2886) =
    keyMomentRow882 := by decide +kernel

theorem keyMomentRowsAt883 : keyMomentRows (883 : Fin 2886) =
    keyMomentRow883 := by decide +kernel

theorem keyMomentRowsAt884 : keyMomentRows (884 : Fin 2886) =
    keyMomentRow884 := by decide +kernel

theorem keyMomentRowsAt885 : keyMomentRows (885 : Fin 2886) =
    keyMomentRow885 := by decide +kernel

theorem keyMomentRowsAt886 : keyMomentRows (886 : Fin 2886) =
    keyMomentRow886 := by decide +kernel

theorem keyMomentRowsAt887 : keyMomentRows (887 : Fin 2886) =
    keyMomentRow887 := by decide +kernel

theorem keyMomentRowsAt888 : keyMomentRows (888 : Fin 2886) =
    keyMomentRow888 := by decide +kernel

theorem keyMomentRowsAt889 : keyMomentRows (889 : Fin 2886) =
    keyMomentRow889 := by decide +kernel

theorem keyMomentRowsAt890 : keyMomentRows (890 : Fin 2886) =
    keyMomentRow890 := by decide +kernel

theorem keyMomentRowsAt891 : keyMomentRows (891 : Fin 2886) =
    keyMomentRow891 := by decide +kernel

theorem keyMomentRowsAt892 : keyMomentRows (892 : Fin 2886) =
    keyMomentRow892 := by decide +kernel

theorem keyMomentRowsAt893 : keyMomentRows (893 : Fin 2886) =
    keyMomentRow893 := by decide +kernel

theorem keyMomentRowsAt894 : keyMomentRows (894 : Fin 2886) =
    keyMomentRow894 := by decide +kernel

theorem keyMomentRowsAt895 : keyMomentRows (895 : Fin 2886) =
    keyMomentRow895 := by decide +kernel

theorem keyMomentChunkSound27 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 27) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 864 ∨ k.val = 865 ∨ k.val = 866 ∨ k.val = 867 ∨ k.val = 868 ∨ k.val = 869 ∨ k.val = 870 ∨ k.val = 871 ∨ k.val = 872 ∨ k.val = 873 ∨ k.val = 874 ∨ k.val = 875 ∨ k.val = 876 ∨ k.val = 877 ∨ k.val = 878 ∨ k.val = 879 ∨ k.val = 880 ∨ k.val = 881 ∨ k.val = 882 ∨ k.val = 883 ∨ k.val = 884 ∨ k.val = 885 ∨ k.val = 886 ∨ k.val = 887 ∨ k.val = 888 ∨ k.val = 889 ∨ k.val = 890 ∨ k.val = 891 ∨ k.val = 892 ∨ k.val = 893 ∨ k.val = 894 ∨ k.val = 895 := by omega
  rcases heq with h864 | h865 | h866 | h867 | h868 | h869 | h870 | h871 | h872 | h873 | h874 | h875 | h876 | h877 | h878 | h879 | h880 | h881 | h882 | h883 | h884 | h885 | h886 | h887 | h888 | h889 | h890 | h891 | h892 | h893 | h894 | h895
  · have he : k = (864 : Fin 2886) := Fin.ext h864
    subst k
    rw [keyMomentRowsAt864]
    exact keyMoment864 B hB
  · have he : k = (865 : Fin 2886) := Fin.ext h865
    subst k
    rw [keyMomentRowsAt865]
    exact keyMoment865 B hB
  · have he : k = (866 : Fin 2886) := Fin.ext h866
    subst k
    rw [keyMomentRowsAt866]
    exact keyMoment866 B hB
  · have he : k = (867 : Fin 2886) := Fin.ext h867
    subst k
    rw [keyMomentRowsAt867]
    exact keyMoment867 B hB
  · have he : k = (868 : Fin 2886) := Fin.ext h868
    subst k
    rw [keyMomentRowsAt868]
    exact keyMoment868 B hB
  · have he : k = (869 : Fin 2886) := Fin.ext h869
    subst k
    rw [keyMomentRowsAt869]
    exact keyMoment869 B hB
  · have he : k = (870 : Fin 2886) := Fin.ext h870
    subst k
    rw [keyMomentRowsAt870]
    exact keyMoment870 B hB
  · have he : k = (871 : Fin 2886) := Fin.ext h871
    subst k
    rw [keyMomentRowsAt871]
    exact keyMoment871 B hB
  · have he : k = (872 : Fin 2886) := Fin.ext h872
    subst k
    rw [keyMomentRowsAt872]
    exact keyMoment872 B hB
  · have he : k = (873 : Fin 2886) := Fin.ext h873
    subst k
    rw [keyMomentRowsAt873]
    exact keyMoment873 B hB
  · have he : k = (874 : Fin 2886) := Fin.ext h874
    subst k
    rw [keyMomentRowsAt874]
    exact keyMoment874 B hB
  · have he : k = (875 : Fin 2886) := Fin.ext h875
    subst k
    rw [keyMomentRowsAt875]
    exact keyMoment875 B hB
  · have he : k = (876 : Fin 2886) := Fin.ext h876
    subst k
    rw [keyMomentRowsAt876]
    exact keyMoment876 B hB
  · have he : k = (877 : Fin 2886) := Fin.ext h877
    subst k
    rw [keyMomentRowsAt877]
    exact keyMoment877 B hB
  · have he : k = (878 : Fin 2886) := Fin.ext h878
    subst k
    rw [keyMomentRowsAt878]
    exact keyMoment878 B hB
  · have he : k = (879 : Fin 2886) := Fin.ext h879
    subst k
    rw [keyMomentRowsAt879]
    exact keyMoment879 B hB
  · have he : k = (880 : Fin 2886) := Fin.ext h880
    subst k
    rw [keyMomentRowsAt880]
    exact keyMoment880 B hB
  · have he : k = (881 : Fin 2886) := Fin.ext h881
    subst k
    rw [keyMomentRowsAt881]
    exact keyMoment881 B hB
  · have he : k = (882 : Fin 2886) := Fin.ext h882
    subst k
    rw [keyMomentRowsAt882]
    exact keyMoment882 B hB
  · have he : k = (883 : Fin 2886) := Fin.ext h883
    subst k
    rw [keyMomentRowsAt883]
    exact keyMoment883 B hB
  · have he : k = (884 : Fin 2886) := Fin.ext h884
    subst k
    rw [keyMomentRowsAt884]
    exact keyMoment884 B hB
  · have he : k = (885 : Fin 2886) := Fin.ext h885
    subst k
    rw [keyMomentRowsAt885]
    exact keyMoment885 B hB
  · have he : k = (886 : Fin 2886) := Fin.ext h886
    subst k
    rw [keyMomentRowsAt886]
    exact keyMoment886 B hB
  · have he : k = (887 : Fin 2886) := Fin.ext h887
    subst k
    rw [keyMomentRowsAt887]
    exact keyMoment887 B hB
  · have he : k = (888 : Fin 2886) := Fin.ext h888
    subst k
    rw [keyMomentRowsAt888]
    exact keyMoment888 B hB
  · have he : k = (889 : Fin 2886) := Fin.ext h889
    subst k
    rw [keyMomentRowsAt889]
    exact keyMoment889 B hB
  · have he : k = (890 : Fin 2886) := Fin.ext h890
    subst k
    rw [keyMomentRowsAt890]
    exact keyMoment890 B hB
  · have he : k = (891 : Fin 2886) := Fin.ext h891
    subst k
    rw [keyMomentRowsAt891]
    exact keyMoment891 B hB
  · have he : k = (892 : Fin 2886) := Fin.ext h892
    subst k
    rw [keyMomentRowsAt892]
    exact keyMoment892 B hB
  · have he : k = (893 : Fin 2886) := Fin.ext h893
    subst k
    rw [keyMomentRowsAt893]
    exact keyMoment893 B hB
  · have he : k = (894 : Fin 2886) := Fin.ext h894
    subst k
    rw [keyMomentRowsAt894]
    exact keyMoment894 B hB
  · have he : k = (895 : Fin 2886) := Fin.ext h895
    subst k
    rw [keyMomentRowsAt895]
    exact keyMoment895 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
