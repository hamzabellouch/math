import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound32
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1024 : keyMomentRows (1024 : Fin 2886) =
    keyMomentRow1024 := by decide +kernel

theorem keyMomentRowsAt1025 : keyMomentRows (1025 : Fin 2886) =
    keyMomentRow1025 := by decide +kernel

theorem keyMomentRowsAt1026 : keyMomentRows (1026 : Fin 2886) =
    keyMomentRow1026 := by decide +kernel

theorem keyMomentRowsAt1027 : keyMomentRows (1027 : Fin 2886) =
    keyMomentRow1027 := by decide +kernel

theorem keyMomentRowsAt1028 : keyMomentRows (1028 : Fin 2886) =
    keyMomentRow1028 := by decide +kernel

theorem keyMomentRowsAt1029 : keyMomentRows (1029 : Fin 2886) =
    keyMomentRow1029 := by decide +kernel

theorem keyMomentRowsAt1030 : keyMomentRows (1030 : Fin 2886) =
    keyMomentRow1030 := by decide +kernel

theorem keyMomentRowsAt1031 : keyMomentRows (1031 : Fin 2886) =
    keyMomentRow1031 := by decide +kernel

theorem keyMomentRowsAt1032 : keyMomentRows (1032 : Fin 2886) =
    keyMomentRow1032 := by decide +kernel

theorem keyMomentRowsAt1033 : keyMomentRows (1033 : Fin 2886) =
    keyMomentRow1033 := by decide +kernel

theorem keyMomentRowsAt1034 : keyMomentRows (1034 : Fin 2886) =
    keyMomentRow1034 := by decide +kernel

theorem keyMomentRowsAt1035 : keyMomentRows (1035 : Fin 2886) =
    keyMomentRow1035 := by decide +kernel

theorem keyMomentRowsAt1036 : keyMomentRows (1036 : Fin 2886) =
    keyMomentRow1036 := by decide +kernel

theorem keyMomentRowsAt1037 : keyMomentRows (1037 : Fin 2886) =
    keyMomentRow1037 := by decide +kernel

theorem keyMomentRowsAt1038 : keyMomentRows (1038 : Fin 2886) =
    keyMomentRow1038 := by decide +kernel

theorem keyMomentRowsAt1039 : keyMomentRows (1039 : Fin 2886) =
    keyMomentRow1039 := by decide +kernel

theorem keyMomentRowsAt1040 : keyMomentRows (1040 : Fin 2886) =
    keyMomentRow1040 := by decide +kernel

theorem keyMomentRowsAt1041 : keyMomentRows (1041 : Fin 2886) =
    keyMomentRow1041 := by decide +kernel

theorem keyMomentRowsAt1042 : keyMomentRows (1042 : Fin 2886) =
    keyMomentRow1042 := by decide +kernel

theorem keyMomentRowsAt1043 : keyMomentRows (1043 : Fin 2886) =
    keyMomentRow1043 := by decide +kernel

theorem keyMomentRowsAt1044 : keyMomentRows (1044 : Fin 2886) =
    keyMomentRow1044 := by decide +kernel

theorem keyMomentRowsAt1045 : keyMomentRows (1045 : Fin 2886) =
    keyMomentRow1045 := by decide +kernel

theorem keyMomentRowsAt1046 : keyMomentRows (1046 : Fin 2886) =
    keyMomentRow1046 := by decide +kernel

theorem keyMomentRowsAt1047 : keyMomentRows (1047 : Fin 2886) =
    keyMomentRow1047 := by decide +kernel

theorem keyMomentRowsAt1048 : keyMomentRows (1048 : Fin 2886) =
    keyMomentRow1048 := by decide +kernel

theorem keyMomentRowsAt1049 : keyMomentRows (1049 : Fin 2886) =
    keyMomentRow1049 := by decide +kernel

theorem keyMomentRowsAt1050 : keyMomentRows (1050 : Fin 2886) =
    keyMomentRow1050 := by decide +kernel

theorem keyMomentRowsAt1051 : keyMomentRows (1051 : Fin 2886) =
    keyMomentRow1051 := by decide +kernel

theorem keyMomentRowsAt1052 : keyMomentRows (1052 : Fin 2886) =
    keyMomentRow1052 := by decide +kernel

theorem keyMomentRowsAt1053 : keyMomentRows (1053 : Fin 2886) =
    keyMomentRow1053 := by decide +kernel

theorem keyMomentRowsAt1054 : keyMomentRows (1054 : Fin 2886) =
    keyMomentRow1054 := by decide +kernel

theorem keyMomentRowsAt1055 : keyMomentRows (1055 : Fin 2886) =
    keyMomentRow1055 := by decide +kernel

theorem keyMomentChunkSound32 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 32) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1024 ∨ k.val = 1025 ∨ k.val = 1026 ∨ k.val = 1027 ∨ k.val = 1028 ∨ k.val = 1029 ∨ k.val = 1030 ∨ k.val = 1031 ∨ k.val = 1032 ∨ k.val = 1033 ∨ k.val = 1034 ∨ k.val = 1035 ∨ k.val = 1036 ∨ k.val = 1037 ∨ k.val = 1038 ∨ k.val = 1039 ∨ k.val = 1040 ∨ k.val = 1041 ∨ k.val = 1042 ∨ k.val = 1043 ∨ k.val = 1044 ∨ k.val = 1045 ∨ k.val = 1046 ∨ k.val = 1047 ∨ k.val = 1048 ∨ k.val = 1049 ∨ k.val = 1050 ∨ k.val = 1051 ∨ k.val = 1052 ∨ k.val = 1053 ∨ k.val = 1054 ∨ k.val = 1055 := by omega
  rcases heq with h1024 | h1025 | h1026 | h1027 | h1028 | h1029 | h1030 | h1031 | h1032 | h1033 | h1034 | h1035 | h1036 | h1037 | h1038 | h1039 | h1040 | h1041 | h1042 | h1043 | h1044 | h1045 | h1046 | h1047 | h1048 | h1049 | h1050 | h1051 | h1052 | h1053 | h1054 | h1055
  · have he : k = (1024 : Fin 2886) := Fin.ext h1024
    subst k
    rw [keyMomentRowsAt1024]
    exact keyMoment1024 B hB
  · have he : k = (1025 : Fin 2886) := Fin.ext h1025
    subst k
    rw [keyMomentRowsAt1025]
    exact keyMoment1025 B hB
  · have he : k = (1026 : Fin 2886) := Fin.ext h1026
    subst k
    rw [keyMomentRowsAt1026]
    exact keyMoment1026 B hB
  · have he : k = (1027 : Fin 2886) := Fin.ext h1027
    subst k
    rw [keyMomentRowsAt1027]
    exact keyMoment1027 B hB
  · have he : k = (1028 : Fin 2886) := Fin.ext h1028
    subst k
    rw [keyMomentRowsAt1028]
    exact keyMoment1028 B hB
  · have he : k = (1029 : Fin 2886) := Fin.ext h1029
    subst k
    rw [keyMomentRowsAt1029]
    exact keyMoment1029 B hB
  · have he : k = (1030 : Fin 2886) := Fin.ext h1030
    subst k
    rw [keyMomentRowsAt1030]
    exact keyMoment1030 B hB
  · have he : k = (1031 : Fin 2886) := Fin.ext h1031
    subst k
    rw [keyMomentRowsAt1031]
    exact keyMoment1031 B hB
  · have he : k = (1032 : Fin 2886) := Fin.ext h1032
    subst k
    rw [keyMomentRowsAt1032]
    exact keyMoment1032 B hB
  · have he : k = (1033 : Fin 2886) := Fin.ext h1033
    subst k
    rw [keyMomentRowsAt1033]
    exact keyMoment1033 B hB
  · have he : k = (1034 : Fin 2886) := Fin.ext h1034
    subst k
    rw [keyMomentRowsAt1034]
    exact keyMoment1034 B hB
  · have he : k = (1035 : Fin 2886) := Fin.ext h1035
    subst k
    rw [keyMomentRowsAt1035]
    exact keyMoment1035 B hB
  · have he : k = (1036 : Fin 2886) := Fin.ext h1036
    subst k
    rw [keyMomentRowsAt1036]
    exact keyMoment1036 B hB
  · have he : k = (1037 : Fin 2886) := Fin.ext h1037
    subst k
    rw [keyMomentRowsAt1037]
    exact keyMoment1037 B hB
  · have he : k = (1038 : Fin 2886) := Fin.ext h1038
    subst k
    rw [keyMomentRowsAt1038]
    exact keyMoment1038 B hB
  · have he : k = (1039 : Fin 2886) := Fin.ext h1039
    subst k
    rw [keyMomentRowsAt1039]
    exact keyMoment1039 B hB
  · have he : k = (1040 : Fin 2886) := Fin.ext h1040
    subst k
    rw [keyMomentRowsAt1040]
    exact keyMoment1040 B hB
  · have he : k = (1041 : Fin 2886) := Fin.ext h1041
    subst k
    rw [keyMomentRowsAt1041]
    exact keyMoment1041 B hB
  · have he : k = (1042 : Fin 2886) := Fin.ext h1042
    subst k
    rw [keyMomentRowsAt1042]
    exact keyMoment1042 B hB
  · have he : k = (1043 : Fin 2886) := Fin.ext h1043
    subst k
    rw [keyMomentRowsAt1043]
    exact keyMoment1043 B hB
  · have he : k = (1044 : Fin 2886) := Fin.ext h1044
    subst k
    rw [keyMomentRowsAt1044]
    exact keyMoment1044 B hB
  · have he : k = (1045 : Fin 2886) := Fin.ext h1045
    subst k
    rw [keyMomentRowsAt1045]
    exact keyMoment1045 B hB
  · have he : k = (1046 : Fin 2886) := Fin.ext h1046
    subst k
    rw [keyMomentRowsAt1046]
    exact keyMoment1046 B hB
  · have he : k = (1047 : Fin 2886) := Fin.ext h1047
    subst k
    rw [keyMomentRowsAt1047]
    exact keyMoment1047 B hB
  · have he : k = (1048 : Fin 2886) := Fin.ext h1048
    subst k
    rw [keyMomentRowsAt1048]
    exact keyMoment1048 B hB
  · have he : k = (1049 : Fin 2886) := Fin.ext h1049
    subst k
    rw [keyMomentRowsAt1049]
    exact keyMoment1049 B hB
  · have he : k = (1050 : Fin 2886) := Fin.ext h1050
    subst k
    rw [keyMomentRowsAt1050]
    exact keyMoment1050 B hB
  · have he : k = (1051 : Fin 2886) := Fin.ext h1051
    subst k
    rw [keyMomentRowsAt1051]
    exact keyMoment1051 B hB
  · have he : k = (1052 : Fin 2886) := Fin.ext h1052
    subst k
    rw [keyMomentRowsAt1052]
    exact keyMoment1052 B hB
  · have he : k = (1053 : Fin 2886) := Fin.ext h1053
    subst k
    rw [keyMomentRowsAt1053]
    exact keyMoment1053 B hB
  · have he : k = (1054 : Fin 2886) := Fin.ext h1054
    subst k
    rw [keyMomentRowsAt1054]
    exact keyMoment1054 B hB
  · have he : k = (1055 : Fin 2886) := Fin.ext h1055
    subst k
    rw [keyMomentRowsAt1055]
    exact keyMoment1055 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
