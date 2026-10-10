import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound33
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1056 : keyMomentRows (1056 : Fin 2886) =
    keyMomentRow1056 := by decide +kernel

theorem keyMomentRowsAt1057 : keyMomentRows (1057 : Fin 2886) =
    keyMomentRow1057 := by decide +kernel

theorem keyMomentRowsAt1058 : keyMomentRows (1058 : Fin 2886) =
    keyMomentRow1058 := by decide +kernel

theorem keyMomentRowsAt1059 : keyMomentRows (1059 : Fin 2886) =
    keyMomentRow1059 := by decide +kernel

theorem keyMomentRowsAt1060 : keyMomentRows (1060 : Fin 2886) =
    keyMomentRow1060 := by decide +kernel

theorem keyMomentRowsAt1061 : keyMomentRows (1061 : Fin 2886) =
    keyMomentRow1061 := by decide +kernel

theorem keyMomentRowsAt1062 : keyMomentRows (1062 : Fin 2886) =
    keyMomentRow1062 := by decide +kernel

theorem keyMomentRowsAt1063 : keyMomentRows (1063 : Fin 2886) =
    keyMomentRow1063 := by decide +kernel

theorem keyMomentRowsAt1064 : keyMomentRows (1064 : Fin 2886) =
    keyMomentRow1064 := by decide +kernel

theorem keyMomentRowsAt1065 : keyMomentRows (1065 : Fin 2886) =
    keyMomentRow1065 := by decide +kernel

theorem keyMomentRowsAt1066 : keyMomentRows (1066 : Fin 2886) =
    keyMomentRow1066 := by decide +kernel

theorem keyMomentRowsAt1067 : keyMomentRows (1067 : Fin 2886) =
    keyMomentRow1067 := by decide +kernel

theorem keyMomentRowsAt1068 : keyMomentRows (1068 : Fin 2886) =
    keyMomentRow1068 := by decide +kernel

theorem keyMomentRowsAt1069 : keyMomentRows (1069 : Fin 2886) =
    keyMomentRow1069 := by decide +kernel

theorem keyMomentRowsAt1070 : keyMomentRows (1070 : Fin 2886) =
    keyMomentRow1070 := by decide +kernel

theorem keyMomentRowsAt1071 : keyMomentRows (1071 : Fin 2886) =
    keyMomentRow1071 := by decide +kernel

theorem keyMomentRowsAt1072 : keyMomentRows (1072 : Fin 2886) =
    keyMomentRow1072 := by decide +kernel

theorem keyMomentRowsAt1073 : keyMomentRows (1073 : Fin 2886) =
    keyMomentRow1073 := by decide +kernel

theorem keyMomentRowsAt1074 : keyMomentRows (1074 : Fin 2886) =
    keyMomentRow1074 := by decide +kernel

theorem keyMomentRowsAt1075 : keyMomentRows (1075 : Fin 2886) =
    keyMomentRow1075 := by decide +kernel

theorem keyMomentRowsAt1076 : keyMomentRows (1076 : Fin 2886) =
    keyMomentRow1076 := by decide +kernel

theorem keyMomentRowsAt1077 : keyMomentRows (1077 : Fin 2886) =
    keyMomentRow1077 := by decide +kernel

theorem keyMomentRowsAt1078 : keyMomentRows (1078 : Fin 2886) =
    keyMomentRow1078 := by decide +kernel

theorem keyMomentRowsAt1079 : keyMomentRows (1079 : Fin 2886) =
    keyMomentRow1079 := by decide +kernel

theorem keyMomentRowsAt1080 : keyMomentRows (1080 : Fin 2886) =
    keyMomentRow1080 := by decide +kernel

theorem keyMomentRowsAt1081 : keyMomentRows (1081 : Fin 2886) =
    keyMomentRow1081 := by decide +kernel

theorem keyMomentRowsAt1082 : keyMomentRows (1082 : Fin 2886) =
    keyMomentRow1082 := by decide +kernel

theorem keyMomentRowsAt1083 : keyMomentRows (1083 : Fin 2886) =
    keyMomentRow1083 := by decide +kernel

theorem keyMomentRowsAt1084 : keyMomentRows (1084 : Fin 2886) =
    keyMomentRow1084 := by decide +kernel

theorem keyMomentRowsAt1085 : keyMomentRows (1085 : Fin 2886) =
    keyMomentRow1085 := by decide +kernel

theorem keyMomentRowsAt1086 : keyMomentRows (1086 : Fin 2886) =
    keyMomentRow1086 := by decide +kernel

theorem keyMomentRowsAt1087 : keyMomentRows (1087 : Fin 2886) =
    keyMomentRow1087 := by decide +kernel

theorem keyMomentChunkSound33 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 33) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1056 ∨ k.val = 1057 ∨ k.val = 1058 ∨ k.val = 1059 ∨ k.val = 1060 ∨ k.val = 1061 ∨ k.val = 1062 ∨ k.val = 1063 ∨ k.val = 1064 ∨ k.val = 1065 ∨ k.val = 1066 ∨ k.val = 1067 ∨ k.val = 1068 ∨ k.val = 1069 ∨ k.val = 1070 ∨ k.val = 1071 ∨ k.val = 1072 ∨ k.val = 1073 ∨ k.val = 1074 ∨ k.val = 1075 ∨ k.val = 1076 ∨ k.val = 1077 ∨ k.val = 1078 ∨ k.val = 1079 ∨ k.val = 1080 ∨ k.val = 1081 ∨ k.val = 1082 ∨ k.val = 1083 ∨ k.val = 1084 ∨ k.val = 1085 ∨ k.val = 1086 ∨ k.val = 1087 := by omega
  rcases heq with h1056 | h1057 | h1058 | h1059 | h1060 | h1061 | h1062 | h1063 | h1064 | h1065 | h1066 | h1067 | h1068 | h1069 | h1070 | h1071 | h1072 | h1073 | h1074 | h1075 | h1076 | h1077 | h1078 | h1079 | h1080 | h1081 | h1082 | h1083 | h1084 | h1085 | h1086 | h1087
  · have he : k = (1056 : Fin 2886) := Fin.ext h1056
    subst k
    rw [keyMomentRowsAt1056]
    exact keyMoment1056 B hB
  · have he : k = (1057 : Fin 2886) := Fin.ext h1057
    subst k
    rw [keyMomentRowsAt1057]
    exact keyMoment1057 B hB
  · have he : k = (1058 : Fin 2886) := Fin.ext h1058
    subst k
    rw [keyMomentRowsAt1058]
    exact keyMoment1058 B hB
  · have he : k = (1059 : Fin 2886) := Fin.ext h1059
    subst k
    rw [keyMomentRowsAt1059]
    exact keyMoment1059 B hB
  · have he : k = (1060 : Fin 2886) := Fin.ext h1060
    subst k
    rw [keyMomentRowsAt1060]
    exact keyMoment1060 B hB
  · have he : k = (1061 : Fin 2886) := Fin.ext h1061
    subst k
    rw [keyMomentRowsAt1061]
    exact keyMoment1061 B hB
  · have he : k = (1062 : Fin 2886) := Fin.ext h1062
    subst k
    rw [keyMomentRowsAt1062]
    exact keyMoment1062 B hB
  · have he : k = (1063 : Fin 2886) := Fin.ext h1063
    subst k
    rw [keyMomentRowsAt1063]
    exact keyMoment1063 B hB
  · have he : k = (1064 : Fin 2886) := Fin.ext h1064
    subst k
    rw [keyMomentRowsAt1064]
    exact keyMoment1064 B hB
  · have he : k = (1065 : Fin 2886) := Fin.ext h1065
    subst k
    rw [keyMomentRowsAt1065]
    exact keyMoment1065 B hB
  · have he : k = (1066 : Fin 2886) := Fin.ext h1066
    subst k
    rw [keyMomentRowsAt1066]
    exact keyMoment1066 B hB
  · have he : k = (1067 : Fin 2886) := Fin.ext h1067
    subst k
    rw [keyMomentRowsAt1067]
    exact keyMoment1067 B hB
  · have he : k = (1068 : Fin 2886) := Fin.ext h1068
    subst k
    rw [keyMomentRowsAt1068]
    exact keyMoment1068 B hB
  · have he : k = (1069 : Fin 2886) := Fin.ext h1069
    subst k
    rw [keyMomentRowsAt1069]
    exact keyMoment1069 B hB
  · have he : k = (1070 : Fin 2886) := Fin.ext h1070
    subst k
    rw [keyMomentRowsAt1070]
    exact keyMoment1070 B hB
  · have he : k = (1071 : Fin 2886) := Fin.ext h1071
    subst k
    rw [keyMomentRowsAt1071]
    exact keyMoment1071 B hB
  · have he : k = (1072 : Fin 2886) := Fin.ext h1072
    subst k
    rw [keyMomentRowsAt1072]
    exact keyMoment1072 B hB
  · have he : k = (1073 : Fin 2886) := Fin.ext h1073
    subst k
    rw [keyMomentRowsAt1073]
    exact keyMoment1073 B hB
  · have he : k = (1074 : Fin 2886) := Fin.ext h1074
    subst k
    rw [keyMomentRowsAt1074]
    exact keyMoment1074 B hB
  · have he : k = (1075 : Fin 2886) := Fin.ext h1075
    subst k
    rw [keyMomentRowsAt1075]
    exact keyMoment1075 B hB
  · have he : k = (1076 : Fin 2886) := Fin.ext h1076
    subst k
    rw [keyMomentRowsAt1076]
    exact keyMoment1076 B hB
  · have he : k = (1077 : Fin 2886) := Fin.ext h1077
    subst k
    rw [keyMomentRowsAt1077]
    exact keyMoment1077 B hB
  · have he : k = (1078 : Fin 2886) := Fin.ext h1078
    subst k
    rw [keyMomentRowsAt1078]
    exact keyMoment1078 B hB
  · have he : k = (1079 : Fin 2886) := Fin.ext h1079
    subst k
    rw [keyMomentRowsAt1079]
    exact keyMoment1079 B hB
  · have he : k = (1080 : Fin 2886) := Fin.ext h1080
    subst k
    rw [keyMomentRowsAt1080]
    exact keyMoment1080 B hB
  · have he : k = (1081 : Fin 2886) := Fin.ext h1081
    subst k
    rw [keyMomentRowsAt1081]
    exact keyMoment1081 B hB
  · have he : k = (1082 : Fin 2886) := Fin.ext h1082
    subst k
    rw [keyMomentRowsAt1082]
    exact keyMoment1082 B hB
  · have he : k = (1083 : Fin 2886) := Fin.ext h1083
    subst k
    rw [keyMomentRowsAt1083]
    exact keyMoment1083 B hB
  · have he : k = (1084 : Fin 2886) := Fin.ext h1084
    subst k
    rw [keyMomentRowsAt1084]
    exact keyMoment1084 B hB
  · have he : k = (1085 : Fin 2886) := Fin.ext h1085
    subst k
    rw [keyMomentRowsAt1085]
    exact keyMoment1085 B hB
  · have he : k = (1086 : Fin 2886) := Fin.ext h1086
    subst k
    rw [keyMomentRowsAt1086]
    exact keyMoment1086 B hB
  · have he : k = (1087 : Fin 2886) := Fin.ext h1087
    subst k
    rw [keyMomentRowsAt1087]
    exact keyMoment1087 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
