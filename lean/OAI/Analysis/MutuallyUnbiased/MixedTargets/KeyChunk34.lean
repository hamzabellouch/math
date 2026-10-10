import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound34
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1088 : keyMomentRows (1088 : Fin 2886) =
    keyMomentRow1088 := by decide +kernel

theorem keyMomentRowsAt1089 : keyMomentRows (1089 : Fin 2886) =
    keyMomentRow1089 := by decide +kernel

theorem keyMomentRowsAt1090 : keyMomentRows (1090 : Fin 2886) =
    keyMomentRow1090 := by decide +kernel

theorem keyMomentRowsAt1091 : keyMomentRows (1091 : Fin 2886) =
    keyMomentRow1091 := by decide +kernel

theorem keyMomentRowsAt1092 : keyMomentRows (1092 : Fin 2886) =
    keyMomentRow1092 := by decide +kernel

theorem keyMomentRowsAt1093 : keyMomentRows (1093 : Fin 2886) =
    keyMomentRow1093 := by decide +kernel

theorem keyMomentRowsAt1094 : keyMomentRows (1094 : Fin 2886) =
    keyMomentRow1094 := by decide +kernel

theorem keyMomentRowsAt1095 : keyMomentRows (1095 : Fin 2886) =
    keyMomentRow1095 := by decide +kernel

theorem keyMomentRowsAt1096 : keyMomentRows (1096 : Fin 2886) =
    keyMomentRow1096 := by decide +kernel

theorem keyMomentRowsAt1097 : keyMomentRows (1097 : Fin 2886) =
    keyMomentRow1097 := by decide +kernel

theorem keyMomentRowsAt1098 : keyMomentRows (1098 : Fin 2886) =
    keyMomentRow1098 := by decide +kernel

theorem keyMomentRowsAt1099 : keyMomentRows (1099 : Fin 2886) =
    keyMomentRow1099 := by decide +kernel

theorem keyMomentRowsAt1100 : keyMomentRows (1100 : Fin 2886) =
    keyMomentRow1100 := by decide +kernel

theorem keyMomentRowsAt1101 : keyMomentRows (1101 : Fin 2886) =
    keyMomentRow1101 := by decide +kernel

theorem keyMomentRowsAt1102 : keyMomentRows (1102 : Fin 2886) =
    keyMomentRow1102 := by decide +kernel

theorem keyMomentRowsAt1103 : keyMomentRows (1103 : Fin 2886) =
    keyMomentRow1103 := by decide +kernel

theorem keyMomentRowsAt1104 : keyMomentRows (1104 : Fin 2886) =
    keyMomentRow1104 := by decide +kernel

theorem keyMomentRowsAt1105 : keyMomentRows (1105 : Fin 2886) =
    keyMomentRow1105 := by decide +kernel

theorem keyMomentRowsAt1106 : keyMomentRows (1106 : Fin 2886) =
    keyMomentRow1106 := by decide +kernel

theorem keyMomentRowsAt1107 : keyMomentRows (1107 : Fin 2886) =
    keyMomentRow1107 := by decide +kernel

theorem keyMomentRowsAt1108 : keyMomentRows (1108 : Fin 2886) =
    keyMomentRow1108 := by decide +kernel

theorem keyMomentRowsAt1109 : keyMomentRows (1109 : Fin 2886) =
    keyMomentRow1109 := by decide +kernel

theorem keyMomentRowsAt1110 : keyMomentRows (1110 : Fin 2886) =
    keyMomentRow1110 := by decide +kernel

theorem keyMomentRowsAt1111 : keyMomentRows (1111 : Fin 2886) =
    keyMomentRow1111 := by decide +kernel

theorem keyMomentRowsAt1112 : keyMomentRows (1112 : Fin 2886) =
    keyMomentRow1112 := by decide +kernel

theorem keyMomentRowsAt1113 : keyMomentRows (1113 : Fin 2886) =
    keyMomentRow1113 := by decide +kernel

theorem keyMomentRowsAt1114 : keyMomentRows (1114 : Fin 2886) =
    keyMomentRow1114 := by decide +kernel

theorem keyMomentRowsAt1115 : keyMomentRows (1115 : Fin 2886) =
    keyMomentRow1115 := by decide +kernel

theorem keyMomentRowsAt1116 : keyMomentRows (1116 : Fin 2886) =
    keyMomentRow1116 := by decide +kernel

theorem keyMomentRowsAt1117 : keyMomentRows (1117 : Fin 2886) =
    keyMomentRow1117 := by decide +kernel

theorem keyMomentRowsAt1118 : keyMomentRows (1118 : Fin 2886) =
    keyMomentRow1118 := by decide +kernel

theorem keyMomentRowsAt1119 : keyMomentRows (1119 : Fin 2886) =
    keyMomentRow1119 := by decide +kernel

theorem keyMomentChunkSound34 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 34) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1088 ∨ k.val = 1089 ∨ k.val = 1090 ∨ k.val = 1091 ∨ k.val = 1092 ∨ k.val = 1093 ∨ k.val = 1094 ∨ k.val = 1095 ∨ k.val = 1096 ∨ k.val = 1097 ∨ k.val = 1098 ∨ k.val = 1099 ∨ k.val = 1100 ∨ k.val = 1101 ∨ k.val = 1102 ∨ k.val = 1103 ∨ k.val = 1104 ∨ k.val = 1105 ∨ k.val = 1106 ∨ k.val = 1107 ∨ k.val = 1108 ∨ k.val = 1109 ∨ k.val = 1110 ∨ k.val = 1111 ∨ k.val = 1112 ∨ k.val = 1113 ∨ k.val = 1114 ∨ k.val = 1115 ∨ k.val = 1116 ∨ k.val = 1117 ∨ k.val = 1118 ∨ k.val = 1119 := by omega
  rcases heq with h1088 | h1089 | h1090 | h1091 | h1092 | h1093 | h1094 | h1095 | h1096 | h1097 | h1098 | h1099 | h1100 | h1101 | h1102 | h1103 | h1104 | h1105 | h1106 | h1107 | h1108 | h1109 | h1110 | h1111 | h1112 | h1113 | h1114 | h1115 | h1116 | h1117 | h1118 | h1119
  · have he : k = (1088 : Fin 2886) := Fin.ext h1088
    subst k
    rw [keyMomentRowsAt1088]
    exact keyMoment1088 B hB
  · have he : k = (1089 : Fin 2886) := Fin.ext h1089
    subst k
    rw [keyMomentRowsAt1089]
    exact keyMoment1089 B hB
  · have he : k = (1090 : Fin 2886) := Fin.ext h1090
    subst k
    rw [keyMomentRowsAt1090]
    exact keyMoment1090 B hB
  · have he : k = (1091 : Fin 2886) := Fin.ext h1091
    subst k
    rw [keyMomentRowsAt1091]
    exact keyMoment1091 B hB
  · have he : k = (1092 : Fin 2886) := Fin.ext h1092
    subst k
    rw [keyMomentRowsAt1092]
    exact keyMoment1092 B hB
  · have he : k = (1093 : Fin 2886) := Fin.ext h1093
    subst k
    rw [keyMomentRowsAt1093]
    exact keyMoment1093 B hB
  · have he : k = (1094 : Fin 2886) := Fin.ext h1094
    subst k
    rw [keyMomentRowsAt1094]
    exact keyMoment1094 B hB
  · have he : k = (1095 : Fin 2886) := Fin.ext h1095
    subst k
    rw [keyMomentRowsAt1095]
    exact keyMoment1095 B hB
  · have he : k = (1096 : Fin 2886) := Fin.ext h1096
    subst k
    rw [keyMomentRowsAt1096]
    exact keyMoment1096 B hB
  · have he : k = (1097 : Fin 2886) := Fin.ext h1097
    subst k
    rw [keyMomentRowsAt1097]
    exact keyMoment1097 B hB
  · have he : k = (1098 : Fin 2886) := Fin.ext h1098
    subst k
    rw [keyMomentRowsAt1098]
    exact keyMoment1098 B hB
  · have he : k = (1099 : Fin 2886) := Fin.ext h1099
    subst k
    rw [keyMomentRowsAt1099]
    exact keyMoment1099 B hB
  · have he : k = (1100 : Fin 2886) := Fin.ext h1100
    subst k
    rw [keyMomentRowsAt1100]
    exact keyMoment1100 B hB
  · have he : k = (1101 : Fin 2886) := Fin.ext h1101
    subst k
    rw [keyMomentRowsAt1101]
    exact keyMoment1101 B hB
  · have he : k = (1102 : Fin 2886) := Fin.ext h1102
    subst k
    rw [keyMomentRowsAt1102]
    exact keyMoment1102 B hB
  · have he : k = (1103 : Fin 2886) := Fin.ext h1103
    subst k
    rw [keyMomentRowsAt1103]
    exact keyMoment1103 B hB
  · have he : k = (1104 : Fin 2886) := Fin.ext h1104
    subst k
    rw [keyMomentRowsAt1104]
    exact keyMoment1104 B hB
  · have he : k = (1105 : Fin 2886) := Fin.ext h1105
    subst k
    rw [keyMomentRowsAt1105]
    exact keyMoment1105 B hB
  · have he : k = (1106 : Fin 2886) := Fin.ext h1106
    subst k
    rw [keyMomentRowsAt1106]
    exact keyMoment1106 B hB
  · have he : k = (1107 : Fin 2886) := Fin.ext h1107
    subst k
    rw [keyMomentRowsAt1107]
    exact keyMoment1107 B hB
  · have he : k = (1108 : Fin 2886) := Fin.ext h1108
    subst k
    rw [keyMomentRowsAt1108]
    exact keyMoment1108 B hB
  · have he : k = (1109 : Fin 2886) := Fin.ext h1109
    subst k
    rw [keyMomentRowsAt1109]
    exact keyMoment1109 B hB
  · have he : k = (1110 : Fin 2886) := Fin.ext h1110
    subst k
    rw [keyMomentRowsAt1110]
    exact keyMoment1110 B hB
  · have he : k = (1111 : Fin 2886) := Fin.ext h1111
    subst k
    rw [keyMomentRowsAt1111]
    exact keyMoment1111 B hB
  · have he : k = (1112 : Fin 2886) := Fin.ext h1112
    subst k
    rw [keyMomentRowsAt1112]
    exact keyMoment1112 B hB
  · have he : k = (1113 : Fin 2886) := Fin.ext h1113
    subst k
    rw [keyMomentRowsAt1113]
    exact keyMoment1113 B hB
  · have he : k = (1114 : Fin 2886) := Fin.ext h1114
    subst k
    rw [keyMomentRowsAt1114]
    exact keyMoment1114 B hB
  · have he : k = (1115 : Fin 2886) := Fin.ext h1115
    subst k
    rw [keyMomentRowsAt1115]
    exact keyMoment1115 B hB
  · have he : k = (1116 : Fin 2886) := Fin.ext h1116
    subst k
    rw [keyMomentRowsAt1116]
    exact keyMoment1116 B hB
  · have he : k = (1117 : Fin 2886) := Fin.ext h1117
    subst k
    rw [keyMomentRowsAt1117]
    exact keyMoment1117 B hB
  · have he : k = (1118 : Fin 2886) := Fin.ext h1118
    subst k
    rw [keyMomentRowsAt1118]
    exact keyMoment1118 B hB
  · have he : k = (1119 : Fin 2886) := Fin.ext h1119
    subst k
    rw [keyMomentRowsAt1119]
    exact keyMoment1119 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
