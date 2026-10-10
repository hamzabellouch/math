import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound35
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1120 : keyMomentRows (1120 : Fin 2886) =
    keyMomentRow1120 := by decide +kernel

theorem keyMomentRowsAt1121 : keyMomentRows (1121 : Fin 2886) =
    keyMomentRow1121 := by decide +kernel

theorem keyMomentRowsAt1122 : keyMomentRows (1122 : Fin 2886) =
    keyMomentRow1122 := by decide +kernel

theorem keyMomentRowsAt1123 : keyMomentRows (1123 : Fin 2886) =
    keyMomentRow1123 := by decide +kernel

theorem keyMomentRowsAt1124 : keyMomentRows (1124 : Fin 2886) =
    keyMomentRow1124 := by decide +kernel

theorem keyMomentRowsAt1125 : keyMomentRows (1125 : Fin 2886) =
    keyMomentRow1125 := by decide +kernel

theorem keyMomentRowsAt1126 : keyMomentRows (1126 : Fin 2886) =
    keyMomentRow1126 := by decide +kernel

theorem keyMomentRowsAt1127 : keyMomentRows (1127 : Fin 2886) =
    keyMomentRow1127 := by decide +kernel

theorem keyMomentRowsAt1128 : keyMomentRows (1128 : Fin 2886) =
    keyMomentRow1128 := by decide +kernel

theorem keyMomentRowsAt1129 : keyMomentRows (1129 : Fin 2886) =
    keyMomentRow1129 := by decide +kernel

theorem keyMomentRowsAt1130 : keyMomentRows (1130 : Fin 2886) =
    keyMomentRow1130 := by decide +kernel

theorem keyMomentRowsAt1131 : keyMomentRows (1131 : Fin 2886) =
    keyMomentRow1131 := by decide +kernel

theorem keyMomentRowsAt1132 : keyMomentRows (1132 : Fin 2886) =
    keyMomentRow1132 := by decide +kernel

theorem keyMomentRowsAt1133 : keyMomentRows (1133 : Fin 2886) =
    keyMomentRow1133 := by decide +kernel

theorem keyMomentRowsAt1134 : keyMomentRows (1134 : Fin 2886) =
    keyMomentRow1134 := by decide +kernel

theorem keyMomentRowsAt1135 : keyMomentRows (1135 : Fin 2886) =
    keyMomentRow1135 := by decide +kernel

theorem keyMomentRowsAt1136 : keyMomentRows (1136 : Fin 2886) =
    keyMomentRow1136 := by decide +kernel

theorem keyMomentRowsAt1137 : keyMomentRows (1137 : Fin 2886) =
    keyMomentRow1137 := by decide +kernel

theorem keyMomentRowsAt1138 : keyMomentRows (1138 : Fin 2886) =
    keyMomentRow1138 := by decide +kernel

theorem keyMomentRowsAt1139 : keyMomentRows (1139 : Fin 2886) =
    keyMomentRow1139 := by decide +kernel

theorem keyMomentRowsAt1140 : keyMomentRows (1140 : Fin 2886) =
    keyMomentRow1140 := by decide +kernel

theorem keyMomentRowsAt1141 : keyMomentRows (1141 : Fin 2886) =
    keyMomentRow1141 := by decide +kernel

theorem keyMomentRowsAt1142 : keyMomentRows (1142 : Fin 2886) =
    keyMomentRow1142 := by decide +kernel

theorem keyMomentRowsAt1143 : keyMomentRows (1143 : Fin 2886) =
    keyMomentRow1143 := by decide +kernel

theorem keyMomentRowsAt1144 : keyMomentRows (1144 : Fin 2886) =
    keyMomentRow1144 := by decide +kernel

theorem keyMomentRowsAt1145 : keyMomentRows (1145 : Fin 2886) =
    keyMomentRow1145 := by decide +kernel

theorem keyMomentRowsAt1146 : keyMomentRows (1146 : Fin 2886) =
    keyMomentRow1146 := by decide +kernel

theorem keyMomentRowsAt1147 : keyMomentRows (1147 : Fin 2886) =
    keyMomentRow1147 := by decide +kernel

theorem keyMomentRowsAt1148 : keyMomentRows (1148 : Fin 2886) =
    keyMomentRow1148 := by decide +kernel

theorem keyMomentRowsAt1149 : keyMomentRows (1149 : Fin 2886) =
    keyMomentRow1149 := by decide +kernel

theorem keyMomentRowsAt1150 : keyMomentRows (1150 : Fin 2886) =
    keyMomentRow1150 := by decide +kernel

theorem keyMomentRowsAt1151 : keyMomentRows (1151 : Fin 2886) =
    keyMomentRow1151 := by decide +kernel

theorem keyMomentChunkSound35 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 35) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1120 ∨ k.val = 1121 ∨ k.val = 1122 ∨ k.val = 1123 ∨ k.val = 1124 ∨ k.val = 1125 ∨ k.val = 1126 ∨ k.val = 1127 ∨ k.val = 1128 ∨ k.val = 1129 ∨ k.val = 1130 ∨ k.val = 1131 ∨ k.val = 1132 ∨ k.val = 1133 ∨ k.val = 1134 ∨ k.val = 1135 ∨ k.val = 1136 ∨ k.val = 1137 ∨ k.val = 1138 ∨ k.val = 1139 ∨ k.val = 1140 ∨ k.val = 1141 ∨ k.val = 1142 ∨ k.val = 1143 ∨ k.val = 1144 ∨ k.val = 1145 ∨ k.val = 1146 ∨ k.val = 1147 ∨ k.val = 1148 ∨ k.val = 1149 ∨ k.val = 1150 ∨ k.val = 1151 := by omega
  rcases heq with h1120 | h1121 | h1122 | h1123 | h1124 | h1125 | h1126 | h1127 | h1128 | h1129 | h1130 | h1131 | h1132 | h1133 | h1134 | h1135 | h1136 | h1137 | h1138 | h1139 | h1140 | h1141 | h1142 | h1143 | h1144 | h1145 | h1146 | h1147 | h1148 | h1149 | h1150 | h1151
  · have he : k = (1120 : Fin 2886) := Fin.ext h1120
    subst k
    rw [keyMomentRowsAt1120]
    exact keyMoment1120 B hB
  · have he : k = (1121 : Fin 2886) := Fin.ext h1121
    subst k
    rw [keyMomentRowsAt1121]
    exact keyMoment1121 B hB
  · have he : k = (1122 : Fin 2886) := Fin.ext h1122
    subst k
    rw [keyMomentRowsAt1122]
    exact keyMoment1122 B hB
  · have he : k = (1123 : Fin 2886) := Fin.ext h1123
    subst k
    rw [keyMomentRowsAt1123]
    exact keyMoment1123 B hB
  · have he : k = (1124 : Fin 2886) := Fin.ext h1124
    subst k
    rw [keyMomentRowsAt1124]
    exact keyMoment1124 B hB
  · have he : k = (1125 : Fin 2886) := Fin.ext h1125
    subst k
    rw [keyMomentRowsAt1125]
    exact keyMoment1125 B hB
  · have he : k = (1126 : Fin 2886) := Fin.ext h1126
    subst k
    rw [keyMomentRowsAt1126]
    exact keyMoment1126 B hB
  · have he : k = (1127 : Fin 2886) := Fin.ext h1127
    subst k
    rw [keyMomentRowsAt1127]
    exact keyMoment1127 B hB
  · have he : k = (1128 : Fin 2886) := Fin.ext h1128
    subst k
    rw [keyMomentRowsAt1128]
    exact keyMoment1128 B hB
  · have he : k = (1129 : Fin 2886) := Fin.ext h1129
    subst k
    rw [keyMomentRowsAt1129]
    exact keyMoment1129 B hB
  · have he : k = (1130 : Fin 2886) := Fin.ext h1130
    subst k
    rw [keyMomentRowsAt1130]
    exact keyMoment1130 B hB
  · have he : k = (1131 : Fin 2886) := Fin.ext h1131
    subst k
    rw [keyMomentRowsAt1131]
    exact keyMoment1131 B hB
  · have he : k = (1132 : Fin 2886) := Fin.ext h1132
    subst k
    rw [keyMomentRowsAt1132]
    exact keyMoment1132 B hB
  · have he : k = (1133 : Fin 2886) := Fin.ext h1133
    subst k
    rw [keyMomentRowsAt1133]
    exact keyMoment1133 B hB
  · have he : k = (1134 : Fin 2886) := Fin.ext h1134
    subst k
    rw [keyMomentRowsAt1134]
    exact keyMoment1134 B hB
  · have he : k = (1135 : Fin 2886) := Fin.ext h1135
    subst k
    rw [keyMomentRowsAt1135]
    exact keyMoment1135 B hB
  · have he : k = (1136 : Fin 2886) := Fin.ext h1136
    subst k
    rw [keyMomentRowsAt1136]
    exact keyMoment1136 B hB
  · have he : k = (1137 : Fin 2886) := Fin.ext h1137
    subst k
    rw [keyMomentRowsAt1137]
    exact keyMoment1137 B hB
  · have he : k = (1138 : Fin 2886) := Fin.ext h1138
    subst k
    rw [keyMomentRowsAt1138]
    exact keyMoment1138 B hB
  · have he : k = (1139 : Fin 2886) := Fin.ext h1139
    subst k
    rw [keyMomentRowsAt1139]
    exact keyMoment1139 B hB
  · have he : k = (1140 : Fin 2886) := Fin.ext h1140
    subst k
    rw [keyMomentRowsAt1140]
    exact keyMoment1140 B hB
  · have he : k = (1141 : Fin 2886) := Fin.ext h1141
    subst k
    rw [keyMomentRowsAt1141]
    exact keyMoment1141 B hB
  · have he : k = (1142 : Fin 2886) := Fin.ext h1142
    subst k
    rw [keyMomentRowsAt1142]
    exact keyMoment1142 B hB
  · have he : k = (1143 : Fin 2886) := Fin.ext h1143
    subst k
    rw [keyMomentRowsAt1143]
    exact keyMoment1143 B hB
  · have he : k = (1144 : Fin 2886) := Fin.ext h1144
    subst k
    rw [keyMomentRowsAt1144]
    exact keyMoment1144 B hB
  · have he : k = (1145 : Fin 2886) := Fin.ext h1145
    subst k
    rw [keyMomentRowsAt1145]
    exact keyMoment1145 B hB
  · have he : k = (1146 : Fin 2886) := Fin.ext h1146
    subst k
    rw [keyMomentRowsAt1146]
    exact keyMoment1146 B hB
  · have he : k = (1147 : Fin 2886) := Fin.ext h1147
    subst k
    rw [keyMomentRowsAt1147]
    exact keyMoment1147 B hB
  · have he : k = (1148 : Fin 2886) := Fin.ext h1148
    subst k
    rw [keyMomentRowsAt1148]
    exact keyMoment1148 B hB
  · have he : k = (1149 : Fin 2886) := Fin.ext h1149
    subst k
    rw [keyMomentRowsAt1149]
    exact keyMoment1149 B hB
  · have he : k = (1150 : Fin 2886) := Fin.ext h1150
    subst k
    rw [keyMomentRowsAt1150]
    exact keyMoment1150 B hB
  · have he : k = (1151 : Fin 2886) := Fin.ext h1151
    subst k
    rw [keyMomentRowsAt1151]
    exact keyMoment1151 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
