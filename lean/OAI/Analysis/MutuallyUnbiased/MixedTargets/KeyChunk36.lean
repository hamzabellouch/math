import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound36
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1152 : keyMomentRows (1152 : Fin 2886) =
    keyMomentRow1152 := by decide +kernel

theorem keyMomentRowsAt1153 : keyMomentRows (1153 : Fin 2886) =
    keyMomentRow1153 := by decide +kernel

theorem keyMomentRowsAt1154 : keyMomentRows (1154 : Fin 2886) =
    keyMomentRow1154 := by decide +kernel

theorem keyMomentRowsAt1155 : keyMomentRows (1155 : Fin 2886) =
    keyMomentRow1155 := by decide +kernel

theorem keyMomentRowsAt1156 : keyMomentRows (1156 : Fin 2886) =
    keyMomentRow1156 := by decide +kernel

theorem keyMomentRowsAt1157 : keyMomentRows (1157 : Fin 2886) =
    keyMomentRow1157 := by decide +kernel

theorem keyMomentRowsAt1158 : keyMomentRows (1158 : Fin 2886) =
    keyMomentRow1158 := by decide +kernel

theorem keyMomentRowsAt1159 : keyMomentRows (1159 : Fin 2886) =
    keyMomentRow1159 := by decide +kernel

theorem keyMomentRowsAt1160 : keyMomentRows (1160 : Fin 2886) =
    keyMomentRow1160 := by decide +kernel

theorem keyMomentRowsAt1161 : keyMomentRows (1161 : Fin 2886) =
    keyMomentRow1161 := by decide +kernel

theorem keyMomentRowsAt1162 : keyMomentRows (1162 : Fin 2886) =
    keyMomentRow1162 := by decide +kernel

theorem keyMomentRowsAt1163 : keyMomentRows (1163 : Fin 2886) =
    keyMomentRow1163 := by decide +kernel

theorem keyMomentRowsAt1164 : keyMomentRows (1164 : Fin 2886) =
    keyMomentRow1164 := by decide +kernel

theorem keyMomentRowsAt1165 : keyMomentRows (1165 : Fin 2886) =
    keyMomentRow1165 := by decide +kernel

theorem keyMomentRowsAt1166 : keyMomentRows (1166 : Fin 2886) =
    keyMomentRow1166 := by decide +kernel

theorem keyMomentRowsAt1167 : keyMomentRows (1167 : Fin 2886) =
    keyMomentRow1167 := by decide +kernel

theorem keyMomentRowsAt1168 : keyMomentRows (1168 : Fin 2886) =
    keyMomentRow1168 := by decide +kernel

theorem keyMomentRowsAt1169 : keyMomentRows (1169 : Fin 2886) =
    keyMomentRow1169 := by decide +kernel

theorem keyMomentRowsAt1170 : keyMomentRows (1170 : Fin 2886) =
    keyMomentRow1170 := by decide +kernel

theorem keyMomentRowsAt1171 : keyMomentRows (1171 : Fin 2886) =
    keyMomentRow1171 := by decide +kernel

theorem keyMomentRowsAt1172 : keyMomentRows (1172 : Fin 2886) =
    keyMomentRow1172 := by decide +kernel

theorem keyMomentRowsAt1173 : keyMomentRows (1173 : Fin 2886) =
    keyMomentRow1173 := by decide +kernel

theorem keyMomentRowsAt1174 : keyMomentRows (1174 : Fin 2886) =
    keyMomentRow1174 := by decide +kernel

theorem keyMomentRowsAt1175 : keyMomentRows (1175 : Fin 2886) =
    keyMomentRow1175 := by decide +kernel

theorem keyMomentRowsAt1176 : keyMomentRows (1176 : Fin 2886) =
    keyMomentRow1176 := by decide +kernel

theorem keyMomentRowsAt1177 : keyMomentRows (1177 : Fin 2886) =
    keyMomentRow1177 := by decide +kernel

theorem keyMomentRowsAt1178 : keyMomentRows (1178 : Fin 2886) =
    keyMomentRow1178 := by decide +kernel

theorem keyMomentRowsAt1179 : keyMomentRows (1179 : Fin 2886) =
    keyMomentRow1179 := by decide +kernel

theorem keyMomentRowsAt1180 : keyMomentRows (1180 : Fin 2886) =
    keyMomentRow1180 := by decide +kernel

theorem keyMomentRowsAt1181 : keyMomentRows (1181 : Fin 2886) =
    keyMomentRow1181 := by decide +kernel

theorem keyMomentRowsAt1182 : keyMomentRows (1182 : Fin 2886) =
    keyMomentRow1182 := by decide +kernel

theorem keyMomentRowsAt1183 : keyMomentRows (1183 : Fin 2886) =
    keyMomentRow1183 := by decide +kernel

theorem keyMomentChunkSound36 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 36) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1152 ∨ k.val = 1153 ∨ k.val = 1154 ∨ k.val = 1155 ∨ k.val = 1156 ∨ k.val = 1157 ∨ k.val = 1158 ∨ k.val = 1159 ∨ k.val = 1160 ∨ k.val = 1161 ∨ k.val = 1162 ∨ k.val = 1163 ∨ k.val = 1164 ∨ k.val = 1165 ∨ k.val = 1166 ∨ k.val = 1167 ∨ k.val = 1168 ∨ k.val = 1169 ∨ k.val = 1170 ∨ k.val = 1171 ∨ k.val = 1172 ∨ k.val = 1173 ∨ k.val = 1174 ∨ k.val = 1175 ∨ k.val = 1176 ∨ k.val = 1177 ∨ k.val = 1178 ∨ k.val = 1179 ∨ k.val = 1180 ∨ k.val = 1181 ∨ k.val = 1182 ∨ k.val = 1183 := by omega
  rcases heq with h1152 | h1153 | h1154 | h1155 | h1156 | h1157 | h1158 | h1159 | h1160 | h1161 | h1162 | h1163 | h1164 | h1165 | h1166 | h1167 | h1168 | h1169 | h1170 | h1171 | h1172 | h1173 | h1174 | h1175 | h1176 | h1177 | h1178 | h1179 | h1180 | h1181 | h1182 | h1183
  · have he : k = (1152 : Fin 2886) := Fin.ext h1152
    subst k
    rw [keyMomentRowsAt1152]
    exact keyMoment1152 B hB
  · have he : k = (1153 : Fin 2886) := Fin.ext h1153
    subst k
    rw [keyMomentRowsAt1153]
    exact keyMoment1153 B hB
  · have he : k = (1154 : Fin 2886) := Fin.ext h1154
    subst k
    rw [keyMomentRowsAt1154]
    exact keyMoment1154 B hB
  · have he : k = (1155 : Fin 2886) := Fin.ext h1155
    subst k
    rw [keyMomentRowsAt1155]
    exact keyMoment1155 B hB
  · have he : k = (1156 : Fin 2886) := Fin.ext h1156
    subst k
    rw [keyMomentRowsAt1156]
    exact keyMoment1156 B hB
  · have he : k = (1157 : Fin 2886) := Fin.ext h1157
    subst k
    rw [keyMomentRowsAt1157]
    exact keyMoment1157 B hB
  · have he : k = (1158 : Fin 2886) := Fin.ext h1158
    subst k
    rw [keyMomentRowsAt1158]
    exact keyMoment1158 B hB
  · have he : k = (1159 : Fin 2886) := Fin.ext h1159
    subst k
    rw [keyMomentRowsAt1159]
    exact keyMoment1159 B hB
  · have he : k = (1160 : Fin 2886) := Fin.ext h1160
    subst k
    rw [keyMomentRowsAt1160]
    exact keyMoment1160 B hB
  · have he : k = (1161 : Fin 2886) := Fin.ext h1161
    subst k
    rw [keyMomentRowsAt1161]
    exact keyMoment1161 B hB
  · have he : k = (1162 : Fin 2886) := Fin.ext h1162
    subst k
    rw [keyMomentRowsAt1162]
    exact keyMoment1162 B hB
  · have he : k = (1163 : Fin 2886) := Fin.ext h1163
    subst k
    rw [keyMomentRowsAt1163]
    exact keyMoment1163 B hB
  · have he : k = (1164 : Fin 2886) := Fin.ext h1164
    subst k
    rw [keyMomentRowsAt1164]
    exact keyMoment1164 B hB
  · have he : k = (1165 : Fin 2886) := Fin.ext h1165
    subst k
    rw [keyMomentRowsAt1165]
    exact keyMoment1165 B hB
  · have he : k = (1166 : Fin 2886) := Fin.ext h1166
    subst k
    rw [keyMomentRowsAt1166]
    exact keyMoment1166 B hB
  · have he : k = (1167 : Fin 2886) := Fin.ext h1167
    subst k
    rw [keyMomentRowsAt1167]
    exact keyMoment1167 B hB
  · have he : k = (1168 : Fin 2886) := Fin.ext h1168
    subst k
    rw [keyMomentRowsAt1168]
    exact keyMoment1168 B hB
  · have he : k = (1169 : Fin 2886) := Fin.ext h1169
    subst k
    rw [keyMomentRowsAt1169]
    exact keyMoment1169 B hB
  · have he : k = (1170 : Fin 2886) := Fin.ext h1170
    subst k
    rw [keyMomentRowsAt1170]
    exact keyMoment1170 B hB
  · have he : k = (1171 : Fin 2886) := Fin.ext h1171
    subst k
    rw [keyMomentRowsAt1171]
    exact keyMoment1171 B hB
  · have he : k = (1172 : Fin 2886) := Fin.ext h1172
    subst k
    rw [keyMomentRowsAt1172]
    exact keyMoment1172 B hB
  · have he : k = (1173 : Fin 2886) := Fin.ext h1173
    subst k
    rw [keyMomentRowsAt1173]
    exact keyMoment1173 B hB
  · have he : k = (1174 : Fin 2886) := Fin.ext h1174
    subst k
    rw [keyMomentRowsAt1174]
    exact keyMoment1174 B hB
  · have he : k = (1175 : Fin 2886) := Fin.ext h1175
    subst k
    rw [keyMomentRowsAt1175]
    exact keyMoment1175 B hB
  · have he : k = (1176 : Fin 2886) := Fin.ext h1176
    subst k
    rw [keyMomentRowsAt1176]
    exact keyMoment1176 B hB
  · have he : k = (1177 : Fin 2886) := Fin.ext h1177
    subst k
    rw [keyMomentRowsAt1177]
    exact keyMoment1177 B hB
  · have he : k = (1178 : Fin 2886) := Fin.ext h1178
    subst k
    rw [keyMomentRowsAt1178]
    exact keyMoment1178 B hB
  · have he : k = (1179 : Fin 2886) := Fin.ext h1179
    subst k
    rw [keyMomentRowsAt1179]
    exact keyMoment1179 B hB
  · have he : k = (1180 : Fin 2886) := Fin.ext h1180
    subst k
    rw [keyMomentRowsAt1180]
    exact keyMoment1180 B hB
  · have he : k = (1181 : Fin 2886) := Fin.ext h1181
    subst k
    rw [keyMomentRowsAt1181]
    exact keyMoment1181 B hB
  · have he : k = (1182 : Fin 2886) := Fin.ext h1182
    subst k
    rw [keyMomentRowsAt1182]
    exact keyMoment1182 B hB
  · have he : k = (1183 : Fin 2886) := Fin.ext h1183
    subst k
    rw [keyMomentRowsAt1183]
    exact keyMoment1183 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
