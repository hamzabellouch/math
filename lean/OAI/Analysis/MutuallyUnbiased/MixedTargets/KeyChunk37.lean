import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound37
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1184 : keyMomentRows (1184 : Fin 2886) =
    keyMomentRow1184 := by decide +kernel

theorem keyMomentRowsAt1185 : keyMomentRows (1185 : Fin 2886) =
    keyMomentRow1185 := by decide +kernel

theorem keyMomentRowsAt1186 : keyMomentRows (1186 : Fin 2886) =
    keyMomentRow1186 := by decide +kernel

theorem keyMomentRowsAt1187 : keyMomentRows (1187 : Fin 2886) =
    keyMomentRow1187 := by decide +kernel

theorem keyMomentRowsAt1188 : keyMomentRows (1188 : Fin 2886) =
    keyMomentRow1188 := by decide +kernel

theorem keyMomentRowsAt1189 : keyMomentRows (1189 : Fin 2886) =
    keyMomentRow1189 := by decide +kernel

theorem keyMomentRowsAt1190 : keyMomentRows (1190 : Fin 2886) =
    keyMomentRow1190 := by decide +kernel

theorem keyMomentRowsAt1191 : keyMomentRows (1191 : Fin 2886) =
    keyMomentRow1191 := by decide +kernel

theorem keyMomentRowsAt1192 : keyMomentRows (1192 : Fin 2886) =
    keyMomentRow1192 := by decide +kernel

theorem keyMomentRowsAt1193 : keyMomentRows (1193 : Fin 2886) =
    keyMomentRow1193 := by decide +kernel

theorem keyMomentRowsAt1194 : keyMomentRows (1194 : Fin 2886) =
    keyMomentRow1194 := by decide +kernel

theorem keyMomentRowsAt1195 : keyMomentRows (1195 : Fin 2886) =
    keyMomentRow1195 := by decide +kernel

theorem keyMomentRowsAt1196 : keyMomentRows (1196 : Fin 2886) =
    keyMomentRow1196 := by decide +kernel

theorem keyMomentRowsAt1197 : keyMomentRows (1197 : Fin 2886) =
    keyMomentRow1197 := by decide +kernel

theorem keyMomentRowsAt1198 : keyMomentRows (1198 : Fin 2886) =
    keyMomentRow1198 := by decide +kernel

theorem keyMomentRowsAt1199 : keyMomentRows (1199 : Fin 2886) =
    keyMomentRow1199 := by decide +kernel

theorem keyMomentRowsAt1200 : keyMomentRows (1200 : Fin 2886) =
    keyMomentRow1200 := by decide +kernel

theorem keyMomentRowsAt1201 : keyMomentRows (1201 : Fin 2886) =
    keyMomentRow1201 := by decide +kernel

theorem keyMomentRowsAt1202 : keyMomentRows (1202 : Fin 2886) =
    keyMomentRow1202 := by decide +kernel

theorem keyMomentRowsAt1203 : keyMomentRows (1203 : Fin 2886) =
    keyMomentRow1203 := by decide +kernel

theorem keyMomentRowsAt1204 : keyMomentRows (1204 : Fin 2886) =
    keyMomentRow1204 := by decide +kernel

theorem keyMomentRowsAt1205 : keyMomentRows (1205 : Fin 2886) =
    keyMomentRow1205 := by decide +kernel

theorem keyMomentRowsAt1206 : keyMomentRows (1206 : Fin 2886) =
    keyMomentRow1206 := by decide +kernel

theorem keyMomentRowsAt1207 : keyMomentRows (1207 : Fin 2886) =
    keyMomentRow1207 := by decide +kernel

theorem keyMomentRowsAt1208 : keyMomentRows (1208 : Fin 2886) =
    keyMomentRow1208 := by decide +kernel

theorem keyMomentRowsAt1209 : keyMomentRows (1209 : Fin 2886) =
    keyMomentRow1209 := by decide +kernel

theorem keyMomentRowsAt1210 : keyMomentRows (1210 : Fin 2886) =
    keyMomentRow1210 := by decide +kernel

theorem keyMomentRowsAt1211 : keyMomentRows (1211 : Fin 2886) =
    keyMomentRow1211 := by decide +kernel

theorem keyMomentRowsAt1212 : keyMomentRows (1212 : Fin 2886) =
    keyMomentRow1212 := by decide +kernel

theorem keyMomentRowsAt1213 : keyMomentRows (1213 : Fin 2886) =
    keyMomentRow1213 := by decide +kernel

theorem keyMomentRowsAt1214 : keyMomentRows (1214 : Fin 2886) =
    keyMomentRow1214 := by decide +kernel

theorem keyMomentRowsAt1215 : keyMomentRows (1215 : Fin 2886) =
    keyMomentRow1215 := by decide +kernel

theorem keyMomentChunkSound37 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 37) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1184 ∨ k.val = 1185 ∨ k.val = 1186 ∨ k.val = 1187 ∨ k.val = 1188 ∨ k.val = 1189 ∨ k.val = 1190 ∨ k.val = 1191 ∨ k.val = 1192 ∨ k.val = 1193 ∨ k.val = 1194 ∨ k.val = 1195 ∨ k.val = 1196 ∨ k.val = 1197 ∨ k.val = 1198 ∨ k.val = 1199 ∨ k.val = 1200 ∨ k.val = 1201 ∨ k.val = 1202 ∨ k.val = 1203 ∨ k.val = 1204 ∨ k.val = 1205 ∨ k.val = 1206 ∨ k.val = 1207 ∨ k.val = 1208 ∨ k.val = 1209 ∨ k.val = 1210 ∨ k.val = 1211 ∨ k.val = 1212 ∨ k.val = 1213 ∨ k.val = 1214 ∨ k.val = 1215 := by omega
  rcases heq with h1184 | h1185 | h1186 | h1187 | h1188 | h1189 | h1190 | h1191 | h1192 | h1193 | h1194 | h1195 | h1196 | h1197 | h1198 | h1199 | h1200 | h1201 | h1202 | h1203 | h1204 | h1205 | h1206 | h1207 | h1208 | h1209 | h1210 | h1211 | h1212 | h1213 | h1214 | h1215
  · have he : k = (1184 : Fin 2886) := Fin.ext h1184
    subst k
    rw [keyMomentRowsAt1184]
    exact keyMoment1184 B hB
  · have he : k = (1185 : Fin 2886) := Fin.ext h1185
    subst k
    rw [keyMomentRowsAt1185]
    exact keyMoment1185 B hB
  · have he : k = (1186 : Fin 2886) := Fin.ext h1186
    subst k
    rw [keyMomentRowsAt1186]
    exact keyMoment1186 B hB
  · have he : k = (1187 : Fin 2886) := Fin.ext h1187
    subst k
    rw [keyMomentRowsAt1187]
    exact keyMoment1187 B hB
  · have he : k = (1188 : Fin 2886) := Fin.ext h1188
    subst k
    rw [keyMomentRowsAt1188]
    exact keyMoment1188 B hB
  · have he : k = (1189 : Fin 2886) := Fin.ext h1189
    subst k
    rw [keyMomentRowsAt1189]
    exact keyMoment1189 B hB
  · have he : k = (1190 : Fin 2886) := Fin.ext h1190
    subst k
    rw [keyMomentRowsAt1190]
    exact keyMoment1190 B hB
  · have he : k = (1191 : Fin 2886) := Fin.ext h1191
    subst k
    rw [keyMomentRowsAt1191]
    exact keyMoment1191 B hB
  · have he : k = (1192 : Fin 2886) := Fin.ext h1192
    subst k
    rw [keyMomentRowsAt1192]
    exact keyMoment1192 B hB
  · have he : k = (1193 : Fin 2886) := Fin.ext h1193
    subst k
    rw [keyMomentRowsAt1193]
    exact keyMoment1193 B hB
  · have he : k = (1194 : Fin 2886) := Fin.ext h1194
    subst k
    rw [keyMomentRowsAt1194]
    exact keyMoment1194 B hB
  · have he : k = (1195 : Fin 2886) := Fin.ext h1195
    subst k
    rw [keyMomentRowsAt1195]
    exact keyMoment1195 B hB
  · have he : k = (1196 : Fin 2886) := Fin.ext h1196
    subst k
    rw [keyMomentRowsAt1196]
    exact keyMoment1196 B hB
  · have he : k = (1197 : Fin 2886) := Fin.ext h1197
    subst k
    rw [keyMomentRowsAt1197]
    exact keyMoment1197 B hB
  · have he : k = (1198 : Fin 2886) := Fin.ext h1198
    subst k
    rw [keyMomentRowsAt1198]
    exact keyMoment1198 B hB
  · have he : k = (1199 : Fin 2886) := Fin.ext h1199
    subst k
    rw [keyMomentRowsAt1199]
    exact keyMoment1199 B hB
  · have he : k = (1200 : Fin 2886) := Fin.ext h1200
    subst k
    rw [keyMomentRowsAt1200]
    exact keyMoment1200 B hB
  · have he : k = (1201 : Fin 2886) := Fin.ext h1201
    subst k
    rw [keyMomentRowsAt1201]
    exact keyMoment1201 B hB
  · have he : k = (1202 : Fin 2886) := Fin.ext h1202
    subst k
    rw [keyMomentRowsAt1202]
    exact keyMoment1202 B hB
  · have he : k = (1203 : Fin 2886) := Fin.ext h1203
    subst k
    rw [keyMomentRowsAt1203]
    exact keyMoment1203 B hB
  · have he : k = (1204 : Fin 2886) := Fin.ext h1204
    subst k
    rw [keyMomentRowsAt1204]
    exact keyMoment1204 B hB
  · have he : k = (1205 : Fin 2886) := Fin.ext h1205
    subst k
    rw [keyMomentRowsAt1205]
    exact keyMoment1205 B hB
  · have he : k = (1206 : Fin 2886) := Fin.ext h1206
    subst k
    rw [keyMomentRowsAt1206]
    exact keyMoment1206 B hB
  · have he : k = (1207 : Fin 2886) := Fin.ext h1207
    subst k
    rw [keyMomentRowsAt1207]
    exact keyMoment1207 B hB
  · have he : k = (1208 : Fin 2886) := Fin.ext h1208
    subst k
    rw [keyMomentRowsAt1208]
    exact keyMoment1208 B hB
  · have he : k = (1209 : Fin 2886) := Fin.ext h1209
    subst k
    rw [keyMomentRowsAt1209]
    exact keyMoment1209 B hB
  · have he : k = (1210 : Fin 2886) := Fin.ext h1210
    subst k
    rw [keyMomentRowsAt1210]
    exact keyMoment1210 B hB
  · have he : k = (1211 : Fin 2886) := Fin.ext h1211
    subst k
    rw [keyMomentRowsAt1211]
    exact keyMoment1211 B hB
  · have he : k = (1212 : Fin 2886) := Fin.ext h1212
    subst k
    rw [keyMomentRowsAt1212]
    exact keyMoment1212 B hB
  · have he : k = (1213 : Fin 2886) := Fin.ext h1213
    subst k
    rw [keyMomentRowsAt1213]
    exact keyMoment1213 B hB
  · have he : k = (1214 : Fin 2886) := Fin.ext h1214
    subst k
    rw [keyMomentRowsAt1214]
    exact keyMoment1214 B hB
  · have he : k = (1215 : Fin 2886) := Fin.ext h1215
    subst k
    rw [keyMomentRowsAt1215]
    exact keyMoment1215 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
