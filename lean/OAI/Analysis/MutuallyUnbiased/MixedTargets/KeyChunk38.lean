import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound38
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1216 : keyMomentRows (1216 : Fin 2886) =
    keyMomentRow1216 := by decide +kernel

theorem keyMomentRowsAt1217 : keyMomentRows (1217 : Fin 2886) =
    keyMomentRow1217 := by decide +kernel

theorem keyMomentRowsAt1218 : keyMomentRows (1218 : Fin 2886) =
    keyMomentRow1218 := by decide +kernel

theorem keyMomentRowsAt1219 : keyMomentRows (1219 : Fin 2886) =
    keyMomentRow1219 := by decide +kernel

theorem keyMomentRowsAt1220 : keyMomentRows (1220 : Fin 2886) =
    keyMomentRow1220 := by decide +kernel

theorem keyMomentRowsAt1221 : keyMomentRows (1221 : Fin 2886) =
    keyMomentRow1221 := by decide +kernel

theorem keyMomentRowsAt1222 : keyMomentRows (1222 : Fin 2886) =
    keyMomentRow1222 := by decide +kernel

theorem keyMomentRowsAt1223 : keyMomentRows (1223 : Fin 2886) =
    keyMomentRow1223 := by decide +kernel

theorem keyMomentRowsAt1224 : keyMomentRows (1224 : Fin 2886) =
    keyMomentRow1224 := by decide +kernel

theorem keyMomentRowsAt1225 : keyMomentRows (1225 : Fin 2886) =
    keyMomentRow1225 := by decide +kernel

theorem keyMomentRowsAt1226 : keyMomentRows (1226 : Fin 2886) =
    keyMomentRow1226 := by decide +kernel

theorem keyMomentRowsAt1227 : keyMomentRows (1227 : Fin 2886) =
    keyMomentRow1227 := by decide +kernel

theorem keyMomentRowsAt1228 : keyMomentRows (1228 : Fin 2886) =
    keyMomentRow1228 := by decide +kernel

theorem keyMomentRowsAt1229 : keyMomentRows (1229 : Fin 2886) =
    keyMomentRow1229 := by decide +kernel

theorem keyMomentRowsAt1230 : keyMomentRows (1230 : Fin 2886) =
    keyMomentRow1230 := by decide +kernel

theorem keyMomentRowsAt1231 : keyMomentRows (1231 : Fin 2886) =
    keyMomentRow1231 := by decide +kernel

theorem keyMomentRowsAt1232 : keyMomentRows (1232 : Fin 2886) =
    keyMomentRow1232 := by decide +kernel

theorem keyMomentRowsAt1233 : keyMomentRows (1233 : Fin 2886) =
    keyMomentRow1233 := by decide +kernel

theorem keyMomentRowsAt1234 : keyMomentRows (1234 : Fin 2886) =
    keyMomentRow1234 := by decide +kernel

theorem keyMomentRowsAt1235 : keyMomentRows (1235 : Fin 2886) =
    keyMomentRow1235 := by decide +kernel

theorem keyMomentRowsAt1236 : keyMomentRows (1236 : Fin 2886) =
    keyMomentRow1236 := by decide +kernel

theorem keyMomentRowsAt1237 : keyMomentRows (1237 : Fin 2886) =
    keyMomentRow1237 := by decide +kernel

theorem keyMomentRowsAt1238 : keyMomentRows (1238 : Fin 2886) =
    keyMomentRow1238 := by decide +kernel

theorem keyMomentRowsAt1239 : keyMomentRows (1239 : Fin 2886) =
    keyMomentRow1239 := by decide +kernel

theorem keyMomentRowsAt1240 : keyMomentRows (1240 : Fin 2886) =
    keyMomentRow1240 := by decide +kernel

theorem keyMomentRowsAt1241 : keyMomentRows (1241 : Fin 2886) =
    keyMomentRow1241 := by decide +kernel

theorem keyMomentRowsAt1242 : keyMomentRows (1242 : Fin 2886) =
    keyMomentRow1242 := by decide +kernel

theorem keyMomentRowsAt1243 : keyMomentRows (1243 : Fin 2886) =
    keyMomentRow1243 := by decide +kernel

theorem keyMomentRowsAt1244 : keyMomentRows (1244 : Fin 2886) =
    keyMomentRow1244 := by decide +kernel

theorem keyMomentRowsAt1245 : keyMomentRows (1245 : Fin 2886) =
    keyMomentRow1245 := by decide +kernel

theorem keyMomentRowsAt1246 : keyMomentRows (1246 : Fin 2886) =
    keyMomentRow1246 := by decide +kernel

theorem keyMomentRowsAt1247 : keyMomentRows (1247 : Fin 2886) =
    keyMomentRow1247 := by decide +kernel

theorem keyMomentChunkSound38 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 38) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1216 ∨ k.val = 1217 ∨ k.val = 1218 ∨ k.val = 1219 ∨ k.val = 1220 ∨ k.val = 1221 ∨ k.val = 1222 ∨ k.val = 1223 ∨ k.val = 1224 ∨ k.val = 1225 ∨ k.val = 1226 ∨ k.val = 1227 ∨ k.val = 1228 ∨ k.val = 1229 ∨ k.val = 1230 ∨ k.val = 1231 ∨ k.val = 1232 ∨ k.val = 1233 ∨ k.val = 1234 ∨ k.val = 1235 ∨ k.val = 1236 ∨ k.val = 1237 ∨ k.val = 1238 ∨ k.val = 1239 ∨ k.val = 1240 ∨ k.val = 1241 ∨ k.val = 1242 ∨ k.val = 1243 ∨ k.val = 1244 ∨ k.val = 1245 ∨ k.val = 1246 ∨ k.val = 1247 := by omega
  rcases heq with h1216 | h1217 | h1218 | h1219 | h1220 | h1221 | h1222 | h1223 | h1224 | h1225 | h1226 | h1227 | h1228 | h1229 | h1230 | h1231 | h1232 | h1233 | h1234 | h1235 | h1236 | h1237 | h1238 | h1239 | h1240 | h1241 | h1242 | h1243 | h1244 | h1245 | h1246 | h1247
  · have he : k = (1216 : Fin 2886) := Fin.ext h1216
    subst k
    rw [keyMomentRowsAt1216]
    exact keyMoment1216 B hB
  · have he : k = (1217 : Fin 2886) := Fin.ext h1217
    subst k
    rw [keyMomentRowsAt1217]
    exact keyMoment1217 B hB
  · have he : k = (1218 : Fin 2886) := Fin.ext h1218
    subst k
    rw [keyMomentRowsAt1218]
    exact keyMoment1218 B hB
  · have he : k = (1219 : Fin 2886) := Fin.ext h1219
    subst k
    rw [keyMomentRowsAt1219]
    exact keyMoment1219 B hB
  · have he : k = (1220 : Fin 2886) := Fin.ext h1220
    subst k
    rw [keyMomentRowsAt1220]
    exact keyMoment1220 B hB
  · have he : k = (1221 : Fin 2886) := Fin.ext h1221
    subst k
    rw [keyMomentRowsAt1221]
    exact keyMoment1221 B hB
  · have he : k = (1222 : Fin 2886) := Fin.ext h1222
    subst k
    rw [keyMomentRowsAt1222]
    exact keyMoment1222 B hB
  · have he : k = (1223 : Fin 2886) := Fin.ext h1223
    subst k
    rw [keyMomentRowsAt1223]
    exact keyMoment1223 B hB
  · have he : k = (1224 : Fin 2886) := Fin.ext h1224
    subst k
    rw [keyMomentRowsAt1224]
    exact keyMoment1224 B hB
  · have he : k = (1225 : Fin 2886) := Fin.ext h1225
    subst k
    rw [keyMomentRowsAt1225]
    exact keyMoment1225 B hB
  · have he : k = (1226 : Fin 2886) := Fin.ext h1226
    subst k
    rw [keyMomentRowsAt1226]
    exact keyMoment1226 B hB
  · have he : k = (1227 : Fin 2886) := Fin.ext h1227
    subst k
    rw [keyMomentRowsAt1227]
    exact keyMoment1227 B hB
  · have he : k = (1228 : Fin 2886) := Fin.ext h1228
    subst k
    rw [keyMomentRowsAt1228]
    exact keyMoment1228 B hB
  · have he : k = (1229 : Fin 2886) := Fin.ext h1229
    subst k
    rw [keyMomentRowsAt1229]
    exact keyMoment1229 B hB
  · have he : k = (1230 : Fin 2886) := Fin.ext h1230
    subst k
    rw [keyMomentRowsAt1230]
    exact keyMoment1230 B hB
  · have he : k = (1231 : Fin 2886) := Fin.ext h1231
    subst k
    rw [keyMomentRowsAt1231]
    exact keyMoment1231 B hB
  · have he : k = (1232 : Fin 2886) := Fin.ext h1232
    subst k
    rw [keyMomentRowsAt1232]
    exact keyMoment1232 B hB
  · have he : k = (1233 : Fin 2886) := Fin.ext h1233
    subst k
    rw [keyMomentRowsAt1233]
    exact keyMoment1233 B hB
  · have he : k = (1234 : Fin 2886) := Fin.ext h1234
    subst k
    rw [keyMomentRowsAt1234]
    exact keyMoment1234 B hB
  · have he : k = (1235 : Fin 2886) := Fin.ext h1235
    subst k
    rw [keyMomentRowsAt1235]
    exact keyMoment1235 B hB
  · have he : k = (1236 : Fin 2886) := Fin.ext h1236
    subst k
    rw [keyMomentRowsAt1236]
    exact keyMoment1236 B hB
  · have he : k = (1237 : Fin 2886) := Fin.ext h1237
    subst k
    rw [keyMomentRowsAt1237]
    exact keyMoment1237 B hB
  · have he : k = (1238 : Fin 2886) := Fin.ext h1238
    subst k
    rw [keyMomentRowsAt1238]
    exact keyMoment1238 B hB
  · have he : k = (1239 : Fin 2886) := Fin.ext h1239
    subst k
    rw [keyMomentRowsAt1239]
    exact keyMoment1239 B hB
  · have he : k = (1240 : Fin 2886) := Fin.ext h1240
    subst k
    rw [keyMomentRowsAt1240]
    exact keyMoment1240 B hB
  · have he : k = (1241 : Fin 2886) := Fin.ext h1241
    subst k
    rw [keyMomentRowsAt1241]
    exact keyMoment1241 B hB
  · have he : k = (1242 : Fin 2886) := Fin.ext h1242
    subst k
    rw [keyMomentRowsAt1242]
    exact keyMoment1242 B hB
  · have he : k = (1243 : Fin 2886) := Fin.ext h1243
    subst k
    rw [keyMomentRowsAt1243]
    exact keyMoment1243 B hB
  · have he : k = (1244 : Fin 2886) := Fin.ext h1244
    subst k
    rw [keyMomentRowsAt1244]
    exact keyMoment1244 B hB
  · have he : k = (1245 : Fin 2886) := Fin.ext h1245
    subst k
    rw [keyMomentRowsAt1245]
    exact keyMoment1245 B hB
  · have he : k = (1246 : Fin 2886) := Fin.ext h1246
    subst k
    rw [keyMomentRowsAt1246]
    exact keyMoment1246 B hB
  · have he : k = (1247 : Fin 2886) := Fin.ext h1247
    subst k
    rw [keyMomentRowsAt1247]
    exact keyMoment1247 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
