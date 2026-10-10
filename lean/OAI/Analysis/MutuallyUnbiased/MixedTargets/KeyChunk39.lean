import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound39
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1248 : keyMomentRows (1248 : Fin 2886) =
    keyMomentRow1248 := by decide +kernel

theorem keyMomentRowsAt1249 : keyMomentRows (1249 : Fin 2886) =
    keyMomentRow1249 := by decide +kernel

theorem keyMomentRowsAt1250 : keyMomentRows (1250 : Fin 2886) =
    keyMomentRow1250 := by decide +kernel

theorem keyMomentRowsAt1251 : keyMomentRows (1251 : Fin 2886) =
    keyMomentRow1251 := by decide +kernel

theorem keyMomentRowsAt1252 : keyMomentRows (1252 : Fin 2886) =
    keyMomentRow1252 := by decide +kernel

theorem keyMomentRowsAt1253 : keyMomentRows (1253 : Fin 2886) =
    keyMomentRow1253 := by decide +kernel

theorem keyMomentRowsAt1254 : keyMomentRows (1254 : Fin 2886) =
    keyMomentRow1254 := by decide +kernel

theorem keyMomentRowsAt1255 : keyMomentRows (1255 : Fin 2886) =
    keyMomentRow1255 := by decide +kernel

theorem keyMomentRowsAt1256 : keyMomentRows (1256 : Fin 2886) =
    keyMomentRow1256 := by decide +kernel

theorem keyMomentRowsAt1257 : keyMomentRows (1257 : Fin 2886) =
    keyMomentRow1257 := by decide +kernel

theorem keyMomentRowsAt1258 : keyMomentRows (1258 : Fin 2886) =
    keyMomentRow1258 := by decide +kernel

theorem keyMomentRowsAt1259 : keyMomentRows (1259 : Fin 2886) =
    keyMomentRow1259 := by decide +kernel

theorem keyMomentRowsAt1260 : keyMomentRows (1260 : Fin 2886) =
    keyMomentRow1260 := by decide +kernel

theorem keyMomentRowsAt1261 : keyMomentRows (1261 : Fin 2886) =
    keyMomentRow1261 := by decide +kernel

theorem keyMomentRowsAt1262 : keyMomentRows (1262 : Fin 2886) =
    keyMomentRow1262 := by decide +kernel

theorem keyMomentRowsAt1263 : keyMomentRows (1263 : Fin 2886) =
    keyMomentRow1263 := by decide +kernel

theorem keyMomentRowsAt1264 : keyMomentRows (1264 : Fin 2886) =
    keyMomentRow1264 := by decide +kernel

theorem keyMomentRowsAt1265 : keyMomentRows (1265 : Fin 2886) =
    keyMomentRow1265 := by decide +kernel

theorem keyMomentRowsAt1266 : keyMomentRows (1266 : Fin 2886) =
    keyMomentRow1266 := by decide +kernel

theorem keyMomentRowsAt1267 : keyMomentRows (1267 : Fin 2886) =
    keyMomentRow1267 := by decide +kernel

theorem keyMomentRowsAt1268 : keyMomentRows (1268 : Fin 2886) =
    keyMomentRow1268 := by decide +kernel

theorem keyMomentRowsAt1269 : keyMomentRows (1269 : Fin 2886) =
    keyMomentRow1269 := by decide +kernel

theorem keyMomentRowsAt1270 : keyMomentRows (1270 : Fin 2886) =
    keyMomentRow1270 := by decide +kernel

theorem keyMomentRowsAt1271 : keyMomentRows (1271 : Fin 2886) =
    keyMomentRow1271 := by decide +kernel

theorem keyMomentRowsAt1272 : keyMomentRows (1272 : Fin 2886) =
    keyMomentRow1272 := by decide +kernel

theorem keyMomentRowsAt1273 : keyMomentRows (1273 : Fin 2886) =
    keyMomentRow1273 := by decide +kernel

theorem keyMomentRowsAt1274 : keyMomentRows (1274 : Fin 2886) =
    keyMomentRow1274 := by decide +kernel

theorem keyMomentRowsAt1275 : keyMomentRows (1275 : Fin 2886) =
    keyMomentRow1275 := by decide +kernel

theorem keyMomentRowsAt1276 : keyMomentRows (1276 : Fin 2886) =
    keyMomentRow1276 := by decide +kernel

theorem keyMomentRowsAt1277 : keyMomentRows (1277 : Fin 2886) =
    keyMomentRow1277 := by decide +kernel

theorem keyMomentRowsAt1278 : keyMomentRows (1278 : Fin 2886) =
    keyMomentRow1278 := by decide +kernel

theorem keyMomentRowsAt1279 : keyMomentRows (1279 : Fin 2886) =
    keyMomentRow1279 := by decide +kernel

theorem keyMomentChunkSound39 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 39) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1248 ∨ k.val = 1249 ∨ k.val = 1250 ∨ k.val = 1251 ∨ k.val = 1252 ∨ k.val = 1253 ∨ k.val = 1254 ∨ k.val = 1255 ∨ k.val = 1256 ∨ k.val = 1257 ∨ k.val = 1258 ∨ k.val = 1259 ∨ k.val = 1260 ∨ k.val = 1261 ∨ k.val = 1262 ∨ k.val = 1263 ∨ k.val = 1264 ∨ k.val = 1265 ∨ k.val = 1266 ∨ k.val = 1267 ∨ k.val = 1268 ∨ k.val = 1269 ∨ k.val = 1270 ∨ k.val = 1271 ∨ k.val = 1272 ∨ k.val = 1273 ∨ k.val = 1274 ∨ k.val = 1275 ∨ k.val = 1276 ∨ k.val = 1277 ∨ k.val = 1278 ∨ k.val = 1279 := by omega
  rcases heq with h1248 | h1249 | h1250 | h1251 | h1252 | h1253 | h1254 | h1255 | h1256 | h1257 | h1258 | h1259 | h1260 | h1261 | h1262 | h1263 | h1264 | h1265 | h1266 | h1267 | h1268 | h1269 | h1270 | h1271 | h1272 | h1273 | h1274 | h1275 | h1276 | h1277 | h1278 | h1279
  · have he : k = (1248 : Fin 2886) := Fin.ext h1248
    subst k
    rw [keyMomentRowsAt1248]
    exact keyMoment1248 B hB
  · have he : k = (1249 : Fin 2886) := Fin.ext h1249
    subst k
    rw [keyMomentRowsAt1249]
    exact keyMoment1249 B hB
  · have he : k = (1250 : Fin 2886) := Fin.ext h1250
    subst k
    rw [keyMomentRowsAt1250]
    exact keyMoment1250 B hB
  · have he : k = (1251 : Fin 2886) := Fin.ext h1251
    subst k
    rw [keyMomentRowsAt1251]
    exact keyMoment1251 B hB
  · have he : k = (1252 : Fin 2886) := Fin.ext h1252
    subst k
    rw [keyMomentRowsAt1252]
    exact keyMoment1252 B hB
  · have he : k = (1253 : Fin 2886) := Fin.ext h1253
    subst k
    rw [keyMomentRowsAt1253]
    exact keyMoment1253 B hB
  · have he : k = (1254 : Fin 2886) := Fin.ext h1254
    subst k
    rw [keyMomentRowsAt1254]
    exact keyMoment1254 B hB
  · have he : k = (1255 : Fin 2886) := Fin.ext h1255
    subst k
    rw [keyMomentRowsAt1255]
    exact keyMoment1255 B hB
  · have he : k = (1256 : Fin 2886) := Fin.ext h1256
    subst k
    rw [keyMomentRowsAt1256]
    exact keyMoment1256 B hB
  · have he : k = (1257 : Fin 2886) := Fin.ext h1257
    subst k
    rw [keyMomentRowsAt1257]
    exact keyMoment1257 B hB
  · have he : k = (1258 : Fin 2886) := Fin.ext h1258
    subst k
    rw [keyMomentRowsAt1258]
    exact keyMoment1258 B hB
  · have he : k = (1259 : Fin 2886) := Fin.ext h1259
    subst k
    rw [keyMomentRowsAt1259]
    exact keyMoment1259 B hB
  · have he : k = (1260 : Fin 2886) := Fin.ext h1260
    subst k
    rw [keyMomentRowsAt1260]
    exact keyMoment1260 B hB
  · have he : k = (1261 : Fin 2886) := Fin.ext h1261
    subst k
    rw [keyMomentRowsAt1261]
    exact keyMoment1261 B hB
  · have he : k = (1262 : Fin 2886) := Fin.ext h1262
    subst k
    rw [keyMomentRowsAt1262]
    exact keyMoment1262 B hB
  · have he : k = (1263 : Fin 2886) := Fin.ext h1263
    subst k
    rw [keyMomentRowsAt1263]
    exact keyMoment1263 B hB
  · have he : k = (1264 : Fin 2886) := Fin.ext h1264
    subst k
    rw [keyMomentRowsAt1264]
    exact keyMoment1264 B hB
  · have he : k = (1265 : Fin 2886) := Fin.ext h1265
    subst k
    rw [keyMomentRowsAt1265]
    exact keyMoment1265 B hB
  · have he : k = (1266 : Fin 2886) := Fin.ext h1266
    subst k
    rw [keyMomentRowsAt1266]
    exact keyMoment1266 B hB
  · have he : k = (1267 : Fin 2886) := Fin.ext h1267
    subst k
    rw [keyMomentRowsAt1267]
    exact keyMoment1267 B hB
  · have he : k = (1268 : Fin 2886) := Fin.ext h1268
    subst k
    rw [keyMomentRowsAt1268]
    exact keyMoment1268 B hB
  · have he : k = (1269 : Fin 2886) := Fin.ext h1269
    subst k
    rw [keyMomentRowsAt1269]
    exact keyMoment1269 B hB
  · have he : k = (1270 : Fin 2886) := Fin.ext h1270
    subst k
    rw [keyMomentRowsAt1270]
    exact keyMoment1270 B hB
  · have he : k = (1271 : Fin 2886) := Fin.ext h1271
    subst k
    rw [keyMomentRowsAt1271]
    exact keyMoment1271 B hB
  · have he : k = (1272 : Fin 2886) := Fin.ext h1272
    subst k
    rw [keyMomentRowsAt1272]
    exact keyMoment1272 B hB
  · have he : k = (1273 : Fin 2886) := Fin.ext h1273
    subst k
    rw [keyMomentRowsAt1273]
    exact keyMoment1273 B hB
  · have he : k = (1274 : Fin 2886) := Fin.ext h1274
    subst k
    rw [keyMomentRowsAt1274]
    exact keyMoment1274 B hB
  · have he : k = (1275 : Fin 2886) := Fin.ext h1275
    subst k
    rw [keyMomentRowsAt1275]
    exact keyMoment1275 B hB
  · have he : k = (1276 : Fin 2886) := Fin.ext h1276
    subst k
    rw [keyMomentRowsAt1276]
    exact keyMoment1276 B hB
  · have he : k = (1277 : Fin 2886) := Fin.ext h1277
    subst k
    rw [keyMomentRowsAt1277]
    exact keyMoment1277 B hB
  · have he : k = (1278 : Fin 2886) := Fin.ext h1278
    subst k
    rw [keyMomentRowsAt1278]
    exact keyMoment1278 B hB
  · have he : k = (1279 : Fin 2886) := Fin.ext h1279
    subst k
    rw [keyMomentRowsAt1279]
    exact keyMoment1279 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
