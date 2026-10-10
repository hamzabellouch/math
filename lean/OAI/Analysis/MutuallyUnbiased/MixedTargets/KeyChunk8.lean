import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound8
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt256 : keyMomentRows (256 : Fin 2886) =
    keyMomentRow256 := by decide +kernel

theorem keyMomentRowsAt257 : keyMomentRows (257 : Fin 2886) =
    keyMomentRow257 := by decide +kernel

theorem keyMomentRowsAt258 : keyMomentRows (258 : Fin 2886) =
    keyMomentRow258 := by decide +kernel

theorem keyMomentRowsAt259 : keyMomentRows (259 : Fin 2886) =
    keyMomentRow259 := by decide +kernel

theorem keyMomentRowsAt260 : keyMomentRows (260 : Fin 2886) =
    keyMomentRow260 := by decide +kernel

theorem keyMomentRowsAt261 : keyMomentRows (261 : Fin 2886) =
    keyMomentRow261 := by decide +kernel

theorem keyMomentRowsAt262 : keyMomentRows (262 : Fin 2886) =
    keyMomentRow262 := by decide +kernel

theorem keyMomentRowsAt263 : keyMomentRows (263 : Fin 2886) =
    keyMomentRow263 := by decide +kernel

theorem keyMomentRowsAt264 : keyMomentRows (264 : Fin 2886) =
    keyMomentRow264 := by decide +kernel

theorem keyMomentRowsAt265 : keyMomentRows (265 : Fin 2886) =
    keyMomentRow265 := by decide +kernel

theorem keyMomentRowsAt266 : keyMomentRows (266 : Fin 2886) =
    keyMomentRow266 := by decide +kernel

theorem keyMomentRowsAt267 : keyMomentRows (267 : Fin 2886) =
    keyMomentRow267 := by decide +kernel

theorem keyMomentRowsAt268 : keyMomentRows (268 : Fin 2886) =
    keyMomentRow268 := by decide +kernel

theorem keyMomentRowsAt269 : keyMomentRows (269 : Fin 2886) =
    keyMomentRow269 := by decide +kernel

theorem keyMomentRowsAt270 : keyMomentRows (270 : Fin 2886) =
    keyMomentRow270 := by decide +kernel

theorem keyMomentRowsAt271 : keyMomentRows (271 : Fin 2886) =
    keyMomentRow271 := by decide +kernel

theorem keyMomentRowsAt272 : keyMomentRows (272 : Fin 2886) =
    keyMomentRow272 := by decide +kernel

theorem keyMomentRowsAt273 : keyMomentRows (273 : Fin 2886) =
    keyMomentRow273 := by decide +kernel

theorem keyMomentRowsAt274 : keyMomentRows (274 : Fin 2886) =
    keyMomentRow274 := by decide +kernel

theorem keyMomentRowsAt275 : keyMomentRows (275 : Fin 2886) =
    keyMomentRow275 := by decide +kernel

theorem keyMomentRowsAt276 : keyMomentRows (276 : Fin 2886) =
    keyMomentRow276 := by decide +kernel

theorem keyMomentRowsAt277 : keyMomentRows (277 : Fin 2886) =
    keyMomentRow277 := by decide +kernel

theorem keyMomentRowsAt278 : keyMomentRows (278 : Fin 2886) =
    keyMomentRow278 := by decide +kernel

theorem keyMomentRowsAt279 : keyMomentRows (279 : Fin 2886) =
    keyMomentRow279 := by decide +kernel

theorem keyMomentRowsAt280 : keyMomentRows (280 : Fin 2886) =
    keyMomentRow280 := by decide +kernel

theorem keyMomentRowsAt281 : keyMomentRows (281 : Fin 2886) =
    keyMomentRow281 := by decide +kernel

theorem keyMomentRowsAt282 : keyMomentRows (282 : Fin 2886) =
    keyMomentRow282 := by decide +kernel

theorem keyMomentRowsAt283 : keyMomentRows (283 : Fin 2886) =
    keyMomentRow283 := by decide +kernel

theorem keyMomentRowsAt284 : keyMomentRows (284 : Fin 2886) =
    keyMomentRow284 := by decide +kernel

theorem keyMomentRowsAt285 : keyMomentRows (285 : Fin 2886) =
    keyMomentRow285 := by decide +kernel

theorem keyMomentRowsAt286 : keyMomentRows (286 : Fin 2886) =
    keyMomentRow286 := by decide +kernel

theorem keyMomentRowsAt287 : keyMomentRows (287 : Fin 2886) =
    keyMomentRow287 := by decide +kernel

theorem keyMomentChunkSound8 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 8) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 256 ∨ k.val = 257 ∨ k.val = 258 ∨ k.val = 259 ∨ k.val = 260 ∨ k.val = 261 ∨ k.val = 262 ∨ k.val = 263 ∨ k.val = 264 ∨ k.val = 265 ∨ k.val = 266 ∨ k.val = 267 ∨ k.val = 268 ∨ k.val = 269 ∨ k.val = 270 ∨ k.val = 271 ∨ k.val = 272 ∨ k.val = 273 ∨ k.val = 274 ∨ k.val = 275 ∨ k.val = 276 ∨ k.val = 277 ∨ k.val = 278 ∨ k.val = 279 ∨ k.val = 280 ∨ k.val = 281 ∨ k.val = 282 ∨ k.val = 283 ∨ k.val = 284 ∨ k.val = 285 ∨ k.val = 286 ∨ k.val = 287 := by omega
  rcases heq with h256 | h257 | h258 | h259 | h260 | h261 | h262 | h263 | h264 | h265 | h266 | h267 | h268 | h269 | h270 | h271 | h272 | h273 | h274 | h275 | h276 | h277 | h278 | h279 | h280 | h281 | h282 | h283 | h284 | h285 | h286 | h287
  · have he : k = (256 : Fin 2886) := Fin.ext h256
    subst k
    rw [keyMomentRowsAt256]
    exact keyMoment256 B hB
  · have he : k = (257 : Fin 2886) := Fin.ext h257
    subst k
    rw [keyMomentRowsAt257]
    exact keyMoment257 B hB
  · have he : k = (258 : Fin 2886) := Fin.ext h258
    subst k
    rw [keyMomentRowsAt258]
    exact keyMoment258 B hB
  · have he : k = (259 : Fin 2886) := Fin.ext h259
    subst k
    rw [keyMomentRowsAt259]
    exact keyMoment259 B hB
  · have he : k = (260 : Fin 2886) := Fin.ext h260
    subst k
    rw [keyMomentRowsAt260]
    exact keyMoment260 B hB
  · have he : k = (261 : Fin 2886) := Fin.ext h261
    subst k
    rw [keyMomentRowsAt261]
    exact keyMoment261 B hB
  · have he : k = (262 : Fin 2886) := Fin.ext h262
    subst k
    rw [keyMomentRowsAt262]
    exact keyMoment262 B hB
  · have he : k = (263 : Fin 2886) := Fin.ext h263
    subst k
    rw [keyMomentRowsAt263]
    exact keyMoment263 B hB
  · have he : k = (264 : Fin 2886) := Fin.ext h264
    subst k
    rw [keyMomentRowsAt264]
    exact keyMoment264 B hB
  · have he : k = (265 : Fin 2886) := Fin.ext h265
    subst k
    rw [keyMomentRowsAt265]
    exact keyMoment265 B hB
  · have he : k = (266 : Fin 2886) := Fin.ext h266
    subst k
    rw [keyMomentRowsAt266]
    exact keyMoment266 B hB
  · have he : k = (267 : Fin 2886) := Fin.ext h267
    subst k
    rw [keyMomentRowsAt267]
    exact keyMoment267 B hB
  · have he : k = (268 : Fin 2886) := Fin.ext h268
    subst k
    rw [keyMomentRowsAt268]
    exact keyMoment268 B hB
  · have he : k = (269 : Fin 2886) := Fin.ext h269
    subst k
    rw [keyMomentRowsAt269]
    exact keyMoment269 B hB
  · have he : k = (270 : Fin 2886) := Fin.ext h270
    subst k
    rw [keyMomentRowsAt270]
    exact keyMoment270 B hB
  · have he : k = (271 : Fin 2886) := Fin.ext h271
    subst k
    rw [keyMomentRowsAt271]
    exact keyMoment271 B hB
  · have he : k = (272 : Fin 2886) := Fin.ext h272
    subst k
    rw [keyMomentRowsAt272]
    exact keyMoment272 B hB
  · have he : k = (273 : Fin 2886) := Fin.ext h273
    subst k
    rw [keyMomentRowsAt273]
    exact keyMoment273 B hB
  · have he : k = (274 : Fin 2886) := Fin.ext h274
    subst k
    rw [keyMomentRowsAt274]
    exact keyMoment274 B hB
  · have he : k = (275 : Fin 2886) := Fin.ext h275
    subst k
    rw [keyMomentRowsAt275]
    exact keyMoment275 B hB
  · have he : k = (276 : Fin 2886) := Fin.ext h276
    subst k
    rw [keyMomentRowsAt276]
    exact keyMoment276 B hB
  · have he : k = (277 : Fin 2886) := Fin.ext h277
    subst k
    rw [keyMomentRowsAt277]
    exact keyMoment277 B hB
  · have he : k = (278 : Fin 2886) := Fin.ext h278
    subst k
    rw [keyMomentRowsAt278]
    exact keyMoment278 B hB
  · have he : k = (279 : Fin 2886) := Fin.ext h279
    subst k
    rw [keyMomentRowsAt279]
    exact keyMoment279 B hB
  · have he : k = (280 : Fin 2886) := Fin.ext h280
    subst k
    rw [keyMomentRowsAt280]
    exact keyMoment280 B hB
  · have he : k = (281 : Fin 2886) := Fin.ext h281
    subst k
    rw [keyMomentRowsAt281]
    exact keyMoment281 B hB
  · have he : k = (282 : Fin 2886) := Fin.ext h282
    subst k
    rw [keyMomentRowsAt282]
    exact keyMoment282 B hB
  · have he : k = (283 : Fin 2886) := Fin.ext h283
    subst k
    rw [keyMomentRowsAt283]
    exact keyMoment283 B hB
  · have he : k = (284 : Fin 2886) := Fin.ext h284
    subst k
    rw [keyMomentRowsAt284]
    exact keyMoment284 B hB
  · have he : k = (285 : Fin 2886) := Fin.ext h285
    subst k
    rw [keyMomentRowsAt285]
    exact keyMoment285 B hB
  · have he : k = (286 : Fin 2886) := Fin.ext h286
    subst k
    rw [keyMomentRowsAt286]
    exact keyMoment286 B hB
  · have he : k = (287 : Fin 2886) := Fin.ext h287
    subst k
    rw [keyMomentRowsAt287]
    exact keyMoment287 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
