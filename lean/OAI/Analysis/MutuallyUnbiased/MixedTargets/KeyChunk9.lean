import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound9
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt288 : keyMomentRows (288 : Fin 2886) =
    keyMomentRow288 := by decide +kernel

theorem keyMomentRowsAt289 : keyMomentRows (289 : Fin 2886) =
    keyMomentRow289 := by decide +kernel

theorem keyMomentRowsAt290 : keyMomentRows (290 : Fin 2886) =
    keyMomentRow290 := by decide +kernel

theorem keyMomentRowsAt291 : keyMomentRows (291 : Fin 2886) =
    keyMomentRow291 := by decide +kernel

theorem keyMomentRowsAt292 : keyMomentRows (292 : Fin 2886) =
    keyMomentRow292 := by decide +kernel

theorem keyMomentRowsAt293 : keyMomentRows (293 : Fin 2886) =
    keyMomentRow293 := by decide +kernel

theorem keyMomentRowsAt294 : keyMomentRows (294 : Fin 2886) =
    keyMomentRow294 := by decide +kernel

theorem keyMomentRowsAt295 : keyMomentRows (295 : Fin 2886) =
    keyMomentRow295 := by decide +kernel

theorem keyMomentRowsAt296 : keyMomentRows (296 : Fin 2886) =
    keyMomentRow296 := by decide +kernel

theorem keyMomentRowsAt297 : keyMomentRows (297 : Fin 2886) =
    keyMomentRow297 := by decide +kernel

theorem keyMomentRowsAt298 : keyMomentRows (298 : Fin 2886) =
    keyMomentRow298 := by decide +kernel

theorem keyMomentRowsAt299 : keyMomentRows (299 : Fin 2886) =
    keyMomentRow299 := by decide +kernel

theorem keyMomentRowsAt300 : keyMomentRows (300 : Fin 2886) =
    keyMomentRow300 := by decide +kernel

theorem keyMomentRowsAt301 : keyMomentRows (301 : Fin 2886) =
    keyMomentRow301 := by decide +kernel

theorem keyMomentRowsAt302 : keyMomentRows (302 : Fin 2886) =
    keyMomentRow302 := by decide +kernel

theorem keyMomentRowsAt303 : keyMomentRows (303 : Fin 2886) =
    keyMomentRow303 := by decide +kernel

theorem keyMomentRowsAt304 : keyMomentRows (304 : Fin 2886) =
    keyMomentRow304 := by decide +kernel

theorem keyMomentRowsAt305 : keyMomentRows (305 : Fin 2886) =
    keyMomentRow305 := by decide +kernel

theorem keyMomentRowsAt306 : keyMomentRows (306 : Fin 2886) =
    keyMomentRow306 := by decide +kernel

theorem keyMomentRowsAt307 : keyMomentRows (307 : Fin 2886) =
    keyMomentRow307 := by decide +kernel

theorem keyMomentRowsAt308 : keyMomentRows (308 : Fin 2886) =
    keyMomentRow308 := by decide +kernel

theorem keyMomentRowsAt309 : keyMomentRows (309 : Fin 2886) =
    keyMomentRow309 := by decide +kernel

theorem keyMomentRowsAt310 : keyMomentRows (310 : Fin 2886) =
    keyMomentRow310 := by decide +kernel

theorem keyMomentRowsAt311 : keyMomentRows (311 : Fin 2886) =
    keyMomentRow311 := by decide +kernel

theorem keyMomentRowsAt312 : keyMomentRows (312 : Fin 2886) =
    keyMomentRow312 := by decide +kernel

theorem keyMomentRowsAt313 : keyMomentRows (313 : Fin 2886) =
    keyMomentRow313 := by decide +kernel

theorem keyMomentRowsAt314 : keyMomentRows (314 : Fin 2886) =
    keyMomentRow314 := by decide +kernel

theorem keyMomentRowsAt315 : keyMomentRows (315 : Fin 2886) =
    keyMomentRow315 := by decide +kernel

theorem keyMomentRowsAt316 : keyMomentRows (316 : Fin 2886) =
    keyMomentRow316 := by decide +kernel

theorem keyMomentRowsAt317 : keyMomentRows (317 : Fin 2886) =
    keyMomentRow317 := by decide +kernel

theorem keyMomentRowsAt318 : keyMomentRows (318 : Fin 2886) =
    keyMomentRow318 := by decide +kernel

theorem keyMomentRowsAt319 : keyMomentRows (319 : Fin 2886) =
    keyMomentRow319 := by decide +kernel

theorem keyMomentChunkSound9 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 9) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 288 ∨ k.val = 289 ∨ k.val = 290 ∨ k.val = 291 ∨ k.val = 292 ∨ k.val = 293 ∨ k.val = 294 ∨ k.val = 295 ∨ k.val = 296 ∨ k.val = 297 ∨ k.val = 298 ∨ k.val = 299 ∨ k.val = 300 ∨ k.val = 301 ∨ k.val = 302 ∨ k.val = 303 ∨ k.val = 304 ∨ k.val = 305 ∨ k.val = 306 ∨ k.val = 307 ∨ k.val = 308 ∨ k.val = 309 ∨ k.val = 310 ∨ k.val = 311 ∨ k.val = 312 ∨ k.val = 313 ∨ k.val = 314 ∨ k.val = 315 ∨ k.val = 316 ∨ k.val = 317 ∨ k.val = 318 ∨ k.val = 319 := by omega
  rcases heq with h288 | h289 | h290 | h291 | h292 | h293 | h294 | h295 | h296 | h297 | h298 | h299 | h300 | h301 | h302 | h303 | h304 | h305 | h306 | h307 | h308 | h309 | h310 | h311 | h312 | h313 | h314 | h315 | h316 | h317 | h318 | h319
  · have he : k = (288 : Fin 2886) := Fin.ext h288
    subst k
    rw [keyMomentRowsAt288]
    exact keyMoment288 B hB
  · have he : k = (289 : Fin 2886) := Fin.ext h289
    subst k
    rw [keyMomentRowsAt289]
    exact keyMoment289 B hB
  · have he : k = (290 : Fin 2886) := Fin.ext h290
    subst k
    rw [keyMomentRowsAt290]
    exact keyMoment290 B hB
  · have he : k = (291 : Fin 2886) := Fin.ext h291
    subst k
    rw [keyMomentRowsAt291]
    exact keyMoment291 B hB
  · have he : k = (292 : Fin 2886) := Fin.ext h292
    subst k
    rw [keyMomentRowsAt292]
    exact keyMoment292 B hB
  · have he : k = (293 : Fin 2886) := Fin.ext h293
    subst k
    rw [keyMomentRowsAt293]
    exact keyMoment293 B hB
  · have he : k = (294 : Fin 2886) := Fin.ext h294
    subst k
    rw [keyMomentRowsAt294]
    exact keyMoment294 B hB
  · have he : k = (295 : Fin 2886) := Fin.ext h295
    subst k
    rw [keyMomentRowsAt295]
    exact keyMoment295 B hB
  · have he : k = (296 : Fin 2886) := Fin.ext h296
    subst k
    rw [keyMomentRowsAt296]
    exact keyMoment296 B hB
  · have he : k = (297 : Fin 2886) := Fin.ext h297
    subst k
    rw [keyMomentRowsAt297]
    exact keyMoment297 B hB
  · have he : k = (298 : Fin 2886) := Fin.ext h298
    subst k
    rw [keyMomentRowsAt298]
    exact keyMoment298 B hB
  · have he : k = (299 : Fin 2886) := Fin.ext h299
    subst k
    rw [keyMomentRowsAt299]
    exact keyMoment299 B hB
  · have he : k = (300 : Fin 2886) := Fin.ext h300
    subst k
    rw [keyMomentRowsAt300]
    exact keyMoment300 B hB
  · have he : k = (301 : Fin 2886) := Fin.ext h301
    subst k
    rw [keyMomentRowsAt301]
    exact keyMoment301 B hB
  · have he : k = (302 : Fin 2886) := Fin.ext h302
    subst k
    rw [keyMomentRowsAt302]
    exact keyMoment302 B hB
  · have he : k = (303 : Fin 2886) := Fin.ext h303
    subst k
    rw [keyMomentRowsAt303]
    exact keyMoment303 B hB
  · have he : k = (304 : Fin 2886) := Fin.ext h304
    subst k
    rw [keyMomentRowsAt304]
    exact keyMoment304 B hB
  · have he : k = (305 : Fin 2886) := Fin.ext h305
    subst k
    rw [keyMomentRowsAt305]
    exact keyMoment305 B hB
  · have he : k = (306 : Fin 2886) := Fin.ext h306
    subst k
    rw [keyMomentRowsAt306]
    exact keyMoment306 B hB
  · have he : k = (307 : Fin 2886) := Fin.ext h307
    subst k
    rw [keyMomentRowsAt307]
    exact keyMoment307 B hB
  · have he : k = (308 : Fin 2886) := Fin.ext h308
    subst k
    rw [keyMomentRowsAt308]
    exact keyMoment308 B hB
  · have he : k = (309 : Fin 2886) := Fin.ext h309
    subst k
    rw [keyMomentRowsAt309]
    exact keyMoment309 B hB
  · have he : k = (310 : Fin 2886) := Fin.ext h310
    subst k
    rw [keyMomentRowsAt310]
    exact keyMoment310 B hB
  · have he : k = (311 : Fin 2886) := Fin.ext h311
    subst k
    rw [keyMomentRowsAt311]
    exact keyMoment311 B hB
  · have he : k = (312 : Fin 2886) := Fin.ext h312
    subst k
    rw [keyMomentRowsAt312]
    exact keyMoment312 B hB
  · have he : k = (313 : Fin 2886) := Fin.ext h313
    subst k
    rw [keyMomentRowsAt313]
    exact keyMoment313 B hB
  · have he : k = (314 : Fin 2886) := Fin.ext h314
    subst k
    rw [keyMomentRowsAt314]
    exact keyMoment314 B hB
  · have he : k = (315 : Fin 2886) := Fin.ext h315
    subst k
    rw [keyMomentRowsAt315]
    exact keyMoment315 B hB
  · have he : k = (316 : Fin 2886) := Fin.ext h316
    subst k
    rw [keyMomentRowsAt316]
    exact keyMoment316 B hB
  · have he : k = (317 : Fin 2886) := Fin.ext h317
    subst k
    rw [keyMomentRowsAt317]
    exact keyMoment317 B hB
  · have he : k = (318 : Fin 2886) := Fin.ext h318
    subst k
    rw [keyMomentRowsAt318]
    exact keyMoment318 B hB
  · have he : k = (319 : Fin 2886) := Fin.ext h319
    subst k
    rw [keyMomentRowsAt319]
    exact keyMoment319 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
