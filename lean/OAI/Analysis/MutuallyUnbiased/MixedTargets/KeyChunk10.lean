import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound10
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt320 : keyMomentRows (320 : Fin 2886) =
    keyMomentRow320 := by decide +kernel

theorem keyMomentRowsAt321 : keyMomentRows (321 : Fin 2886) =
    keyMomentRow321 := by decide +kernel

theorem keyMomentRowsAt322 : keyMomentRows (322 : Fin 2886) =
    keyMomentRow322 := by decide +kernel

theorem keyMomentRowsAt323 : keyMomentRows (323 : Fin 2886) =
    keyMomentRow323 := by decide +kernel

theorem keyMomentRowsAt324 : keyMomentRows (324 : Fin 2886) =
    keyMomentRow324 := by decide +kernel

theorem keyMomentRowsAt325 : keyMomentRows (325 : Fin 2886) =
    keyMomentRow325 := by decide +kernel

theorem keyMomentRowsAt326 : keyMomentRows (326 : Fin 2886) =
    keyMomentRow326 := by decide +kernel

theorem keyMomentRowsAt327 : keyMomentRows (327 : Fin 2886) =
    keyMomentRow327 := by decide +kernel

theorem keyMomentRowsAt328 : keyMomentRows (328 : Fin 2886) =
    keyMomentRow328 := by decide +kernel

theorem keyMomentRowsAt329 : keyMomentRows (329 : Fin 2886) =
    keyMomentRow329 := by decide +kernel

theorem keyMomentRowsAt330 : keyMomentRows (330 : Fin 2886) =
    keyMomentRow330 := by decide +kernel

theorem keyMomentRowsAt331 : keyMomentRows (331 : Fin 2886) =
    keyMomentRow331 := by decide +kernel

theorem keyMomentRowsAt332 : keyMomentRows (332 : Fin 2886) =
    keyMomentRow332 := by decide +kernel

theorem keyMomentRowsAt333 : keyMomentRows (333 : Fin 2886) =
    keyMomentRow333 := by decide +kernel

theorem keyMomentRowsAt334 : keyMomentRows (334 : Fin 2886) =
    keyMomentRow334 := by decide +kernel

theorem keyMomentRowsAt335 : keyMomentRows (335 : Fin 2886) =
    keyMomentRow335 := by decide +kernel

theorem keyMomentRowsAt336 : keyMomentRows (336 : Fin 2886) =
    keyMomentRow336 := by decide +kernel

theorem keyMomentRowsAt337 : keyMomentRows (337 : Fin 2886) =
    keyMomentRow337 := by decide +kernel

theorem keyMomentRowsAt338 : keyMomentRows (338 : Fin 2886) =
    keyMomentRow338 := by decide +kernel

theorem keyMomentRowsAt339 : keyMomentRows (339 : Fin 2886) =
    keyMomentRow339 := by decide +kernel

theorem keyMomentRowsAt340 : keyMomentRows (340 : Fin 2886) =
    keyMomentRow340 := by decide +kernel

theorem keyMomentRowsAt341 : keyMomentRows (341 : Fin 2886) =
    keyMomentRow341 := by decide +kernel

theorem keyMomentRowsAt342 : keyMomentRows (342 : Fin 2886) =
    keyMomentRow342 := by decide +kernel

theorem keyMomentRowsAt343 : keyMomentRows (343 : Fin 2886) =
    keyMomentRow343 := by decide +kernel

theorem keyMomentRowsAt344 : keyMomentRows (344 : Fin 2886) =
    keyMomentRow344 := by decide +kernel

theorem keyMomentRowsAt345 : keyMomentRows (345 : Fin 2886) =
    keyMomentRow345 := by decide +kernel

theorem keyMomentRowsAt346 : keyMomentRows (346 : Fin 2886) =
    keyMomentRow346 := by decide +kernel

theorem keyMomentRowsAt347 : keyMomentRows (347 : Fin 2886) =
    keyMomentRow347 := by decide +kernel

theorem keyMomentRowsAt348 : keyMomentRows (348 : Fin 2886) =
    keyMomentRow348 := by decide +kernel

theorem keyMomentRowsAt349 : keyMomentRows (349 : Fin 2886) =
    keyMomentRow349 := by decide +kernel

theorem keyMomentRowsAt350 : keyMomentRows (350 : Fin 2886) =
    keyMomentRow350 := by decide +kernel

theorem keyMomentRowsAt351 : keyMomentRows (351 : Fin 2886) =
    keyMomentRow351 := by decide +kernel

theorem keyMomentChunkSound10 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 10) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 320 ∨ k.val = 321 ∨ k.val = 322 ∨ k.val = 323 ∨ k.val = 324 ∨ k.val = 325 ∨ k.val = 326 ∨ k.val = 327 ∨ k.val = 328 ∨ k.val = 329 ∨ k.val = 330 ∨ k.val = 331 ∨ k.val = 332 ∨ k.val = 333 ∨ k.val = 334 ∨ k.val = 335 ∨ k.val = 336 ∨ k.val = 337 ∨ k.val = 338 ∨ k.val = 339 ∨ k.val = 340 ∨ k.val = 341 ∨ k.val = 342 ∨ k.val = 343 ∨ k.val = 344 ∨ k.val = 345 ∨ k.val = 346 ∨ k.val = 347 ∨ k.val = 348 ∨ k.val = 349 ∨ k.val = 350 ∨ k.val = 351 := by omega
  rcases heq with h320 | h321 | h322 | h323 | h324 | h325 | h326 | h327 | h328 | h329 | h330 | h331 | h332 | h333 | h334 | h335 | h336 | h337 | h338 | h339 | h340 | h341 | h342 | h343 | h344 | h345 | h346 | h347 | h348 | h349 | h350 | h351
  · have he : k = (320 : Fin 2886) := Fin.ext h320
    subst k
    rw [keyMomentRowsAt320]
    exact keyMoment320 B hB
  · have he : k = (321 : Fin 2886) := Fin.ext h321
    subst k
    rw [keyMomentRowsAt321]
    exact keyMoment321 B hB
  · have he : k = (322 : Fin 2886) := Fin.ext h322
    subst k
    rw [keyMomentRowsAt322]
    exact keyMoment322 B hB
  · have he : k = (323 : Fin 2886) := Fin.ext h323
    subst k
    rw [keyMomentRowsAt323]
    exact keyMoment323 B hB
  · have he : k = (324 : Fin 2886) := Fin.ext h324
    subst k
    rw [keyMomentRowsAt324]
    exact keyMoment324 B hB
  · have he : k = (325 : Fin 2886) := Fin.ext h325
    subst k
    rw [keyMomentRowsAt325]
    exact keyMoment325 B hB
  · have he : k = (326 : Fin 2886) := Fin.ext h326
    subst k
    rw [keyMomentRowsAt326]
    exact keyMoment326 B hB
  · have he : k = (327 : Fin 2886) := Fin.ext h327
    subst k
    rw [keyMomentRowsAt327]
    exact keyMoment327 B hB
  · have he : k = (328 : Fin 2886) := Fin.ext h328
    subst k
    rw [keyMomentRowsAt328]
    exact keyMoment328 B hB
  · have he : k = (329 : Fin 2886) := Fin.ext h329
    subst k
    rw [keyMomentRowsAt329]
    exact keyMoment329 B hB
  · have he : k = (330 : Fin 2886) := Fin.ext h330
    subst k
    rw [keyMomentRowsAt330]
    exact keyMoment330 B hB
  · have he : k = (331 : Fin 2886) := Fin.ext h331
    subst k
    rw [keyMomentRowsAt331]
    exact keyMoment331 B hB
  · have he : k = (332 : Fin 2886) := Fin.ext h332
    subst k
    rw [keyMomentRowsAt332]
    exact keyMoment332 B hB
  · have he : k = (333 : Fin 2886) := Fin.ext h333
    subst k
    rw [keyMomentRowsAt333]
    exact keyMoment333 B hB
  · have he : k = (334 : Fin 2886) := Fin.ext h334
    subst k
    rw [keyMomentRowsAt334]
    exact keyMoment334 B hB
  · have he : k = (335 : Fin 2886) := Fin.ext h335
    subst k
    rw [keyMomentRowsAt335]
    exact keyMoment335 B hB
  · have he : k = (336 : Fin 2886) := Fin.ext h336
    subst k
    rw [keyMomentRowsAt336]
    exact keyMoment336 B hB
  · have he : k = (337 : Fin 2886) := Fin.ext h337
    subst k
    rw [keyMomentRowsAt337]
    exact keyMoment337 B hB
  · have he : k = (338 : Fin 2886) := Fin.ext h338
    subst k
    rw [keyMomentRowsAt338]
    exact keyMoment338 B hB
  · have he : k = (339 : Fin 2886) := Fin.ext h339
    subst k
    rw [keyMomentRowsAt339]
    exact keyMoment339 B hB
  · have he : k = (340 : Fin 2886) := Fin.ext h340
    subst k
    rw [keyMomentRowsAt340]
    exact keyMoment340 B hB
  · have he : k = (341 : Fin 2886) := Fin.ext h341
    subst k
    rw [keyMomentRowsAt341]
    exact keyMoment341 B hB
  · have he : k = (342 : Fin 2886) := Fin.ext h342
    subst k
    rw [keyMomentRowsAt342]
    exact keyMoment342 B hB
  · have he : k = (343 : Fin 2886) := Fin.ext h343
    subst k
    rw [keyMomentRowsAt343]
    exact keyMoment343 B hB
  · have he : k = (344 : Fin 2886) := Fin.ext h344
    subst k
    rw [keyMomentRowsAt344]
    exact keyMoment344 B hB
  · have he : k = (345 : Fin 2886) := Fin.ext h345
    subst k
    rw [keyMomentRowsAt345]
    exact keyMoment345 B hB
  · have he : k = (346 : Fin 2886) := Fin.ext h346
    subst k
    rw [keyMomentRowsAt346]
    exact keyMoment346 B hB
  · have he : k = (347 : Fin 2886) := Fin.ext h347
    subst k
    rw [keyMomentRowsAt347]
    exact keyMoment347 B hB
  · have he : k = (348 : Fin 2886) := Fin.ext h348
    subst k
    rw [keyMomentRowsAt348]
    exact keyMoment348 B hB
  · have he : k = (349 : Fin 2886) := Fin.ext h349
    subst k
    rw [keyMomentRowsAt349]
    exact keyMoment349 B hB
  · have he : k = (350 : Fin 2886) := Fin.ext h350
    subst k
    rw [keyMomentRowsAt350]
    exact keyMoment350 B hB
  · have he : k = (351 : Fin 2886) := Fin.ext h351
    subst k
    rw [keyMomentRowsAt351]
    exact keyMoment351 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
