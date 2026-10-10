import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound11
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt352 : keyMomentRows (352 : Fin 2886) =
    keyMomentRow352 := by decide +kernel

theorem keyMomentRowsAt353 : keyMomentRows (353 : Fin 2886) =
    keyMomentRow353 := by decide +kernel

theorem keyMomentRowsAt354 : keyMomentRows (354 : Fin 2886) =
    keyMomentRow354 := by decide +kernel

theorem keyMomentRowsAt355 : keyMomentRows (355 : Fin 2886) =
    keyMomentRow355 := by decide +kernel

theorem keyMomentRowsAt356 : keyMomentRows (356 : Fin 2886) =
    keyMomentRow356 := by decide +kernel

theorem keyMomentRowsAt357 : keyMomentRows (357 : Fin 2886) =
    keyMomentRow357 := by decide +kernel

theorem keyMomentRowsAt358 : keyMomentRows (358 : Fin 2886) =
    keyMomentRow358 := by decide +kernel

theorem keyMomentRowsAt359 : keyMomentRows (359 : Fin 2886) =
    keyMomentRow359 := by decide +kernel

theorem keyMomentRowsAt360 : keyMomentRows (360 : Fin 2886) =
    keyMomentRow360 := by decide +kernel

theorem keyMomentRowsAt361 : keyMomentRows (361 : Fin 2886) =
    keyMomentRow361 := by decide +kernel

theorem keyMomentRowsAt362 : keyMomentRows (362 : Fin 2886) =
    keyMomentRow362 := by decide +kernel

theorem keyMomentRowsAt363 : keyMomentRows (363 : Fin 2886) =
    keyMomentRow363 := by decide +kernel

theorem keyMomentRowsAt364 : keyMomentRows (364 : Fin 2886) =
    keyMomentRow364 := by decide +kernel

theorem keyMomentRowsAt365 : keyMomentRows (365 : Fin 2886) =
    keyMomentRow365 := by decide +kernel

theorem keyMomentRowsAt366 : keyMomentRows (366 : Fin 2886) =
    keyMomentRow366 := by decide +kernel

theorem keyMomentRowsAt367 : keyMomentRows (367 : Fin 2886) =
    keyMomentRow367 := by decide +kernel

theorem keyMomentRowsAt368 : keyMomentRows (368 : Fin 2886) =
    keyMomentRow368 := by decide +kernel

theorem keyMomentRowsAt369 : keyMomentRows (369 : Fin 2886) =
    keyMomentRow369 := by decide +kernel

theorem keyMomentRowsAt370 : keyMomentRows (370 : Fin 2886) =
    keyMomentRow370 := by decide +kernel

theorem keyMomentRowsAt371 : keyMomentRows (371 : Fin 2886) =
    keyMomentRow371 := by decide +kernel

theorem keyMomentRowsAt372 : keyMomentRows (372 : Fin 2886) =
    keyMomentRow372 := by decide +kernel

theorem keyMomentRowsAt373 : keyMomentRows (373 : Fin 2886) =
    keyMomentRow373 := by decide +kernel

theorem keyMomentRowsAt374 : keyMomentRows (374 : Fin 2886) =
    keyMomentRow374 := by decide +kernel

theorem keyMomentRowsAt375 : keyMomentRows (375 : Fin 2886) =
    keyMomentRow375 := by decide +kernel

theorem keyMomentRowsAt376 : keyMomentRows (376 : Fin 2886) =
    keyMomentRow376 := by decide +kernel

theorem keyMomentRowsAt377 : keyMomentRows (377 : Fin 2886) =
    keyMomentRow377 := by decide +kernel

theorem keyMomentRowsAt378 : keyMomentRows (378 : Fin 2886) =
    keyMomentRow378 := by decide +kernel

theorem keyMomentRowsAt379 : keyMomentRows (379 : Fin 2886) =
    keyMomentRow379 := by decide +kernel

theorem keyMomentRowsAt380 : keyMomentRows (380 : Fin 2886) =
    keyMomentRow380 := by decide +kernel

theorem keyMomentRowsAt381 : keyMomentRows (381 : Fin 2886) =
    keyMomentRow381 := by decide +kernel

theorem keyMomentRowsAt382 : keyMomentRows (382 : Fin 2886) =
    keyMomentRow382 := by decide +kernel

theorem keyMomentRowsAt383 : keyMomentRows (383 : Fin 2886) =
    keyMomentRow383 := by decide +kernel

theorem keyMomentChunkSound11 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 11) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 352 ∨ k.val = 353 ∨ k.val = 354 ∨ k.val = 355 ∨ k.val = 356 ∨ k.val = 357 ∨ k.val = 358 ∨ k.val = 359 ∨ k.val = 360 ∨ k.val = 361 ∨ k.val = 362 ∨ k.val = 363 ∨ k.val = 364 ∨ k.val = 365 ∨ k.val = 366 ∨ k.val = 367 ∨ k.val = 368 ∨ k.val = 369 ∨ k.val = 370 ∨ k.val = 371 ∨ k.val = 372 ∨ k.val = 373 ∨ k.val = 374 ∨ k.val = 375 ∨ k.val = 376 ∨ k.val = 377 ∨ k.val = 378 ∨ k.val = 379 ∨ k.val = 380 ∨ k.val = 381 ∨ k.val = 382 ∨ k.val = 383 := by omega
  rcases heq with h352 | h353 | h354 | h355 | h356 | h357 | h358 | h359 | h360 | h361 | h362 | h363 | h364 | h365 | h366 | h367 | h368 | h369 | h370 | h371 | h372 | h373 | h374 | h375 | h376 | h377 | h378 | h379 | h380 | h381 | h382 | h383
  · have he : k = (352 : Fin 2886) := Fin.ext h352
    subst k
    rw [keyMomentRowsAt352]
    exact keyMoment352 B hB
  · have he : k = (353 : Fin 2886) := Fin.ext h353
    subst k
    rw [keyMomentRowsAt353]
    exact keyMoment353 B hB
  · have he : k = (354 : Fin 2886) := Fin.ext h354
    subst k
    rw [keyMomentRowsAt354]
    exact keyMoment354 B hB
  · have he : k = (355 : Fin 2886) := Fin.ext h355
    subst k
    rw [keyMomentRowsAt355]
    exact keyMoment355 B hB
  · have he : k = (356 : Fin 2886) := Fin.ext h356
    subst k
    rw [keyMomentRowsAt356]
    exact keyMoment356 B hB
  · have he : k = (357 : Fin 2886) := Fin.ext h357
    subst k
    rw [keyMomentRowsAt357]
    exact keyMoment357 B hB
  · have he : k = (358 : Fin 2886) := Fin.ext h358
    subst k
    rw [keyMomentRowsAt358]
    exact keyMoment358 B hB
  · have he : k = (359 : Fin 2886) := Fin.ext h359
    subst k
    rw [keyMomentRowsAt359]
    exact keyMoment359 B hB
  · have he : k = (360 : Fin 2886) := Fin.ext h360
    subst k
    rw [keyMomentRowsAt360]
    exact keyMoment360 B hB
  · have he : k = (361 : Fin 2886) := Fin.ext h361
    subst k
    rw [keyMomentRowsAt361]
    exact keyMoment361 B hB
  · have he : k = (362 : Fin 2886) := Fin.ext h362
    subst k
    rw [keyMomentRowsAt362]
    exact keyMoment362 B hB
  · have he : k = (363 : Fin 2886) := Fin.ext h363
    subst k
    rw [keyMomentRowsAt363]
    exact keyMoment363 B hB
  · have he : k = (364 : Fin 2886) := Fin.ext h364
    subst k
    rw [keyMomentRowsAt364]
    exact keyMoment364 B hB
  · have he : k = (365 : Fin 2886) := Fin.ext h365
    subst k
    rw [keyMomentRowsAt365]
    exact keyMoment365 B hB
  · have he : k = (366 : Fin 2886) := Fin.ext h366
    subst k
    rw [keyMomentRowsAt366]
    exact keyMoment366 B hB
  · have he : k = (367 : Fin 2886) := Fin.ext h367
    subst k
    rw [keyMomentRowsAt367]
    exact keyMoment367 B hB
  · have he : k = (368 : Fin 2886) := Fin.ext h368
    subst k
    rw [keyMomentRowsAt368]
    exact keyMoment368 B hB
  · have he : k = (369 : Fin 2886) := Fin.ext h369
    subst k
    rw [keyMomentRowsAt369]
    exact keyMoment369 B hB
  · have he : k = (370 : Fin 2886) := Fin.ext h370
    subst k
    rw [keyMomentRowsAt370]
    exact keyMoment370 B hB
  · have he : k = (371 : Fin 2886) := Fin.ext h371
    subst k
    rw [keyMomentRowsAt371]
    exact keyMoment371 B hB
  · have he : k = (372 : Fin 2886) := Fin.ext h372
    subst k
    rw [keyMomentRowsAt372]
    exact keyMoment372 B hB
  · have he : k = (373 : Fin 2886) := Fin.ext h373
    subst k
    rw [keyMomentRowsAt373]
    exact keyMoment373 B hB
  · have he : k = (374 : Fin 2886) := Fin.ext h374
    subst k
    rw [keyMomentRowsAt374]
    exact keyMoment374 B hB
  · have he : k = (375 : Fin 2886) := Fin.ext h375
    subst k
    rw [keyMomentRowsAt375]
    exact keyMoment375 B hB
  · have he : k = (376 : Fin 2886) := Fin.ext h376
    subst k
    rw [keyMomentRowsAt376]
    exact keyMoment376 B hB
  · have he : k = (377 : Fin 2886) := Fin.ext h377
    subst k
    rw [keyMomentRowsAt377]
    exact keyMoment377 B hB
  · have he : k = (378 : Fin 2886) := Fin.ext h378
    subst k
    rw [keyMomentRowsAt378]
    exact keyMoment378 B hB
  · have he : k = (379 : Fin 2886) := Fin.ext h379
    subst k
    rw [keyMomentRowsAt379]
    exact keyMoment379 B hB
  · have he : k = (380 : Fin 2886) := Fin.ext h380
    subst k
    rw [keyMomentRowsAt380]
    exact keyMoment380 B hB
  · have he : k = (381 : Fin 2886) := Fin.ext h381
    subst k
    rw [keyMomentRowsAt381]
    exact keyMoment381 B hB
  · have he : k = (382 : Fin 2886) := Fin.ext h382
    subst k
    rw [keyMomentRowsAt382]
    exact keyMoment382 B hB
  · have he : k = (383 : Fin 2886) := Fin.ext h383
    subst k
    rw [keyMomentRowsAt383]
    exact keyMoment383 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
