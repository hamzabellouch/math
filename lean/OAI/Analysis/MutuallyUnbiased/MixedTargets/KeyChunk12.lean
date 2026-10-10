import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound12
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt384 : keyMomentRows (384 : Fin 2886) =
    keyMomentRow384 := by decide +kernel

theorem keyMomentRowsAt385 : keyMomentRows (385 : Fin 2886) =
    keyMomentRow385 := by decide +kernel

theorem keyMomentRowsAt386 : keyMomentRows (386 : Fin 2886) =
    keyMomentRow386 := by decide +kernel

theorem keyMomentRowsAt387 : keyMomentRows (387 : Fin 2886) =
    keyMomentRow387 := by decide +kernel

theorem keyMomentRowsAt388 : keyMomentRows (388 : Fin 2886) =
    keyMomentRow388 := by decide +kernel

theorem keyMomentRowsAt389 : keyMomentRows (389 : Fin 2886) =
    keyMomentRow389 := by decide +kernel

theorem keyMomentRowsAt390 : keyMomentRows (390 : Fin 2886) =
    keyMomentRow390 := by decide +kernel

theorem keyMomentRowsAt391 : keyMomentRows (391 : Fin 2886) =
    keyMomentRow391 := by decide +kernel

theorem keyMomentRowsAt392 : keyMomentRows (392 : Fin 2886) =
    keyMomentRow392 := by decide +kernel

theorem keyMomentRowsAt393 : keyMomentRows (393 : Fin 2886) =
    keyMomentRow393 := by decide +kernel

theorem keyMomentRowsAt394 : keyMomentRows (394 : Fin 2886) =
    keyMomentRow394 := by decide +kernel

theorem keyMomentRowsAt395 : keyMomentRows (395 : Fin 2886) =
    keyMomentRow395 := by decide +kernel

theorem keyMomentRowsAt396 : keyMomentRows (396 : Fin 2886) =
    keyMomentRow396 := by decide +kernel

theorem keyMomentRowsAt397 : keyMomentRows (397 : Fin 2886) =
    keyMomentRow397 := by decide +kernel

theorem keyMomentRowsAt398 : keyMomentRows (398 : Fin 2886) =
    keyMomentRow398 := by decide +kernel

theorem keyMomentRowsAt399 : keyMomentRows (399 : Fin 2886) =
    keyMomentRow399 := by decide +kernel

theorem keyMomentRowsAt400 : keyMomentRows (400 : Fin 2886) =
    keyMomentRow400 := by decide +kernel

theorem keyMomentRowsAt401 : keyMomentRows (401 : Fin 2886) =
    keyMomentRow401 := by decide +kernel

theorem keyMomentRowsAt402 : keyMomentRows (402 : Fin 2886) =
    keyMomentRow402 := by decide +kernel

theorem keyMomentRowsAt403 : keyMomentRows (403 : Fin 2886) =
    keyMomentRow403 := by decide +kernel

theorem keyMomentRowsAt404 : keyMomentRows (404 : Fin 2886) =
    keyMomentRow404 := by decide +kernel

theorem keyMomentRowsAt405 : keyMomentRows (405 : Fin 2886) =
    keyMomentRow405 := by decide +kernel

theorem keyMomentRowsAt406 : keyMomentRows (406 : Fin 2886) =
    keyMomentRow406 := by decide +kernel

theorem keyMomentRowsAt407 : keyMomentRows (407 : Fin 2886) =
    keyMomentRow407 := by decide +kernel

theorem keyMomentRowsAt408 : keyMomentRows (408 : Fin 2886) =
    keyMomentRow408 := by decide +kernel

theorem keyMomentRowsAt409 : keyMomentRows (409 : Fin 2886) =
    keyMomentRow409 := by decide +kernel

theorem keyMomentRowsAt410 : keyMomentRows (410 : Fin 2886) =
    keyMomentRow410 := by decide +kernel

theorem keyMomentRowsAt411 : keyMomentRows (411 : Fin 2886) =
    keyMomentRow411 := by decide +kernel

theorem keyMomentRowsAt412 : keyMomentRows (412 : Fin 2886) =
    keyMomentRow412 := by decide +kernel

theorem keyMomentRowsAt413 : keyMomentRows (413 : Fin 2886) =
    keyMomentRow413 := by decide +kernel

theorem keyMomentRowsAt414 : keyMomentRows (414 : Fin 2886) =
    keyMomentRow414 := by decide +kernel

theorem keyMomentRowsAt415 : keyMomentRows (415 : Fin 2886) =
    keyMomentRow415 := by decide +kernel

theorem keyMomentChunkSound12 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 12) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 384 ∨ k.val = 385 ∨ k.val = 386 ∨ k.val = 387 ∨ k.val = 388 ∨ k.val = 389 ∨ k.val = 390 ∨ k.val = 391 ∨ k.val = 392 ∨ k.val = 393 ∨ k.val = 394 ∨ k.val = 395 ∨ k.val = 396 ∨ k.val = 397 ∨ k.val = 398 ∨ k.val = 399 ∨ k.val = 400 ∨ k.val = 401 ∨ k.val = 402 ∨ k.val = 403 ∨ k.val = 404 ∨ k.val = 405 ∨ k.val = 406 ∨ k.val = 407 ∨ k.val = 408 ∨ k.val = 409 ∨ k.val = 410 ∨ k.val = 411 ∨ k.val = 412 ∨ k.val = 413 ∨ k.val = 414 ∨ k.val = 415 := by omega
  rcases heq with h384 | h385 | h386 | h387 | h388 | h389 | h390 | h391 | h392 | h393 | h394 | h395 | h396 | h397 | h398 | h399 | h400 | h401 | h402 | h403 | h404 | h405 | h406 | h407 | h408 | h409 | h410 | h411 | h412 | h413 | h414 | h415
  · have he : k = (384 : Fin 2886) := Fin.ext h384
    subst k
    rw [keyMomentRowsAt384]
    exact keyMoment384 B hB
  · have he : k = (385 : Fin 2886) := Fin.ext h385
    subst k
    rw [keyMomentRowsAt385]
    exact keyMoment385 B hB
  · have he : k = (386 : Fin 2886) := Fin.ext h386
    subst k
    rw [keyMomentRowsAt386]
    exact keyMoment386 B hB
  · have he : k = (387 : Fin 2886) := Fin.ext h387
    subst k
    rw [keyMomentRowsAt387]
    exact keyMoment387 B hB
  · have he : k = (388 : Fin 2886) := Fin.ext h388
    subst k
    rw [keyMomentRowsAt388]
    exact keyMoment388 B hB
  · have he : k = (389 : Fin 2886) := Fin.ext h389
    subst k
    rw [keyMomentRowsAt389]
    exact keyMoment389 B hB
  · have he : k = (390 : Fin 2886) := Fin.ext h390
    subst k
    rw [keyMomentRowsAt390]
    exact keyMoment390 B hB
  · have he : k = (391 : Fin 2886) := Fin.ext h391
    subst k
    rw [keyMomentRowsAt391]
    exact keyMoment391 B hB
  · have he : k = (392 : Fin 2886) := Fin.ext h392
    subst k
    rw [keyMomentRowsAt392]
    exact keyMoment392 B hB
  · have he : k = (393 : Fin 2886) := Fin.ext h393
    subst k
    rw [keyMomentRowsAt393]
    exact keyMoment393 B hB
  · have he : k = (394 : Fin 2886) := Fin.ext h394
    subst k
    rw [keyMomentRowsAt394]
    exact keyMoment394 B hB
  · have he : k = (395 : Fin 2886) := Fin.ext h395
    subst k
    rw [keyMomentRowsAt395]
    exact keyMoment395 B hB
  · have he : k = (396 : Fin 2886) := Fin.ext h396
    subst k
    rw [keyMomentRowsAt396]
    exact keyMoment396 B hB
  · have he : k = (397 : Fin 2886) := Fin.ext h397
    subst k
    rw [keyMomentRowsAt397]
    exact keyMoment397 B hB
  · have he : k = (398 : Fin 2886) := Fin.ext h398
    subst k
    rw [keyMomentRowsAt398]
    exact keyMoment398 B hB
  · have he : k = (399 : Fin 2886) := Fin.ext h399
    subst k
    rw [keyMomentRowsAt399]
    exact keyMoment399 B hB
  · have he : k = (400 : Fin 2886) := Fin.ext h400
    subst k
    rw [keyMomentRowsAt400]
    exact keyMoment400 B hB
  · have he : k = (401 : Fin 2886) := Fin.ext h401
    subst k
    rw [keyMomentRowsAt401]
    exact keyMoment401 B hB
  · have he : k = (402 : Fin 2886) := Fin.ext h402
    subst k
    rw [keyMomentRowsAt402]
    exact keyMoment402 B hB
  · have he : k = (403 : Fin 2886) := Fin.ext h403
    subst k
    rw [keyMomentRowsAt403]
    exact keyMoment403 B hB
  · have he : k = (404 : Fin 2886) := Fin.ext h404
    subst k
    rw [keyMomentRowsAt404]
    exact keyMoment404 B hB
  · have he : k = (405 : Fin 2886) := Fin.ext h405
    subst k
    rw [keyMomentRowsAt405]
    exact keyMoment405 B hB
  · have he : k = (406 : Fin 2886) := Fin.ext h406
    subst k
    rw [keyMomentRowsAt406]
    exact keyMoment406 B hB
  · have he : k = (407 : Fin 2886) := Fin.ext h407
    subst k
    rw [keyMomentRowsAt407]
    exact keyMoment407 B hB
  · have he : k = (408 : Fin 2886) := Fin.ext h408
    subst k
    rw [keyMomentRowsAt408]
    exact keyMoment408 B hB
  · have he : k = (409 : Fin 2886) := Fin.ext h409
    subst k
    rw [keyMomentRowsAt409]
    exact keyMoment409 B hB
  · have he : k = (410 : Fin 2886) := Fin.ext h410
    subst k
    rw [keyMomentRowsAt410]
    exact keyMoment410 B hB
  · have he : k = (411 : Fin 2886) := Fin.ext h411
    subst k
    rw [keyMomentRowsAt411]
    exact keyMoment411 B hB
  · have he : k = (412 : Fin 2886) := Fin.ext h412
    subst k
    rw [keyMomentRowsAt412]
    exact keyMoment412 B hB
  · have he : k = (413 : Fin 2886) := Fin.ext h413
    subst k
    rw [keyMomentRowsAt413]
    exact keyMoment413 B hB
  · have he : k = (414 : Fin 2886) := Fin.ext h414
    subst k
    rw [keyMomentRowsAt414]
    exact keyMoment414 B hB
  · have he : k = (415 : Fin 2886) := Fin.ext h415
    subst k
    rw [keyMomentRowsAt415]
    exact keyMoment415 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
