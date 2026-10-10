import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound13
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt416 : keyMomentRows (416 : Fin 2886) =
    keyMomentRow416 := by decide +kernel

theorem keyMomentRowsAt417 : keyMomentRows (417 : Fin 2886) =
    keyMomentRow417 := by decide +kernel

theorem keyMomentRowsAt418 : keyMomentRows (418 : Fin 2886) =
    keyMomentRow418 := by decide +kernel

theorem keyMomentRowsAt419 : keyMomentRows (419 : Fin 2886) =
    keyMomentRow419 := by decide +kernel

theorem keyMomentRowsAt420 : keyMomentRows (420 : Fin 2886) =
    keyMomentRow420 := by decide +kernel

theorem keyMomentRowsAt421 : keyMomentRows (421 : Fin 2886) =
    keyMomentRow421 := by decide +kernel

theorem keyMomentRowsAt422 : keyMomentRows (422 : Fin 2886) =
    keyMomentRow422 := by decide +kernel

theorem keyMomentRowsAt423 : keyMomentRows (423 : Fin 2886) =
    keyMomentRow423 := by decide +kernel

theorem keyMomentRowsAt424 : keyMomentRows (424 : Fin 2886) =
    keyMomentRow424 := by decide +kernel

theorem keyMomentRowsAt425 : keyMomentRows (425 : Fin 2886) =
    keyMomentRow425 := by decide +kernel

theorem keyMomentRowsAt426 : keyMomentRows (426 : Fin 2886) =
    keyMomentRow426 := by decide +kernel

theorem keyMomentRowsAt427 : keyMomentRows (427 : Fin 2886) =
    keyMomentRow427 := by decide +kernel

theorem keyMomentRowsAt428 : keyMomentRows (428 : Fin 2886) =
    keyMomentRow428 := by decide +kernel

theorem keyMomentRowsAt429 : keyMomentRows (429 : Fin 2886) =
    keyMomentRow429 := by decide +kernel

theorem keyMomentRowsAt430 : keyMomentRows (430 : Fin 2886) =
    keyMomentRow430 := by decide +kernel

theorem keyMomentRowsAt431 : keyMomentRows (431 : Fin 2886) =
    keyMomentRow431 := by decide +kernel

theorem keyMomentRowsAt432 : keyMomentRows (432 : Fin 2886) =
    keyMomentRow432 := by decide +kernel

theorem keyMomentRowsAt433 : keyMomentRows (433 : Fin 2886) =
    keyMomentRow433 := by decide +kernel

theorem keyMomentRowsAt434 : keyMomentRows (434 : Fin 2886) =
    keyMomentRow434 := by decide +kernel

theorem keyMomentRowsAt435 : keyMomentRows (435 : Fin 2886) =
    keyMomentRow435 := by decide +kernel

theorem keyMomentRowsAt436 : keyMomentRows (436 : Fin 2886) =
    keyMomentRow436 := by decide +kernel

theorem keyMomentRowsAt437 : keyMomentRows (437 : Fin 2886) =
    keyMomentRow437 := by decide +kernel

theorem keyMomentRowsAt438 : keyMomentRows (438 : Fin 2886) =
    keyMomentRow438 := by decide +kernel

theorem keyMomentRowsAt439 : keyMomentRows (439 : Fin 2886) =
    keyMomentRow439 := by decide +kernel

theorem keyMomentRowsAt440 : keyMomentRows (440 : Fin 2886) =
    keyMomentRow440 := by decide +kernel

theorem keyMomentRowsAt441 : keyMomentRows (441 : Fin 2886) =
    keyMomentRow441 := by decide +kernel

theorem keyMomentRowsAt442 : keyMomentRows (442 : Fin 2886) =
    keyMomentRow442 := by decide +kernel

theorem keyMomentRowsAt443 : keyMomentRows (443 : Fin 2886) =
    keyMomentRow443 := by decide +kernel

theorem keyMomentRowsAt444 : keyMomentRows (444 : Fin 2886) =
    keyMomentRow444 := by decide +kernel

theorem keyMomentRowsAt445 : keyMomentRows (445 : Fin 2886) =
    keyMomentRow445 := by decide +kernel

theorem keyMomentRowsAt446 : keyMomentRows (446 : Fin 2886) =
    keyMomentRow446 := by decide +kernel

theorem keyMomentRowsAt447 : keyMomentRows (447 : Fin 2886) =
    keyMomentRow447 := by decide +kernel

theorem keyMomentChunkSound13 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 13) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 416 ∨ k.val = 417 ∨ k.val = 418 ∨ k.val = 419 ∨ k.val = 420 ∨ k.val = 421 ∨ k.val = 422 ∨ k.val = 423 ∨ k.val = 424 ∨ k.val = 425 ∨ k.val = 426 ∨ k.val = 427 ∨ k.val = 428 ∨ k.val = 429 ∨ k.val = 430 ∨ k.val = 431 ∨ k.val = 432 ∨ k.val = 433 ∨ k.val = 434 ∨ k.val = 435 ∨ k.val = 436 ∨ k.val = 437 ∨ k.val = 438 ∨ k.val = 439 ∨ k.val = 440 ∨ k.val = 441 ∨ k.val = 442 ∨ k.val = 443 ∨ k.val = 444 ∨ k.val = 445 ∨ k.val = 446 ∨ k.val = 447 := by omega
  rcases heq with h416 | h417 | h418 | h419 | h420 | h421 | h422 | h423 | h424 | h425 | h426 | h427 | h428 | h429 | h430 | h431 | h432 | h433 | h434 | h435 | h436 | h437 | h438 | h439 | h440 | h441 | h442 | h443 | h444 | h445 | h446 | h447
  · have he : k = (416 : Fin 2886) := Fin.ext h416
    subst k
    rw [keyMomentRowsAt416]
    exact keyMoment416 B hB
  · have he : k = (417 : Fin 2886) := Fin.ext h417
    subst k
    rw [keyMomentRowsAt417]
    exact keyMoment417 B hB
  · have he : k = (418 : Fin 2886) := Fin.ext h418
    subst k
    rw [keyMomentRowsAt418]
    exact keyMoment418 B hB
  · have he : k = (419 : Fin 2886) := Fin.ext h419
    subst k
    rw [keyMomentRowsAt419]
    exact keyMoment419 B hB
  · have he : k = (420 : Fin 2886) := Fin.ext h420
    subst k
    rw [keyMomentRowsAt420]
    exact keyMoment420 B hB
  · have he : k = (421 : Fin 2886) := Fin.ext h421
    subst k
    rw [keyMomentRowsAt421]
    exact keyMoment421 B hB
  · have he : k = (422 : Fin 2886) := Fin.ext h422
    subst k
    rw [keyMomentRowsAt422]
    exact keyMoment422 B hB
  · have he : k = (423 : Fin 2886) := Fin.ext h423
    subst k
    rw [keyMomentRowsAt423]
    exact keyMoment423 B hB
  · have he : k = (424 : Fin 2886) := Fin.ext h424
    subst k
    rw [keyMomentRowsAt424]
    exact keyMoment424 B hB
  · have he : k = (425 : Fin 2886) := Fin.ext h425
    subst k
    rw [keyMomentRowsAt425]
    exact keyMoment425 B hB
  · have he : k = (426 : Fin 2886) := Fin.ext h426
    subst k
    rw [keyMomentRowsAt426]
    exact keyMoment426 B hB
  · have he : k = (427 : Fin 2886) := Fin.ext h427
    subst k
    rw [keyMomentRowsAt427]
    exact keyMoment427 B hB
  · have he : k = (428 : Fin 2886) := Fin.ext h428
    subst k
    rw [keyMomentRowsAt428]
    exact keyMoment428 B hB
  · have he : k = (429 : Fin 2886) := Fin.ext h429
    subst k
    rw [keyMomentRowsAt429]
    exact keyMoment429 B hB
  · have he : k = (430 : Fin 2886) := Fin.ext h430
    subst k
    rw [keyMomentRowsAt430]
    exact keyMoment430 B hB
  · have he : k = (431 : Fin 2886) := Fin.ext h431
    subst k
    rw [keyMomentRowsAt431]
    exact keyMoment431 B hB
  · have he : k = (432 : Fin 2886) := Fin.ext h432
    subst k
    rw [keyMomentRowsAt432]
    exact keyMoment432 B hB
  · have he : k = (433 : Fin 2886) := Fin.ext h433
    subst k
    rw [keyMomentRowsAt433]
    exact keyMoment433 B hB
  · have he : k = (434 : Fin 2886) := Fin.ext h434
    subst k
    rw [keyMomentRowsAt434]
    exact keyMoment434 B hB
  · have he : k = (435 : Fin 2886) := Fin.ext h435
    subst k
    rw [keyMomentRowsAt435]
    exact keyMoment435 B hB
  · have he : k = (436 : Fin 2886) := Fin.ext h436
    subst k
    rw [keyMomentRowsAt436]
    exact keyMoment436 B hB
  · have he : k = (437 : Fin 2886) := Fin.ext h437
    subst k
    rw [keyMomentRowsAt437]
    exact keyMoment437 B hB
  · have he : k = (438 : Fin 2886) := Fin.ext h438
    subst k
    rw [keyMomentRowsAt438]
    exact keyMoment438 B hB
  · have he : k = (439 : Fin 2886) := Fin.ext h439
    subst k
    rw [keyMomentRowsAt439]
    exact keyMoment439 B hB
  · have he : k = (440 : Fin 2886) := Fin.ext h440
    subst k
    rw [keyMomentRowsAt440]
    exact keyMoment440 B hB
  · have he : k = (441 : Fin 2886) := Fin.ext h441
    subst k
    rw [keyMomentRowsAt441]
    exact keyMoment441 B hB
  · have he : k = (442 : Fin 2886) := Fin.ext h442
    subst k
    rw [keyMomentRowsAt442]
    exact keyMoment442 B hB
  · have he : k = (443 : Fin 2886) := Fin.ext h443
    subst k
    rw [keyMomentRowsAt443]
    exact keyMoment443 B hB
  · have he : k = (444 : Fin 2886) := Fin.ext h444
    subst k
    rw [keyMomentRowsAt444]
    exact keyMoment444 B hB
  · have he : k = (445 : Fin 2886) := Fin.ext h445
    subst k
    rw [keyMomentRowsAt445]
    exact keyMoment445 B hB
  · have he : k = (446 : Fin 2886) := Fin.ext h446
    subst k
    rw [keyMomentRowsAt446]
    exact keyMoment446 B hB
  · have he : k = (447 : Fin 2886) := Fin.ext h447
    subst k
    rw [keyMomentRowsAt447]
    exact keyMoment447 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
