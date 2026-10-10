import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound14
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt448 : keyMomentRows (448 : Fin 2886) =
    keyMomentRow448 := by decide +kernel

theorem keyMomentRowsAt449 : keyMomentRows (449 : Fin 2886) =
    keyMomentRow449 := by decide +kernel

theorem keyMomentRowsAt450 : keyMomentRows (450 : Fin 2886) =
    keyMomentRow450 := by decide +kernel

theorem keyMomentRowsAt451 : keyMomentRows (451 : Fin 2886) =
    keyMomentRow451 := by decide +kernel

theorem keyMomentRowsAt452 : keyMomentRows (452 : Fin 2886) =
    keyMomentRow452 := by decide +kernel

theorem keyMomentRowsAt453 : keyMomentRows (453 : Fin 2886) =
    keyMomentRow453 := by decide +kernel

theorem keyMomentRowsAt454 : keyMomentRows (454 : Fin 2886) =
    keyMomentRow454 := by decide +kernel

theorem keyMomentRowsAt455 : keyMomentRows (455 : Fin 2886) =
    keyMomentRow455 := by decide +kernel

theorem keyMomentRowsAt456 : keyMomentRows (456 : Fin 2886) =
    keyMomentRow456 := by decide +kernel

theorem keyMomentRowsAt457 : keyMomentRows (457 : Fin 2886) =
    keyMomentRow457 := by decide +kernel

theorem keyMomentRowsAt458 : keyMomentRows (458 : Fin 2886) =
    keyMomentRow458 := by decide +kernel

theorem keyMomentRowsAt459 : keyMomentRows (459 : Fin 2886) =
    keyMomentRow459 := by decide +kernel

theorem keyMomentRowsAt460 : keyMomentRows (460 : Fin 2886) =
    keyMomentRow460 := by decide +kernel

theorem keyMomentRowsAt461 : keyMomentRows (461 : Fin 2886) =
    keyMomentRow461 := by decide +kernel

theorem keyMomentRowsAt462 : keyMomentRows (462 : Fin 2886) =
    keyMomentRow462 := by decide +kernel

theorem keyMomentRowsAt463 : keyMomentRows (463 : Fin 2886) =
    keyMomentRow463 := by decide +kernel

theorem keyMomentRowsAt464 : keyMomentRows (464 : Fin 2886) =
    keyMomentRow464 := by decide +kernel

theorem keyMomentRowsAt465 : keyMomentRows (465 : Fin 2886) =
    keyMomentRow465 := by decide +kernel

theorem keyMomentRowsAt466 : keyMomentRows (466 : Fin 2886) =
    keyMomentRow466 := by decide +kernel

theorem keyMomentRowsAt467 : keyMomentRows (467 : Fin 2886) =
    keyMomentRow467 := by decide +kernel

theorem keyMomentRowsAt468 : keyMomentRows (468 : Fin 2886) =
    keyMomentRow468 := by decide +kernel

theorem keyMomentRowsAt469 : keyMomentRows (469 : Fin 2886) =
    keyMomentRow469 := by decide +kernel

theorem keyMomentRowsAt470 : keyMomentRows (470 : Fin 2886) =
    keyMomentRow470 := by decide +kernel

theorem keyMomentRowsAt471 : keyMomentRows (471 : Fin 2886) =
    keyMomentRow471 := by decide +kernel

theorem keyMomentRowsAt472 : keyMomentRows (472 : Fin 2886) =
    keyMomentRow472 := by decide +kernel

theorem keyMomentRowsAt473 : keyMomentRows (473 : Fin 2886) =
    keyMomentRow473 := by decide +kernel

theorem keyMomentRowsAt474 : keyMomentRows (474 : Fin 2886) =
    keyMomentRow474 := by decide +kernel

theorem keyMomentRowsAt475 : keyMomentRows (475 : Fin 2886) =
    keyMomentRow475 := by decide +kernel

theorem keyMomentRowsAt476 : keyMomentRows (476 : Fin 2886) =
    keyMomentRow476 := by decide +kernel

theorem keyMomentRowsAt477 : keyMomentRows (477 : Fin 2886) =
    keyMomentRow477 := by decide +kernel

theorem keyMomentRowsAt478 : keyMomentRows (478 : Fin 2886) =
    keyMomentRow478 := by decide +kernel

theorem keyMomentRowsAt479 : keyMomentRows (479 : Fin 2886) =
    keyMomentRow479 := by decide +kernel

theorem keyMomentChunkSound14 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 14) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 448 ∨ k.val = 449 ∨ k.val = 450 ∨ k.val = 451 ∨ k.val = 452 ∨ k.val = 453 ∨ k.val = 454 ∨ k.val = 455 ∨ k.val = 456 ∨ k.val = 457 ∨ k.val = 458 ∨ k.val = 459 ∨ k.val = 460 ∨ k.val = 461 ∨ k.val = 462 ∨ k.val = 463 ∨ k.val = 464 ∨ k.val = 465 ∨ k.val = 466 ∨ k.val = 467 ∨ k.val = 468 ∨ k.val = 469 ∨ k.val = 470 ∨ k.val = 471 ∨ k.val = 472 ∨ k.val = 473 ∨ k.val = 474 ∨ k.val = 475 ∨ k.val = 476 ∨ k.val = 477 ∨ k.val = 478 ∨ k.val = 479 := by omega
  rcases heq with h448 | h449 | h450 | h451 | h452 | h453 | h454 | h455 | h456 | h457 | h458 | h459 | h460 | h461 | h462 | h463 | h464 | h465 | h466 | h467 | h468 | h469 | h470 | h471 | h472 | h473 | h474 | h475 | h476 | h477 | h478 | h479
  · have he : k = (448 : Fin 2886) := Fin.ext h448
    subst k
    rw [keyMomentRowsAt448]
    exact keyMoment448 B hB
  · have he : k = (449 : Fin 2886) := Fin.ext h449
    subst k
    rw [keyMomentRowsAt449]
    exact keyMoment449 B hB
  · have he : k = (450 : Fin 2886) := Fin.ext h450
    subst k
    rw [keyMomentRowsAt450]
    exact keyMoment450 B hB
  · have he : k = (451 : Fin 2886) := Fin.ext h451
    subst k
    rw [keyMomentRowsAt451]
    exact keyMoment451 B hB
  · have he : k = (452 : Fin 2886) := Fin.ext h452
    subst k
    rw [keyMomentRowsAt452]
    exact keyMoment452 B hB
  · have he : k = (453 : Fin 2886) := Fin.ext h453
    subst k
    rw [keyMomentRowsAt453]
    exact keyMoment453 B hB
  · have he : k = (454 : Fin 2886) := Fin.ext h454
    subst k
    rw [keyMomentRowsAt454]
    exact keyMoment454 B hB
  · have he : k = (455 : Fin 2886) := Fin.ext h455
    subst k
    rw [keyMomentRowsAt455]
    exact keyMoment455 B hB
  · have he : k = (456 : Fin 2886) := Fin.ext h456
    subst k
    rw [keyMomentRowsAt456]
    exact keyMoment456 B hB
  · have he : k = (457 : Fin 2886) := Fin.ext h457
    subst k
    rw [keyMomentRowsAt457]
    exact keyMoment457 B hB
  · have he : k = (458 : Fin 2886) := Fin.ext h458
    subst k
    rw [keyMomentRowsAt458]
    exact keyMoment458 B hB
  · have he : k = (459 : Fin 2886) := Fin.ext h459
    subst k
    rw [keyMomentRowsAt459]
    exact keyMoment459 B hB
  · have he : k = (460 : Fin 2886) := Fin.ext h460
    subst k
    rw [keyMomentRowsAt460]
    exact keyMoment460 B hB
  · have he : k = (461 : Fin 2886) := Fin.ext h461
    subst k
    rw [keyMomentRowsAt461]
    exact keyMoment461 B hB
  · have he : k = (462 : Fin 2886) := Fin.ext h462
    subst k
    rw [keyMomentRowsAt462]
    exact keyMoment462 B hB
  · have he : k = (463 : Fin 2886) := Fin.ext h463
    subst k
    rw [keyMomentRowsAt463]
    exact keyMoment463 B hB
  · have he : k = (464 : Fin 2886) := Fin.ext h464
    subst k
    rw [keyMomentRowsAt464]
    exact keyMoment464 B hB
  · have he : k = (465 : Fin 2886) := Fin.ext h465
    subst k
    rw [keyMomentRowsAt465]
    exact keyMoment465 B hB
  · have he : k = (466 : Fin 2886) := Fin.ext h466
    subst k
    rw [keyMomentRowsAt466]
    exact keyMoment466 B hB
  · have he : k = (467 : Fin 2886) := Fin.ext h467
    subst k
    rw [keyMomentRowsAt467]
    exact keyMoment467 B hB
  · have he : k = (468 : Fin 2886) := Fin.ext h468
    subst k
    rw [keyMomentRowsAt468]
    exact keyMoment468 B hB
  · have he : k = (469 : Fin 2886) := Fin.ext h469
    subst k
    rw [keyMomentRowsAt469]
    exact keyMoment469 B hB
  · have he : k = (470 : Fin 2886) := Fin.ext h470
    subst k
    rw [keyMomentRowsAt470]
    exact keyMoment470 B hB
  · have he : k = (471 : Fin 2886) := Fin.ext h471
    subst k
    rw [keyMomentRowsAt471]
    exact keyMoment471 B hB
  · have he : k = (472 : Fin 2886) := Fin.ext h472
    subst k
    rw [keyMomentRowsAt472]
    exact keyMoment472 B hB
  · have he : k = (473 : Fin 2886) := Fin.ext h473
    subst k
    rw [keyMomentRowsAt473]
    exact keyMoment473 B hB
  · have he : k = (474 : Fin 2886) := Fin.ext h474
    subst k
    rw [keyMomentRowsAt474]
    exact keyMoment474 B hB
  · have he : k = (475 : Fin 2886) := Fin.ext h475
    subst k
    rw [keyMomentRowsAt475]
    exact keyMoment475 B hB
  · have he : k = (476 : Fin 2886) := Fin.ext h476
    subst k
    rw [keyMomentRowsAt476]
    exact keyMoment476 B hB
  · have he : k = (477 : Fin 2886) := Fin.ext h477
    subst k
    rw [keyMomentRowsAt477]
    exact keyMoment477 B hB
  · have he : k = (478 : Fin 2886) := Fin.ext h478
    subst k
    rw [keyMomentRowsAt478]
    exact keyMoment478 B hB
  · have he : k = (479 : Fin 2886) := Fin.ext h479
    subst k
    rw [keyMomentRowsAt479]
    exact keyMoment479 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
