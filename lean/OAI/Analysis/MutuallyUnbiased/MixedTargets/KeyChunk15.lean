import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound15
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt480 : keyMomentRows (480 : Fin 2886) =
    keyMomentRow480 := by decide +kernel

theorem keyMomentRowsAt481 : keyMomentRows (481 : Fin 2886) =
    keyMomentRow481 := by decide +kernel

theorem keyMomentRowsAt482 : keyMomentRows (482 : Fin 2886) =
    keyMomentRow482 := by decide +kernel

theorem keyMomentRowsAt483 : keyMomentRows (483 : Fin 2886) =
    keyMomentRow483 := by decide +kernel

theorem keyMomentRowsAt484 : keyMomentRows (484 : Fin 2886) =
    keyMomentRow484 := by decide +kernel

theorem keyMomentRowsAt485 : keyMomentRows (485 : Fin 2886) =
    keyMomentRow485 := by decide +kernel

theorem keyMomentRowsAt486 : keyMomentRows (486 : Fin 2886) =
    keyMomentRow486 := by decide +kernel

theorem keyMomentRowsAt487 : keyMomentRows (487 : Fin 2886) =
    keyMomentRow487 := by decide +kernel

theorem keyMomentRowsAt488 : keyMomentRows (488 : Fin 2886) =
    keyMomentRow488 := by decide +kernel

theorem keyMomentRowsAt489 : keyMomentRows (489 : Fin 2886) =
    keyMomentRow489 := by decide +kernel

theorem keyMomentRowsAt490 : keyMomentRows (490 : Fin 2886) =
    keyMomentRow490 := by decide +kernel

theorem keyMomentRowsAt491 : keyMomentRows (491 : Fin 2886) =
    keyMomentRow491 := by decide +kernel

theorem keyMomentRowsAt492 : keyMomentRows (492 : Fin 2886) =
    keyMomentRow492 := by decide +kernel

theorem keyMomentRowsAt493 : keyMomentRows (493 : Fin 2886) =
    keyMomentRow493 := by decide +kernel

theorem keyMomentRowsAt494 : keyMomentRows (494 : Fin 2886) =
    keyMomentRow494 := by decide +kernel

theorem keyMomentRowsAt495 : keyMomentRows (495 : Fin 2886) =
    keyMomentRow495 := by decide +kernel

theorem keyMomentRowsAt496 : keyMomentRows (496 : Fin 2886) =
    keyMomentRow496 := by decide +kernel

theorem keyMomentRowsAt497 : keyMomentRows (497 : Fin 2886) =
    keyMomentRow497 := by decide +kernel

theorem keyMomentRowsAt498 : keyMomentRows (498 : Fin 2886) =
    keyMomentRow498 := by decide +kernel

theorem keyMomentRowsAt499 : keyMomentRows (499 : Fin 2886) =
    keyMomentRow499 := by decide +kernel

theorem keyMomentRowsAt500 : keyMomentRows (500 : Fin 2886) =
    keyMomentRow500 := by decide +kernel

theorem keyMomentRowsAt501 : keyMomentRows (501 : Fin 2886) =
    keyMomentRow501 := by decide +kernel

theorem keyMomentRowsAt502 : keyMomentRows (502 : Fin 2886) =
    keyMomentRow502 := by decide +kernel

theorem keyMomentRowsAt503 : keyMomentRows (503 : Fin 2886) =
    keyMomentRow503 := by decide +kernel

theorem keyMomentRowsAt504 : keyMomentRows (504 : Fin 2886) =
    keyMomentRow504 := by decide +kernel

theorem keyMomentRowsAt505 : keyMomentRows (505 : Fin 2886) =
    keyMomentRow505 := by decide +kernel

theorem keyMomentRowsAt506 : keyMomentRows (506 : Fin 2886) =
    keyMomentRow506 := by decide +kernel

theorem keyMomentRowsAt507 : keyMomentRows (507 : Fin 2886) =
    keyMomentRow507 := by decide +kernel

theorem keyMomentRowsAt508 : keyMomentRows (508 : Fin 2886) =
    keyMomentRow508 := by decide +kernel

theorem keyMomentRowsAt509 : keyMomentRows (509 : Fin 2886) =
    keyMomentRow509 := by decide +kernel

theorem keyMomentRowsAt510 : keyMomentRows (510 : Fin 2886) =
    keyMomentRow510 := by decide +kernel

theorem keyMomentRowsAt511 : keyMomentRows (511 : Fin 2886) =
    keyMomentRow511 := by decide +kernel

theorem keyMomentChunkSound15 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 15) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 480 ∨ k.val = 481 ∨ k.val = 482 ∨ k.val = 483 ∨ k.val = 484 ∨ k.val = 485 ∨ k.val = 486 ∨ k.val = 487 ∨ k.val = 488 ∨ k.val = 489 ∨ k.val = 490 ∨ k.val = 491 ∨ k.val = 492 ∨ k.val = 493 ∨ k.val = 494 ∨ k.val = 495 ∨ k.val = 496 ∨ k.val = 497 ∨ k.val = 498 ∨ k.val = 499 ∨ k.val = 500 ∨ k.val = 501 ∨ k.val = 502 ∨ k.val = 503 ∨ k.val = 504 ∨ k.val = 505 ∨ k.val = 506 ∨ k.val = 507 ∨ k.val = 508 ∨ k.val = 509 ∨ k.val = 510 ∨ k.val = 511 := by omega
  rcases heq with h480 | h481 | h482 | h483 | h484 | h485 | h486 | h487 | h488 | h489 | h490 | h491 | h492 | h493 | h494 | h495 | h496 | h497 | h498 | h499 | h500 | h501 | h502 | h503 | h504 | h505 | h506 | h507 | h508 | h509 | h510 | h511
  · have he : k = (480 : Fin 2886) := Fin.ext h480
    subst k
    rw [keyMomentRowsAt480]
    exact keyMoment480 B hB
  · have he : k = (481 : Fin 2886) := Fin.ext h481
    subst k
    rw [keyMomentRowsAt481]
    exact keyMoment481 B hB
  · have he : k = (482 : Fin 2886) := Fin.ext h482
    subst k
    rw [keyMomentRowsAt482]
    exact keyMoment482 B hB
  · have he : k = (483 : Fin 2886) := Fin.ext h483
    subst k
    rw [keyMomentRowsAt483]
    exact keyMoment483 B hB
  · have he : k = (484 : Fin 2886) := Fin.ext h484
    subst k
    rw [keyMomentRowsAt484]
    exact keyMoment484 B hB
  · have he : k = (485 : Fin 2886) := Fin.ext h485
    subst k
    rw [keyMomentRowsAt485]
    exact keyMoment485 B hB
  · have he : k = (486 : Fin 2886) := Fin.ext h486
    subst k
    rw [keyMomentRowsAt486]
    exact keyMoment486 B hB
  · have he : k = (487 : Fin 2886) := Fin.ext h487
    subst k
    rw [keyMomentRowsAt487]
    exact keyMoment487 B hB
  · have he : k = (488 : Fin 2886) := Fin.ext h488
    subst k
    rw [keyMomentRowsAt488]
    exact keyMoment488 B hB
  · have he : k = (489 : Fin 2886) := Fin.ext h489
    subst k
    rw [keyMomentRowsAt489]
    exact keyMoment489 B hB
  · have he : k = (490 : Fin 2886) := Fin.ext h490
    subst k
    rw [keyMomentRowsAt490]
    exact keyMoment490 B hB
  · have he : k = (491 : Fin 2886) := Fin.ext h491
    subst k
    rw [keyMomentRowsAt491]
    exact keyMoment491 B hB
  · have he : k = (492 : Fin 2886) := Fin.ext h492
    subst k
    rw [keyMomentRowsAt492]
    exact keyMoment492 B hB
  · have he : k = (493 : Fin 2886) := Fin.ext h493
    subst k
    rw [keyMomentRowsAt493]
    exact keyMoment493 B hB
  · have he : k = (494 : Fin 2886) := Fin.ext h494
    subst k
    rw [keyMomentRowsAt494]
    exact keyMoment494 B hB
  · have he : k = (495 : Fin 2886) := Fin.ext h495
    subst k
    rw [keyMomentRowsAt495]
    exact keyMoment495 B hB
  · have he : k = (496 : Fin 2886) := Fin.ext h496
    subst k
    rw [keyMomentRowsAt496]
    exact keyMoment496 B hB
  · have he : k = (497 : Fin 2886) := Fin.ext h497
    subst k
    rw [keyMomentRowsAt497]
    exact keyMoment497 B hB
  · have he : k = (498 : Fin 2886) := Fin.ext h498
    subst k
    rw [keyMomentRowsAt498]
    exact keyMoment498 B hB
  · have he : k = (499 : Fin 2886) := Fin.ext h499
    subst k
    rw [keyMomentRowsAt499]
    exact keyMoment499 B hB
  · have he : k = (500 : Fin 2886) := Fin.ext h500
    subst k
    rw [keyMomentRowsAt500]
    exact keyMoment500 B hB
  · have he : k = (501 : Fin 2886) := Fin.ext h501
    subst k
    rw [keyMomentRowsAt501]
    exact keyMoment501 B hB
  · have he : k = (502 : Fin 2886) := Fin.ext h502
    subst k
    rw [keyMomentRowsAt502]
    exact keyMoment502 B hB
  · have he : k = (503 : Fin 2886) := Fin.ext h503
    subst k
    rw [keyMomentRowsAt503]
    exact keyMoment503 B hB
  · have he : k = (504 : Fin 2886) := Fin.ext h504
    subst k
    rw [keyMomentRowsAt504]
    exact keyMoment504 B hB
  · have he : k = (505 : Fin 2886) := Fin.ext h505
    subst k
    rw [keyMomentRowsAt505]
    exact keyMoment505 B hB
  · have he : k = (506 : Fin 2886) := Fin.ext h506
    subst k
    rw [keyMomentRowsAt506]
    exact keyMoment506 B hB
  · have he : k = (507 : Fin 2886) := Fin.ext h507
    subst k
    rw [keyMomentRowsAt507]
    exact keyMoment507 B hB
  · have he : k = (508 : Fin 2886) := Fin.ext h508
    subst k
    rw [keyMomentRowsAt508]
    exact keyMoment508 B hB
  · have he : k = (509 : Fin 2886) := Fin.ext h509
    subst k
    rw [keyMomentRowsAt509]
    exact keyMoment509 B hB
  · have he : k = (510 : Fin 2886) := Fin.ext h510
    subst k
    rw [keyMomentRowsAt510]
    exact keyMoment510 B hB
  · have he : k = (511 : Fin 2886) := Fin.ext h511
    subst k
    rw [keyMomentRowsAt511]
    exact keyMoment511 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
