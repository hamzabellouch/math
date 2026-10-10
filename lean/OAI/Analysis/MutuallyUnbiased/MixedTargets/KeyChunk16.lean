import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound16
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt512 : keyMomentRows (512 : Fin 2886) =
    keyMomentRow512 := by decide +kernel

theorem keyMomentRowsAt513 : keyMomentRows (513 : Fin 2886) =
    keyMomentRow513 := by decide +kernel

theorem keyMomentRowsAt514 : keyMomentRows (514 : Fin 2886) =
    keyMomentRow514 := by decide +kernel

theorem keyMomentRowsAt515 : keyMomentRows (515 : Fin 2886) =
    keyMomentRow515 := by decide +kernel

theorem keyMomentRowsAt516 : keyMomentRows (516 : Fin 2886) =
    keyMomentRow516 := by decide +kernel

theorem keyMomentRowsAt517 : keyMomentRows (517 : Fin 2886) =
    keyMomentRow517 := by decide +kernel

theorem keyMomentRowsAt518 : keyMomentRows (518 : Fin 2886) =
    keyMomentRow518 := by decide +kernel

theorem keyMomentRowsAt519 : keyMomentRows (519 : Fin 2886) =
    keyMomentRow519 := by decide +kernel

theorem keyMomentRowsAt520 : keyMomentRows (520 : Fin 2886) =
    keyMomentRow520 := by decide +kernel

theorem keyMomentRowsAt521 : keyMomentRows (521 : Fin 2886) =
    keyMomentRow521 := by decide +kernel

theorem keyMomentRowsAt522 : keyMomentRows (522 : Fin 2886) =
    keyMomentRow522 := by decide +kernel

theorem keyMomentRowsAt523 : keyMomentRows (523 : Fin 2886) =
    keyMomentRow523 := by decide +kernel

theorem keyMomentRowsAt524 : keyMomentRows (524 : Fin 2886) =
    keyMomentRow524 := by decide +kernel

theorem keyMomentRowsAt525 : keyMomentRows (525 : Fin 2886) =
    keyMomentRow525 := by decide +kernel

theorem keyMomentRowsAt526 : keyMomentRows (526 : Fin 2886) =
    keyMomentRow526 := by decide +kernel

theorem keyMomentRowsAt527 : keyMomentRows (527 : Fin 2886) =
    keyMomentRow527 := by decide +kernel

theorem keyMomentRowsAt528 : keyMomentRows (528 : Fin 2886) =
    keyMomentRow528 := by decide +kernel

theorem keyMomentRowsAt529 : keyMomentRows (529 : Fin 2886) =
    keyMomentRow529 := by decide +kernel

theorem keyMomentRowsAt530 : keyMomentRows (530 : Fin 2886) =
    keyMomentRow530 := by decide +kernel

theorem keyMomentRowsAt531 : keyMomentRows (531 : Fin 2886) =
    keyMomentRow531 := by decide +kernel

theorem keyMomentRowsAt532 : keyMomentRows (532 : Fin 2886) =
    keyMomentRow532 := by decide +kernel

theorem keyMomentRowsAt533 : keyMomentRows (533 : Fin 2886) =
    keyMomentRow533 := by decide +kernel

theorem keyMomentRowsAt534 : keyMomentRows (534 : Fin 2886) =
    keyMomentRow534 := by decide +kernel

theorem keyMomentRowsAt535 : keyMomentRows (535 : Fin 2886) =
    keyMomentRow535 := by decide +kernel

theorem keyMomentRowsAt536 : keyMomentRows (536 : Fin 2886) =
    keyMomentRow536 := by decide +kernel

theorem keyMomentRowsAt537 : keyMomentRows (537 : Fin 2886) =
    keyMomentRow537 := by decide +kernel

theorem keyMomentRowsAt538 : keyMomentRows (538 : Fin 2886) =
    keyMomentRow538 := by decide +kernel

theorem keyMomentRowsAt539 : keyMomentRows (539 : Fin 2886) =
    keyMomentRow539 := by decide +kernel

theorem keyMomentRowsAt540 : keyMomentRows (540 : Fin 2886) =
    keyMomentRow540 := by decide +kernel

theorem keyMomentRowsAt541 : keyMomentRows (541 : Fin 2886) =
    keyMomentRow541 := by decide +kernel

theorem keyMomentRowsAt542 : keyMomentRows (542 : Fin 2886) =
    keyMomentRow542 := by decide +kernel

theorem keyMomentRowsAt543 : keyMomentRows (543 : Fin 2886) =
    keyMomentRow543 := by decide +kernel

theorem keyMomentChunkSound16 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 16) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 512 ∨ k.val = 513 ∨ k.val = 514 ∨ k.val = 515 ∨ k.val = 516 ∨ k.val = 517 ∨ k.val = 518 ∨ k.val = 519 ∨ k.val = 520 ∨ k.val = 521 ∨ k.val = 522 ∨ k.val = 523 ∨ k.val = 524 ∨ k.val = 525 ∨ k.val = 526 ∨ k.val = 527 ∨ k.val = 528 ∨ k.val = 529 ∨ k.val = 530 ∨ k.val = 531 ∨ k.val = 532 ∨ k.val = 533 ∨ k.val = 534 ∨ k.val = 535 ∨ k.val = 536 ∨ k.val = 537 ∨ k.val = 538 ∨ k.val = 539 ∨ k.val = 540 ∨ k.val = 541 ∨ k.val = 542 ∨ k.val = 543 := by omega
  rcases heq with h512 | h513 | h514 | h515 | h516 | h517 | h518 | h519 | h520 | h521 | h522 | h523 | h524 | h525 | h526 | h527 | h528 | h529 | h530 | h531 | h532 | h533 | h534 | h535 | h536 | h537 | h538 | h539 | h540 | h541 | h542 | h543
  · have he : k = (512 : Fin 2886) := Fin.ext h512
    subst k
    rw [keyMomentRowsAt512]
    exact keyMoment512 B hB
  · have he : k = (513 : Fin 2886) := Fin.ext h513
    subst k
    rw [keyMomentRowsAt513]
    exact keyMoment513 B hB
  · have he : k = (514 : Fin 2886) := Fin.ext h514
    subst k
    rw [keyMomentRowsAt514]
    exact keyMoment514 B hB
  · have he : k = (515 : Fin 2886) := Fin.ext h515
    subst k
    rw [keyMomentRowsAt515]
    exact keyMoment515 B hB
  · have he : k = (516 : Fin 2886) := Fin.ext h516
    subst k
    rw [keyMomentRowsAt516]
    exact keyMoment516 B hB
  · have he : k = (517 : Fin 2886) := Fin.ext h517
    subst k
    rw [keyMomentRowsAt517]
    exact keyMoment517 B hB
  · have he : k = (518 : Fin 2886) := Fin.ext h518
    subst k
    rw [keyMomentRowsAt518]
    exact keyMoment518 B hB
  · have he : k = (519 : Fin 2886) := Fin.ext h519
    subst k
    rw [keyMomentRowsAt519]
    exact keyMoment519 B hB
  · have he : k = (520 : Fin 2886) := Fin.ext h520
    subst k
    rw [keyMomentRowsAt520]
    exact keyMoment520 B hB
  · have he : k = (521 : Fin 2886) := Fin.ext h521
    subst k
    rw [keyMomentRowsAt521]
    exact keyMoment521 B hB
  · have he : k = (522 : Fin 2886) := Fin.ext h522
    subst k
    rw [keyMomentRowsAt522]
    exact keyMoment522 B hB
  · have he : k = (523 : Fin 2886) := Fin.ext h523
    subst k
    rw [keyMomentRowsAt523]
    exact keyMoment523 B hB
  · have he : k = (524 : Fin 2886) := Fin.ext h524
    subst k
    rw [keyMomentRowsAt524]
    exact keyMoment524 B hB
  · have he : k = (525 : Fin 2886) := Fin.ext h525
    subst k
    rw [keyMomentRowsAt525]
    exact keyMoment525 B hB
  · have he : k = (526 : Fin 2886) := Fin.ext h526
    subst k
    rw [keyMomentRowsAt526]
    exact keyMoment526 B hB
  · have he : k = (527 : Fin 2886) := Fin.ext h527
    subst k
    rw [keyMomentRowsAt527]
    exact keyMoment527 B hB
  · have he : k = (528 : Fin 2886) := Fin.ext h528
    subst k
    rw [keyMomentRowsAt528]
    exact keyMoment528 B hB
  · have he : k = (529 : Fin 2886) := Fin.ext h529
    subst k
    rw [keyMomentRowsAt529]
    exact keyMoment529 B hB
  · have he : k = (530 : Fin 2886) := Fin.ext h530
    subst k
    rw [keyMomentRowsAt530]
    exact keyMoment530 B hB
  · have he : k = (531 : Fin 2886) := Fin.ext h531
    subst k
    rw [keyMomentRowsAt531]
    exact keyMoment531 B hB
  · have he : k = (532 : Fin 2886) := Fin.ext h532
    subst k
    rw [keyMomentRowsAt532]
    exact keyMoment532 B hB
  · have he : k = (533 : Fin 2886) := Fin.ext h533
    subst k
    rw [keyMomentRowsAt533]
    exact keyMoment533 B hB
  · have he : k = (534 : Fin 2886) := Fin.ext h534
    subst k
    rw [keyMomentRowsAt534]
    exact keyMoment534 B hB
  · have he : k = (535 : Fin 2886) := Fin.ext h535
    subst k
    rw [keyMomentRowsAt535]
    exact keyMoment535 B hB
  · have he : k = (536 : Fin 2886) := Fin.ext h536
    subst k
    rw [keyMomentRowsAt536]
    exact keyMoment536 B hB
  · have he : k = (537 : Fin 2886) := Fin.ext h537
    subst k
    rw [keyMomentRowsAt537]
    exact keyMoment537 B hB
  · have he : k = (538 : Fin 2886) := Fin.ext h538
    subst k
    rw [keyMomentRowsAt538]
    exact keyMoment538 B hB
  · have he : k = (539 : Fin 2886) := Fin.ext h539
    subst k
    rw [keyMomentRowsAt539]
    exact keyMoment539 B hB
  · have he : k = (540 : Fin 2886) := Fin.ext h540
    subst k
    rw [keyMomentRowsAt540]
    exact keyMoment540 B hB
  · have he : k = (541 : Fin 2886) := Fin.ext h541
    subst k
    rw [keyMomentRowsAt541]
    exact keyMoment541 B hB
  · have he : k = (542 : Fin 2886) := Fin.ext h542
    subst k
    rw [keyMomentRowsAt542]
    exact keyMoment542 B hB
  · have he : k = (543 : Fin 2886) := Fin.ext h543
    subst k
    rw [keyMomentRowsAt543]
    exact keyMoment543 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
