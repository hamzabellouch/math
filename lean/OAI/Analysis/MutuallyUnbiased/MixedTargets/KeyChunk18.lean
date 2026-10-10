import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound18
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt576 : keyMomentRows (576 : Fin 2886) =
    keyMomentRow576 := by decide +kernel

theorem keyMomentRowsAt577 : keyMomentRows (577 : Fin 2886) =
    keyMomentRow577 := by decide +kernel

theorem keyMomentRowsAt578 : keyMomentRows (578 : Fin 2886) =
    keyMomentRow578 := by decide +kernel

theorem keyMomentRowsAt579 : keyMomentRows (579 : Fin 2886) =
    keyMomentRow579 := by decide +kernel

theorem keyMomentRowsAt580 : keyMomentRows (580 : Fin 2886) =
    keyMomentRow580 := by decide +kernel

theorem keyMomentRowsAt581 : keyMomentRows (581 : Fin 2886) =
    keyMomentRow581 := by decide +kernel

theorem keyMomentRowsAt582 : keyMomentRows (582 : Fin 2886) =
    keyMomentRow582 := by decide +kernel

theorem keyMomentRowsAt583 : keyMomentRows (583 : Fin 2886) =
    keyMomentRow583 := by decide +kernel

theorem keyMomentRowsAt584 : keyMomentRows (584 : Fin 2886) =
    keyMomentRow584 := by decide +kernel

theorem keyMomentRowsAt585 : keyMomentRows (585 : Fin 2886) =
    keyMomentRow585 := by decide +kernel

theorem keyMomentRowsAt586 : keyMomentRows (586 : Fin 2886) =
    keyMomentRow586 := by decide +kernel

theorem keyMomentRowsAt587 : keyMomentRows (587 : Fin 2886) =
    keyMomentRow587 := by decide +kernel

theorem keyMomentRowsAt588 : keyMomentRows (588 : Fin 2886) =
    keyMomentRow588 := by decide +kernel

theorem keyMomentRowsAt589 : keyMomentRows (589 : Fin 2886) =
    keyMomentRow589 := by decide +kernel

theorem keyMomentRowsAt590 : keyMomentRows (590 : Fin 2886) =
    keyMomentRow590 := by decide +kernel

theorem keyMomentRowsAt591 : keyMomentRows (591 : Fin 2886) =
    keyMomentRow591 := by decide +kernel

theorem keyMomentRowsAt592 : keyMomentRows (592 : Fin 2886) =
    keyMomentRow592 := by decide +kernel

theorem keyMomentRowsAt593 : keyMomentRows (593 : Fin 2886) =
    keyMomentRow593 := by decide +kernel

theorem keyMomentRowsAt594 : keyMomentRows (594 : Fin 2886) =
    keyMomentRow594 := by decide +kernel

theorem keyMomentRowsAt595 : keyMomentRows (595 : Fin 2886) =
    keyMomentRow595 := by decide +kernel

theorem keyMomentRowsAt596 : keyMomentRows (596 : Fin 2886) =
    keyMomentRow596 := by decide +kernel

theorem keyMomentRowsAt597 : keyMomentRows (597 : Fin 2886) =
    keyMomentRow597 := by decide +kernel

theorem keyMomentRowsAt598 : keyMomentRows (598 : Fin 2886) =
    keyMomentRow598 := by decide +kernel

theorem keyMomentRowsAt599 : keyMomentRows (599 : Fin 2886) =
    keyMomentRow599 := by decide +kernel

theorem keyMomentRowsAt600 : keyMomentRows (600 : Fin 2886) =
    keyMomentRow600 := by decide +kernel

theorem keyMomentRowsAt601 : keyMomentRows (601 : Fin 2886) =
    keyMomentRow601 := by decide +kernel

theorem keyMomentRowsAt602 : keyMomentRows (602 : Fin 2886) =
    keyMomentRow602 := by decide +kernel

theorem keyMomentRowsAt603 : keyMomentRows (603 : Fin 2886) =
    keyMomentRow603 := by decide +kernel

theorem keyMomentRowsAt604 : keyMomentRows (604 : Fin 2886) =
    keyMomentRow604 := by decide +kernel

theorem keyMomentRowsAt605 : keyMomentRows (605 : Fin 2886) =
    keyMomentRow605 := by decide +kernel

theorem keyMomentRowsAt606 : keyMomentRows (606 : Fin 2886) =
    keyMomentRow606 := by decide +kernel

theorem keyMomentRowsAt607 : keyMomentRows (607 : Fin 2886) =
    keyMomentRow607 := by decide +kernel

theorem keyMomentChunkSound18 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 18) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 576 ∨ k.val = 577 ∨ k.val = 578 ∨ k.val = 579 ∨ k.val = 580 ∨ k.val = 581 ∨ k.val = 582 ∨ k.val = 583 ∨ k.val = 584 ∨ k.val = 585 ∨ k.val = 586 ∨ k.val = 587 ∨ k.val = 588 ∨ k.val = 589 ∨ k.val = 590 ∨ k.val = 591 ∨ k.val = 592 ∨ k.val = 593 ∨ k.val = 594 ∨ k.val = 595 ∨ k.val = 596 ∨ k.val = 597 ∨ k.val = 598 ∨ k.val = 599 ∨ k.val = 600 ∨ k.val = 601 ∨ k.val = 602 ∨ k.val = 603 ∨ k.val = 604 ∨ k.val = 605 ∨ k.val = 606 ∨ k.val = 607 := by omega
  rcases heq with h576 | h577 | h578 | h579 | h580 | h581 | h582 | h583 | h584 | h585 | h586 | h587 | h588 | h589 | h590 | h591 | h592 | h593 | h594 | h595 | h596 | h597 | h598 | h599 | h600 | h601 | h602 | h603 | h604 | h605 | h606 | h607
  · have he : k = (576 : Fin 2886) := Fin.ext h576
    subst k
    rw [keyMomentRowsAt576]
    exact keyMoment576 B hB
  · have he : k = (577 : Fin 2886) := Fin.ext h577
    subst k
    rw [keyMomentRowsAt577]
    exact keyMoment577 B hB
  · have he : k = (578 : Fin 2886) := Fin.ext h578
    subst k
    rw [keyMomentRowsAt578]
    exact keyMoment578 B hB
  · have he : k = (579 : Fin 2886) := Fin.ext h579
    subst k
    rw [keyMomentRowsAt579]
    exact keyMoment579 B hB
  · have he : k = (580 : Fin 2886) := Fin.ext h580
    subst k
    rw [keyMomentRowsAt580]
    exact keyMoment580 B hB
  · have he : k = (581 : Fin 2886) := Fin.ext h581
    subst k
    rw [keyMomentRowsAt581]
    exact keyMoment581 B hB
  · have he : k = (582 : Fin 2886) := Fin.ext h582
    subst k
    rw [keyMomentRowsAt582]
    exact keyMoment582 B hB
  · have he : k = (583 : Fin 2886) := Fin.ext h583
    subst k
    rw [keyMomentRowsAt583]
    exact keyMoment583 B hB
  · have he : k = (584 : Fin 2886) := Fin.ext h584
    subst k
    rw [keyMomentRowsAt584]
    exact keyMoment584 B hB
  · have he : k = (585 : Fin 2886) := Fin.ext h585
    subst k
    rw [keyMomentRowsAt585]
    exact keyMoment585 B hB
  · have he : k = (586 : Fin 2886) := Fin.ext h586
    subst k
    rw [keyMomentRowsAt586]
    exact keyMoment586 B hB
  · have he : k = (587 : Fin 2886) := Fin.ext h587
    subst k
    rw [keyMomentRowsAt587]
    exact keyMoment587 B hB
  · have he : k = (588 : Fin 2886) := Fin.ext h588
    subst k
    rw [keyMomentRowsAt588]
    exact keyMoment588 B hB
  · have he : k = (589 : Fin 2886) := Fin.ext h589
    subst k
    rw [keyMomentRowsAt589]
    exact keyMoment589 B hB
  · have he : k = (590 : Fin 2886) := Fin.ext h590
    subst k
    rw [keyMomentRowsAt590]
    exact keyMoment590 B hB
  · have he : k = (591 : Fin 2886) := Fin.ext h591
    subst k
    rw [keyMomentRowsAt591]
    exact keyMoment591 B hB
  · have he : k = (592 : Fin 2886) := Fin.ext h592
    subst k
    rw [keyMomentRowsAt592]
    exact keyMoment592 B hB
  · have he : k = (593 : Fin 2886) := Fin.ext h593
    subst k
    rw [keyMomentRowsAt593]
    exact keyMoment593 B hB
  · have he : k = (594 : Fin 2886) := Fin.ext h594
    subst k
    rw [keyMomentRowsAt594]
    exact keyMoment594 B hB
  · have he : k = (595 : Fin 2886) := Fin.ext h595
    subst k
    rw [keyMomentRowsAt595]
    exact keyMoment595 B hB
  · have he : k = (596 : Fin 2886) := Fin.ext h596
    subst k
    rw [keyMomentRowsAt596]
    exact keyMoment596 B hB
  · have he : k = (597 : Fin 2886) := Fin.ext h597
    subst k
    rw [keyMomentRowsAt597]
    exact keyMoment597 B hB
  · have he : k = (598 : Fin 2886) := Fin.ext h598
    subst k
    rw [keyMomentRowsAt598]
    exact keyMoment598 B hB
  · have he : k = (599 : Fin 2886) := Fin.ext h599
    subst k
    rw [keyMomentRowsAt599]
    exact keyMoment599 B hB
  · have he : k = (600 : Fin 2886) := Fin.ext h600
    subst k
    rw [keyMomentRowsAt600]
    exact keyMoment600 B hB
  · have he : k = (601 : Fin 2886) := Fin.ext h601
    subst k
    rw [keyMomentRowsAt601]
    exact keyMoment601 B hB
  · have he : k = (602 : Fin 2886) := Fin.ext h602
    subst k
    rw [keyMomentRowsAt602]
    exact keyMoment602 B hB
  · have he : k = (603 : Fin 2886) := Fin.ext h603
    subst k
    rw [keyMomentRowsAt603]
    exact keyMoment603 B hB
  · have he : k = (604 : Fin 2886) := Fin.ext h604
    subst k
    rw [keyMomentRowsAt604]
    exact keyMoment604 B hB
  · have he : k = (605 : Fin 2886) := Fin.ext h605
    subst k
    rw [keyMomentRowsAt605]
    exact keyMoment605 B hB
  · have he : k = (606 : Fin 2886) := Fin.ext h606
    subst k
    rw [keyMomentRowsAt606]
    exact keyMoment606 B hB
  · have he : k = (607 : Fin 2886) := Fin.ext h607
    subst k
    rw [keyMomentRowsAt607]
    exact keyMoment607 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
