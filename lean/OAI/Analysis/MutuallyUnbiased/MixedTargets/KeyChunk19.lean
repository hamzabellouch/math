import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound19
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt608 : keyMomentRows (608 : Fin 2886) =
    keyMomentRow608 := by decide +kernel

theorem keyMomentRowsAt609 : keyMomentRows (609 : Fin 2886) =
    keyMomentRow609 := by decide +kernel

theorem keyMomentRowsAt610 : keyMomentRows (610 : Fin 2886) =
    keyMomentRow610 := by decide +kernel

theorem keyMomentRowsAt611 : keyMomentRows (611 : Fin 2886) =
    keyMomentRow611 := by decide +kernel

theorem keyMomentRowsAt612 : keyMomentRows (612 : Fin 2886) =
    keyMomentRow612 := by decide +kernel

theorem keyMomentRowsAt613 : keyMomentRows (613 : Fin 2886) =
    keyMomentRow613 := by decide +kernel

theorem keyMomentRowsAt614 : keyMomentRows (614 : Fin 2886) =
    keyMomentRow614 := by decide +kernel

theorem keyMomentRowsAt615 : keyMomentRows (615 : Fin 2886) =
    keyMomentRow615 := by decide +kernel

theorem keyMomentRowsAt616 : keyMomentRows (616 : Fin 2886) =
    keyMomentRow616 := by decide +kernel

theorem keyMomentRowsAt617 : keyMomentRows (617 : Fin 2886) =
    keyMomentRow617 := by decide +kernel

theorem keyMomentRowsAt618 : keyMomentRows (618 : Fin 2886) =
    keyMomentRow618 := by decide +kernel

theorem keyMomentRowsAt619 : keyMomentRows (619 : Fin 2886) =
    keyMomentRow619 := by decide +kernel

theorem keyMomentRowsAt620 : keyMomentRows (620 : Fin 2886) =
    keyMomentRow620 := by decide +kernel

theorem keyMomentRowsAt621 : keyMomentRows (621 : Fin 2886) =
    keyMomentRow621 := by decide +kernel

theorem keyMomentRowsAt622 : keyMomentRows (622 : Fin 2886) =
    keyMomentRow622 := by decide +kernel

theorem keyMomentRowsAt623 : keyMomentRows (623 : Fin 2886) =
    keyMomentRow623 := by decide +kernel

theorem keyMomentRowsAt624 : keyMomentRows (624 : Fin 2886) =
    keyMomentRow624 := by decide +kernel

theorem keyMomentRowsAt625 : keyMomentRows (625 : Fin 2886) =
    keyMomentRow625 := by decide +kernel

theorem keyMomentRowsAt626 : keyMomentRows (626 : Fin 2886) =
    keyMomentRow626 := by decide +kernel

theorem keyMomentRowsAt627 : keyMomentRows (627 : Fin 2886) =
    keyMomentRow627 := by decide +kernel

theorem keyMomentRowsAt628 : keyMomentRows (628 : Fin 2886) =
    keyMomentRow628 := by decide +kernel

theorem keyMomentRowsAt629 : keyMomentRows (629 : Fin 2886) =
    keyMomentRow629 := by decide +kernel

theorem keyMomentRowsAt630 : keyMomentRows (630 : Fin 2886) =
    keyMomentRow630 := by decide +kernel

theorem keyMomentRowsAt631 : keyMomentRows (631 : Fin 2886) =
    keyMomentRow631 := by decide +kernel

theorem keyMomentRowsAt632 : keyMomentRows (632 : Fin 2886) =
    keyMomentRow632 := by decide +kernel

theorem keyMomentRowsAt633 : keyMomentRows (633 : Fin 2886) =
    keyMomentRow633 := by decide +kernel

theorem keyMomentRowsAt634 : keyMomentRows (634 : Fin 2886) =
    keyMomentRow634 := by decide +kernel

theorem keyMomentRowsAt635 : keyMomentRows (635 : Fin 2886) =
    keyMomentRow635 := by decide +kernel

theorem keyMomentRowsAt636 : keyMomentRows (636 : Fin 2886) =
    keyMomentRow636 := by decide +kernel

theorem keyMomentRowsAt637 : keyMomentRows (637 : Fin 2886) =
    keyMomentRow637 := by decide +kernel

theorem keyMomentRowsAt638 : keyMomentRows (638 : Fin 2886) =
    keyMomentRow638 := by decide +kernel

theorem keyMomentRowsAt639 : keyMomentRows (639 : Fin 2886) =
    keyMomentRow639 := by decide +kernel

theorem keyMomentChunkSound19 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 19) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 608 ∨ k.val = 609 ∨ k.val = 610 ∨ k.val = 611 ∨ k.val = 612 ∨ k.val = 613 ∨ k.val = 614 ∨ k.val = 615 ∨ k.val = 616 ∨ k.val = 617 ∨ k.val = 618 ∨ k.val = 619 ∨ k.val = 620 ∨ k.val = 621 ∨ k.val = 622 ∨ k.val = 623 ∨ k.val = 624 ∨ k.val = 625 ∨ k.val = 626 ∨ k.val = 627 ∨ k.val = 628 ∨ k.val = 629 ∨ k.val = 630 ∨ k.val = 631 ∨ k.val = 632 ∨ k.val = 633 ∨ k.val = 634 ∨ k.val = 635 ∨ k.val = 636 ∨ k.val = 637 ∨ k.val = 638 ∨ k.val = 639 := by omega
  rcases heq with h608 | h609 | h610 | h611 | h612 | h613 | h614 | h615 | h616 | h617 | h618 | h619 | h620 | h621 | h622 | h623 | h624 | h625 | h626 | h627 | h628 | h629 | h630 | h631 | h632 | h633 | h634 | h635 | h636 | h637 | h638 | h639
  · have he : k = (608 : Fin 2886) := Fin.ext h608
    subst k
    rw [keyMomentRowsAt608]
    exact keyMoment608 B hB
  · have he : k = (609 : Fin 2886) := Fin.ext h609
    subst k
    rw [keyMomentRowsAt609]
    exact keyMoment609 B hB
  · have he : k = (610 : Fin 2886) := Fin.ext h610
    subst k
    rw [keyMomentRowsAt610]
    exact keyMoment610 B hB
  · have he : k = (611 : Fin 2886) := Fin.ext h611
    subst k
    rw [keyMomentRowsAt611]
    exact keyMoment611 B hB
  · have he : k = (612 : Fin 2886) := Fin.ext h612
    subst k
    rw [keyMomentRowsAt612]
    exact keyMoment612 B hB
  · have he : k = (613 : Fin 2886) := Fin.ext h613
    subst k
    rw [keyMomentRowsAt613]
    exact keyMoment613 B hB
  · have he : k = (614 : Fin 2886) := Fin.ext h614
    subst k
    rw [keyMomentRowsAt614]
    exact keyMoment614 B hB
  · have he : k = (615 : Fin 2886) := Fin.ext h615
    subst k
    rw [keyMomentRowsAt615]
    exact keyMoment615 B hB
  · have he : k = (616 : Fin 2886) := Fin.ext h616
    subst k
    rw [keyMomentRowsAt616]
    exact keyMoment616 B hB
  · have he : k = (617 : Fin 2886) := Fin.ext h617
    subst k
    rw [keyMomentRowsAt617]
    exact keyMoment617 B hB
  · have he : k = (618 : Fin 2886) := Fin.ext h618
    subst k
    rw [keyMomentRowsAt618]
    exact keyMoment618 B hB
  · have he : k = (619 : Fin 2886) := Fin.ext h619
    subst k
    rw [keyMomentRowsAt619]
    exact keyMoment619 B hB
  · have he : k = (620 : Fin 2886) := Fin.ext h620
    subst k
    rw [keyMomentRowsAt620]
    exact keyMoment620 B hB
  · have he : k = (621 : Fin 2886) := Fin.ext h621
    subst k
    rw [keyMomentRowsAt621]
    exact keyMoment621 B hB
  · have he : k = (622 : Fin 2886) := Fin.ext h622
    subst k
    rw [keyMomentRowsAt622]
    exact keyMoment622 B hB
  · have he : k = (623 : Fin 2886) := Fin.ext h623
    subst k
    rw [keyMomentRowsAt623]
    exact keyMoment623 B hB
  · have he : k = (624 : Fin 2886) := Fin.ext h624
    subst k
    rw [keyMomentRowsAt624]
    exact keyMoment624 B hB
  · have he : k = (625 : Fin 2886) := Fin.ext h625
    subst k
    rw [keyMomentRowsAt625]
    exact keyMoment625 B hB
  · have he : k = (626 : Fin 2886) := Fin.ext h626
    subst k
    rw [keyMomentRowsAt626]
    exact keyMoment626 B hB
  · have he : k = (627 : Fin 2886) := Fin.ext h627
    subst k
    rw [keyMomentRowsAt627]
    exact keyMoment627 B hB
  · have he : k = (628 : Fin 2886) := Fin.ext h628
    subst k
    rw [keyMomentRowsAt628]
    exact keyMoment628 B hB
  · have he : k = (629 : Fin 2886) := Fin.ext h629
    subst k
    rw [keyMomentRowsAt629]
    exact keyMoment629 B hB
  · have he : k = (630 : Fin 2886) := Fin.ext h630
    subst k
    rw [keyMomentRowsAt630]
    exact keyMoment630 B hB
  · have he : k = (631 : Fin 2886) := Fin.ext h631
    subst k
    rw [keyMomentRowsAt631]
    exact keyMoment631 B hB
  · have he : k = (632 : Fin 2886) := Fin.ext h632
    subst k
    rw [keyMomentRowsAt632]
    exact keyMoment632 B hB
  · have he : k = (633 : Fin 2886) := Fin.ext h633
    subst k
    rw [keyMomentRowsAt633]
    exact keyMoment633 B hB
  · have he : k = (634 : Fin 2886) := Fin.ext h634
    subst k
    rw [keyMomentRowsAt634]
    exact keyMoment634 B hB
  · have he : k = (635 : Fin 2886) := Fin.ext h635
    subst k
    rw [keyMomentRowsAt635]
    exact keyMoment635 B hB
  · have he : k = (636 : Fin 2886) := Fin.ext h636
    subst k
    rw [keyMomentRowsAt636]
    exact keyMoment636 B hB
  · have he : k = (637 : Fin 2886) := Fin.ext h637
    subst k
    rw [keyMomentRowsAt637]
    exact keyMoment637 B hB
  · have he : k = (638 : Fin 2886) := Fin.ext h638
    subst k
    rw [keyMomentRowsAt638]
    exact keyMoment638 B hB
  · have he : k = (639 : Fin 2886) := Fin.ext h639
    subst k
    rw [keyMomentRowsAt639]
    exact keyMoment639 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
