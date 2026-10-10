import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound20
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt640 : keyMomentRows (640 : Fin 2886) =
    keyMomentRow640 := by decide +kernel

theorem keyMomentRowsAt641 : keyMomentRows (641 : Fin 2886) =
    keyMomentRow641 := by decide +kernel

theorem keyMomentRowsAt642 : keyMomentRows (642 : Fin 2886) =
    keyMomentRow642 := by decide +kernel

theorem keyMomentRowsAt643 : keyMomentRows (643 : Fin 2886) =
    keyMomentRow643 := by decide +kernel

theorem keyMomentRowsAt644 : keyMomentRows (644 : Fin 2886) =
    keyMomentRow644 := by decide +kernel

theorem keyMomentRowsAt645 : keyMomentRows (645 : Fin 2886) =
    keyMomentRow645 := by decide +kernel

theorem keyMomentRowsAt646 : keyMomentRows (646 : Fin 2886) =
    keyMomentRow646 := by decide +kernel

theorem keyMomentRowsAt647 : keyMomentRows (647 : Fin 2886) =
    keyMomentRow647 := by decide +kernel

theorem keyMomentRowsAt648 : keyMomentRows (648 : Fin 2886) =
    keyMomentRow648 := by decide +kernel

theorem keyMomentRowsAt649 : keyMomentRows (649 : Fin 2886) =
    keyMomentRow649 := by decide +kernel

theorem keyMomentRowsAt650 : keyMomentRows (650 : Fin 2886) =
    keyMomentRow650 := by decide +kernel

theorem keyMomentRowsAt651 : keyMomentRows (651 : Fin 2886) =
    keyMomentRow651 := by decide +kernel

theorem keyMomentRowsAt652 : keyMomentRows (652 : Fin 2886) =
    keyMomentRow652 := by decide +kernel

theorem keyMomentRowsAt653 : keyMomentRows (653 : Fin 2886) =
    keyMomentRow653 := by decide +kernel

theorem keyMomentRowsAt654 : keyMomentRows (654 : Fin 2886) =
    keyMomentRow654 := by decide +kernel

theorem keyMomentRowsAt655 : keyMomentRows (655 : Fin 2886) =
    keyMomentRow655 := by decide +kernel

theorem keyMomentRowsAt656 : keyMomentRows (656 : Fin 2886) =
    keyMomentRow656 := by decide +kernel

theorem keyMomentRowsAt657 : keyMomentRows (657 : Fin 2886) =
    keyMomentRow657 := by decide +kernel

theorem keyMomentRowsAt658 : keyMomentRows (658 : Fin 2886) =
    keyMomentRow658 := by decide +kernel

theorem keyMomentRowsAt659 : keyMomentRows (659 : Fin 2886) =
    keyMomentRow659 := by decide +kernel

theorem keyMomentRowsAt660 : keyMomentRows (660 : Fin 2886) =
    keyMomentRow660 := by decide +kernel

theorem keyMomentRowsAt661 : keyMomentRows (661 : Fin 2886) =
    keyMomentRow661 := by decide +kernel

theorem keyMomentRowsAt662 : keyMomentRows (662 : Fin 2886) =
    keyMomentRow662 := by decide +kernel

theorem keyMomentRowsAt663 : keyMomentRows (663 : Fin 2886) =
    keyMomentRow663 := by decide +kernel

theorem keyMomentRowsAt664 : keyMomentRows (664 : Fin 2886) =
    keyMomentRow664 := by decide +kernel

theorem keyMomentRowsAt665 : keyMomentRows (665 : Fin 2886) =
    keyMomentRow665 := by decide +kernel

theorem keyMomentRowsAt666 : keyMomentRows (666 : Fin 2886) =
    keyMomentRow666 := by decide +kernel

theorem keyMomentRowsAt667 : keyMomentRows (667 : Fin 2886) =
    keyMomentRow667 := by decide +kernel

theorem keyMomentRowsAt668 : keyMomentRows (668 : Fin 2886) =
    keyMomentRow668 := by decide +kernel

theorem keyMomentRowsAt669 : keyMomentRows (669 : Fin 2886) =
    keyMomentRow669 := by decide +kernel

theorem keyMomentRowsAt670 : keyMomentRows (670 : Fin 2886) =
    keyMomentRow670 := by decide +kernel

theorem keyMomentRowsAt671 : keyMomentRows (671 : Fin 2886) =
    keyMomentRow671 := by decide +kernel

theorem keyMomentChunkSound20 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 20) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 640 ∨ k.val = 641 ∨ k.val = 642 ∨ k.val = 643 ∨ k.val = 644 ∨ k.val = 645 ∨ k.val = 646 ∨ k.val = 647 ∨ k.val = 648 ∨ k.val = 649 ∨ k.val = 650 ∨ k.val = 651 ∨ k.val = 652 ∨ k.val = 653 ∨ k.val = 654 ∨ k.val = 655 ∨ k.val = 656 ∨ k.val = 657 ∨ k.val = 658 ∨ k.val = 659 ∨ k.val = 660 ∨ k.val = 661 ∨ k.val = 662 ∨ k.val = 663 ∨ k.val = 664 ∨ k.val = 665 ∨ k.val = 666 ∨ k.val = 667 ∨ k.val = 668 ∨ k.val = 669 ∨ k.val = 670 ∨ k.val = 671 := by omega
  rcases heq with h640 | h641 | h642 | h643 | h644 | h645 | h646 | h647 | h648 | h649 | h650 | h651 | h652 | h653 | h654 | h655 | h656 | h657 | h658 | h659 | h660 | h661 | h662 | h663 | h664 | h665 | h666 | h667 | h668 | h669 | h670 | h671
  · have he : k = (640 : Fin 2886) := Fin.ext h640
    subst k
    rw [keyMomentRowsAt640]
    exact keyMoment640 B hB
  · have he : k = (641 : Fin 2886) := Fin.ext h641
    subst k
    rw [keyMomentRowsAt641]
    exact keyMoment641 B hB
  · have he : k = (642 : Fin 2886) := Fin.ext h642
    subst k
    rw [keyMomentRowsAt642]
    exact keyMoment642 B hB
  · have he : k = (643 : Fin 2886) := Fin.ext h643
    subst k
    rw [keyMomentRowsAt643]
    exact keyMoment643 B hB
  · have he : k = (644 : Fin 2886) := Fin.ext h644
    subst k
    rw [keyMomentRowsAt644]
    exact keyMoment644 B hB
  · have he : k = (645 : Fin 2886) := Fin.ext h645
    subst k
    rw [keyMomentRowsAt645]
    exact keyMoment645 B hB
  · have he : k = (646 : Fin 2886) := Fin.ext h646
    subst k
    rw [keyMomentRowsAt646]
    exact keyMoment646 B hB
  · have he : k = (647 : Fin 2886) := Fin.ext h647
    subst k
    rw [keyMomentRowsAt647]
    exact keyMoment647 B hB
  · have he : k = (648 : Fin 2886) := Fin.ext h648
    subst k
    rw [keyMomentRowsAt648]
    exact keyMoment648 B hB
  · have he : k = (649 : Fin 2886) := Fin.ext h649
    subst k
    rw [keyMomentRowsAt649]
    exact keyMoment649 B hB
  · have he : k = (650 : Fin 2886) := Fin.ext h650
    subst k
    rw [keyMomentRowsAt650]
    exact keyMoment650 B hB
  · have he : k = (651 : Fin 2886) := Fin.ext h651
    subst k
    rw [keyMomentRowsAt651]
    exact keyMoment651 B hB
  · have he : k = (652 : Fin 2886) := Fin.ext h652
    subst k
    rw [keyMomentRowsAt652]
    exact keyMoment652 B hB
  · have he : k = (653 : Fin 2886) := Fin.ext h653
    subst k
    rw [keyMomentRowsAt653]
    exact keyMoment653 B hB
  · have he : k = (654 : Fin 2886) := Fin.ext h654
    subst k
    rw [keyMomentRowsAt654]
    exact keyMoment654 B hB
  · have he : k = (655 : Fin 2886) := Fin.ext h655
    subst k
    rw [keyMomentRowsAt655]
    exact keyMoment655 B hB
  · have he : k = (656 : Fin 2886) := Fin.ext h656
    subst k
    rw [keyMomentRowsAt656]
    exact keyMoment656 B hB
  · have he : k = (657 : Fin 2886) := Fin.ext h657
    subst k
    rw [keyMomentRowsAt657]
    exact keyMoment657 B hB
  · have he : k = (658 : Fin 2886) := Fin.ext h658
    subst k
    rw [keyMomentRowsAt658]
    exact keyMoment658 B hB
  · have he : k = (659 : Fin 2886) := Fin.ext h659
    subst k
    rw [keyMomentRowsAt659]
    exact keyMoment659 B hB
  · have he : k = (660 : Fin 2886) := Fin.ext h660
    subst k
    rw [keyMomentRowsAt660]
    exact keyMoment660 B hB
  · have he : k = (661 : Fin 2886) := Fin.ext h661
    subst k
    rw [keyMomentRowsAt661]
    exact keyMoment661 B hB
  · have he : k = (662 : Fin 2886) := Fin.ext h662
    subst k
    rw [keyMomentRowsAt662]
    exact keyMoment662 B hB
  · have he : k = (663 : Fin 2886) := Fin.ext h663
    subst k
    rw [keyMomentRowsAt663]
    exact keyMoment663 B hB
  · have he : k = (664 : Fin 2886) := Fin.ext h664
    subst k
    rw [keyMomentRowsAt664]
    exact keyMoment664 B hB
  · have he : k = (665 : Fin 2886) := Fin.ext h665
    subst k
    rw [keyMomentRowsAt665]
    exact keyMoment665 B hB
  · have he : k = (666 : Fin 2886) := Fin.ext h666
    subst k
    rw [keyMomentRowsAt666]
    exact keyMoment666 B hB
  · have he : k = (667 : Fin 2886) := Fin.ext h667
    subst k
    rw [keyMomentRowsAt667]
    exact keyMoment667 B hB
  · have he : k = (668 : Fin 2886) := Fin.ext h668
    subst k
    rw [keyMomentRowsAt668]
    exact keyMoment668 B hB
  · have he : k = (669 : Fin 2886) := Fin.ext h669
    subst k
    rw [keyMomentRowsAt669]
    exact keyMoment669 B hB
  · have he : k = (670 : Fin 2886) := Fin.ext h670
    subst k
    rw [keyMomentRowsAt670]
    exact keyMoment670 B hB
  · have he : k = (671 : Fin 2886) := Fin.ext h671
    subst k
    rw [keyMomentRowsAt671]
    exact keyMoment671 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
