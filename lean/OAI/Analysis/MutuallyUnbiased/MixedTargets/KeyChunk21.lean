import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound21
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt672 : keyMomentRows (672 : Fin 2886) =
    keyMomentRow672 := by decide +kernel

theorem keyMomentRowsAt673 : keyMomentRows (673 : Fin 2886) =
    keyMomentRow673 := by decide +kernel

theorem keyMomentRowsAt674 : keyMomentRows (674 : Fin 2886) =
    keyMomentRow674 := by decide +kernel

theorem keyMomentRowsAt675 : keyMomentRows (675 : Fin 2886) =
    keyMomentRow675 := by decide +kernel

theorem keyMomentRowsAt676 : keyMomentRows (676 : Fin 2886) =
    keyMomentRow676 := by decide +kernel

theorem keyMomentRowsAt677 : keyMomentRows (677 : Fin 2886) =
    keyMomentRow677 := by decide +kernel

theorem keyMomentRowsAt678 : keyMomentRows (678 : Fin 2886) =
    keyMomentRow678 := by decide +kernel

theorem keyMomentRowsAt679 : keyMomentRows (679 : Fin 2886) =
    keyMomentRow679 := by decide +kernel

theorem keyMomentRowsAt680 : keyMomentRows (680 : Fin 2886) =
    keyMomentRow680 := by decide +kernel

theorem keyMomentRowsAt681 : keyMomentRows (681 : Fin 2886) =
    keyMomentRow681 := by decide +kernel

theorem keyMomentRowsAt682 : keyMomentRows (682 : Fin 2886) =
    keyMomentRow682 := by decide +kernel

theorem keyMomentRowsAt683 : keyMomentRows (683 : Fin 2886) =
    keyMomentRow683 := by decide +kernel

theorem keyMomentRowsAt684 : keyMomentRows (684 : Fin 2886) =
    keyMomentRow684 := by decide +kernel

theorem keyMomentRowsAt685 : keyMomentRows (685 : Fin 2886) =
    keyMomentRow685 := by decide +kernel

theorem keyMomentRowsAt686 : keyMomentRows (686 : Fin 2886) =
    keyMomentRow686 := by decide +kernel

theorem keyMomentRowsAt687 : keyMomentRows (687 : Fin 2886) =
    keyMomentRow687 := by decide +kernel

theorem keyMomentRowsAt688 : keyMomentRows (688 : Fin 2886) =
    keyMomentRow688 := by decide +kernel

theorem keyMomentRowsAt689 : keyMomentRows (689 : Fin 2886) =
    keyMomentRow689 := by decide +kernel

theorem keyMomentRowsAt690 : keyMomentRows (690 : Fin 2886) =
    keyMomentRow690 := by decide +kernel

theorem keyMomentRowsAt691 : keyMomentRows (691 : Fin 2886) =
    keyMomentRow691 := by decide +kernel

theorem keyMomentRowsAt692 : keyMomentRows (692 : Fin 2886) =
    keyMomentRow692 := by decide +kernel

theorem keyMomentRowsAt693 : keyMomentRows (693 : Fin 2886) =
    keyMomentRow693 := by decide +kernel

theorem keyMomentRowsAt694 : keyMomentRows (694 : Fin 2886) =
    keyMomentRow694 := by decide +kernel

theorem keyMomentRowsAt695 : keyMomentRows (695 : Fin 2886) =
    keyMomentRow695 := by decide +kernel

theorem keyMomentRowsAt696 : keyMomentRows (696 : Fin 2886) =
    keyMomentRow696 := by decide +kernel

theorem keyMomentRowsAt697 : keyMomentRows (697 : Fin 2886) =
    keyMomentRow697 := by decide +kernel

theorem keyMomentRowsAt698 : keyMomentRows (698 : Fin 2886) =
    keyMomentRow698 := by decide +kernel

theorem keyMomentRowsAt699 : keyMomentRows (699 : Fin 2886) =
    keyMomentRow699 := by decide +kernel

theorem keyMomentRowsAt700 : keyMomentRows (700 : Fin 2886) =
    keyMomentRow700 := by decide +kernel

theorem keyMomentRowsAt701 : keyMomentRows (701 : Fin 2886) =
    keyMomentRow701 := by decide +kernel

theorem keyMomentRowsAt702 : keyMomentRows (702 : Fin 2886) =
    keyMomentRow702 := by decide +kernel

theorem keyMomentRowsAt703 : keyMomentRows (703 : Fin 2886) =
    keyMomentRow703 := by decide +kernel

theorem keyMomentChunkSound21 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 21) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 672 ∨ k.val = 673 ∨ k.val = 674 ∨ k.val = 675 ∨ k.val = 676 ∨ k.val = 677 ∨ k.val = 678 ∨ k.val = 679 ∨ k.val = 680 ∨ k.val = 681 ∨ k.val = 682 ∨ k.val = 683 ∨ k.val = 684 ∨ k.val = 685 ∨ k.val = 686 ∨ k.val = 687 ∨ k.val = 688 ∨ k.val = 689 ∨ k.val = 690 ∨ k.val = 691 ∨ k.val = 692 ∨ k.val = 693 ∨ k.val = 694 ∨ k.val = 695 ∨ k.val = 696 ∨ k.val = 697 ∨ k.val = 698 ∨ k.val = 699 ∨ k.val = 700 ∨ k.val = 701 ∨ k.val = 702 ∨ k.val = 703 := by omega
  rcases heq with h672 | h673 | h674 | h675 | h676 | h677 | h678 | h679 | h680 | h681 | h682 | h683 | h684 | h685 | h686 | h687 | h688 | h689 | h690 | h691 | h692 | h693 | h694 | h695 | h696 | h697 | h698 | h699 | h700 | h701 | h702 | h703
  · have he : k = (672 : Fin 2886) := Fin.ext h672
    subst k
    rw [keyMomentRowsAt672]
    exact keyMoment672 B hB
  · have he : k = (673 : Fin 2886) := Fin.ext h673
    subst k
    rw [keyMomentRowsAt673]
    exact keyMoment673 B hB
  · have he : k = (674 : Fin 2886) := Fin.ext h674
    subst k
    rw [keyMomentRowsAt674]
    exact keyMoment674 B hB
  · have he : k = (675 : Fin 2886) := Fin.ext h675
    subst k
    rw [keyMomentRowsAt675]
    exact keyMoment675 B hB
  · have he : k = (676 : Fin 2886) := Fin.ext h676
    subst k
    rw [keyMomentRowsAt676]
    exact keyMoment676 B hB
  · have he : k = (677 : Fin 2886) := Fin.ext h677
    subst k
    rw [keyMomentRowsAt677]
    exact keyMoment677 B hB
  · have he : k = (678 : Fin 2886) := Fin.ext h678
    subst k
    rw [keyMomentRowsAt678]
    exact keyMoment678 B hB
  · have he : k = (679 : Fin 2886) := Fin.ext h679
    subst k
    rw [keyMomentRowsAt679]
    exact keyMoment679 B hB
  · have he : k = (680 : Fin 2886) := Fin.ext h680
    subst k
    rw [keyMomentRowsAt680]
    exact keyMoment680 B hB
  · have he : k = (681 : Fin 2886) := Fin.ext h681
    subst k
    rw [keyMomentRowsAt681]
    exact keyMoment681 B hB
  · have he : k = (682 : Fin 2886) := Fin.ext h682
    subst k
    rw [keyMomentRowsAt682]
    exact keyMoment682 B hB
  · have he : k = (683 : Fin 2886) := Fin.ext h683
    subst k
    rw [keyMomentRowsAt683]
    exact keyMoment683 B hB
  · have he : k = (684 : Fin 2886) := Fin.ext h684
    subst k
    rw [keyMomentRowsAt684]
    exact keyMoment684 B hB
  · have he : k = (685 : Fin 2886) := Fin.ext h685
    subst k
    rw [keyMomentRowsAt685]
    exact keyMoment685 B hB
  · have he : k = (686 : Fin 2886) := Fin.ext h686
    subst k
    rw [keyMomentRowsAt686]
    exact keyMoment686 B hB
  · have he : k = (687 : Fin 2886) := Fin.ext h687
    subst k
    rw [keyMomentRowsAt687]
    exact keyMoment687 B hB
  · have he : k = (688 : Fin 2886) := Fin.ext h688
    subst k
    rw [keyMomentRowsAt688]
    exact keyMoment688 B hB
  · have he : k = (689 : Fin 2886) := Fin.ext h689
    subst k
    rw [keyMomentRowsAt689]
    exact keyMoment689 B hB
  · have he : k = (690 : Fin 2886) := Fin.ext h690
    subst k
    rw [keyMomentRowsAt690]
    exact keyMoment690 B hB
  · have he : k = (691 : Fin 2886) := Fin.ext h691
    subst k
    rw [keyMomentRowsAt691]
    exact keyMoment691 B hB
  · have he : k = (692 : Fin 2886) := Fin.ext h692
    subst k
    rw [keyMomentRowsAt692]
    exact keyMoment692 B hB
  · have he : k = (693 : Fin 2886) := Fin.ext h693
    subst k
    rw [keyMomentRowsAt693]
    exact keyMoment693 B hB
  · have he : k = (694 : Fin 2886) := Fin.ext h694
    subst k
    rw [keyMomentRowsAt694]
    exact keyMoment694 B hB
  · have he : k = (695 : Fin 2886) := Fin.ext h695
    subst k
    rw [keyMomentRowsAt695]
    exact keyMoment695 B hB
  · have he : k = (696 : Fin 2886) := Fin.ext h696
    subst k
    rw [keyMomentRowsAt696]
    exact keyMoment696 B hB
  · have he : k = (697 : Fin 2886) := Fin.ext h697
    subst k
    rw [keyMomentRowsAt697]
    exact keyMoment697 B hB
  · have he : k = (698 : Fin 2886) := Fin.ext h698
    subst k
    rw [keyMomentRowsAt698]
    exact keyMoment698 B hB
  · have he : k = (699 : Fin 2886) := Fin.ext h699
    subst k
    rw [keyMomentRowsAt699]
    exact keyMoment699 B hB
  · have he : k = (700 : Fin 2886) := Fin.ext h700
    subst k
    rw [keyMomentRowsAt700]
    exact keyMoment700 B hB
  · have he : k = (701 : Fin 2886) := Fin.ext h701
    subst k
    rw [keyMomentRowsAt701]
    exact keyMoment701 B hB
  · have he : k = (702 : Fin 2886) := Fin.ext h702
    subst k
    rw [keyMomentRowsAt702]
    exact keyMoment702 B hB
  · have he : k = (703 : Fin 2886) := Fin.ext h703
    subst k
    rw [keyMomentRowsAt703]
    exact keyMoment703 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
