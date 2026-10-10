import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound22
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt704 : keyMomentRows (704 : Fin 2886) =
    keyMomentRow704 := by decide +kernel

theorem keyMomentRowsAt705 : keyMomentRows (705 : Fin 2886) =
    keyMomentRow705 := by decide +kernel

theorem keyMomentRowsAt706 : keyMomentRows (706 : Fin 2886) =
    keyMomentRow706 := by decide +kernel

theorem keyMomentRowsAt707 : keyMomentRows (707 : Fin 2886) =
    keyMomentRow707 := by decide +kernel

theorem keyMomentRowsAt708 : keyMomentRows (708 : Fin 2886) =
    keyMomentRow708 := by decide +kernel

theorem keyMomentRowsAt709 : keyMomentRows (709 : Fin 2886) =
    keyMomentRow709 := by decide +kernel

theorem keyMomentRowsAt710 : keyMomentRows (710 : Fin 2886) =
    keyMomentRow710 := by decide +kernel

theorem keyMomentRowsAt711 : keyMomentRows (711 : Fin 2886) =
    keyMomentRow711 := by decide +kernel

theorem keyMomentRowsAt712 : keyMomentRows (712 : Fin 2886) =
    keyMomentRow712 := by decide +kernel

theorem keyMomentRowsAt713 : keyMomentRows (713 : Fin 2886) =
    keyMomentRow713 := by decide +kernel

theorem keyMomentRowsAt714 : keyMomentRows (714 : Fin 2886) =
    keyMomentRow714 := by decide +kernel

theorem keyMomentRowsAt715 : keyMomentRows (715 : Fin 2886) =
    keyMomentRow715 := by decide +kernel

theorem keyMomentRowsAt716 : keyMomentRows (716 : Fin 2886) =
    keyMomentRow716 := by decide +kernel

theorem keyMomentRowsAt717 : keyMomentRows (717 : Fin 2886) =
    keyMomentRow717 := by decide +kernel

theorem keyMomentRowsAt718 : keyMomentRows (718 : Fin 2886) =
    keyMomentRow718 := by decide +kernel

theorem keyMomentRowsAt719 : keyMomentRows (719 : Fin 2886) =
    keyMomentRow719 := by decide +kernel

theorem keyMomentRowsAt720 : keyMomentRows (720 : Fin 2886) =
    keyMomentRow720 := by decide +kernel

theorem keyMomentRowsAt721 : keyMomentRows (721 : Fin 2886) =
    keyMomentRow721 := by decide +kernel

theorem keyMomentRowsAt722 : keyMomentRows (722 : Fin 2886) =
    keyMomentRow722 := by decide +kernel

theorem keyMomentRowsAt723 : keyMomentRows (723 : Fin 2886) =
    keyMomentRow723 := by decide +kernel

theorem keyMomentRowsAt724 : keyMomentRows (724 : Fin 2886) =
    keyMomentRow724 := by decide +kernel

theorem keyMomentRowsAt725 : keyMomentRows (725 : Fin 2886) =
    keyMomentRow725 := by decide +kernel

theorem keyMomentRowsAt726 : keyMomentRows (726 : Fin 2886) =
    keyMomentRow726 := by decide +kernel

theorem keyMomentRowsAt727 : keyMomentRows (727 : Fin 2886) =
    keyMomentRow727 := by decide +kernel

theorem keyMomentRowsAt728 : keyMomentRows (728 : Fin 2886) =
    keyMomentRow728 := by decide +kernel

theorem keyMomentRowsAt729 : keyMomentRows (729 : Fin 2886) =
    keyMomentRow729 := by decide +kernel

theorem keyMomentRowsAt730 : keyMomentRows (730 : Fin 2886) =
    keyMomentRow730 := by decide +kernel

theorem keyMomentRowsAt731 : keyMomentRows (731 : Fin 2886) =
    keyMomentRow731 := by decide +kernel

theorem keyMomentRowsAt732 : keyMomentRows (732 : Fin 2886) =
    keyMomentRow732 := by decide +kernel

theorem keyMomentRowsAt733 : keyMomentRows (733 : Fin 2886) =
    keyMomentRow733 := by decide +kernel

theorem keyMomentRowsAt734 : keyMomentRows (734 : Fin 2886) =
    keyMomentRow734 := by decide +kernel

theorem keyMomentRowsAt735 : keyMomentRows (735 : Fin 2886) =
    keyMomentRow735 := by decide +kernel

theorem keyMomentChunkSound22 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 22) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 704 ∨ k.val = 705 ∨ k.val = 706 ∨ k.val = 707 ∨ k.val = 708 ∨ k.val = 709 ∨ k.val = 710 ∨ k.val = 711 ∨ k.val = 712 ∨ k.val = 713 ∨ k.val = 714 ∨ k.val = 715 ∨ k.val = 716 ∨ k.val = 717 ∨ k.val = 718 ∨ k.val = 719 ∨ k.val = 720 ∨ k.val = 721 ∨ k.val = 722 ∨ k.val = 723 ∨ k.val = 724 ∨ k.val = 725 ∨ k.val = 726 ∨ k.val = 727 ∨ k.val = 728 ∨ k.val = 729 ∨ k.val = 730 ∨ k.val = 731 ∨ k.val = 732 ∨ k.val = 733 ∨ k.val = 734 ∨ k.val = 735 := by omega
  rcases heq with h704 | h705 | h706 | h707 | h708 | h709 | h710 | h711 | h712 | h713 | h714 | h715 | h716 | h717 | h718 | h719 | h720 | h721 | h722 | h723 | h724 | h725 | h726 | h727 | h728 | h729 | h730 | h731 | h732 | h733 | h734 | h735
  · have he : k = (704 : Fin 2886) := Fin.ext h704
    subst k
    rw [keyMomentRowsAt704]
    exact keyMoment704 B hB
  · have he : k = (705 : Fin 2886) := Fin.ext h705
    subst k
    rw [keyMomentRowsAt705]
    exact keyMoment705 B hB
  · have he : k = (706 : Fin 2886) := Fin.ext h706
    subst k
    rw [keyMomentRowsAt706]
    exact keyMoment706 B hB
  · have he : k = (707 : Fin 2886) := Fin.ext h707
    subst k
    rw [keyMomentRowsAt707]
    exact keyMoment707 B hB
  · have he : k = (708 : Fin 2886) := Fin.ext h708
    subst k
    rw [keyMomentRowsAt708]
    exact keyMoment708 B hB
  · have he : k = (709 : Fin 2886) := Fin.ext h709
    subst k
    rw [keyMomentRowsAt709]
    exact keyMoment709 B hB
  · have he : k = (710 : Fin 2886) := Fin.ext h710
    subst k
    rw [keyMomentRowsAt710]
    exact keyMoment710 B hB
  · have he : k = (711 : Fin 2886) := Fin.ext h711
    subst k
    rw [keyMomentRowsAt711]
    exact keyMoment711 B hB
  · have he : k = (712 : Fin 2886) := Fin.ext h712
    subst k
    rw [keyMomentRowsAt712]
    exact keyMoment712 B hB
  · have he : k = (713 : Fin 2886) := Fin.ext h713
    subst k
    rw [keyMomentRowsAt713]
    exact keyMoment713 B hB
  · have he : k = (714 : Fin 2886) := Fin.ext h714
    subst k
    rw [keyMomentRowsAt714]
    exact keyMoment714 B hB
  · have he : k = (715 : Fin 2886) := Fin.ext h715
    subst k
    rw [keyMomentRowsAt715]
    exact keyMoment715 B hB
  · have he : k = (716 : Fin 2886) := Fin.ext h716
    subst k
    rw [keyMomentRowsAt716]
    exact keyMoment716 B hB
  · have he : k = (717 : Fin 2886) := Fin.ext h717
    subst k
    rw [keyMomentRowsAt717]
    exact keyMoment717 B hB
  · have he : k = (718 : Fin 2886) := Fin.ext h718
    subst k
    rw [keyMomentRowsAt718]
    exact keyMoment718 B hB
  · have he : k = (719 : Fin 2886) := Fin.ext h719
    subst k
    rw [keyMomentRowsAt719]
    exact keyMoment719 B hB
  · have he : k = (720 : Fin 2886) := Fin.ext h720
    subst k
    rw [keyMomentRowsAt720]
    exact keyMoment720 B hB
  · have he : k = (721 : Fin 2886) := Fin.ext h721
    subst k
    rw [keyMomentRowsAt721]
    exact keyMoment721 B hB
  · have he : k = (722 : Fin 2886) := Fin.ext h722
    subst k
    rw [keyMomentRowsAt722]
    exact keyMoment722 B hB
  · have he : k = (723 : Fin 2886) := Fin.ext h723
    subst k
    rw [keyMomentRowsAt723]
    exact keyMoment723 B hB
  · have he : k = (724 : Fin 2886) := Fin.ext h724
    subst k
    rw [keyMomentRowsAt724]
    exact keyMoment724 B hB
  · have he : k = (725 : Fin 2886) := Fin.ext h725
    subst k
    rw [keyMomentRowsAt725]
    exact keyMoment725 B hB
  · have he : k = (726 : Fin 2886) := Fin.ext h726
    subst k
    rw [keyMomentRowsAt726]
    exact keyMoment726 B hB
  · have he : k = (727 : Fin 2886) := Fin.ext h727
    subst k
    rw [keyMomentRowsAt727]
    exact keyMoment727 B hB
  · have he : k = (728 : Fin 2886) := Fin.ext h728
    subst k
    rw [keyMomentRowsAt728]
    exact keyMoment728 B hB
  · have he : k = (729 : Fin 2886) := Fin.ext h729
    subst k
    rw [keyMomentRowsAt729]
    exact keyMoment729 B hB
  · have he : k = (730 : Fin 2886) := Fin.ext h730
    subst k
    rw [keyMomentRowsAt730]
    exact keyMoment730 B hB
  · have he : k = (731 : Fin 2886) := Fin.ext h731
    subst k
    rw [keyMomentRowsAt731]
    exact keyMoment731 B hB
  · have he : k = (732 : Fin 2886) := Fin.ext h732
    subst k
    rw [keyMomentRowsAt732]
    exact keyMoment732 B hB
  · have he : k = (733 : Fin 2886) := Fin.ext h733
    subst k
    rw [keyMomentRowsAt733]
    exact keyMoment733 B hB
  · have he : k = (734 : Fin 2886) := Fin.ext h734
    subst k
    rw [keyMomentRowsAt734]
    exact keyMoment734 B hB
  · have he : k = (735 : Fin 2886) := Fin.ext h735
    subst k
    rw [keyMomentRowsAt735]
    exact keyMoment735 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
