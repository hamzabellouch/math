import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound25
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt800 : keyMomentRows (800 : Fin 2886) =
    keyMomentRow800 := by decide +kernel

theorem keyMomentRowsAt801 : keyMomentRows (801 : Fin 2886) =
    keyMomentRow801 := by decide +kernel

theorem keyMomentRowsAt802 : keyMomentRows (802 : Fin 2886) =
    keyMomentRow802 := by decide +kernel

theorem keyMomentRowsAt803 : keyMomentRows (803 : Fin 2886) =
    keyMomentRow803 := by decide +kernel

theorem keyMomentRowsAt804 : keyMomentRows (804 : Fin 2886) =
    keyMomentRow804 := by decide +kernel

theorem keyMomentRowsAt805 : keyMomentRows (805 : Fin 2886) =
    keyMomentRow805 := by decide +kernel

theorem keyMomentRowsAt806 : keyMomentRows (806 : Fin 2886) =
    keyMomentRow806 := by decide +kernel

theorem keyMomentRowsAt807 : keyMomentRows (807 : Fin 2886) =
    keyMomentRow807 := by decide +kernel

theorem keyMomentRowsAt808 : keyMomentRows (808 : Fin 2886) =
    keyMomentRow808 := by decide +kernel

theorem keyMomentRowsAt809 : keyMomentRows (809 : Fin 2886) =
    keyMomentRow809 := by decide +kernel

theorem keyMomentRowsAt810 : keyMomentRows (810 : Fin 2886) =
    keyMomentRow810 := by decide +kernel

theorem keyMomentRowsAt811 : keyMomentRows (811 : Fin 2886) =
    keyMomentRow811 := by decide +kernel

theorem keyMomentRowsAt812 : keyMomentRows (812 : Fin 2886) =
    keyMomentRow812 := by decide +kernel

theorem keyMomentRowsAt813 : keyMomentRows (813 : Fin 2886) =
    keyMomentRow813 := by decide +kernel

theorem keyMomentRowsAt814 : keyMomentRows (814 : Fin 2886) =
    keyMomentRow814 := by decide +kernel

theorem keyMomentRowsAt815 : keyMomentRows (815 : Fin 2886) =
    keyMomentRow815 := by decide +kernel

theorem keyMomentRowsAt816 : keyMomentRows (816 : Fin 2886) =
    keyMomentRow816 := by decide +kernel

theorem keyMomentRowsAt817 : keyMomentRows (817 : Fin 2886) =
    keyMomentRow817 := by decide +kernel

theorem keyMomentRowsAt818 : keyMomentRows (818 : Fin 2886) =
    keyMomentRow818 := by decide +kernel

theorem keyMomentRowsAt819 : keyMomentRows (819 : Fin 2886) =
    keyMomentRow819 := by decide +kernel

theorem keyMomentRowsAt820 : keyMomentRows (820 : Fin 2886) =
    keyMomentRow820 := by decide +kernel

theorem keyMomentRowsAt821 : keyMomentRows (821 : Fin 2886) =
    keyMomentRow821 := by decide +kernel

theorem keyMomentRowsAt822 : keyMomentRows (822 : Fin 2886) =
    keyMomentRow822 := by decide +kernel

theorem keyMomentRowsAt823 : keyMomentRows (823 : Fin 2886) =
    keyMomentRow823 := by decide +kernel

theorem keyMomentRowsAt824 : keyMomentRows (824 : Fin 2886) =
    keyMomentRow824 := by decide +kernel

theorem keyMomentRowsAt825 : keyMomentRows (825 : Fin 2886) =
    keyMomentRow825 := by decide +kernel

theorem keyMomentRowsAt826 : keyMomentRows (826 : Fin 2886) =
    keyMomentRow826 := by decide +kernel

theorem keyMomentRowsAt827 : keyMomentRows (827 : Fin 2886) =
    keyMomentRow827 := by decide +kernel

theorem keyMomentRowsAt828 : keyMomentRows (828 : Fin 2886) =
    keyMomentRow828 := by decide +kernel

theorem keyMomentRowsAt829 : keyMomentRows (829 : Fin 2886) =
    keyMomentRow829 := by decide +kernel

theorem keyMomentRowsAt830 : keyMomentRows (830 : Fin 2886) =
    keyMomentRow830 := by decide +kernel

theorem keyMomentRowsAt831 : keyMomentRows (831 : Fin 2886) =
    keyMomentRow831 := by decide +kernel

theorem keyMomentChunkSound25 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 25) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 800 ∨ k.val = 801 ∨ k.val = 802 ∨ k.val = 803 ∨ k.val = 804 ∨ k.val = 805 ∨ k.val = 806 ∨ k.val = 807 ∨ k.val = 808 ∨ k.val = 809 ∨ k.val = 810 ∨ k.val = 811 ∨ k.val = 812 ∨ k.val = 813 ∨ k.val = 814 ∨ k.val = 815 ∨ k.val = 816 ∨ k.val = 817 ∨ k.val = 818 ∨ k.val = 819 ∨ k.val = 820 ∨ k.val = 821 ∨ k.val = 822 ∨ k.val = 823 ∨ k.val = 824 ∨ k.val = 825 ∨ k.val = 826 ∨ k.val = 827 ∨ k.val = 828 ∨ k.val = 829 ∨ k.val = 830 ∨ k.val = 831 := by omega
  rcases heq with h800 | h801 | h802 | h803 | h804 | h805 | h806 | h807 | h808 | h809 | h810 | h811 | h812 | h813 | h814 | h815 | h816 | h817 | h818 | h819 | h820 | h821 | h822 | h823 | h824 | h825 | h826 | h827 | h828 | h829 | h830 | h831
  · have he : k = (800 : Fin 2886) := Fin.ext h800
    subst k
    rw [keyMomentRowsAt800]
    exact keyMoment800 B hB
  · have he : k = (801 : Fin 2886) := Fin.ext h801
    subst k
    rw [keyMomentRowsAt801]
    exact keyMoment801 B hB
  · have he : k = (802 : Fin 2886) := Fin.ext h802
    subst k
    rw [keyMomentRowsAt802]
    exact keyMoment802 B hB
  · have he : k = (803 : Fin 2886) := Fin.ext h803
    subst k
    rw [keyMomentRowsAt803]
    exact keyMoment803 B hB
  · have he : k = (804 : Fin 2886) := Fin.ext h804
    subst k
    rw [keyMomentRowsAt804]
    exact keyMoment804 B hB
  · have he : k = (805 : Fin 2886) := Fin.ext h805
    subst k
    rw [keyMomentRowsAt805]
    exact keyMoment805 B hB
  · have he : k = (806 : Fin 2886) := Fin.ext h806
    subst k
    rw [keyMomentRowsAt806]
    exact keyMoment806 B hB
  · have he : k = (807 : Fin 2886) := Fin.ext h807
    subst k
    rw [keyMomentRowsAt807]
    exact keyMoment807 B hB
  · have he : k = (808 : Fin 2886) := Fin.ext h808
    subst k
    rw [keyMomentRowsAt808]
    exact keyMoment808 B hB
  · have he : k = (809 : Fin 2886) := Fin.ext h809
    subst k
    rw [keyMomentRowsAt809]
    exact keyMoment809 B hB
  · have he : k = (810 : Fin 2886) := Fin.ext h810
    subst k
    rw [keyMomentRowsAt810]
    exact keyMoment810 B hB
  · have he : k = (811 : Fin 2886) := Fin.ext h811
    subst k
    rw [keyMomentRowsAt811]
    exact keyMoment811 B hB
  · have he : k = (812 : Fin 2886) := Fin.ext h812
    subst k
    rw [keyMomentRowsAt812]
    exact keyMoment812 B hB
  · have he : k = (813 : Fin 2886) := Fin.ext h813
    subst k
    rw [keyMomentRowsAt813]
    exact keyMoment813 B hB
  · have he : k = (814 : Fin 2886) := Fin.ext h814
    subst k
    rw [keyMomentRowsAt814]
    exact keyMoment814 B hB
  · have he : k = (815 : Fin 2886) := Fin.ext h815
    subst k
    rw [keyMomentRowsAt815]
    exact keyMoment815 B hB
  · have he : k = (816 : Fin 2886) := Fin.ext h816
    subst k
    rw [keyMomentRowsAt816]
    exact keyMoment816 B hB
  · have he : k = (817 : Fin 2886) := Fin.ext h817
    subst k
    rw [keyMomentRowsAt817]
    exact keyMoment817 B hB
  · have he : k = (818 : Fin 2886) := Fin.ext h818
    subst k
    rw [keyMomentRowsAt818]
    exact keyMoment818 B hB
  · have he : k = (819 : Fin 2886) := Fin.ext h819
    subst k
    rw [keyMomentRowsAt819]
    exact keyMoment819 B hB
  · have he : k = (820 : Fin 2886) := Fin.ext h820
    subst k
    rw [keyMomentRowsAt820]
    exact keyMoment820 B hB
  · have he : k = (821 : Fin 2886) := Fin.ext h821
    subst k
    rw [keyMomentRowsAt821]
    exact keyMoment821 B hB
  · have he : k = (822 : Fin 2886) := Fin.ext h822
    subst k
    rw [keyMomentRowsAt822]
    exact keyMoment822 B hB
  · have he : k = (823 : Fin 2886) := Fin.ext h823
    subst k
    rw [keyMomentRowsAt823]
    exact keyMoment823 B hB
  · have he : k = (824 : Fin 2886) := Fin.ext h824
    subst k
    rw [keyMomentRowsAt824]
    exact keyMoment824 B hB
  · have he : k = (825 : Fin 2886) := Fin.ext h825
    subst k
    rw [keyMomentRowsAt825]
    exact keyMoment825 B hB
  · have he : k = (826 : Fin 2886) := Fin.ext h826
    subst k
    rw [keyMomentRowsAt826]
    exact keyMoment826 B hB
  · have he : k = (827 : Fin 2886) := Fin.ext h827
    subst k
    rw [keyMomentRowsAt827]
    exact keyMoment827 B hB
  · have he : k = (828 : Fin 2886) := Fin.ext h828
    subst k
    rw [keyMomentRowsAt828]
    exact keyMoment828 B hB
  · have he : k = (829 : Fin 2886) := Fin.ext h829
    subst k
    rw [keyMomentRowsAt829]
    exact keyMoment829 B hB
  · have he : k = (830 : Fin 2886) := Fin.ext h830
    subst k
    rw [keyMomentRowsAt830]
    exact keyMoment830 B hB
  · have he : k = (831 : Fin 2886) := Fin.ext h831
    subst k
    rw [keyMomentRowsAt831]
    exact keyMoment831 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
