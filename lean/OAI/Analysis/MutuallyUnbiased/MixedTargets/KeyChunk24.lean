import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeySound24
import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt768 : keyMomentRows (768 : Fin 2886) =
    keyMomentRow768 := by decide +kernel

theorem keyMomentRowsAt769 : keyMomentRows (769 : Fin 2886) =
    keyMomentRow769 := by decide +kernel

theorem keyMomentRowsAt770 : keyMomentRows (770 : Fin 2886) =
    keyMomentRow770 := by decide +kernel

theorem keyMomentRowsAt771 : keyMomentRows (771 : Fin 2886) =
    keyMomentRow771 := by decide +kernel

theorem keyMomentRowsAt772 : keyMomentRows (772 : Fin 2886) =
    keyMomentRow772 := by decide +kernel

theorem keyMomentRowsAt773 : keyMomentRows (773 : Fin 2886) =
    keyMomentRow773 := by decide +kernel

theorem keyMomentRowsAt774 : keyMomentRows (774 : Fin 2886) =
    keyMomentRow774 := by decide +kernel

theorem keyMomentRowsAt775 : keyMomentRows (775 : Fin 2886) =
    keyMomentRow775 := by decide +kernel

theorem keyMomentRowsAt776 : keyMomentRows (776 : Fin 2886) =
    keyMomentRow776 := by decide +kernel

theorem keyMomentRowsAt777 : keyMomentRows (777 : Fin 2886) =
    keyMomentRow777 := by decide +kernel

theorem keyMomentRowsAt778 : keyMomentRows (778 : Fin 2886) =
    keyMomentRow778 := by decide +kernel

theorem keyMomentRowsAt779 : keyMomentRows (779 : Fin 2886) =
    keyMomentRow779 := by decide +kernel

theorem keyMomentRowsAt780 : keyMomentRows (780 : Fin 2886) =
    keyMomentRow780 := by decide +kernel

theorem keyMomentRowsAt781 : keyMomentRows (781 : Fin 2886) =
    keyMomentRow781 := by decide +kernel

theorem keyMomentRowsAt782 : keyMomentRows (782 : Fin 2886) =
    keyMomentRow782 := by decide +kernel

theorem keyMomentRowsAt783 : keyMomentRows (783 : Fin 2886) =
    keyMomentRow783 := by decide +kernel

theorem keyMomentRowsAt784 : keyMomentRows (784 : Fin 2886) =
    keyMomentRow784 := by decide +kernel

theorem keyMomentRowsAt785 : keyMomentRows (785 : Fin 2886) =
    keyMomentRow785 := by decide +kernel

theorem keyMomentRowsAt786 : keyMomentRows (786 : Fin 2886) =
    keyMomentRow786 := by decide +kernel

theorem keyMomentRowsAt787 : keyMomentRows (787 : Fin 2886) =
    keyMomentRow787 := by decide +kernel

theorem keyMomentRowsAt788 : keyMomentRows (788 : Fin 2886) =
    keyMomentRow788 := by decide +kernel

theorem keyMomentRowsAt789 : keyMomentRows (789 : Fin 2886) =
    keyMomentRow789 := by decide +kernel

theorem keyMomentRowsAt790 : keyMomentRows (790 : Fin 2886) =
    keyMomentRow790 := by decide +kernel

theorem keyMomentRowsAt791 : keyMomentRows (791 : Fin 2886) =
    keyMomentRow791 := by decide +kernel

theorem keyMomentRowsAt792 : keyMomentRows (792 : Fin 2886) =
    keyMomentRow792 := by decide +kernel

theorem keyMomentRowsAt793 : keyMomentRows (793 : Fin 2886) =
    keyMomentRow793 := by decide +kernel

theorem keyMomentRowsAt794 : keyMomentRows (794 : Fin 2886) =
    keyMomentRow794 := by decide +kernel

theorem keyMomentRowsAt795 : keyMomentRows (795 : Fin 2886) =
    keyMomentRow795 := by decide +kernel

theorem keyMomentRowsAt796 : keyMomentRows (796 : Fin 2886) =
    keyMomentRow796 := by decide +kernel

theorem keyMomentRowsAt797 : keyMomentRows (797 : Fin 2886) =
    keyMomentRow797 := by decide +kernel

theorem keyMomentRowsAt798 : keyMomentRows (798 : Fin 2886) =
    keyMomentRow798 := by decide +kernel

theorem keyMomentRowsAt799 : keyMomentRows (799 : Fin 2886) =
    keyMomentRow799 := by decide +kernel

theorem keyMomentChunkSound24 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 24) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 768 ∨ k.val = 769 ∨ k.val = 770 ∨ k.val = 771 ∨ k.val = 772 ∨ k.val = 773 ∨ k.val = 774 ∨ k.val = 775 ∨ k.val = 776 ∨ k.val = 777 ∨ k.val = 778 ∨ k.val = 779 ∨ k.val = 780 ∨ k.val = 781 ∨ k.val = 782 ∨ k.val = 783 ∨ k.val = 784 ∨ k.val = 785 ∨ k.val = 786 ∨ k.val = 787 ∨ k.val = 788 ∨ k.val = 789 ∨ k.val = 790 ∨ k.val = 791 ∨ k.val = 792 ∨ k.val = 793 ∨ k.val = 794 ∨ k.val = 795 ∨ k.val = 796 ∨ k.val = 797 ∨ k.val = 798 ∨ k.val = 799 := by omega
  rcases heq with h768 | h769 | h770 | h771 | h772 | h773 | h774 | h775 | h776 | h777 | h778 | h779 | h780 | h781 | h782 | h783 | h784 | h785 | h786 | h787 | h788 | h789 | h790 | h791 | h792 | h793 | h794 | h795 | h796 | h797 | h798 | h799
  · have he : k = (768 : Fin 2886) := Fin.ext h768
    subst k
    rw [keyMomentRowsAt768]
    exact keyMoment768 B hB
  · have he : k = (769 : Fin 2886) := Fin.ext h769
    subst k
    rw [keyMomentRowsAt769]
    exact keyMoment769 B hB
  · have he : k = (770 : Fin 2886) := Fin.ext h770
    subst k
    rw [keyMomentRowsAt770]
    exact keyMoment770 B hB
  · have he : k = (771 : Fin 2886) := Fin.ext h771
    subst k
    rw [keyMomentRowsAt771]
    exact keyMoment771 B hB
  · have he : k = (772 : Fin 2886) := Fin.ext h772
    subst k
    rw [keyMomentRowsAt772]
    exact keyMoment772 B hB
  · have he : k = (773 : Fin 2886) := Fin.ext h773
    subst k
    rw [keyMomentRowsAt773]
    exact keyMoment773 B hB
  · have he : k = (774 : Fin 2886) := Fin.ext h774
    subst k
    rw [keyMomentRowsAt774]
    exact keyMoment774 B hB
  · have he : k = (775 : Fin 2886) := Fin.ext h775
    subst k
    rw [keyMomentRowsAt775]
    exact keyMoment775 B hB
  · have he : k = (776 : Fin 2886) := Fin.ext h776
    subst k
    rw [keyMomentRowsAt776]
    exact keyMoment776 B hB
  · have he : k = (777 : Fin 2886) := Fin.ext h777
    subst k
    rw [keyMomentRowsAt777]
    exact keyMoment777 B hB
  · have he : k = (778 : Fin 2886) := Fin.ext h778
    subst k
    rw [keyMomentRowsAt778]
    exact keyMoment778 B hB
  · have he : k = (779 : Fin 2886) := Fin.ext h779
    subst k
    rw [keyMomentRowsAt779]
    exact keyMoment779 B hB
  · have he : k = (780 : Fin 2886) := Fin.ext h780
    subst k
    rw [keyMomentRowsAt780]
    exact keyMoment780 B hB
  · have he : k = (781 : Fin 2886) := Fin.ext h781
    subst k
    rw [keyMomentRowsAt781]
    exact keyMoment781 B hB
  · have he : k = (782 : Fin 2886) := Fin.ext h782
    subst k
    rw [keyMomentRowsAt782]
    exact keyMoment782 B hB
  · have he : k = (783 : Fin 2886) := Fin.ext h783
    subst k
    rw [keyMomentRowsAt783]
    exact keyMoment783 B hB
  · have he : k = (784 : Fin 2886) := Fin.ext h784
    subst k
    rw [keyMomentRowsAt784]
    exact keyMoment784 B hB
  · have he : k = (785 : Fin 2886) := Fin.ext h785
    subst k
    rw [keyMomentRowsAt785]
    exact keyMoment785 B hB
  · have he : k = (786 : Fin 2886) := Fin.ext h786
    subst k
    rw [keyMomentRowsAt786]
    exact keyMoment786 B hB
  · have he : k = (787 : Fin 2886) := Fin.ext h787
    subst k
    rw [keyMomentRowsAt787]
    exact keyMoment787 B hB
  · have he : k = (788 : Fin 2886) := Fin.ext h788
    subst k
    rw [keyMomentRowsAt788]
    exact keyMoment788 B hB
  · have he : k = (789 : Fin 2886) := Fin.ext h789
    subst k
    rw [keyMomentRowsAt789]
    exact keyMoment789 B hB
  · have he : k = (790 : Fin 2886) := Fin.ext h790
    subst k
    rw [keyMomentRowsAt790]
    exact keyMoment790 B hB
  · have he : k = (791 : Fin 2886) := Fin.ext h791
    subst k
    rw [keyMomentRowsAt791]
    exact keyMoment791 B hB
  · have he : k = (792 : Fin 2886) := Fin.ext h792
    subst k
    rw [keyMomentRowsAt792]
    exact keyMoment792 B hB
  · have he : k = (793 : Fin 2886) := Fin.ext h793
    subst k
    rw [keyMomentRowsAt793]
    exact keyMoment793 B hB
  · have he : k = (794 : Fin 2886) := Fin.ext h794
    subst k
    rw [keyMomentRowsAt794]
    exact keyMoment794 B hB
  · have he : k = (795 : Fin 2886) := Fin.ext h795
    subst k
    rw [keyMomentRowsAt795]
    exact keyMoment795 B hB
  · have he : k = (796 : Fin 2886) := Fin.ext h796
    subst k
    rw [keyMomentRowsAt796]
    exact keyMoment796 B hB
  · have he : k = (797 : Fin 2886) := Fin.ext h797
    subst k
    rw [keyMomentRowsAt797]
    exact keyMoment797 B hB
  · have he : k = (798 : Fin 2886) := Fin.ext h798
    subst k
    rw [keyMomentRowsAt798]
    exact keyMoment798 B hB
  · have he : k = (799 : Fin 2886) := Fin.ext h799
    subst k
    rw [keyMomentRowsAt799]
    exact keyMoment799 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
