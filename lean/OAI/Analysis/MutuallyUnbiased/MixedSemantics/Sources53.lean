import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical106
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical111
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical112
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical164
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical165
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical166
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical180
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical185
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical189
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical190
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical192
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical194
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical195
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical196
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical197

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1696 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1696 : Charge := ![2, -1, -1, 1, -1, 0]
def sourceC1696 : Charge := ![2, 1, 1, -2, 0, -2]
def sourceForm1696 : Integer.Sparse Master := [(Sum.inr 1198, 1), (Sum.inr 2459, 2), (Sum.inr 2697, 1), (Sum.inr 2701, 1), (Sum.inr 2705, 1), (Sum.inr 4088, -1)]

theorem sourceEq1696 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1696 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1696 + difference 0 0) (sourceB1696 + difference 0 0) sourceC1696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1198) := by
    have ha : (tripleCharges (sourceA1696 + difference 0 0) (sourceB1696 + difference 0 0) sourceC1696) = raw24886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1696 sourceB1696 sourceC1696 difference raw24886; decide +kernel
    rw [ha]
    exact (canonical24886 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1696 + difference 0 1) (sourceB1696 + difference 1 0) sourceC1696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2459) := by
    have ha : (tripleCharges (sourceA1696 + difference 0 1) (sourceB1696 + difference 1 0) sourceC1696) = raw24887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1696 sourceB1696 sourceC1696 difference raw24887; decide +kernel
    rw [ha]
    exact (canonical24887 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1696 + difference 0 2) (sourceB1696 + difference 2 0) sourceC1696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2459) := by
    have ha : (tripleCharges (sourceA1696 + difference 0 2) (sourceB1696 + difference 2 0) sourceC1696) = raw24888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1696 sourceB1696 sourceC1696 difference raw24888; decide +kernel
    rw [ha]
    exact (canonical24888 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1696 + difference 0 3) (sourceB1696 + difference 3 0) sourceC1696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA1696 + difference 0 3) (sourceB1696 + difference 3 0) sourceC1696) = raw24889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1696 sourceB1696 sourceC1696 difference raw24889; decide +kernel
    rw [ha]
    exact (canonical24889 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1696 + difference 0 4) (sourceB1696 + difference 4 0) sourceC1696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2705) := by
    have ha : (tripleCharges (sourceA1696 + difference 0 4) (sourceB1696 + difference 4 0) sourceC1696) = raw24890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1696 sourceB1696 sourceC1696 difference raw24890; decide +kernel
    rw [ha]
    exact (canonical24890 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1696 + difference 0 5) (sourceB1696 + difference 5 0) sourceC1696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2701) := by
    have ha : (tripleCharges (sourceA1696 + difference 0 5) (sourceB1696 + difference 5 0) sourceC1696) = raw24891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1696 sourceB1696 sourceC1696 difference raw24891; decide +kernel
    rw [ha]
    exact (canonical24891 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1696 + sourceB1696) sourceC1696) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1696 + sourceB1696) sourceC1696) = raw24892 := by
      apply Matrix.ext; unfold doubleCharges sourceA1696 sourceB1696 sourceC1696 raw24892; decide +kernel
    rw [ha]
    exact (canonical24892 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1696 sourceB1696 sourceC1696
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1696, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1697 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1697 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC1697 : Charge := ![2, 1, 1, -1, -1, -2]
def sourceForm1697 : Integer.Sparse Master := [(Sum.inr 1200, 1), (Sum.inr 2461, 2), (Sum.inr 2694, 2), (Sum.inr 2703, 1), (Sum.inr 4090, -1)]

theorem sourceEq1697 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1697 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1697 + difference 0 0) (sourceB1697 + difference 0 0) sourceC1697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA1697 + difference 0 0) (sourceB1697 + difference 0 0) sourceC1697) = raw24893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1697 sourceB1697 sourceC1697 difference raw24893; decide +kernel
    rw [ha]
    exact (canonical24893 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1697 + difference 0 1) (sourceB1697 + difference 1 0) sourceC1697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2461) := by
    have ha : (tripleCharges (sourceA1697 + difference 0 1) (sourceB1697 + difference 1 0) sourceC1697) = raw24894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1697 sourceB1697 sourceC1697 difference raw24894; decide +kernel
    rw [ha]
    exact (canonical24894 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1697 + difference 0 2) (sourceB1697 + difference 2 0) sourceC1697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2461) := by
    have ha : (tripleCharges (sourceA1697 + difference 0 2) (sourceB1697 + difference 2 0) sourceC1697) = raw24895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1697 sourceB1697 sourceC1697 difference raw24895; decide +kernel
    rw [ha]
    exact (canonical24895 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1697 + difference 0 3) (sourceB1697 + difference 3 0) sourceC1697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA1697 + difference 0 3) (sourceB1697 + difference 3 0) sourceC1697) = raw24896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1697 sourceB1697 sourceC1697 difference raw24896; decide +kernel
    rw [ha]
    exact (canonical24896 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1697 + difference 0 4) (sourceB1697 + difference 4 0) sourceC1697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA1697 + difference 0 4) (sourceB1697 + difference 4 0) sourceC1697) = raw24897 := by
      apply Matrix.ext; unfold tripleCharges sourceA1697 sourceB1697 sourceC1697 difference raw24897; decide +kernel
    rw [ha]
    exact (canonical24897 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1697 + difference 0 5) (sourceB1697 + difference 5 0) sourceC1697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA1697 + difference 0 5) (sourceB1697 + difference 5 0) sourceC1697) = raw24898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1697 sourceB1697 sourceC1697 difference raw24898; decide +kernel
    rw [ha]
    exact (canonical24898 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1697 + sourceB1697) sourceC1697) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1697 + sourceB1697) sourceC1697) = raw24899 := by
      apply Matrix.ext; unfold doubleCharges sourceA1697 sourceB1697 sourceC1697 raw24899; decide +kernel
    rw [ha]
    exact (canonical24899 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1697 sourceB1697 sourceC1697
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1697, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1698 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1698 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceC1698 : Charge := ![2, 1, 1, -1, -1, -2]
def sourceForm1698 : Integer.Sparse Master := [(Sum.inr 1107, 1), (Sum.inr 1108, 2), (Sum.inr 1122, 1), (Sum.inr 1200, 1), (Sum.inr 2461, 1), (Sum.inr 4090, -1)]

theorem sourceEq1698 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1698 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1698 + difference 0 1) (sourceB1698 + difference 1 0) sourceC1698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2461) := by
    have ha : (tripleCharges (sourceA1698 + difference 0 1) (sourceB1698 + difference 1 0) sourceC1698) = raw24894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1698 sourceB1698 sourceC1698 difference raw24894; decide +kernel
    rw [ha]
    exact (canonical24894 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1698 + difference 1 1) (sourceB1698 + difference 1 1) sourceC1698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1200) := by
    have ha : (tripleCharges (sourceA1698 + difference 1 1) (sourceB1698 + difference 1 1) sourceC1698) = raw24893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1698 sourceB1698 sourceC1698 difference raw24893; decide +kernel
    rw [ha]
    exact (canonical24893 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1698 + difference 2 1) (sourceB1698 + difference 1 2) sourceC1698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1122) := by
    have ha : (tripleCharges (sourceA1698 + difference 2 1) (sourceB1698 + difference 1 2) sourceC1698) = raw24900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1698 sourceB1698 sourceC1698 difference raw24900; decide +kernel
    rw [ha]
    exact (canonical24900 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1698 + difference 3 1) (sourceB1698 + difference 1 3) sourceC1698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1108) := by
    have ha : (tripleCharges (sourceA1698 + difference 3 1) (sourceB1698 + difference 1 3) sourceC1698) = raw24901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1698 sourceB1698 sourceC1698 difference raw24901; decide +kernel
    rw [ha]
    exact (canonical24901 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1698 + difference 4 1) (sourceB1698 + difference 1 4) sourceC1698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1108) := by
    have ha : (tripleCharges (sourceA1698 + difference 4 1) (sourceB1698 + difference 1 4) sourceC1698) = raw24902 := by
      apply Matrix.ext; unfold tripleCharges sourceA1698 sourceB1698 sourceC1698 difference raw24902; decide +kernel
    rw [ha]
    exact (canonical24902 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1698 + difference 5 1) (sourceB1698 + difference 1 5) sourceC1698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1107) := by
    have ha : (tripleCharges (sourceA1698 + difference 5 1) (sourceB1698 + difference 1 5) sourceC1698) = raw24903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1698 sourceB1698 sourceC1698 difference raw24903; decide +kernel
    rw [ha]
    exact (canonical24903 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1698 + sourceB1698) sourceC1698) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1698 + sourceB1698) sourceC1698) = raw24899 := by
      apply Matrix.ext; unfold doubleCharges sourceA1698 sourceB1698 sourceC1698 raw24899; decide +kernel
    rw [ha]
    exact (canonical24899 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1698 sourceB1698 sourceC1698
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1698, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1699 : Charge := ![2, -1, -1, 0, 0, 0]
def sourceB1699 : Charge := ![2, 1, 1, -1, -1, -2]
def sourceC1699 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1699 : Integer.Sparse Master := [(Sum.inr 1582, 1), (Sum.inr 1583, 2), (Sum.inr 1622, 2), (Sum.inr 3281, 1), (Sum.inr 4069, -1)]

theorem sourceEq1699 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1699 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1699 + difference 0 0) (sourceB1699 + difference 0 0) sourceC1699) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3281) := by
    have ha : (tripleCharges (sourceA1699 + difference 0 0) (sourceB1699 + difference 0 0) sourceC1699) = raw24904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1699 sourceB1699 sourceC1699 difference raw24904; decide +kernel
    rw [ha]
    exact (canonical24904 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1699 + difference 1 0) (sourceB1699 + difference 0 1) sourceC1699) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1622) := by
    have ha : (tripleCharges (sourceA1699 + difference 1 0) (sourceB1699 + difference 0 1) sourceC1699) = raw24864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1699 sourceB1699 sourceC1699 difference raw24864; decide +kernel
    rw [ha]
    exact (canonical24864 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1699 + difference 2 0) (sourceB1699 + difference 0 2) sourceC1699) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1622) := by
    have ha : (tripleCharges (sourceA1699 + difference 2 0) (sourceB1699 + difference 0 2) sourceC1699) = raw24905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1699 sourceB1699 sourceC1699 difference raw24905; decide +kernel
    rw [ha]
    exact (canonical24905 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1699 + difference 3 0) (sourceB1699 + difference 0 3) sourceC1699) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1583) := by
    have ha : (tripleCharges (sourceA1699 + difference 3 0) (sourceB1699 + difference 0 3) sourceC1699) = raw24906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1699 sourceB1699 sourceC1699 difference raw24906; decide +kernel
    rw [ha]
    exact (canonical24906 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1699 + difference 4 0) (sourceB1699 + difference 0 4) sourceC1699) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1583) := by
    have ha : (tripleCharges (sourceA1699 + difference 4 0) (sourceB1699 + difference 0 4) sourceC1699) = raw24907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1699 sourceB1699 sourceC1699 difference raw24907; decide +kernel
    rw [ha]
    exact (canonical24907 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1699 + difference 5 0) (sourceB1699 + difference 0 5) sourceC1699) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1582) := by
    have ha : (tripleCharges (sourceA1699 + difference 5 0) (sourceB1699 + difference 0 5) sourceC1699) = raw24908 := by
      apply Matrix.ext; unfold tripleCharges sourceA1699 sourceB1699 sourceC1699 difference raw24908; decide +kernel
    rw [ha]
    exact (canonical24908 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1699 + sourceB1699) sourceC1699) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1699 + sourceB1699) sourceC1699) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1699 sourceB1699 sourceC1699 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1699 sourceB1699 sourceC1699
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1699, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1700 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1700 : Charge := ![2, -1, -1, 0, -1, 1]
def sourceC1700 : Charge := ![2, 1, 1, -1, 0, -3]
def sourceForm1700 : Integer.Sparse Master := [(Sum.inr 1197, 1), (Sum.inr 2458, 2), (Sum.inr 2693, 1), (Sum.inr 2700, 1), (Sum.inr 2704, 1), (Sum.inr 4080, -1)]

theorem sourceEq1700 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1700 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1700 + difference 0 0) (sourceB1700 + difference 0 0) sourceC1700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1197) := by
    have ha : (tripleCharges (sourceA1700 + difference 0 0) (sourceB1700 + difference 0 0) sourceC1700) = raw24909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1700 sourceB1700 sourceC1700 difference raw24909; decide +kernel
    rw [ha]
    exact (canonical24909 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1700 + difference 0 1) (sourceB1700 + difference 1 0) sourceC1700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2458) := by
    have ha : (tripleCharges (sourceA1700 + difference 0 1) (sourceB1700 + difference 1 0) sourceC1700) = raw24910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1700 sourceB1700 sourceC1700 difference raw24910; decide +kernel
    rw [ha]
    exact (canonical24910 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1700 + difference 0 2) (sourceB1700 + difference 2 0) sourceC1700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2458) := by
    have ha : (tripleCharges (sourceA1700 + difference 0 2) (sourceB1700 + difference 2 0) sourceC1700) = raw24911 := by
      apply Matrix.ext; unfold tripleCharges sourceA1700 sourceB1700 sourceC1700 difference raw24911; decide +kernel
    rw [ha]
    exact (canonical24911 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1700 + difference 0 3) (sourceB1700 + difference 3 0) sourceC1700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2693) := by
    have ha : (tripleCharges (sourceA1700 + difference 0 3) (sourceB1700 + difference 3 0) sourceC1700) = raw24912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1700 sourceB1700 sourceC1700 difference raw24912; decide +kernel
    rw [ha]
    exact (canonical24912 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1700 + difference 0 4) (sourceB1700 + difference 4 0) sourceC1700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2704) := by
    have ha : (tripleCharges (sourceA1700 + difference 0 4) (sourceB1700 + difference 4 0) sourceC1700) = raw24913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1700 sourceB1700 sourceC1700 difference raw24913; decide +kernel
    rw [ha]
    exact (canonical24913 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1700 + difference 0 5) (sourceB1700 + difference 5 0) sourceC1700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2700) := by
    have ha : (tripleCharges (sourceA1700 + difference 0 5) (sourceB1700 + difference 5 0) sourceC1700) = raw24914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1700 sourceB1700 sourceC1700 difference raw24914; decide +kernel
    rw [ha]
    exact (canonical24914 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1700 + sourceB1700) sourceC1700) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1700 + sourceB1700) sourceC1700) = raw24915 := by
      apply Matrix.ext; unfold doubleCharges sourceA1700 sourceB1700 sourceC1700 raw24915; decide +kernel
    rw [ha]
    exact (canonical24915 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1700 sourceB1700 sourceC1700
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1700, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1701 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1701 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceC1701 : Charge := ![3, -2, 0, -1, -1, 1]
def sourceForm1701 : Integer.Sparse Master := [(Sum.inr 1060, 1), (Sum.inr 2036, 1), (Sum.inr 2135, 1), (Sum.inr 2254, 2), (Sum.inr 2275, 1), (Sum.inr 4080, -1)]

theorem sourceEq1701 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1701 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1701 + difference 0 0) (sourceB1701 + difference 0 0) sourceC1701) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1060) := by
    have ha : (tripleCharges (sourceA1701 + difference 0 0) (sourceB1701 + difference 0 0) sourceC1701) = raw24916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1701 sourceB1701 sourceC1701 difference raw24916; decide +kernel
    rw [ha]
    exact (canonical24916 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1701 + difference 0 1) (sourceB1701 + difference 1 0) sourceC1701) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2135) := by
    have ha : (tripleCharges (sourceA1701 + difference 0 1) (sourceB1701 + difference 1 0) sourceC1701) = raw24917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1701 sourceB1701 sourceC1701 difference raw24917; decide +kernel
    rw [ha]
    exact (canonical24917 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1701 + difference 0 2) (sourceB1701 + difference 2 0) sourceC1701) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2036) := by
    have ha : (tripleCharges (sourceA1701 + difference 0 2) (sourceB1701 + difference 2 0) sourceC1701) = raw24918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1701 sourceB1701 sourceC1701 difference raw24918; decide +kernel
    rw [ha]
    exact (canonical24918 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1701 + difference 0 3) (sourceB1701 + difference 3 0) sourceC1701) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA1701 + difference 0 3) (sourceB1701 + difference 3 0) sourceC1701) = raw24919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1701 sourceB1701 sourceC1701 difference raw24919; decide +kernel
    rw [ha]
    exact (canonical24919 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1701 + difference 0 4) (sourceB1701 + difference 4 0) sourceC1701) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA1701 + difference 0 4) (sourceB1701 + difference 4 0) sourceC1701) = raw24920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1701 sourceB1701 sourceC1701 difference raw24920; decide +kernel
    rw [ha]
    exact (canonical24920 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1701 + difference 0 5) (sourceB1701 + difference 5 0) sourceC1701) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA1701 + difference 0 5) (sourceB1701 + difference 5 0) sourceC1701) = raw24921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1701 sourceB1701 sourceC1701 difference raw24921; decide +kernel
    rw [ha]
    exact (canonical24921 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1701 + sourceB1701) sourceC1701) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1701 + sourceB1701) sourceC1701) = raw24922 := by
      apply Matrix.ext; unfold doubleCharges sourceA1701 sourceB1701 sourceC1701 raw24922; decide +kernel
    rw [ha]
    exact (canonical24922 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1701 sourceB1701 sourceC1701
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1701, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1702 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1702 : Charge := ![1, 2, 0, 0, 0, -3]
def sourceC1702 : Charge := ![3, -2, 0, -1, -1, 1]
def sourceForm1702 : Integer.Sparse Master := [(Sum.inr 1052, 1), (Sum.inr 1054, 2), (Sum.inr 1060, 1), (Sum.inr 1073, 1), (Sum.inr 2275, 1), (Sum.inr 4080, -1)]

theorem sourceEq1702 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1702 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1702 + difference 0 5) (sourceB1702 + difference 5 0) sourceC1702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA1702 + difference 0 5) (sourceB1702 + difference 5 0) sourceC1702) = raw24921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1702 sourceB1702 sourceC1702 difference raw24921; decide +kernel
    rw [ha]
    exact (canonical24921 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1702 + difference 1 5) (sourceB1702 + difference 5 1) sourceC1702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1702 + difference 1 5) (sourceB1702 + difference 5 1) sourceC1702) = raw24923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1702 sourceB1702 sourceC1702 difference raw24923; decide +kernel
    rw [ha]
    exact (canonical24923 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1702 + difference 2 5) (sourceB1702 + difference 5 2) sourceC1702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1052) := by
    have ha : (tripleCharges (sourceA1702 + difference 2 5) (sourceB1702 + difference 5 2) sourceC1702) = raw24924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1702 sourceB1702 sourceC1702 difference raw24924; decide +kernel
    rw [ha]
    exact (canonical24924 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1702 + difference 3 5) (sourceB1702 + difference 5 3) sourceC1702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1054) := by
    have ha : (tripleCharges (sourceA1702 + difference 3 5) (sourceB1702 + difference 5 3) sourceC1702) = raw24925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1702 sourceB1702 sourceC1702 difference raw24925; decide +kernel
    rw [ha]
    exact (canonical24925 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1702 + difference 4 5) (sourceB1702 + difference 5 4) sourceC1702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1054) := by
    have ha : (tripleCharges (sourceA1702 + difference 4 5) (sourceB1702 + difference 5 4) sourceC1702) = raw24926 := by
      apply Matrix.ext; unfold tripleCharges sourceA1702 sourceB1702 sourceC1702 difference raw24926; decide +kernel
    rw [ha]
    exact (canonical24926 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1702 + difference 5 5) (sourceB1702 + difference 5 5) sourceC1702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1060) := by
    have ha : (tripleCharges (sourceA1702 + difference 5 5) (sourceB1702 + difference 5 5) sourceC1702) = raw24916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1702 sourceB1702 sourceC1702 difference raw24916; decide +kernel
    rw [ha]
    exact (canonical24916 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1702 + sourceB1702) sourceC1702) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1702 + sourceB1702) sourceC1702) = raw24922 := by
      apply Matrix.ext; unfold doubleCharges sourceA1702 sourceB1702 sourceC1702 raw24922; decide +kernel
    rw [ha]
    exact (canonical24922 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1702 sourceB1702 sourceC1702
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1702, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1703 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1703 : Charge := ![1, 2, 0, 0, -2, -1]
def sourceC1703 : Charge := ![3, -2, 0, -1, 1, -1]
def sourceForm1703 : Integer.Sparse Master := [(Sum.inr 1054, 1), (Sum.inr 2031, 1), (Sum.inr 2129, 1), (Sum.inr 2216, 1), (Sum.inr 2251, 1), (Sum.inr 2275, 1), (Sum.inr 4080, -1)]

theorem sourceEq1703 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1703 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1703 + difference 0 0) (sourceB1703 + difference 0 0) sourceC1703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1054) := by
    have ha : (tripleCharges (sourceA1703 + difference 0 0) (sourceB1703 + difference 0 0) sourceC1703) = raw24927 := by
      apply Matrix.ext; unfold tripleCharges sourceA1703 sourceB1703 sourceC1703 difference raw24927; decide +kernel
    rw [ha]
    exact (canonical24927 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1703 + difference 0 1) (sourceB1703 + difference 1 0) sourceC1703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2129) := by
    have ha : (tripleCharges (sourceA1703 + difference 0 1) (sourceB1703 + difference 1 0) sourceC1703) = raw24928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1703 sourceB1703 sourceC1703 difference raw24928; decide +kernel
    rw [ha]
    exact (canonical24928 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1703 + difference 0 2) (sourceB1703 + difference 2 0) sourceC1703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2031) := by
    have ha : (tripleCharges (sourceA1703 + difference 0 2) (sourceB1703 + difference 2 0) sourceC1703) = raw24929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1703 sourceB1703 sourceC1703 difference raw24929; decide +kernel
    rw [ha]
    exact (canonical24929 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1703 + difference 0 3) (sourceB1703 + difference 3 0) sourceC1703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA1703 + difference 0 3) (sourceB1703 + difference 3 0) sourceC1703) = raw24930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1703 sourceB1703 sourceC1703 difference raw24930; decide +kernel
    rw [ha]
    exact (canonical24930 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1703 + difference 0 4) (sourceB1703 + difference 4 0) sourceC1703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1703 + difference 0 4) (sourceB1703 + difference 4 0) sourceC1703) = raw24931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1703 sourceB1703 sourceC1703 difference raw24931; decide +kernel
    rw [ha]
    exact (canonical24931 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1703 + difference 0 5) (sourceB1703 + difference 5 0) sourceC1703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA1703 + difference 0 5) (sourceB1703 + difference 5 0) sourceC1703) = raw24932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1703 sourceB1703 sourceC1703 difference raw24932; decide +kernel
    rw [ha]
    exact (canonical24932 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1703 + sourceB1703) sourceC1703) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1703 + sourceB1703) sourceC1703) = raw24933 := by
      apply Matrix.ext; unfold doubleCharges sourceA1703 sourceB1703 sourceC1703 raw24933; decide +kernel
    rw [ha]
    exact (canonical24933 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1703 sourceB1703 sourceC1703
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1703, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1704 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1704 : Charge := ![1, 2, 0, -1, -2, 0]
def sourceC1704 : Charge := ![3, -2, 0, 0, 1, -2]
def sourceForm1704 : Integer.Sparse Master := [(Sum.inr 1053, 1), (Sum.inr 2030, 1), (Sum.inr 2128, 1), (Sum.inr 2215, 1), (Sum.inr 2274, 1), (Sum.inr 2276, 1), (Sum.inr 4082, -1)]

theorem sourceEq1704 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1704 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1704 + difference 0 0) (sourceB1704 + difference 0 0) sourceC1704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1053) := by
    have ha : (tripleCharges (sourceA1704 + difference 0 0) (sourceB1704 + difference 0 0) sourceC1704) = raw21087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1704 sourceB1704 sourceC1704 difference raw21087; decide +kernel
    rw [ha]
    exact (canonical21087 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1704 + difference 0 1) (sourceB1704 + difference 1 0) sourceC1704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2128) := by
    have ha : (tripleCharges (sourceA1704 + difference 0 1) (sourceB1704 + difference 1 0) sourceC1704) = raw24934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1704 sourceB1704 sourceC1704 difference raw24934; decide +kernel
    rw [ha]
    exact (canonical24934 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1704 + difference 0 2) (sourceB1704 + difference 2 0) sourceC1704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2030) := by
    have ha : (tripleCharges (sourceA1704 + difference 0 2) (sourceB1704 + difference 2 0) sourceC1704) = raw24935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1704 sourceB1704 sourceC1704 difference raw24935; decide +kernel
    rw [ha]
    exact (canonical24935 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1704 + difference 0 3) (sourceB1704 + difference 3 0) sourceC1704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA1704 + difference 0 3) (sourceB1704 + difference 3 0) sourceC1704) = raw21083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1704 sourceB1704 sourceC1704 difference raw21083; decide +kernel
    rw [ha]
    exact (canonical21083 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1704 + difference 0 4) (sourceB1704 + difference 4 0) sourceC1704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA1704 + difference 0 4) (sourceB1704 + difference 4 0) sourceC1704) = raw24936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1704 sourceB1704 sourceC1704 difference raw24936; decide +kernel
    rw [ha]
    exact (canonical24936 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1704 + difference 0 5) (sourceB1704 + difference 5 0) sourceC1704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA1704 + difference 0 5) (sourceB1704 + difference 5 0) sourceC1704) = raw24937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1704 sourceB1704 sourceC1704 difference raw24937; decide +kernel
    rw [ha]
    exact (canonical24937 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1704 + sourceB1704) sourceC1704) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1704 + sourceB1704) sourceC1704) = raw21084 := by
      apply Matrix.ext; unfold doubleCharges sourceA1704 sourceB1704 sourceC1704 raw21084; decide +kernel
    rw [ha]
    exact (canonical21084 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1704 sourceB1704 sourceC1704
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1704, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1705 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1705 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceC1705 : Charge := ![3, -2, 1, -1, -1, 0]
def sourceForm1705 : Integer.Sparse Master := [(Sum.inr 990, 1), (Sum.inr 1925, 1), (Sum.inr 2120, 1), (Sum.inr 2196, 2), (Sum.inr 2214, 1), (Sum.inr 4080, -1)]

theorem sourceEq1705 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1705 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1705 + difference 0 0) (sourceB1705 + difference 0 0) sourceC1705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 990) := by
    have ha : (tripleCharges (sourceA1705 + difference 0 0) (sourceB1705 + difference 0 0) sourceC1705) = raw24938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1705 sourceB1705 sourceC1705 difference raw24938; decide +kernel
    rw [ha]
    exact (canonical24938 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1705 + difference 0 1) (sourceB1705 + difference 1 0) sourceC1705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2120) := by
    have ha : (tripleCharges (sourceA1705 + difference 0 1) (sourceB1705 + difference 1 0) sourceC1705) = raw24939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1705 sourceB1705 sourceC1705 difference raw24939; decide +kernel
    rw [ha]
    exact (canonical24939 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1705 + difference 0 2) (sourceB1705 + difference 2 0) sourceC1705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1925) := by
    have ha : (tripleCharges (sourceA1705 + difference 0 2) (sourceB1705 + difference 2 0) sourceC1705) = raw24940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1705 sourceB1705 sourceC1705 difference raw24940; decide +kernel
    rw [ha]
    exact (canonical24940 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1705 + difference 0 3) (sourceB1705 + difference 3 0) sourceC1705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA1705 + difference 0 3) (sourceB1705 + difference 3 0) sourceC1705) = raw24941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1705 sourceB1705 sourceC1705 difference raw24941; decide +kernel
    rw [ha]
    exact (canonical24941 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1705 + difference 0 4) (sourceB1705 + difference 4 0) sourceC1705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA1705 + difference 0 4) (sourceB1705 + difference 4 0) sourceC1705) = raw24942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1705 sourceB1705 sourceC1705 difference raw24942; decide +kernel
    rw [ha]
    exact (canonical24942 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1705 + difference 0 5) (sourceB1705 + difference 5 0) sourceC1705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA1705 + difference 0 5) (sourceB1705 + difference 5 0) sourceC1705) = raw24943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1705 sourceB1705 sourceC1705 difference raw24943; decide +kernel
    rw [ha]
    exact (canonical24943 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1705 + sourceB1705) sourceC1705) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1705 + sourceB1705) sourceC1705) = raw24944 := by
      apply Matrix.ext; unfold doubleCharges sourceA1705 sourceB1705 sourceC1705 raw24944; decide +kernel
    rw [ha]
    exact (canonical24944 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1705 sourceB1705 sourceC1705
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1705, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1706 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1706 : Charge := ![1, 2, -1, 0, 0, -2]
def sourceC1706 : Charge := ![3, -2, 1, -1, -1, 0]
def sourceForm1706 : Integer.Sparse Master := [(Sum.inr 988, 2), (Sum.inr 990, 1), (Sum.inr 998, 1), (Sum.inr 1052, 1), (Sum.inr 2214, 1), (Sum.inr 4080, -1)]

theorem sourceEq1706 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1706 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1706 + difference 0 5) (sourceB1706 + difference 5 0) sourceC1706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA1706 + difference 0 5) (sourceB1706 + difference 5 0) sourceC1706) = raw24943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1706 sourceB1706 sourceC1706 difference raw24943; decide +kernel
    rw [ha]
    exact (canonical24943 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1706 + difference 1 5) (sourceB1706 + difference 5 1) sourceC1706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 998) := by
    have ha : (tripleCharges (sourceA1706 + difference 1 5) (sourceB1706 + difference 5 1) sourceC1706) = raw24945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1706 sourceB1706 sourceC1706 difference raw24945; decide +kernel
    rw [ha]
    exact (canonical24945 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1706 + difference 2 5) (sourceB1706 + difference 5 2) sourceC1706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1052) := by
    have ha : (tripleCharges (sourceA1706 + difference 2 5) (sourceB1706 + difference 5 2) sourceC1706) = raw24946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1706 sourceB1706 sourceC1706 difference raw24946; decide +kernel
    rw [ha]
    exact (canonical24946 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1706 + difference 3 5) (sourceB1706 + difference 5 3) sourceC1706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 988) := by
    have ha : (tripleCharges (sourceA1706 + difference 3 5) (sourceB1706 + difference 5 3) sourceC1706) = raw24947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1706 sourceB1706 sourceC1706 difference raw24947; decide +kernel
    rw [ha]
    exact (canonical24947 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1706 + difference 4 5) (sourceB1706 + difference 5 4) sourceC1706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 988) := by
    have ha : (tripleCharges (sourceA1706 + difference 4 5) (sourceB1706 + difference 5 4) sourceC1706) = raw24948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1706 sourceB1706 sourceC1706 difference raw24948; decide +kernel
    rw [ha]
    exact (canonical24948 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1706 + difference 5 5) (sourceB1706 + difference 5 5) sourceC1706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 990) := by
    have ha : (tripleCharges (sourceA1706 + difference 5 5) (sourceB1706 + difference 5 5) sourceC1706) = raw24938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1706 sourceB1706 sourceC1706 difference raw24938; decide +kernel
    rw [ha]
    exact (canonical24938 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1706 + sourceB1706) sourceC1706) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1706 + sourceB1706) sourceC1706) = raw24944 := by
      apply Matrix.ext; unfold doubleCharges sourceA1706 sourceB1706 sourceC1706 raw24944; decide +kernel
    rw [ha]
    exact (canonical24944 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1706 sourceB1706 sourceC1706
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1706, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1707 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1707 : Charge := ![1, 2, -1, 0, -1, -1]
def sourceC1707 : Charge := ![3, -2, 1, -1, 0, -1]
def sourceForm1707 : Integer.Sparse Master := [(Sum.inr 988, 1), (Sum.inr 1922, 1), (Sum.inr 2118, 1), (Sum.inr 2195, 1), (Sum.inr 2214, 1), (Sum.inr 2216, 1), (Sum.inr 4080, -1)]

theorem sourceEq1707 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1707 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1707 + difference 0 0) (sourceB1707 + difference 0 0) sourceC1707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 988) := by
    have ha : (tripleCharges (sourceA1707 + difference 0 0) (sourceB1707 + difference 0 0) sourceC1707) = raw24949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1707 sourceB1707 sourceC1707 difference raw24949; decide +kernel
    rw [ha]
    exact (canonical24949 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1707 + difference 0 1) (sourceB1707 + difference 1 0) sourceC1707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2118) := by
    have ha : (tripleCharges (sourceA1707 + difference 0 1) (sourceB1707 + difference 1 0) sourceC1707) = raw24950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1707 sourceB1707 sourceC1707 difference raw24950; decide +kernel
    rw [ha]
    exact (canonical24950 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1707 + difference 0 2) (sourceB1707 + difference 2 0) sourceC1707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1922) := by
    have ha : (tripleCharges (sourceA1707 + difference 0 2) (sourceB1707 + difference 2 0) sourceC1707) = raw24951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1707 sourceB1707 sourceC1707 difference raw24951; decide +kernel
    rw [ha]
    exact (canonical24951 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1707 + difference 0 3) (sourceB1707 + difference 3 0) sourceC1707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA1707 + difference 0 3) (sourceB1707 + difference 3 0) sourceC1707) = raw24952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1707 sourceB1707 sourceC1707 difference raw24952; decide +kernel
    rw [ha]
    exact (canonical24952 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1707 + difference 0 4) (sourceB1707 + difference 4 0) sourceC1707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1707 + difference 0 4) (sourceB1707 + difference 4 0) sourceC1707) = raw24953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1707 sourceB1707 sourceC1707 difference raw24953; decide +kernel
    rw [ha]
    exact (canonical24953 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1707 + difference 0 5) (sourceB1707 + difference 5 0) sourceC1707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA1707 + difference 0 5) (sourceB1707 + difference 5 0) sourceC1707) = raw24954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1707 sourceB1707 sourceC1707 difference raw24954; decide +kernel
    rw [ha]
    exact (canonical24954 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1707 + sourceB1707) sourceC1707) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1707 + sourceB1707) sourceC1707) = raw24955 := by
      apply Matrix.ext; unfold doubleCharges sourceA1707 sourceB1707 sourceC1707 raw24955; decide +kernel
    rw [ha]
    exact (canonical24955 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1707 sourceB1707 sourceC1707
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1707, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1708 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1708 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceC1708 : Charge := ![3, -2, 1, 0, 0, -2]
def sourceForm1708 : Integer.Sparse Master := [(Sum.inr 987, 1), (Sum.inr 1921, 1), (Sum.inr 2117, 1), (Sum.inr 2213, 1), (Sum.inr 2215, 2), (Sum.inr 4082, -1)]

theorem sourceEq1708 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1708 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1708 + difference 0 0) (sourceB1708 + difference 0 0) sourceC1708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 987) := by
    have ha : (tripleCharges (sourceA1708 + difference 0 0) (sourceB1708 + difference 0 0) sourceC1708) = raw24956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1708 sourceB1708 sourceC1708 difference raw24956; decide +kernel
    rw [ha]
    exact (canonical24956 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1708 + difference 0 1) (sourceB1708 + difference 1 0) sourceC1708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2117) := by
    have ha : (tripleCharges (sourceA1708 + difference 0 1) (sourceB1708 + difference 1 0) sourceC1708) = raw24957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1708 sourceB1708 sourceC1708 difference raw24957; decide +kernel
    rw [ha]
    exact (canonical24957 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1708 + difference 0 2) (sourceB1708 + difference 2 0) sourceC1708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1921) := by
    have ha : (tripleCharges (sourceA1708 + difference 0 2) (sourceB1708 + difference 2 0) sourceC1708) = raw24958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1708 sourceB1708 sourceC1708 difference raw24958; decide +kernel
    rw [ha]
    exact (canonical24958 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1708 + difference 0 3) (sourceB1708 + difference 3 0) sourceC1708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA1708 + difference 0 3) (sourceB1708 + difference 3 0) sourceC1708) = raw24959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1708 sourceB1708 sourceC1708 difference raw24959; decide +kernel
    rw [ha]
    exact (canonical24959 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1708 + difference 0 4) (sourceB1708 + difference 4 0) sourceC1708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA1708 + difference 0 4) (sourceB1708 + difference 4 0) sourceC1708) = raw24960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1708 sourceB1708 sourceC1708 difference raw24960; decide +kernel
    rw [ha]
    exact (canonical24960 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1708 + difference 0 5) (sourceB1708 + difference 5 0) sourceC1708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA1708 + difference 0 5) (sourceB1708 + difference 5 0) sourceC1708) = raw24961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1708 sourceB1708 sourceC1708 difference raw24961; decide +kernel
    rw [ha]
    exact (canonical24961 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1708 + sourceB1708) sourceC1708) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1708 + sourceB1708) sourceC1708) = raw24962 := by
      apply Matrix.ext; unfold doubleCharges sourceA1708 sourceB1708 sourceC1708 raw24962; decide +kernel
    rw [ha]
    exact (canonical24962 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1708 sourceB1708 sourceC1708
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1708, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1709 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1709 : Charge := ![1, 1, 1, 0, 0, -3]
def sourceC1709 : Charge := ![3, -1, -1, -1, -1, 1]
def sourceForm1709 : Integer.Sparse Master := [(Sum.inr 1023, 1), (Sum.inr 2091, 2), (Sum.inr 2234, 2), (Sum.inr 2241, 1), (Sum.inr 4079, -1)]

theorem sourceEq1709 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1709 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1709 + difference 0 0) (sourceB1709 + difference 0 0) sourceC1709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1023) := by
    have ha : (tripleCharges (sourceA1709 + difference 0 0) (sourceB1709 + difference 0 0) sourceC1709) = raw24963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1709 sourceB1709 sourceC1709 difference raw24963; decide +kernel
    rw [ha]
    exact (canonical24963 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1709 + difference 0 1) (sourceB1709 + difference 1 0) sourceC1709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2091) := by
    have ha : (tripleCharges (sourceA1709 + difference 0 1) (sourceB1709 + difference 1 0) sourceC1709) = raw24964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1709 sourceB1709 sourceC1709 difference raw24964; decide +kernel
    rw [ha]
    exact (canonical24964 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1709 + difference 0 2) (sourceB1709 + difference 2 0) sourceC1709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2091) := by
    have ha : (tripleCharges (sourceA1709 + difference 0 2) (sourceB1709 + difference 2 0) sourceC1709) = raw24965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1709 sourceB1709 sourceC1709 difference raw24965; decide +kernel
    rw [ha]
    exact (canonical24965 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1709 + difference 0 3) (sourceB1709 + difference 3 0) sourceC1709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2234) := by
    have ha : (tripleCharges (sourceA1709 + difference 0 3) (sourceB1709 + difference 3 0) sourceC1709) = raw24966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1709 sourceB1709 sourceC1709 difference raw24966; decide +kernel
    rw [ha]
    exact (canonical24966 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1709 + difference 0 4) (sourceB1709 + difference 4 0) sourceC1709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2234) := by
    have ha : (tripleCharges (sourceA1709 + difference 0 4) (sourceB1709 + difference 4 0) sourceC1709) = raw24967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1709 sourceB1709 sourceC1709 difference raw24967; decide +kernel
    rw [ha]
    exact (canonical24967 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1709 + difference 0 5) (sourceB1709 + difference 5 0) sourceC1709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA1709 + difference 0 5) (sourceB1709 + difference 5 0) sourceC1709) = raw24968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1709 sourceB1709 sourceC1709 difference raw24968; decide +kernel
    rw [ha]
    exact (canonical24968 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1709 + sourceB1709) sourceC1709) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1709 + sourceB1709) sourceC1709) = raw24969 := by
      apply Matrix.ext; unfold doubleCharges sourceA1709 sourceB1709 sourceC1709 raw24969; decide +kernel
    rw [ha]
    exact (canonical24969 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1709 sourceB1709 sourceC1709
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1709, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1710 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1710 : Charge := ![1, 1, 1, 0, 0, -3]
def sourceC1710 : Charge := ![3, -1, -1, -1, -1, 1]
def sourceForm1710 : Integer.Sparse Master := [(Sum.inr 1018, 2), (Sum.inr 1023, 1), (Sum.inr 1034, 2), (Sum.inr 2241, 1), (Sum.inr 4079, -1)]

theorem sourceEq1710 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1710 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1710 + difference 0 5) (sourceB1710 + difference 5 0) sourceC1710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA1710 + difference 0 5) (sourceB1710 + difference 5 0) sourceC1710) = raw24968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1710 sourceB1710 sourceC1710 difference raw24968; decide +kernel
    rw [ha]
    exact (canonical24968 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1710 + difference 1 5) (sourceB1710 + difference 5 1) sourceC1710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1034) := by
    have ha : (tripleCharges (sourceA1710 + difference 1 5) (sourceB1710 + difference 5 1) sourceC1710) = raw24970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1710 sourceB1710 sourceC1710 difference raw24970; decide +kernel
    rw [ha]
    exact (canonical24970 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1710 + difference 2 5) (sourceB1710 + difference 5 2) sourceC1710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1034) := by
    have ha : (tripleCharges (sourceA1710 + difference 2 5) (sourceB1710 + difference 5 2) sourceC1710) = raw24971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1710 sourceB1710 sourceC1710 difference raw24971; decide +kernel
    rw [ha]
    exact (canonical24971 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1710 + difference 3 5) (sourceB1710 + difference 5 3) sourceC1710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1018) := by
    have ha : (tripleCharges (sourceA1710 + difference 3 5) (sourceB1710 + difference 5 3) sourceC1710) = raw24972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1710 sourceB1710 sourceC1710 difference raw24972; decide +kernel
    rw [ha]
    exact (canonical24972 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1710 + difference 4 5) (sourceB1710 + difference 5 4) sourceC1710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1018) := by
    have ha : (tripleCharges (sourceA1710 + difference 4 5) (sourceB1710 + difference 5 4) sourceC1710) = raw24973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1710 sourceB1710 sourceC1710 difference raw24973; decide +kernel
    rw [ha]
    exact (canonical24973 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1710 + difference 5 5) (sourceB1710 + difference 5 5) sourceC1710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1023) := by
    have ha : (tripleCharges (sourceA1710 + difference 5 5) (sourceB1710 + difference 5 5) sourceC1710) = raw24963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1710 sourceB1710 sourceC1710 difference raw24963; decide +kernel
    rw [ha]
    exact (canonical24963 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1710 + sourceB1710) sourceC1710) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1710 + sourceB1710) sourceC1710) = raw24969 := by
      apply Matrix.ext; unfold doubleCharges sourceA1710 sourceB1710 sourceC1710 raw24969; decide +kernel
    rw [ha]
    exact (canonical24969 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1710 sourceB1710 sourceC1710
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1710, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1711 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1711 : Charge := ![1, 1, 1, 0, -2, -1]
def sourceC1711 : Charge := ![3, -1, -1, -1, 1, -1]
def sourceForm1711 : Integer.Sparse Master := [(Sum.inr 1018, 1), (Sum.inr 2086, 2), (Sum.inr 2191, 1), (Sum.inr 2232, 1), (Sum.inr 2241, 1), (Sum.inr 4079, -1)]

theorem sourceEq1711 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1711 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1711 + difference 0 0) (sourceB1711 + difference 0 0) sourceC1711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1018) := by
    have ha : (tripleCharges (sourceA1711 + difference 0 0) (sourceB1711 + difference 0 0) sourceC1711) = raw24974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1711 sourceB1711 sourceC1711 difference raw24974; decide +kernel
    rw [ha]
    exact (canonical24974 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1711 + difference 0 1) (sourceB1711 + difference 1 0) sourceC1711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2086) := by
    have ha : (tripleCharges (sourceA1711 + difference 0 1) (sourceB1711 + difference 1 0) sourceC1711) = raw24975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1711 sourceB1711 sourceC1711 difference raw24975; decide +kernel
    rw [ha]
    exact (canonical24975 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1711 + difference 0 2) (sourceB1711 + difference 2 0) sourceC1711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2086) := by
    have ha : (tripleCharges (sourceA1711 + difference 0 2) (sourceB1711 + difference 2 0) sourceC1711) = raw24976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1711 sourceB1711 sourceC1711 difference raw24976; decide +kernel
    rw [ha]
    exact (canonical24976 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1711 + difference 0 3) (sourceB1711 + difference 3 0) sourceC1711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2232) := by
    have ha : (tripleCharges (sourceA1711 + difference 0 3) (sourceB1711 + difference 3 0) sourceC1711) = raw24977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1711 sourceB1711 sourceC1711 difference raw24977; decide +kernel
    rw [ha]
    exact (canonical24977 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1711 + difference 0 4) (sourceB1711 + difference 4 0) sourceC1711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1711 + difference 0 4) (sourceB1711 + difference 4 0) sourceC1711) = raw24978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1711 sourceB1711 sourceC1711 difference raw24978; decide +kernel
    rw [ha]
    exact (canonical24978 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1711 + difference 0 5) (sourceB1711 + difference 5 0) sourceC1711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2241) := by
    have ha : (tripleCharges (sourceA1711 + difference 0 5) (sourceB1711 + difference 5 0) sourceC1711) = raw24979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1711 sourceB1711 sourceC1711 difference raw24979; decide +kernel
    rw [ha]
    exact (canonical24979 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1711 + sourceB1711) sourceC1711) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1711 + sourceB1711) sourceC1711) = raw24980 := by
      apply Matrix.ext; unfold doubleCharges sourceA1711 sourceB1711 sourceC1711 raw24980; decide +kernel
    rw [ha]
    exact (canonical24980 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1711 sourceB1711 sourceC1711
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1711, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1712 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1712 : Charge := ![1, 1, 1, -1, -2, 0]
def sourceC1712 : Charge := ![3, -1, -1, 0, 1, -2]
def sourceForm1712 : Integer.Sparse Master := [(Sum.inr 1017, 1), (Sum.inr 2085, 2), (Sum.inr 2190, 1), (Sum.inr 2240, 1), (Sum.inr 2242, 1), (Sum.inr 4080, -1)]

theorem sourceEq1712 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1712 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1712 + difference 0 0) (sourceB1712 + difference 0 0) sourceC1712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1017) := by
    have ha : (tripleCharges (sourceA1712 + difference 0 0) (sourceB1712 + difference 0 0) sourceC1712) = raw21120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1712 sourceB1712 sourceC1712 difference raw21120; decide +kernel
    rw [ha]
    exact (canonical21120 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1712 + difference 0 1) (sourceB1712 + difference 1 0) sourceC1712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2085) := by
    have ha : (tripleCharges (sourceA1712 + difference 0 1) (sourceB1712 + difference 1 0) sourceC1712) = raw24981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1712 sourceB1712 sourceC1712 difference raw24981; decide +kernel
    rw [ha]
    exact (canonical24981 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1712 + difference 0 2) (sourceB1712 + difference 2 0) sourceC1712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2085) := by
    have ha : (tripleCharges (sourceA1712 + difference 0 2) (sourceB1712 + difference 2 0) sourceC1712) = raw24982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1712 sourceB1712 sourceC1712 difference raw24982; decide +kernel
    rw [ha]
    exact (canonical24982 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1712 + difference 0 3) (sourceB1712 + difference 3 0) sourceC1712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2242) := by
    have ha : (tripleCharges (sourceA1712 + difference 0 3) (sourceB1712 + difference 3 0) sourceC1712) = raw21116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1712 sourceB1712 sourceC1712 difference raw21116; decide +kernel
    rw [ha]
    exact (canonical21116 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1712 + difference 0 4) (sourceB1712 + difference 4 0) sourceC1712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2190) := by
    have ha : (tripleCharges (sourceA1712 + difference 0 4) (sourceB1712 + difference 4 0) sourceC1712) = raw24983 := by
      apply Matrix.ext; unfold tripleCharges sourceA1712 sourceB1712 sourceC1712 difference raw24983; decide +kernel
    rw [ha]
    exact (canonical24983 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1712 + difference 0 5) (sourceB1712 + difference 5 0) sourceC1712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA1712 + difference 0 5) (sourceB1712 + difference 5 0) sourceC1712) = raw24984 := by
      apply Matrix.ext; unfold tripleCharges sourceA1712 sourceB1712 sourceC1712 difference raw24984; decide +kernel
    rw [ha]
    exact (canonical24984 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1712 + sourceB1712) sourceC1712) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1712 + sourceB1712) sourceC1712) = raw21117 := by
      apply Matrix.ext; unfold doubleCharges sourceA1712 sourceB1712 sourceC1712 raw21117; decide +kernel
    rw [ha]
    exact (canonical21117 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1712 sourceB1712 sourceC1712
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1712, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1713 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1713 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceC1713 : Charge := ![3, -1, 0, -2, -1, 1]
def sourceForm1713 : Integer.Sparse Master := [(Sum.inr 1045, 1), (Sum.inr 2024, 1), (Sum.inr 2111, 1), (Sum.inr 2246, 1), (Sum.inr 2254, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

theorem sourceEq1713 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1713 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1713 + difference 0 0) (sourceB1713 + difference 0 0) sourceC1713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1045) := by
    have ha : (tripleCharges (sourceA1713 + difference 0 0) (sourceB1713 + difference 0 0) sourceC1713) = raw24985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1713 sourceB1713 sourceC1713 difference raw24985; decide +kernel
    rw [ha]
    exact (canonical24985 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1713 + difference 0 1) (sourceB1713 + difference 1 0) sourceC1713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2111) := by
    have ha : (tripleCharges (sourceA1713 + difference 0 1) (sourceB1713 + difference 1 0) sourceC1713) = raw24986 := by
      apply Matrix.ext; unfold tripleCharges sourceA1713 sourceB1713 sourceC1713 difference raw24986; decide +kernel
    rw [ha]
    exact (canonical24986 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1713 + difference 0 2) (sourceB1713 + difference 2 0) sourceC1713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2024) := by
    have ha : (tripleCharges (sourceA1713 + difference 0 2) (sourceB1713 + difference 2 0) sourceC1713) = raw24987 := by
      apply Matrix.ext; unfold tripleCharges sourceA1713 sourceB1713 sourceC1713 difference raw24987; decide +kernel
    rw [ha]
    exact (canonical24987 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1713 + difference 0 3) (sourceB1713 + difference 3 0) sourceC1713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA1713 + difference 0 3) (sourceB1713 + difference 3 0) sourceC1713) = raw24988 := by
      apply Matrix.ext; unfold tripleCharges sourceA1713 sourceB1713 sourceC1713 difference raw24988; decide +kernel
    rw [ha]
    exact (canonical24988 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1713 + difference 0 4) (sourceB1713 + difference 4 0) sourceC1713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA1713 + difference 0 4) (sourceB1713 + difference 4 0) sourceC1713) = raw24989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1713 sourceB1713 sourceC1713 difference raw24989; decide +kernel
    rw [ha]
    exact (canonical24989 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1713 + difference 0 5) (sourceB1713 + difference 5 0) sourceC1713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1713 + difference 0 5) (sourceB1713 + difference 5 0) sourceC1713) = raw24990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1713 sourceB1713 sourceC1713 difference raw24990; decide +kernel
    rw [ha]
    exact (canonical24990 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1713 + sourceB1713) sourceC1713) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1713 + sourceB1713) sourceC1713) = raw24991 := by
      apply Matrix.ext; unfold doubleCharges sourceA1713 sourceB1713 sourceC1713 raw24991; decide +kernel
    rw [ha]
    exact (canonical24991 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1713 sourceB1713 sourceC1713
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1713, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1714 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1714 : Charge := ![1, 1, 0, 1, 0, -3]
def sourceC1714 : Charge := ![3, -1, 0, -2, -1, 1]
def sourceForm1714 : Integer.Sparse Master := [(Sum.inr 1032, 1), (Sum.inr 1035, 1), (Sum.inr 1036, 1), (Sum.inr 1045, 1), (Sum.inr 1073, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

theorem sourceEq1714 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1714 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1714 + difference 0 5) (sourceB1714 + difference 5 0) sourceC1714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1714 + difference 0 5) (sourceB1714 + difference 5 0) sourceC1714) = raw24990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1714 sourceB1714 sourceC1714 difference raw24990; decide +kernel
    rw [ha]
    exact (canonical24990 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1714 + difference 1 5) (sourceB1714 + difference 5 1) sourceC1714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1714 + difference 1 5) (sourceB1714 + difference 5 1) sourceC1714) = raw24992 := by
      apply Matrix.ext; unfold tripleCharges sourceA1714 sourceB1714 sourceC1714 difference raw24992; decide +kernel
    rw [ha]
    exact (canonical24992 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1714 + difference 2 5) (sourceB1714 + difference 5 2) sourceC1714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1032) := by
    have ha : (tripleCharges (sourceA1714 + difference 2 5) (sourceB1714 + difference 5 2) sourceC1714) = raw24993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1714 sourceB1714 sourceC1714 difference raw24993; decide +kernel
    rw [ha]
    exact (canonical24993 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1714 + difference 3 5) (sourceB1714 + difference 5 3) sourceC1714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1714 + difference 3 5) (sourceB1714 + difference 5 3) sourceC1714) = raw24994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1714 sourceB1714 sourceC1714 difference raw24994; decide +kernel
    rw [ha]
    exact (canonical24994 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1714 + difference 4 5) (sourceB1714 + difference 5 4) sourceC1714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1036) := by
    have ha : (tripleCharges (sourceA1714 + difference 4 5) (sourceB1714 + difference 5 4) sourceC1714) = raw24995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1714 sourceB1714 sourceC1714 difference raw24995; decide +kernel
    rw [ha]
    exact (canonical24995 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1714 + difference 5 5) (sourceB1714 + difference 5 5) sourceC1714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1045) := by
    have ha : (tripleCharges (sourceA1714 + difference 5 5) (sourceB1714 + difference 5 5) sourceC1714) = raw24985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1714 sourceB1714 sourceC1714 difference raw24985; decide +kernel
    rw [ha]
    exact (canonical24985 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1714 + sourceB1714) sourceC1714) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1714 + sourceB1714) sourceC1714) = raw24991 := by
      apply Matrix.ext; unfold doubleCharges sourceA1714 sourceB1714 sourceC1714 raw24991; decide +kernel
    rw [ha]
    exact (canonical24991 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1714 sourceB1714 sourceC1714
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1714, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1715 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1715 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceC1715 : Charge := ![3, -1, 0, -2, 1, -1]
def sourceForm1715 : Integer.Sparse Master := [(Sum.inr 1036, 1), (Sum.inr 2017, 1), (Sum.inr 2102, 1), (Sum.inr 2206, 1), (Sum.inr 2251, 1), (Sum.inr 2260, 1), (Sum.inr 4080, -1)]

theorem sourceEq1715 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1715 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1715 + difference 0 0) (sourceB1715 + difference 0 0) sourceC1715) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1036) := by
    have ha : (tripleCharges (sourceA1715 + difference 0 0) (sourceB1715 + difference 0 0) sourceC1715) = raw24996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1715 sourceB1715 sourceC1715 difference raw24996; decide +kernel
    rw [ha]
    exact (canonical24996 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1715 + difference 0 1) (sourceB1715 + difference 1 0) sourceC1715) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2102) := by
    have ha : (tripleCharges (sourceA1715 + difference 0 1) (sourceB1715 + difference 1 0) sourceC1715) = raw24997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1715 sourceB1715 sourceC1715 difference raw24997; decide +kernel
    rw [ha]
    exact (canonical24997 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1715 + difference 0 2) (sourceB1715 + difference 2 0) sourceC1715) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2017) := by
    have ha : (tripleCharges (sourceA1715 + difference 0 2) (sourceB1715 + difference 2 0) sourceC1715) = raw24998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1715 sourceB1715 sourceC1715 difference raw24998; decide +kernel
    rw [ha]
    exact (canonical24998 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1715 + difference 0 3) (sourceB1715 + difference 3 0) sourceC1715) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA1715 + difference 0 3) (sourceB1715 + difference 3 0) sourceC1715) = raw24999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1715 sourceB1715 sourceC1715 difference raw24999; decide +kernel
    rw [ha]
    exact (canonical24999 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1715 + difference 0 4) (sourceB1715 + difference 4 0) sourceC1715) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2206) := by
    have ha : (tripleCharges (sourceA1715 + difference 0 4) (sourceB1715 + difference 4 0) sourceC1715) = raw25000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1715 sourceB1715 sourceC1715 difference raw25000; decide +kernel
    rw [ha]
    exact (canonical25000 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1715 + difference 0 5) (sourceB1715 + difference 5 0) sourceC1715) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1715 + difference 0 5) (sourceB1715 + difference 5 0) sourceC1715) = raw25001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1715 sourceB1715 sourceC1715 difference raw25001; decide +kernel
    rw [ha]
    exact (canonical25001 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1715 + sourceB1715) sourceC1715) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1715 + sourceB1715) sourceC1715) = raw25002 := by
      apply Matrix.ext; unfold doubleCharges sourceA1715 sourceB1715 sourceC1715 raw25002; decide +kernel
    rw [ha]
    exact (canonical25002 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1715 sourceB1715 sourceC1715
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1715, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1716 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1716 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1716 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceForm1716 : Integer.Sparse Master := [(Sum.inr 4152, 1), (Sum.inr 4157, 1), (Sum.inr 4158, 2), (Sum.inr 4182, 1), (Sum.inr 4331, 1), (Sum.inr 4332, 2), (Sum.inr 4351, 1), (Sum.inr 4366, 1), (Sum.inr 4371, 1), (Sum.inr 4372, 2), (Sum.inr 4439, 2), (Sum.inr 4442, 2), (Sum.inr 4444, 2), (Sum.inr 4456, 1), (Sum.inr 4458, 2), (Sum.inr 4461, 2), (Sum.inr 4497, 1), (Sum.inr 4805, 1), (Sum.inr 4869, 1), (Sum.inr 4889, 2), (Sum.inr 4893, 1)]

theorem sourceEq1716 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1716 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1716 + difference 0 1) (sourceB1716 + difference 1 0) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4869) := by
    have ha : (tripleCharges (sourceA1716 + difference 0 1) (sourceB1716 + difference 1 0) sourceC1716) = raw14356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw14356; decide +kernel
    rw [ha]
    exact (canonical14356 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1716 + difference 0 2) (sourceB1716 + difference 2 0) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4805) := by
    have ha : (tripleCharges (sourceA1716 + difference 0 2) (sourceB1716 + difference 2 0) sourceC1716) = raw14357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw14357; decide +kernel
    rw [ha]
    exact (canonical14357 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1716 + difference 0 3) (sourceB1716 + difference 3 0) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA1716 + difference 0 3) (sourceB1716 + difference 3 0) sourceC1716) = raw14358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw14358; decide +kernel
    rw [ha]
    exact (canonical14358 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1716 + difference 0 4) (sourceB1716 + difference 4 0) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA1716 + difference 0 4) (sourceB1716 + difference 4 0) sourceC1716) = raw14359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw14359; decide +kernel
    rw [ha]
    exact (canonical14359 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1716 + difference 0 5) (sourceB1716 + difference 5 0) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA1716 + difference 0 5) (sourceB1716 + difference 5 0) sourceC1716) = raw25003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25003; decide +kernel
    rw [ha]
    exact (canonical25003 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1716 + difference 1 0) (sourceB1716 + difference 0 1) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4182) := by
    have ha : (tripleCharges (sourceA1716 + difference 1 0) (sourceB1716 + difference 0 1) sourceC1716) = raw25004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25004; decide +kernel
    rw [ha]
    exact (canonical25004 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1716 + difference 1 2) (sourceB1716 + difference 2 1) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4351) := by
    have ha : (tripleCharges (sourceA1716 + difference 1 2) (sourceB1716 + difference 2 1) sourceC1716) = raw25005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25005; decide +kernel
    rw [ha]
    exact (canonical25005 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1716 + difference 1 3) (sourceB1716 + difference 3 1) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1716 + difference 1 3) (sourceB1716 + difference 3 1) sourceC1716) = raw25006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25006; decide +kernel
    rw [ha]
    exact (canonical25006 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1716 + difference 1 4) (sourceB1716 + difference 4 1) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1716 + difference 1 4) (sourceB1716 + difference 4 1) sourceC1716) = raw25007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25007; decide +kernel
    rw [ha]
    exact (canonical25007 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1716 + difference 1 5) (sourceB1716 + difference 5 1) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1716 + difference 1 5) (sourceB1716 + difference 5 1) sourceC1716) = raw14335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw14335; decide +kernel
    rw [ha]
    exact (canonical14335 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1716 + difference 2 0) (sourceB1716 + difference 0 2) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4152) := by
    have ha : (tripleCharges (sourceA1716 + difference 2 0) (sourceB1716 + difference 0 2) sourceC1716) = raw25008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25008; decide +kernel
    rw [ha]
    exact (canonical25008 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1716 + difference 2 1) (sourceB1716 + difference 1 2) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4366) := by
    have ha : (tripleCharges (sourceA1716 + difference 2 1) (sourceB1716 + difference 1 2) sourceC1716) = raw25009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25009; decide +kernel
    rw [ha]
    exact (canonical25009 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1716 + difference 2 3) (sourceB1716 + difference 3 2) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA1716 + difference 2 3) (sourceB1716 + difference 3 2) sourceC1716) = raw25010 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25010; decide +kernel
    rw [ha]
    exact (canonical25010 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1716 + difference 2 4) (sourceB1716 + difference 4 2) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA1716 + difference 2 4) (sourceB1716 + difference 4 2) sourceC1716) = raw25011 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25011; decide +kernel
    rw [ha]
    exact (canonical25011 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1716 + difference 2 5) (sourceB1716 + difference 5 2) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1716 + difference 2 5) (sourceB1716 + difference 5 2) sourceC1716) = raw14340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw14340; decide +kernel
    rw [ha]
    exact (canonical14340 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1716 + difference 3 0) (sourceB1716 + difference 0 3) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4158) := by
    have ha : (tripleCharges (sourceA1716 + difference 3 0) (sourceB1716 + difference 0 3) sourceC1716) = raw25012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25012; decide +kernel
    rw [ha]
    exact (canonical25012 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1716 + difference 3 1) (sourceB1716 + difference 1 3) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4372) := by
    have ha : (tripleCharges (sourceA1716 + difference 3 1) (sourceB1716 + difference 1 3) sourceC1716) = raw25013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25013; decide +kernel
    rw [ha]
    exact (canonical25013 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1716 + difference 3 2) (sourceB1716 + difference 2 3) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4332) := by
    have ha : (tripleCharges (sourceA1716 + difference 3 2) (sourceB1716 + difference 2 3) sourceC1716) = raw25014 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25014; decide +kernel
    rw [ha]
    exact (canonical25014 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1716 + difference 3 4) (sourceB1716 + difference 4 3) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA1716 + difference 3 4) (sourceB1716 + difference 4 3) sourceC1716) = raw25015 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25015; decide +kernel
    rw [ha]
    exact (canonical25015 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1716 + difference 3 5) (sourceB1716 + difference 5 3) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1716 + difference 3 5) (sourceB1716 + difference 5 3) sourceC1716) = raw14345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw14345; decide +kernel
    rw [ha]
    exact (canonical14345 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1716 + difference 4 0) (sourceB1716 + difference 0 4) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4158) := by
    have ha : (tripleCharges (sourceA1716 + difference 4 0) (sourceB1716 + difference 0 4) sourceC1716) = raw25016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25016; decide +kernel
    rw [ha]
    exact (canonical25016 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1716 + difference 4 1) (sourceB1716 + difference 1 4) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4372) := by
    have ha : (tripleCharges (sourceA1716 + difference 4 1) (sourceB1716 + difference 1 4) sourceC1716) = raw25017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25017; decide +kernel
    rw [ha]
    exact (canonical25017 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1716 + difference 4 2) (sourceB1716 + difference 2 4) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4332) := by
    have ha : (tripleCharges (sourceA1716 + difference 4 2) (sourceB1716 + difference 2 4) sourceC1716) = raw25018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25018; decide +kernel
    rw [ha]
    exact (canonical25018 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1716 + difference 4 3) (sourceB1716 + difference 3 4) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA1716 + difference 4 3) (sourceB1716 + difference 3 4) sourceC1716) = raw25019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25019; decide +kernel
    rw [ha]
    exact (canonical25019 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1716 + difference 4 5) (sourceB1716 + difference 5 4) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1716 + difference 4 5) (sourceB1716 + difference 5 4) sourceC1716) = raw14350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw14350; decide +kernel
    rw [ha]
    exact (canonical14350 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1716 + difference 5 0) (sourceB1716 + difference 0 5) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4157) := by
    have ha : (tripleCharges (sourceA1716 + difference 5 0) (sourceB1716 + difference 0 5) sourceC1716) = raw25020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25020; decide +kernel
    rw [ha]
    exact (canonical25020 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1716 + difference 5 1) (sourceB1716 + difference 1 5) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4371) := by
    have ha : (tripleCharges (sourceA1716 + difference 5 1) (sourceB1716 + difference 1 5) sourceC1716) = raw25021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25021; decide +kernel
    rw [ha]
    exact (canonical25021 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1716 + difference 5 2) (sourceB1716 + difference 2 5) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4331) := by
    have ha : (tripleCharges (sourceA1716 + difference 5 2) (sourceB1716 + difference 2 5) sourceC1716) = raw25022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25022; decide +kernel
    rw [ha]
    exact (canonical25022 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1716 + difference 5 3) (sourceB1716 + difference 3 5) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA1716 + difference 5 3) (sourceB1716 + difference 3 5) sourceC1716) = raw25023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25023; decide +kernel
    rw [ha]
    exact (canonical25023 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1716 + difference 5 4) (sourceB1716 + difference 4 5) sourceC1716) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA1716 + difference 5 4) (sourceB1716 + difference 4 5) sourceC1716) = raw25024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1716 sourceB1716 sourceC1716 difference raw25024; decide +kernel
    rw [ha]
    exact (canonical25024 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1716 sourceB1716 sourceC1716
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1716, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1717 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1717 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1717 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceForm1717 : Integer.Sparse Master := [(Sum.inr 1510, 1), (Sum.inr 1522, 2), (Sum.inr 1524, 1), (Sum.inr 1528, 1), (Sum.inr 1678, 2), (Sum.inr 1680, 1), (Sum.inr 1684, 1), (Sum.inr 1706, 1), (Sum.inr 1711, 1), (Sum.inr 1713, 2), (Sum.inr 1724, 2), (Sum.inr 1726, 1), (Sum.inr 1734, 2), (Sum.inr 1736, 2), (Sum.inr 1737, 2), (Sum.inr 1742, 1), (Sum.inr 1744, 2), (Sum.inr 2214, 1), (Sum.inr 2263, 1), (Sum.inr 2275, 1), (Sum.inr 2277, 2)]

theorem sourceEq1717 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1717 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1717 + difference 0 1) (sourceB1717 + difference 1 0) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2275) := by
    have ha : (tripleCharges (sourceA1717 + difference 0 1) (sourceB1717 + difference 1 0) sourceC1717) = raw25025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25025; decide +kernel
    rw [ha]
    exact (canonical25025 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1717 + difference 0 2) (sourceB1717 + difference 2 0) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2214) := by
    have ha : (tripleCharges (sourceA1717 + difference 0 2) (sourceB1717 + difference 2 0) sourceC1717) = raw25026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25026; decide +kernel
    rw [ha]
    exact (canonical25026 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1717 + difference 0 3) (sourceB1717 + difference 3 0) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA1717 + difference 0 3) (sourceB1717 + difference 3 0) sourceC1717) = raw25027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25027; decide +kernel
    rw [ha]
    exact (canonical25027 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1717 + difference 0 4) (sourceB1717 + difference 4 0) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA1717 + difference 0 4) (sourceB1717 + difference 4 0) sourceC1717) = raw25028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25028; decide +kernel
    rw [ha]
    exact (canonical25028 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1717 + difference 0 5) (sourceB1717 + difference 5 0) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA1717 + difference 0 5) (sourceB1717 + difference 5 0) sourceC1717) = raw25029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25029; decide +kernel
    rw [ha]
    exact (canonical25029 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1717 + difference 1 0) (sourceB1717 + difference 0 1) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1524) := by
    have ha : (tripleCharges (sourceA1717 + difference 1 0) (sourceB1717 + difference 0 1) sourceC1717) = raw25030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25030; decide +kernel
    rw [ha]
    exact (canonical25030 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1717 + difference 1 2) (sourceB1717 + difference 2 1) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1680) := by
    have ha : (tripleCharges (sourceA1717 + difference 1 2) (sourceB1717 + difference 2 1) sourceC1717) = raw25031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25031; decide +kernel
    rw [ha]
    exact (canonical25031 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1717 + difference 1 3) (sourceB1717 + difference 3 1) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1717 + difference 1 3) (sourceB1717 + difference 3 1) sourceC1717) = raw25032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25032; decide +kernel
    rw [ha]
    exact (canonical25032 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1717 + difference 1 4) (sourceB1717 + difference 4 1) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1717 + difference 1 4) (sourceB1717 + difference 4 1) sourceC1717) = raw25033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25033; decide +kernel
    rw [ha]
    exact (canonical25033 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1717 + difference 1 5) (sourceB1717 + difference 5 1) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1726) := by
    have ha : (tripleCharges (sourceA1717 + difference 1 5) (sourceB1717 + difference 5 1) sourceC1717) = raw25034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25034; decide +kernel
    rw [ha]
    exact (canonical25034 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1717 + difference 2 0) (sourceB1717 + difference 0 2) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1510) := by
    have ha : (tripleCharges (sourceA1717 + difference 2 0) (sourceB1717 + difference 0 2) sourceC1717) = raw25035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25035; decide +kernel
    rw [ha]
    exact (canonical25035 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1717 + difference 2 1) (sourceB1717 + difference 1 2) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1711) := by
    have ha : (tripleCharges (sourceA1717 + difference 2 1) (sourceB1717 + difference 1 2) sourceC1717) = raw25036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25036; decide +kernel
    rw [ha]
    exact (canonical25036 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1717 + difference 2 3) (sourceB1717 + difference 3 2) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1717 + difference 2 3) (sourceB1717 + difference 3 2) sourceC1717) = raw25037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25037; decide +kernel
    rw [ha]
    exact (canonical25037 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1717 + difference 2 4) (sourceB1717 + difference 4 2) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1717 + difference 2 4) (sourceB1717 + difference 4 2) sourceC1717) = raw25038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25038; decide +kernel
    rw [ha]
    exact (canonical25038 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1717 + difference 2 5) (sourceB1717 + difference 5 2) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1717 + difference 2 5) (sourceB1717 + difference 5 2) sourceC1717) = raw25039 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25039; decide +kernel
    rw [ha]
    exact (canonical25039 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1717 + difference 3 0) (sourceB1717 + difference 0 3) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1522) := by
    have ha : (tripleCharges (sourceA1717 + difference 3 0) (sourceB1717 + difference 0 3) sourceC1717) = raw25040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25040; decide +kernel
    rw [ha]
    exact (canonical25040 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1717 + difference 3 1) (sourceB1717 + difference 1 3) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1734) := by
    have ha : (tripleCharges (sourceA1717 + difference 3 1) (sourceB1717 + difference 1 3) sourceC1717) = raw25041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25041; decide +kernel
    rw [ha]
    exact (canonical25041 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1717 + difference 3 2) (sourceB1717 + difference 2 3) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1678) := by
    have ha : (tripleCharges (sourceA1717 + difference 3 2) (sourceB1717 + difference 2 3) sourceC1717) = raw25042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25042; decide +kernel
    rw [ha]
    exact (canonical25042 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1717 + difference 3 4) (sourceB1717 + difference 4 3) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1717 + difference 3 4) (sourceB1717 + difference 4 3) sourceC1717) = raw25043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25043; decide +kernel
    rw [ha]
    exact (canonical25043 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1717 + difference 3 5) (sourceB1717 + difference 5 3) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1717 + difference 3 5) (sourceB1717 + difference 5 3) sourceC1717) = raw25044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25044; decide +kernel
    rw [ha]
    exact (canonical25044 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1717 + difference 4 0) (sourceB1717 + difference 0 4) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1522) := by
    have ha : (tripleCharges (sourceA1717 + difference 4 0) (sourceB1717 + difference 0 4) sourceC1717) = raw25045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25045; decide +kernel
    rw [ha]
    exact (canonical25045 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1717 + difference 4 1) (sourceB1717 + difference 1 4) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1734) := by
    have ha : (tripleCharges (sourceA1717 + difference 4 1) (sourceB1717 + difference 1 4) sourceC1717) = raw25046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25046; decide +kernel
    rw [ha]
    exact (canonical25046 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1717 + difference 4 2) (sourceB1717 + difference 2 4) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1678) := by
    have ha : (tripleCharges (sourceA1717 + difference 4 2) (sourceB1717 + difference 2 4) sourceC1717) = raw25047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25047; decide +kernel
    rw [ha]
    exact (canonical25047 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1717 + difference 4 3) (sourceB1717 + difference 3 4) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1717 + difference 4 3) (sourceB1717 + difference 3 4) sourceC1717) = raw25048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25048; decide +kernel
    rw [ha]
    exact (canonical25048 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1717 + difference 4 5) (sourceB1717 + difference 5 4) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1717 + difference 4 5) (sourceB1717 + difference 5 4) sourceC1717) = raw25049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25049; decide +kernel
    rw [ha]
    exact (canonical25049 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1717 + difference 5 0) (sourceB1717 + difference 0 5) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1528) := by
    have ha : (tripleCharges (sourceA1717 + difference 5 0) (sourceB1717 + difference 0 5) sourceC1717) = raw25050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25050; decide +kernel
    rw [ha]
    exact (canonical25050 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1717 + difference 5 1) (sourceB1717 + difference 1 5) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1742) := by
    have ha : (tripleCharges (sourceA1717 + difference 5 1) (sourceB1717 + difference 1 5) sourceC1717) = raw25051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25051; decide +kernel
    rw [ha]
    exact (canonical25051 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1717 + difference 5 2) (sourceB1717 + difference 2 5) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1684) := by
    have ha : (tripleCharges (sourceA1717 + difference 5 2) (sourceB1717 + difference 2 5) sourceC1717) = raw25052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25052; decide +kernel
    rw [ha]
    exact (canonical25052 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1717 + difference 5 3) (sourceB1717 + difference 3 5) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA1717 + difference 5 3) (sourceB1717 + difference 3 5) sourceC1717) = raw25053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25053; decide +kernel
    rw [ha]
    exact (canonical25053 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1717 + difference 5 4) (sourceB1717 + difference 4 5) sourceC1717) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA1717 + difference 5 4) (sourceB1717 + difference 4 5) sourceC1717) = raw25054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1717 sourceB1717 sourceC1717 difference raw25054; decide +kernel
    rw [ha]
    exact (canonical25054 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1717 sourceB1717 sourceC1717
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1717, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1718 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1718 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1718 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceForm1718 : Integer.Sparse Master := [(Sum.inr 610, 1), (Sum.inr 929, 1), (Sum.inr 1044, 3), (Sum.inr 1081, 1), (Sum.inr 4083, -1)]

theorem sourceEq1718 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1718 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1718 + difference 1 0) (sourceB1718 + difference 0 1) sourceC1718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 610) := by
    have ha : (tripleCharges (sourceA1718 + difference 1 0) (sourceB1718 + difference 0 1) sourceC1718) = raw25055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1718 sourceB1718 sourceC1718 difference raw25055; decide +kernel
    rw [ha]
    exact (canonical25055 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1718 + difference 1 1) (sourceB1718 + difference 1 1) sourceC1718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1718 + difference 1 1) (sourceB1718 + difference 1 1) sourceC1718) = raw25056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1718 sourceB1718 sourceC1718 difference raw25056; decide +kernel
    rw [ha]
    exact (canonical25056 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1718 + difference 1 2) (sourceB1718 + difference 2 1) sourceC1718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 929) := by
    have ha : (tripleCharges (sourceA1718 + difference 1 2) (sourceB1718 + difference 2 1) sourceC1718) = raw25057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1718 sourceB1718 sourceC1718 difference raw25057; decide +kernel
    rw [ha]
    exact (canonical25057 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1718 + difference 1 3) (sourceB1718 + difference 3 1) sourceC1718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1718 + difference 1 3) (sourceB1718 + difference 3 1) sourceC1718) = raw25058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1718 sourceB1718 sourceC1718 difference raw25058; decide +kernel
    rw [ha]
    exact (canonical25058 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1718 + difference 1 4) (sourceB1718 + difference 4 1) sourceC1718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1718 + difference 1 4) (sourceB1718 + difference 4 1) sourceC1718) = raw25059 := by
      apply Matrix.ext; unfold tripleCharges sourceA1718 sourceB1718 sourceC1718 difference raw25059; decide +kernel
    rw [ha]
    exact (canonical25059 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1718 + difference 1 5) (sourceB1718 + difference 5 1) sourceC1718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1081) := by
    have ha : (tripleCharges (sourceA1718 + difference 1 5) (sourceB1718 + difference 5 1) sourceC1718) = raw25060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1718 sourceB1718 sourceC1718 difference raw25060; decide +kernel
    rw [ha]
    exact (canonical25060 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1718 + sourceB1718) sourceC1718) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1718 + sourceB1718) sourceC1718) = raw25061 := by
      apply Matrix.ext; unfold doubleCharges sourceA1718 sourceB1718 sourceC1718 raw25061; decide +kernel
    rw [ha]
    exact (canonical25061 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1718 sourceB1718 sourceC1718
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1718, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1719 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1719 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceC1719 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceForm1719 : Integer.Sparse Master := [(Sum.inr 944, 1), (Sum.inr 949, 1), (Sum.inr 950, 2), (Sum.inr 1044, 1), (Sum.inr 2110, 1), (Sum.inr 4083, -1)]

theorem sourceEq1719 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1719 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1719 + difference 0 1) (sourceB1719 + difference 1 0) sourceC1719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA1719 + difference 0 1) (sourceB1719 + difference 1 0) sourceC1719) = raw25062 := by
      apply Matrix.ext; unfold tripleCharges sourceA1719 sourceB1719 sourceC1719 difference raw25062; decide +kernel
    rw [ha]
    exact (canonical25062 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1719 + difference 1 1) (sourceB1719 + difference 1 1) sourceC1719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1719 + difference 1 1) (sourceB1719 + difference 1 1) sourceC1719) = raw25056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1719 sourceB1719 sourceC1719 difference raw25056; decide +kernel
    rw [ha]
    exact (canonical25056 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1719 + difference 2 1) (sourceB1719 + difference 1 2) sourceC1719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 944) := by
    have ha : (tripleCharges (sourceA1719 + difference 2 1) (sourceB1719 + difference 1 2) sourceC1719) = raw25063 := by
      apply Matrix.ext; unfold tripleCharges sourceA1719 sourceB1719 sourceC1719 difference raw25063; decide +kernel
    rw [ha]
    exact (canonical25063 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1719 + difference 3 1) (sourceB1719 + difference 1 3) sourceC1719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 950) := by
    have ha : (tripleCharges (sourceA1719 + difference 3 1) (sourceB1719 + difference 1 3) sourceC1719) = raw25064 := by
      apply Matrix.ext; unfold tripleCharges sourceA1719 sourceB1719 sourceC1719 difference raw25064; decide +kernel
    rw [ha]
    exact (canonical25064 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1719 + difference 4 1) (sourceB1719 + difference 1 4) sourceC1719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 950) := by
    have ha : (tripleCharges (sourceA1719 + difference 4 1) (sourceB1719 + difference 1 4) sourceC1719) = raw25065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1719 sourceB1719 sourceC1719 difference raw25065; decide +kernel
    rw [ha]
    exact (canonical25065 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1719 + difference 5 1) (sourceB1719 + difference 1 5) sourceC1719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 949) := by
    have ha : (tripleCharges (sourceA1719 + difference 5 1) (sourceB1719 + difference 1 5) sourceC1719) = raw25066 := by
      apply Matrix.ext; unfold tripleCharges sourceA1719 sourceB1719 sourceC1719 difference raw25066; decide +kernel
    rw [ha]
    exact (canonical25066 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1719 + sourceB1719) sourceC1719) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1719 + sourceB1719) sourceC1719) = raw25061 := by
      apply Matrix.ext; unfold doubleCharges sourceA1719 sourceB1719 sourceC1719 raw25061; decide +kernel
    rw [ha]
    exact (canonical25061 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1719 sourceB1719 sourceC1719
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1719, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1720 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1720 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceC1720 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceForm1720 : Integer.Sparse Master := [(Sum.inr 4104, 1), (Sum.inr 4105, 1), (Sum.inr 4106, 2), (Sum.inr 4126, 1), (Sum.inr 4290, 1), (Sum.inr 4291, 2), (Sum.inr 4307, 1), (Sum.inr 4351, 1), (Sum.inr 4352, 1), (Sum.inr 4354, 2), (Sum.inr 4451, 1), (Sum.inr 4452, 2), (Sum.inr 4461, 2), (Sum.inr 4463, 2), (Sum.inr 4466, 2), (Sum.inr 4489, 1), (Sum.inr 4503, 2), (Sum.inr 5076, 1), (Sum.inr 5172, 1), (Sum.inr 5290, 1), (Sum.inr 5294, 2)]

theorem sourceEq1720 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1720 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1720 + difference 0 1) (sourceB1720 + difference 1 0) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA1720 + difference 0 1) (sourceB1720 + difference 1 0) sourceC1720) = raw13592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw13592; decide +kernel
    rw [ha]
    exact (canonical13592 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1720 + difference 0 2) (sourceB1720 + difference 2 0) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA1720 + difference 0 2) (sourceB1720 + difference 2 0) sourceC1720) = raw13593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw13593; decide +kernel
    rw [ha]
    exact (canonical13593 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1720 + difference 0 3) (sourceB1720 + difference 3 0) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1720 + difference 0 3) (sourceB1720 + difference 3 0) sourceC1720) = raw3054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw3054; decide +kernel
    rw [ha]
    exact (canonical3054 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1720 + difference 0 4) (sourceB1720 + difference 4 0) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA1720 + difference 0 4) (sourceB1720 + difference 4 0) sourceC1720) = raw13594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw13594; decide +kernel
    rw [ha]
    exact (canonical13594 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1720 + difference 0 5) (sourceB1720 + difference 5 0) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA1720 + difference 0 5) (sourceB1720 + difference 5 0) sourceC1720) = raw3044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw3044; decide +kernel
    rw [ha]
    exact (canonical3044 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1720 + difference 1 0) (sourceB1720 + difference 0 1) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4126) := by
    have ha : (tripleCharges (sourceA1720 + difference 1 0) (sourceB1720 + difference 0 1) sourceC1720) = raw25067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25067; decide +kernel
    rw [ha]
    exact (canonical25067 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1720 + difference 1 2) (sourceB1720 + difference 2 1) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4307) := by
    have ha : (tripleCharges (sourceA1720 + difference 1 2) (sourceB1720 + difference 2 1) sourceC1720) = raw25068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25068; decide +kernel
    rw [ha]
    exact (canonical25068 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1720 + difference 1 3) (sourceB1720 + difference 3 1) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1720 + difference 1 3) (sourceB1720 + difference 3 1) sourceC1720) = raw21243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw21243; decide +kernel
    rw [ha]
    exact (canonical21243 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1720 + difference 1 4) (sourceB1720 + difference 4 1) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1720 + difference 1 4) (sourceB1720 + difference 4 1) sourceC1720) = raw25069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25069; decide +kernel
    rw [ha]
    exact (canonical25069 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1720 + difference 1 5) (sourceB1720 + difference 5 1) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA1720 + difference 1 5) (sourceB1720 + difference 5 1) sourceC1720) = raw13574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw13574; decide +kernel
    rw [ha]
    exact (canonical13574 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1720 + difference 2 0) (sourceB1720 + difference 0 2) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4104) := by
    have ha : (tripleCharges (sourceA1720 + difference 2 0) (sourceB1720 + difference 0 2) sourceC1720) = raw25070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25070; decide +kernel
    rw [ha]
    exact (canonical25070 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1720 + difference 2 1) (sourceB1720 + difference 1 2) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4351) := by
    have ha : (tripleCharges (sourceA1720 + difference 2 1) (sourceB1720 + difference 1 2) sourceC1720) = raw25071 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25071; decide +kernel
    rw [ha]
    exact (canonical25071 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1720 + difference 2 3) (sourceB1720 + difference 3 2) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1720 + difference 2 3) (sourceB1720 + difference 3 2) sourceC1720) = raw21248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw21248; decide +kernel
    rw [ha]
    exact (canonical21248 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1720 + difference 2 4) (sourceB1720 + difference 4 2) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1720 + difference 2 4) (sourceB1720 + difference 4 2) sourceC1720) = raw25072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25072; decide +kernel
    rw [ha]
    exact (canonical25072 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1720 + difference 2 5) (sourceB1720 + difference 5 2) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA1720 + difference 2 5) (sourceB1720 + difference 5 2) sourceC1720) = raw13578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw13578; decide +kernel
    rw [ha]
    exact (canonical13578 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1720 + difference 3 0) (sourceB1720 + difference 0 3) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4106) := by
    have ha : (tripleCharges (sourceA1720 + difference 3 0) (sourceB1720 + difference 0 3) sourceC1720) = raw25073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25073; decide +kernel
    rw [ha]
    exact (canonical25073 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1720 + difference 3 1) (sourceB1720 + difference 1 3) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA1720 + difference 3 1) (sourceB1720 + difference 1 3) sourceC1720) = raw25074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25074; decide +kernel
    rw [ha]
    exact (canonical25074 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1720 + difference 3 2) (sourceB1720 + difference 2 3) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4291) := by
    have ha : (tripleCharges (sourceA1720 + difference 3 2) (sourceB1720 + difference 2 3) sourceC1720) = raw25075 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25075; decide +kernel
    rw [ha]
    exact (canonical25075 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1720 + difference 3 4) (sourceB1720 + difference 4 3) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1720 + difference 3 4) (sourceB1720 + difference 4 3) sourceC1720) = raw25076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw25076; decide +kernel
    rw [ha]
    exact (canonical25076 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1720 + difference 3 5) (sourceB1720 + difference 5 3) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA1720 + difference 3 5) (sourceB1720 + difference 5 3) sourceC1720) = raw13582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw13582; decide +kernel
    rw [ha]
    exact (canonical13582 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1720 + difference 4 0) (sourceB1720 + difference 0 4) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4106) := by
    have ha : (tripleCharges (sourceA1720 + difference 4 0) (sourceB1720 + difference 0 4) sourceC1720) = raw23046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw23046; decide +kernel
    rw [ha]
    exact (canonical23046 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1720 + difference 4 1) (sourceB1720 + difference 1 4) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4354) := by
    have ha : (tripleCharges (sourceA1720 + difference 4 1) (sourceB1720 + difference 1 4) sourceC1720) = raw23047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw23047; decide +kernel
    rw [ha]
    exact (canonical23047 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1720 + difference 4 2) (sourceB1720 + difference 2 4) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4291) := by
    have ha : (tripleCharges (sourceA1720 + difference 4 2) (sourceB1720 + difference 2 4) sourceC1720) = raw23048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw23048; decide +kernel
    rw [ha]
    exact (canonical23048 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1720 + difference 4 3) (sourceB1720 + difference 3 4) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1720 + difference 4 3) (sourceB1720 + difference 3 4) sourceC1720) = raw21257 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw21257; decide +kernel
    rw [ha]
    exact (canonical21257 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1720 + difference 4 5) (sourceB1720 + difference 5 4) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4452) := by
    have ha : (tripleCharges (sourceA1720 + difference 4 5) (sourceB1720 + difference 5 4) sourceC1720) = raw13587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw13587; decide +kernel
    rw [ha]
    exact (canonical13587 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1720 + difference 5 0) (sourceB1720 + difference 0 5) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4105) := by
    have ha : (tripleCharges (sourceA1720 + difference 5 0) (sourceB1720 + difference 0 5) sourceC1720) = raw21249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw21249; decide +kernel
    rw [ha]
    exact (canonical21249 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1720 + difference 5 1) (sourceB1720 + difference 1 5) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4352) := by
    have ha : (tripleCharges (sourceA1720 + difference 5 1) (sourceB1720 + difference 1 5) sourceC1720) = raw21250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw21250; decide +kernel
    rw [ha]
    exact (canonical21250 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1720 + difference 5 2) (sourceB1720 + difference 2 5) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4290) := by
    have ha : (tripleCharges (sourceA1720 + difference 5 2) (sourceB1720 + difference 2 5) sourceC1720) = raw21251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw21251; decide +kernel
    rw [ha]
    exact (canonical21251 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1720 + difference 5 3) (sourceB1720 + difference 3 5) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1720 + difference 5 3) (sourceB1720 + difference 3 5) sourceC1720) = raw23054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw23054; decide +kernel
    rw [ha]
    exact (canonical23054 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1720 + difference 5 4) (sourceB1720 + difference 4 5) sourceC1720) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1720 + difference 5 4) (sourceB1720 + difference 4 5) sourceC1720) = raw21252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1720 sourceB1720 sourceC1720 difference raw21252; decide +kernel
    rw [ha]
    exact (canonical21252 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1720 sourceB1720 sourceC1720
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1720, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1721 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1721 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceC1721 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceForm1721 : Integer.Sparse Master := [(Sum.inr 541, 1), (Sum.inr 542, 1), (Sum.inr 543, 2), (Sum.inr 557, 1), (Sum.inr 868, 1), (Sum.inr 869, 2), (Sum.inr 885, 1), (Sum.inr 929, 1), (Sum.inr 930, 1), (Sum.inr 932, 2), (Sum.inr 1034, 1), (Sum.inr 1035, 2), (Sum.inr 1044, 2), (Sum.inr 1046, 2), (Sum.inr 1049, 2), (Sum.inr 1073, 1), (Sum.inr 1087, 2), (Sum.inr 2483, 1), (Sum.inr 2599, 1), (Sum.inr 2764, 1), (Sum.inr 2768, 2)]

theorem sourceEq1721 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1721 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1721 + difference 0 1) (sourceB1721 + difference 1 0) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2599) := by
    have ha : (tripleCharges (sourceA1721 + difference 0 1) (sourceB1721 + difference 1 0) sourceC1721) = raw13614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw13614; decide +kernel
    rw [ha]
    exact (canonical13614 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1721 + difference 0 2) (sourceB1721 + difference 2 0) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA1721 + difference 0 2) (sourceB1721 + difference 2 0) sourceC1721) = raw13615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw13615; decide +kernel
    rw [ha]
    exact (canonical13615 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1721 + difference 0 3) (sourceB1721 + difference 3 0) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA1721 + difference 0 3) (sourceB1721 + difference 3 0) sourceC1721) = raw3084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw3084; decide +kernel
    rw [ha]
    exact (canonical3084 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1721 + difference 0 4) (sourceB1721 + difference 4 0) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA1721 + difference 0 4) (sourceB1721 + difference 4 0) sourceC1721) = raw13616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw13616; decide +kernel
    rw [ha]
    exact (canonical13616 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1721 + difference 0 5) (sourceB1721 + difference 5 0) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA1721 + difference 0 5) (sourceB1721 + difference 5 0) sourceC1721) = raw3074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw3074; decide +kernel
    rw [ha]
    exact (canonical3074 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1721 + difference 1 0) (sourceB1721 + difference 0 1) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 557) := by
    have ha : (tripleCharges (sourceA1721 + difference 1 0) (sourceB1721 + difference 0 1) sourceC1721) = raw25077 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw25077; decide +kernel
    rw [ha]
    exact (canonical25077 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1721 + difference 1 2) (sourceB1721 + difference 2 1) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 885) := by
    have ha : (tripleCharges (sourceA1721 + difference 1 2) (sourceB1721 + difference 2 1) sourceC1721) = raw25078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw25078; decide +kernel
    rw [ha]
    exact (canonical25078 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1721 + difference 1 3) (sourceB1721 + difference 3 1) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1721 + difference 1 3) (sourceB1721 + difference 3 1) sourceC1721) = raw21271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw21271; decide +kernel
    rw [ha]
    exact (canonical21271 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1721 + difference 1 4) (sourceB1721 + difference 4 1) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1721 + difference 1 4) (sourceB1721 + difference 4 1) sourceC1721) = raw25079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw25079; decide +kernel
    rw [ha]
    exact (canonical25079 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1721 + difference 1 5) (sourceB1721 + difference 5 1) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1721 + difference 1 5) (sourceB1721 + difference 5 1) sourceC1721) = raw13596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw13596; decide +kernel
    rw [ha]
    exact (canonical13596 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1721 + difference 2 0) (sourceB1721 + difference 0 2) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 541) := by
    have ha : (tripleCharges (sourceA1721 + difference 2 0) (sourceB1721 + difference 0 2) sourceC1721) = raw25080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw25080; decide +kernel
    rw [ha]
    exact (canonical25080 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1721 + difference 2 1) (sourceB1721 + difference 1 2) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 929) := by
    have ha : (tripleCharges (sourceA1721 + difference 2 1) (sourceB1721 + difference 1 2) sourceC1721) = raw25081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw25081; decide +kernel
    rw [ha]
    exact (canonical25081 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1721 + difference 2 3) (sourceB1721 + difference 3 2) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1721 + difference 2 3) (sourceB1721 + difference 3 2) sourceC1721) = raw21276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw21276; decide +kernel
    rw [ha]
    exact (canonical21276 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1721 + difference 2 4) (sourceB1721 + difference 4 2) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1721 + difference 2 4) (sourceB1721 + difference 4 2) sourceC1721) = raw25082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw25082; decide +kernel
    rw [ha]
    exact (canonical25082 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1721 + difference 2 5) (sourceB1721 + difference 5 2) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1034) := by
    have ha : (tripleCharges (sourceA1721 + difference 2 5) (sourceB1721 + difference 5 2) sourceC1721) = raw13600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw13600; decide +kernel
    rw [ha]
    exact (canonical13600 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1721 + difference 3 0) (sourceB1721 + difference 0 3) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 543) := by
    have ha : (tripleCharges (sourceA1721 + difference 3 0) (sourceB1721 + difference 0 3) sourceC1721) = raw25083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw25083; decide +kernel
    rw [ha]
    exact (canonical25083 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1721 + difference 3 1) (sourceB1721 + difference 1 3) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 932) := by
    have ha : (tripleCharges (sourceA1721 + difference 3 1) (sourceB1721 + difference 1 3) sourceC1721) = raw25084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw25084; decide +kernel
    rw [ha]
    exact (canonical25084 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1721 + difference 3 2) (sourceB1721 + difference 2 3) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 869) := by
    have ha : (tripleCharges (sourceA1721 + difference 3 2) (sourceB1721 + difference 2 3) sourceC1721) = raw25085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw25085; decide +kernel
    rw [ha]
    exact (canonical25085 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1721 + difference 3 4) (sourceB1721 + difference 4 3) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1721 + difference 3 4) (sourceB1721 + difference 4 3) sourceC1721) = raw25086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw25086; decide +kernel
    rw [ha]
    exact (canonical25086 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1721 + difference 3 5) (sourceB1721 + difference 5 3) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1721 + difference 3 5) (sourceB1721 + difference 5 3) sourceC1721) = raw13604 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw13604; decide +kernel
    rw [ha]
    exact (canonical13604 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1721 + difference 4 0) (sourceB1721 + difference 0 4) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 543) := by
    have ha : (tripleCharges (sourceA1721 + difference 4 0) (sourceB1721 + difference 0 4) sourceC1721) = raw23066 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw23066; decide +kernel
    rw [ha]
    exact (canonical23066 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1721 + difference 4 1) (sourceB1721 + difference 1 4) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 932) := by
    have ha : (tripleCharges (sourceA1721 + difference 4 1) (sourceB1721 + difference 1 4) sourceC1721) = raw23067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw23067; decide +kernel
    rw [ha]
    exact (canonical23067 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1721 + difference 4 2) (sourceB1721 + difference 2 4) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 869) := by
    have ha : (tripleCharges (sourceA1721 + difference 4 2) (sourceB1721 + difference 2 4) sourceC1721) = raw23068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw23068; decide +kernel
    rw [ha]
    exact (canonical23068 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1721 + difference 4 3) (sourceB1721 + difference 3 4) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1721 + difference 4 3) (sourceB1721 + difference 3 4) sourceC1721) = raw21285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw21285; decide +kernel
    rw [ha]
    exact (canonical21285 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1721 + difference 4 5) (sourceB1721 + difference 5 4) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1035) := by
    have ha : (tripleCharges (sourceA1721 + difference 4 5) (sourceB1721 + difference 5 4) sourceC1721) = raw13609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw13609; decide +kernel
    rw [ha]
    exact (canonical13609 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1721 + difference 5 0) (sourceB1721 + difference 0 5) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 542) := by
    have ha : (tripleCharges (sourceA1721 + difference 5 0) (sourceB1721 + difference 0 5) sourceC1721) = raw21277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw21277; decide +kernel
    rw [ha]
    exact (canonical21277 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1721 + difference 5 1) (sourceB1721 + difference 1 5) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 930) := by
    have ha : (tripleCharges (sourceA1721 + difference 5 1) (sourceB1721 + difference 1 5) sourceC1721) = raw21278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw21278; decide +kernel
    rw [ha]
    exact (canonical21278 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1721 + difference 5 2) (sourceB1721 + difference 2 5) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 868) := by
    have ha : (tripleCharges (sourceA1721 + difference 5 2) (sourceB1721 + difference 2 5) sourceC1721) = raw21279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw21279; decide +kernel
    rw [ha]
    exact (canonical21279 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1721 + difference 5 3) (sourceB1721 + difference 3 5) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1721 + difference 5 3) (sourceB1721 + difference 3 5) sourceC1721) = raw23074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw23074; decide +kernel
    rw [ha]
    exact (canonical23074 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1721 + difference 5 4) (sourceB1721 + difference 4 5) sourceC1721) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1721 + difference 5 4) (sourceB1721 + difference 4 5) sourceC1721) = raw21280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1721 sourceB1721 sourceC1721 difference raw21280; decide +kernel
    rw [ha]
    exact (canonical21280 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1721 sourceB1721 sourceC1721
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1721, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1722 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1722 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceC1722 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1722 : Integer.Sparse Master := [(Sum.inr 4252, 1), (Sum.inr 4267, 1), (Sum.inr 4268, 2), (Sum.inr 4275, 1), (Sum.inr 4399, 1), (Sum.inr 4400, 2), (Sum.inr 4409, 1), (Sum.inr 4439, 2), (Sum.inr 4441, 1), (Sum.inr 4458, 2), (Sum.inr 4459, 2), (Sum.inr 4461, 1), (Sum.inr 4462, 2), (Sum.inr 4475, 2), (Sum.inr 4477, 1), (Sum.inr 4502, 1), (Sum.inr 4503, 2), (Sum.inr 4589, 1), (Sum.inr 4600, 1), (Sum.inr 4602, 2), (Sum.inr 4623, 1)]

theorem sourceEq1722 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1722 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1722 + difference 0 1) (sourceB1722 + difference 1 0) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1722 + difference 0 1) (sourceB1722 + difference 1 0) sourceC1722) = raw24263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw24263; decide +kernel
    rw [ha]
    exact (canonical24263 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1722 + difference 0 2) (sourceB1722 + difference 2 0) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4589) := by
    have ha : (tripleCharges (sourceA1722 + difference 0 2) (sourceB1722 + difference 2 0) sourceC1722) = raw24608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw24608; decide +kernel
    rw [ha]
    exact (canonical24608 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1722 + difference 0 3) (sourceB1722 + difference 3 0) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1722 + difference 0 3) (sourceB1722 + difference 3 0) sourceC1722) = raw24255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw24255; decide +kernel
    rw [ha]
    exact (canonical24255 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1722 + difference 0 4) (sourceB1722 + difference 4 0) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1722 + difference 0 4) (sourceB1722 + difference 4 0) sourceC1722) = raw25087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25087; decide +kernel
    rw [ha]
    exact (canonical25087 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1722 + difference 0 5) (sourceB1722 + difference 5 0) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA1722 + difference 0 5) (sourceB1722 + difference 5 0) sourceC1722) = raw25088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25088; decide +kernel
    rw [ha]
    exact (canonical25088 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1722 + difference 1 0) (sourceB1722 + difference 0 1) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4275) := by
    have ha : (tripleCharges (sourceA1722 + difference 1 0) (sourceB1722 + difference 0 1) sourceC1722) = raw25089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25089; decide +kernel
    rw [ha]
    exact (canonical25089 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1722 + difference 1 2) (sourceB1722 + difference 2 1) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4409) := by
    have ha : (tripleCharges (sourceA1722 + difference 1 2) (sourceB1722 + difference 2 1) sourceC1722) = raw25090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25090; decide +kernel
    rw [ha]
    exact (canonical25090 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1722 + difference 1 3) (sourceB1722 + difference 3 1) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA1722 + difference 1 3) (sourceB1722 + difference 3 1) sourceC1722) = raw25091 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25091; decide +kernel
    rw [ha]
    exact (canonical25091 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1722 + difference 1 4) (sourceB1722 + difference 4 1) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA1722 + difference 1 4) (sourceB1722 + difference 4 1) sourceC1722) = raw25092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25092; decide +kernel
    rw [ha]
    exact (canonical25092 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1722 + difference 1 5) (sourceB1722 + difference 5 1) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4477) := by
    have ha : (tripleCharges (sourceA1722 + difference 1 5) (sourceB1722 + difference 5 1) sourceC1722) = raw25093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25093; decide +kernel
    rw [ha]
    exact (canonical25093 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1722 + difference 2 0) (sourceB1722 + difference 0 2) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4252) := by
    have ha : (tripleCharges (sourceA1722 + difference 2 0) (sourceB1722 + difference 0 2) sourceC1722) = raw25094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25094; decide +kernel
    rw [ha]
    exact (canonical25094 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1722 + difference 2 1) (sourceB1722 + difference 1 2) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1722 + difference 2 1) (sourceB1722 + difference 1 2) sourceC1722) = raw25095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25095; decide +kernel
    rw [ha]
    exact (canonical25095 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1722 + difference 2 3) (sourceB1722 + difference 3 2) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA1722 + difference 2 3) (sourceB1722 + difference 3 2) sourceC1722) = raw25096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25096; decide +kernel
    rw [ha]
    exact (canonical25096 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1722 + difference 2 4) (sourceB1722 + difference 4 2) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA1722 + difference 2 4) (sourceB1722 + difference 4 2) sourceC1722) = raw25097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25097; decide +kernel
    rw [ha]
    exact (canonical25097 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1722 + difference 2 5) (sourceB1722 + difference 5 2) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4441) := by
    have ha : (tripleCharges (sourceA1722 + difference 2 5) (sourceB1722 + difference 5 2) sourceC1722) = raw25098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25098; decide +kernel
    rw [ha]
    exact (canonical25098 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1722 + difference 3 0) (sourceB1722 + difference 0 3) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA1722 + difference 3 0) (sourceB1722 + difference 0 3) sourceC1722) = raw25099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25099; decide +kernel
    rw [ha]
    exact (canonical25099 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1722 + difference 3 1) (sourceB1722 + difference 1 3) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1722 + difference 3 1) (sourceB1722 + difference 1 3) sourceC1722) = raw25100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25100; decide +kernel
    rw [ha]
    exact (canonical25100 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1722 + difference 3 2) (sourceB1722 + difference 2 3) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4400) := by
    have ha : (tripleCharges (sourceA1722 + difference 3 2) (sourceB1722 + difference 2 3) sourceC1722) = raw25101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25101; decide +kernel
    rw [ha]
    exact (canonical25101 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1722 + difference 3 4) (sourceB1722 + difference 4 3) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1722 + difference 3 4) (sourceB1722 + difference 4 3) sourceC1722) = raw25102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25102; decide +kernel
    rw [ha]
    exact (canonical25102 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1722 + difference 3 5) (sourceB1722 + difference 5 3) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4462) := by
    have ha : (tripleCharges (sourceA1722 + difference 3 5) (sourceB1722 + difference 5 3) sourceC1722) = raw25103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25103; decide +kernel
    rw [ha]
    exact (canonical25103 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1722 + difference 4 0) (sourceB1722 + difference 0 4) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4268) := by
    have ha : (tripleCharges (sourceA1722 + difference 4 0) (sourceB1722 + difference 0 4) sourceC1722) = raw25104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25104; decide +kernel
    rw [ha]
    exact (canonical25104 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1722 + difference 4 1) (sourceB1722 + difference 1 4) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1722 + difference 4 1) (sourceB1722 + difference 1 4) sourceC1722) = raw24413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw24413; decide +kernel
    rw [ha]
    exact (canonical24413 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1722 + difference 4 2) (sourceB1722 + difference 2 4) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4400) := by
    have ha : (tripleCharges (sourceA1722 + difference 4 2) (sourceB1722 + difference 2 4) sourceC1722) = raw25105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25105; decide +kernel
    rw [ha]
    exact (canonical25105 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1722 + difference 4 3) (sourceB1722 + difference 3 4) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA1722 + difference 4 3) (sourceB1722 + difference 3 4) sourceC1722) = raw24405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw24405; decide +kernel
    rw [ha]
    exact (canonical24405 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1722 + difference 4 5) (sourceB1722 + difference 5 4) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4462) := by
    have ha : (tripleCharges (sourceA1722 + difference 4 5) (sourceB1722 + difference 5 4) sourceC1722) = raw25106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25106; decide +kernel
    rw [ha]
    exact (canonical25106 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1722 + difference 5 0) (sourceB1722 + difference 0 5) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4267) := by
    have ha : (tripleCharges (sourceA1722 + difference 5 0) (sourceB1722 + difference 0 5) sourceC1722) = raw25107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25107; decide +kernel
    rw [ha]
    exact (canonical25107 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1722 + difference 5 1) (sourceB1722 + difference 1 5) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1722 + difference 5 1) (sourceB1722 + difference 1 5) sourceC1722) = raw24260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw24260; decide +kernel
    rw [ha]
    exact (canonical24260 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1722 + difference 5 2) (sourceB1722 + difference 2 5) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4399) := by
    have ha : (tripleCharges (sourceA1722 + difference 5 2) (sourceB1722 + difference 2 5) sourceC1722) = raw24605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw24605; decide +kernel
    rw [ha]
    exact (canonical24605 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1722 + difference 5 3) (sourceB1722 + difference 3 5) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1722 + difference 5 3) (sourceB1722 + difference 3 5) sourceC1722) = raw24252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw24252; decide +kernel
    rw [ha]
    exact (canonical24252 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1722 + difference 5 4) (sourceB1722 + difference 4 5) sourceC1722) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1722 + difference 5 4) (sourceB1722 + difference 4 5) sourceC1722) = raw25108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1722 sourceB1722 sourceC1722 difference raw25108; decide +kernel
    rw [ha]
    exact (canonical25108 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1722 sourceB1722 sourceC1722
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1722, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1723 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB1723 : Charge := ![3, -1, 0, -1, -1, 0]
def sourceC1723 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1723 : Integer.Sparse Master := [(Sum.inr 786, 1), (Sum.inr 810, 1), (Sum.inr 811, 2), (Sum.inr 827, 1), (Sum.inr 980, 1), (Sum.inr 981, 2), (Sum.inr 990, 1), (Sum.inr 1021, 2), (Sum.inr 1023, 1), (Sum.inr 1041, 2), (Sum.inr 1042, 2), (Sum.inr 1044, 1), (Sum.inr 1045, 2), (Sum.inr 1058, 2), (Sum.inr 1060, 1), (Sum.inr 1086, 1), (Sum.inr 1087, 2), (Sum.inr 1216, 1), (Sum.inr 1267, 2), (Sum.inr 1270, 1), (Sum.inr 1305, 1)]

theorem sourceEq1723 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1723 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1723 + difference 0 1) (sourceB1723 + difference 1 0) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1723 + difference 0 1) (sourceB1723 + difference 1 0) sourceC1723) = raw24634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw24634; decide +kernel
    rw [ha]
    exact (canonical24634 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1723 + difference 0 2) (sourceB1723 + difference 2 0) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA1723 + difference 0 2) (sourceB1723 + difference 2 0) sourceC1723) = raw24629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw24629; decide +kernel
    rw [ha]
    exact (canonical24629 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1723 + difference 0 3) (sourceB1723 + difference 3 0) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1267) := by
    have ha : (tripleCharges (sourceA1723 + difference 0 3) (sourceB1723 + difference 3 0) sourceC1723) = raw25109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25109; decide +kernel
    rw [ha]
    exact (canonical25109 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1723 + difference 0 4) (sourceB1723 + difference 4 0) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1267) := by
    have ha : (tripleCharges (sourceA1723 + difference 0 4) (sourceB1723 + difference 4 0) sourceC1723) = raw25110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25110; decide +kernel
    rw [ha]
    exact (canonical25110 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1723 + difference 0 5) (sourceB1723 + difference 5 0) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA1723 + difference 0 5) (sourceB1723 + difference 5 0) sourceC1723) = raw25111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25111; decide +kernel
    rw [ha]
    exact (canonical25111 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1723 + difference 1 0) (sourceB1723 + difference 0 1) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 827) := by
    have ha : (tripleCharges (sourceA1723 + difference 1 0) (sourceB1723 + difference 0 1) sourceC1723) = raw25112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25112; decide +kernel
    rw [ha]
    exact (canonical25112 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1723 + difference 1 2) (sourceB1723 + difference 2 1) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 990) := by
    have ha : (tripleCharges (sourceA1723 + difference 1 2) (sourceB1723 + difference 2 1) sourceC1723) = raw25113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25113; decide +kernel
    rw [ha]
    exact (canonical25113 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1723 + difference 1 3) (sourceB1723 + difference 3 1) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1058) := by
    have ha : (tripleCharges (sourceA1723 + difference 1 3) (sourceB1723 + difference 3 1) sourceC1723) = raw25114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25114; decide +kernel
    rw [ha]
    exact (canonical25114 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1723 + difference 1 4) (sourceB1723 + difference 4 1) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1058) := by
    have ha : (tripleCharges (sourceA1723 + difference 1 4) (sourceB1723 + difference 4 1) sourceC1723) = raw25115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25115; decide +kernel
    rw [ha]
    exact (canonical25115 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1723 + difference 1 5) (sourceB1723 + difference 5 1) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1060) := by
    have ha : (tripleCharges (sourceA1723 + difference 1 5) (sourceB1723 + difference 5 1) sourceC1723) = raw25116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25116; decide +kernel
    rw [ha]
    exact (canonical25116 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1723 + difference 2 0) (sourceB1723 + difference 0 2) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 786) := by
    have ha : (tripleCharges (sourceA1723 + difference 2 0) (sourceB1723 + difference 0 2) sourceC1723) = raw25117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25117; decide +kernel
    rw [ha]
    exact (canonical25117 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1723 + difference 2 1) (sourceB1723 + difference 1 2) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1723 + difference 2 1) (sourceB1723 + difference 1 2) sourceC1723) = raw25118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25118; decide +kernel
    rw [ha]
    exact (canonical25118 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1723 + difference 2 3) (sourceB1723 + difference 3 2) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA1723 + difference 2 3) (sourceB1723 + difference 3 2) sourceC1723) = raw25119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25119; decide +kernel
    rw [ha]
    exact (canonical25119 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1723 + difference 2 4) (sourceB1723 + difference 4 2) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA1723 + difference 2 4) (sourceB1723 + difference 4 2) sourceC1723) = raw25120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25120; decide +kernel
    rw [ha]
    exact (canonical25120 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1723 + difference 2 5) (sourceB1723 + difference 5 2) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1023) := by
    have ha : (tripleCharges (sourceA1723 + difference 2 5) (sourceB1723 + difference 5 2) sourceC1723) = raw25121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25121; decide +kernel
    rw [ha]
    exact (canonical25121 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1723 + difference 3 0) (sourceB1723 + difference 0 3) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 811) := by
    have ha : (tripleCharges (sourceA1723 + difference 3 0) (sourceB1723 + difference 0 3) sourceC1723) = raw25122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25122; decide +kernel
    rw [ha]
    exact (canonical25122 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1723 + difference 3 1) (sourceB1723 + difference 1 3) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1723 + difference 3 1) (sourceB1723 + difference 1 3) sourceC1723) = raw25123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25123; decide +kernel
    rw [ha]
    exact (canonical25123 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1723 + difference 3 2) (sourceB1723 + difference 2 3) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 981) := by
    have ha : (tripleCharges (sourceA1723 + difference 3 2) (sourceB1723 + difference 2 3) sourceC1723) = raw25124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25124; decide +kernel
    rw [ha]
    exact (canonical25124 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1723 + difference 3 4) (sourceB1723 + difference 4 3) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA1723 + difference 3 4) (sourceB1723 + difference 4 3) sourceC1723) = raw25125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25125; decide +kernel
    rw [ha]
    exact (canonical25125 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1723 + difference 3 5) (sourceB1723 + difference 5 3) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1045) := by
    have ha : (tripleCharges (sourceA1723 + difference 3 5) (sourceB1723 + difference 5 3) sourceC1723) = raw25126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25126; decide +kernel
    rw [ha]
    exact (canonical25126 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1723 + difference 4 0) (sourceB1723 + difference 0 4) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 811) := by
    have ha : (tripleCharges (sourceA1723 + difference 4 0) (sourceB1723 + difference 0 4) sourceC1723) = raw25127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25127; decide +kernel
    rw [ha]
    exact (canonical25127 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1723 + difference 4 1) (sourceB1723 + difference 1 4) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1723 + difference 4 1) (sourceB1723 + difference 1 4) sourceC1723) = raw25128 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25128; decide +kernel
    rw [ha]
    exact (canonical25128 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1723 + difference 4 2) (sourceB1723 + difference 2 4) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 981) := by
    have ha : (tripleCharges (sourceA1723 + difference 4 2) (sourceB1723 + difference 2 4) sourceC1723) = raw25129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25129; decide +kernel
    rw [ha]
    exact (canonical25129 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1723 + difference 4 3) (sourceB1723 + difference 3 4) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA1723 + difference 4 3) (sourceB1723 + difference 3 4) sourceC1723) = raw25130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25130; decide +kernel
    rw [ha]
    exact (canonical25130 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1723 + difference 4 5) (sourceB1723 + difference 5 4) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1045) := by
    have ha : (tripleCharges (sourceA1723 + difference 4 5) (sourceB1723 + difference 5 4) sourceC1723) = raw25131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25131; decide +kernel
    rw [ha]
    exact (canonical25131 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1723 + difference 5 0) (sourceB1723 + difference 0 5) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 810) := by
    have ha : (tripleCharges (sourceA1723 + difference 5 0) (sourceB1723 + difference 0 5) sourceC1723) = raw25132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25132; decide +kernel
    rw [ha]
    exact (canonical25132 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1723 + difference 5 1) (sourceB1723 + difference 1 5) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1086) := by
    have ha : (tripleCharges (sourceA1723 + difference 5 1) (sourceB1723 + difference 1 5) sourceC1723) = raw24630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw24630; decide +kernel
    rw [ha]
    exact (canonical24630 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1723 + difference 5 2) (sourceB1723 + difference 2 5) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 980) := by
    have ha : (tripleCharges (sourceA1723 + difference 5 2) (sourceB1723 + difference 2 5) sourceC1723) = raw24625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw24625; decide +kernel
    rw [ha]
    exact (canonical24625 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1723 + difference 5 3) (sourceB1723 + difference 3 5) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1723 + difference 5 3) (sourceB1723 + difference 3 5) sourceC1723) = raw25133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25133; decide +kernel
    rw [ha]
    exact (canonical25133 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1723 + difference 5 4) (sourceB1723 + difference 4 5) sourceC1723) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1723 + difference 5 4) (sourceB1723 + difference 4 5) sourceC1723) = raw25134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1723 sourceB1723 sourceC1723 difference raw25134; decide +kernel
    rw [ha]
    exact (canonical25134 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1723 sourceB1723 sourceC1723
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1723, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1724 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1724 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1724 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceForm1724 : Integer.Sparse Master := [(Sum.inr 4150, 1), (Sum.inr 4153, 1), (Sum.inr 4155, 1), (Sum.inr 4158, 1), (Sum.inr 4175, 1), (Sum.inr 4327, 1), (Sum.inr 4329, 1), (Sum.inr 4332, 1), (Sum.inr 4344, 1), (Sum.inr 4364, 1), (Sum.inr 4367, 1), (Sum.inr 4369, 1), (Sum.inr 4372, 1), (Sum.inr 4438, 1), (Sum.inr 4440, 1), (Sum.inr 4444, 1), (Sum.inr 4456, 1), (Sum.inr 4458, 3), (Sum.inr 4461, 1), (Sum.inr 4463, 1), (Sum.inr 4467, 1), (Sum.inr 4497, 1), (Sum.inr 4502, 1), (Sum.inr 4802, 1), (Sum.inr 4866, 1), (Sum.inr 4888, 1), (Sum.inr 4893, 1), (Sum.inr 4895, 1)]

theorem sourceEq1724 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1724 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1724 + difference 0 1) (sourceB1724 + difference 1 0) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA1724 + difference 0 1) (sourceB1724 + difference 1 0) sourceC1724) = raw25135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25135; decide +kernel
    rw [ha]
    exact (canonical25135 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1724 + difference 0 2) (sourceB1724 + difference 2 0) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4802) := by
    have ha : (tripleCharges (sourceA1724 + difference 0 2) (sourceB1724 + difference 2 0) sourceC1724) = raw25136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25136; decide +kernel
    rw [ha]
    exact (canonical25136 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1724 + difference 0 3) (sourceB1724 + difference 3 0) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA1724 + difference 0 3) (sourceB1724 + difference 3 0) sourceC1724) = raw25137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25137; decide +kernel
    rw [ha]
    exact (canonical25137 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1724 + difference 0 4) (sourceB1724 + difference 4 0) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4895) := by
    have ha : (tripleCharges (sourceA1724 + difference 0 4) (sourceB1724 + difference 4 0) sourceC1724) = raw25138 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25138; decide +kernel
    rw [ha]
    exact (canonical25138 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1724 + difference 0 5) (sourceB1724 + difference 5 0) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA1724 + difference 0 5) (sourceB1724 + difference 5 0) sourceC1724) = raw25139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25139; decide +kernel
    rw [ha]
    exact (canonical25139 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1724 + difference 1 0) (sourceB1724 + difference 0 1) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4175) := by
    have ha : (tripleCharges (sourceA1724 + difference 1 0) (sourceB1724 + difference 0 1) sourceC1724) = raw25140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25140; decide +kernel
    rw [ha]
    exact (canonical25140 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1724 + difference 1 2) (sourceB1724 + difference 2 1) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4344) := by
    have ha : (tripleCharges (sourceA1724 + difference 1 2) (sourceB1724 + difference 2 1) sourceC1724) = raw25141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25141; decide +kernel
    rw [ha]
    exact (canonical25141 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1724 + difference 1 3) (sourceB1724 + difference 3 1) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1724 + difference 1 3) (sourceB1724 + difference 3 1) sourceC1724) = raw25142 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25142; decide +kernel
    rw [ha]
    exact (canonical25142 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1724 + difference 1 4) (sourceB1724 + difference 4 1) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4502) := by
    have ha : (tripleCharges (sourceA1724 + difference 1 4) (sourceB1724 + difference 4 1) sourceC1724) = raw25143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25143; decide +kernel
    rw [ha]
    exact (canonical25143 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1724 + difference 1 5) (sourceB1724 + difference 5 1) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1724 + difference 1 5) (sourceB1724 + difference 5 1) sourceC1724) = raw25144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25144; decide +kernel
    rw [ha]
    exact (canonical25144 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1724 + difference 2 0) (sourceB1724 + difference 0 2) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4150) := by
    have ha : (tripleCharges (sourceA1724 + difference 2 0) (sourceB1724 + difference 0 2) sourceC1724) = raw25145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25145; decide +kernel
    rw [ha]
    exact (canonical25145 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1724 + difference 2 1) (sourceB1724 + difference 1 2) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4364) := by
    have ha : (tripleCharges (sourceA1724 + difference 2 1) (sourceB1724 + difference 1 2) sourceC1724) = raw25146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25146; decide +kernel
    rw [ha]
    exact (canonical25146 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1724 + difference 2 3) (sourceB1724 + difference 3 2) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4438) := by
    have ha : (tripleCharges (sourceA1724 + difference 2 3) (sourceB1724 + difference 3 2) sourceC1724) = raw25147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25147; decide +kernel
    rw [ha]
    exact (canonical25147 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1724 + difference 2 4) (sourceB1724 + difference 4 2) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1724 + difference 2 4) (sourceB1724 + difference 4 2) sourceC1724) = raw25148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25148; decide +kernel
    rw [ha]
    exact (canonical25148 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1724 + difference 2 5) (sourceB1724 + difference 5 2) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1724 + difference 2 5) (sourceB1724 + difference 5 2) sourceC1724) = raw25149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25149; decide +kernel
    rw [ha]
    exact (canonical25149 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1724 + difference 3 0) (sourceB1724 + difference 0 3) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4155) := by
    have ha : (tripleCharges (sourceA1724 + difference 3 0) (sourceB1724 + difference 0 3) sourceC1724) = raw25150 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25150; decide +kernel
    rw [ha]
    exact (canonical25150 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1724 + difference 3 1) (sourceB1724 + difference 1 3) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4369) := by
    have ha : (tripleCharges (sourceA1724 + difference 3 1) (sourceB1724 + difference 1 3) sourceC1724) = raw25151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25151; decide +kernel
    rw [ha]
    exact (canonical25151 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1724 + difference 3 2) (sourceB1724 + difference 2 3) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4329) := by
    have ha : (tripleCharges (sourceA1724 + difference 3 2) (sourceB1724 + difference 2 3) sourceC1724) = raw25152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25152; decide +kernel
    rw [ha]
    exact (canonical25152 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1724 + difference 3 4) (sourceB1724 + difference 4 3) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1724 + difference 3 4) (sourceB1724 + difference 4 3) sourceC1724) = raw25153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25153; decide +kernel
    rw [ha]
    exact (canonical25153 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1724 + difference 3 5) (sourceB1724 + difference 5 3) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA1724 + difference 3 5) (sourceB1724 + difference 5 3) sourceC1724) = raw25154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25154; decide +kernel
    rw [ha]
    exact (canonical25154 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1724 + difference 4 0) (sourceB1724 + difference 0 4) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4158) := by
    have ha : (tripleCharges (sourceA1724 + difference 4 0) (sourceB1724 + difference 0 4) sourceC1724) = raw25155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25155; decide +kernel
    rw [ha]
    exact (canonical25155 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1724 + difference 4 1) (sourceB1724 + difference 1 4) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4372) := by
    have ha : (tripleCharges (sourceA1724 + difference 4 1) (sourceB1724 + difference 1 4) sourceC1724) = raw25156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25156; decide +kernel
    rw [ha]
    exact (canonical25156 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1724 + difference 4 2) (sourceB1724 + difference 2 4) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4332) := by
    have ha : (tripleCharges (sourceA1724 + difference 4 2) (sourceB1724 + difference 2 4) sourceC1724) = raw25157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25157; decide +kernel
    rw [ha]
    exact (canonical25157 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1724 + difference 4 3) (sourceB1724 + difference 3 4) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA1724 + difference 4 3) (sourceB1724 + difference 3 4) sourceC1724) = raw25158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25158; decide +kernel
    rw [ha]
    exact (canonical25158 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1724 + difference 4 5) (sourceB1724 + difference 5 4) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA1724 + difference 4 5) (sourceB1724 + difference 5 4) sourceC1724) = raw25159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25159; decide +kernel
    rw [ha]
    exact (canonical25159 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1724 + difference 5 0) (sourceB1724 + difference 0 5) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4153) := by
    have ha : (tripleCharges (sourceA1724 + difference 5 0) (sourceB1724 + difference 0 5) sourceC1724) = raw25160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25160; decide +kernel
    rw [ha]
    exact (canonical25160 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1724 + difference 5 1) (sourceB1724 + difference 1 5) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4367) := by
    have ha : (tripleCharges (sourceA1724 + difference 5 1) (sourceB1724 + difference 1 5) sourceC1724) = raw25161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25161; decide +kernel
    rw [ha]
    exact (canonical25161 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1724 + difference 5 2) (sourceB1724 + difference 2 5) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4327) := by
    have ha : (tripleCharges (sourceA1724 + difference 5 2) (sourceB1724 + difference 2 5) sourceC1724) = raw25162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25162; decide +kernel
    rw [ha]
    exact (canonical25162 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1724 + difference 5 3) (sourceB1724 + difference 3 5) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4440) := by
    have ha : (tripleCharges (sourceA1724 + difference 5 3) (sourceB1724 + difference 3 5) sourceC1724) = raw25163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25163; decide +kernel
    rw [ha]
    exact (canonical25163 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1724 + difference 5 4) (sourceB1724 + difference 4 5) sourceC1724) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1724 + difference 5 4) (sourceB1724 + difference 4 5) sourceC1724) = raw25164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1724 sourceB1724 sourceC1724 difference raw25164; decide +kernel
    rw [ha]
    exact (canonical25164 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1724 sourceB1724 sourceC1724
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1724, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1725 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1725 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1725 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceForm1725 : Integer.Sparse Master := [(Sum.inr 625, 1), (Sum.inr 626, 1), (Sum.inr 627, 1), (Sum.inr 632, 1), (Sum.inr 644, 1), (Sum.inr 1316, 1), (Sum.inr 1317, 1), (Sum.inr 1318, 1), (Sum.inr 1322, 1), (Sum.inr 1327, 1), (Sum.inr 1328, 1), (Sum.inr 1331, 1), (Sum.inr 1339, 1), (Sum.inr 1386, 1), (Sum.inr 1388, 1), (Sum.inr 1391, 1), (Sum.inr 1409, 1), (Sum.inr 1410, 1), (Sum.inr 1411, 3), (Sum.inr 1413, 1), (Sum.inr 1420, 1), (Sum.inr 1446, 1), (Sum.inr 1447, 1), (Sum.inr 3184, 1), (Sum.inr 3204, 1), (Sum.inr 3227, 1), (Sum.inr 3228, 1), (Sum.inr 3229, 1)]

theorem sourceEq1725 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1725 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1725 + difference 0 1) (sourceB1725 + difference 1 0) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3184) := by
    have ha : (tripleCharges (sourceA1725 + difference 0 1) (sourceB1725 + difference 1 0) sourceC1725) = raw25165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25165; decide +kernel
    rw [ha]
    exact (canonical25165 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1725 + difference 0 2) (sourceB1725 + difference 2 0) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3204) := by
    have ha : (tripleCharges (sourceA1725 + difference 0 2) (sourceB1725 + difference 2 0) sourceC1725) = raw25166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25166; decide +kernel
    rw [ha]
    exact (canonical25166 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1725 + difference 0 3) (sourceB1725 + difference 3 0) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA1725 + difference 0 3) (sourceB1725 + difference 3 0) sourceC1725) = raw25167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25167; decide +kernel
    rw [ha]
    exact (canonical25167 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1725 + difference 0 4) (sourceB1725 + difference 4 0) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3229) := by
    have ha : (tripleCharges (sourceA1725 + difference 0 4) (sourceB1725 + difference 4 0) sourceC1725) = raw25168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25168; decide +kernel
    rw [ha]
    exact (canonical25168 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1725 + difference 0 5) (sourceB1725 + difference 5 0) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3228) := by
    have ha : (tripleCharges (sourceA1725 + difference 0 5) (sourceB1725 + difference 5 0) sourceC1725) = raw25169 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25169; decide +kernel
    rw [ha]
    exact (canonical25169 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1725 + difference 1 0) (sourceB1725 + difference 0 1) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 644) := by
    have ha : (tripleCharges (sourceA1725 + difference 1 0) (sourceB1725 + difference 0 1) sourceC1725) = raw25170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25170; decide +kernel
    rw [ha]
    exact (canonical25170 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1725 + difference 1 2) (sourceB1725 + difference 2 1) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1339) := by
    have ha : (tripleCharges (sourceA1725 + difference 1 2) (sourceB1725 + difference 2 1) sourceC1725) = raw25171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25171; decide +kernel
    rw [ha]
    exact (canonical25171 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1725 + difference 1 3) (sourceB1725 + difference 3 1) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1411) := by
    have ha : (tripleCharges (sourceA1725 + difference 1 3) (sourceB1725 + difference 3 1) sourceC1725) = raw25172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25172; decide +kernel
    rw [ha]
    exact (canonical25172 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1725 + difference 1 4) (sourceB1725 + difference 4 1) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1447) := by
    have ha : (tripleCharges (sourceA1725 + difference 1 4) (sourceB1725 + difference 4 1) sourceC1725) = raw25173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25173; decide +kernel
    rw [ha]
    exact (canonical25173 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1725 + difference 1 5) (sourceB1725 + difference 5 1) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1446) := by
    have ha : (tripleCharges (sourceA1725 + difference 1 5) (sourceB1725 + difference 5 1) sourceC1725) = raw25174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25174; decide +kernel
    rw [ha]
    exact (canonical25174 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1725 + difference 2 0) (sourceB1725 + difference 0 2) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 625) := by
    have ha : (tripleCharges (sourceA1725 + difference 2 0) (sourceB1725 + difference 0 2) sourceC1725) = raw25175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25175; decide +kernel
    rw [ha]
    exact (canonical25175 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1725 + difference 2 1) (sourceB1725 + difference 1 2) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1316) := by
    have ha : (tripleCharges (sourceA1725 + difference 2 1) (sourceB1725 + difference 1 2) sourceC1725) = raw25176 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25176; decide +kernel
    rw [ha]
    exact (canonical25176 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1725 + difference 2 3) (sourceB1725 + difference 3 2) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1386) := by
    have ha : (tripleCharges (sourceA1725 + difference 2 3) (sourceB1725 + difference 3 2) sourceC1725) = raw25177 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25177; decide +kernel
    rw [ha]
    exact (canonical25177 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1725 + difference 2 4) (sourceB1725 + difference 4 2) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1411) := by
    have ha : (tripleCharges (sourceA1725 + difference 2 4) (sourceB1725 + difference 4 2) sourceC1725) = raw25178 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25178; decide +kernel
    rw [ha]
    exact (canonical25178 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1725 + difference 2 5) (sourceB1725 + difference 5 2) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1409) := by
    have ha : (tripleCharges (sourceA1725 + difference 2 5) (sourceB1725 + difference 5 2) sourceC1725) = raw25179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25179; decide +kernel
    rw [ha]
    exact (canonical25179 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1725 + difference 3 0) (sourceB1725 + difference 0 3) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 632) := by
    have ha : (tripleCharges (sourceA1725 + difference 3 0) (sourceB1725 + difference 0 3) sourceC1725) = raw25180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25180; decide +kernel
    rw [ha]
    exact (canonical25180 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1725 + difference 3 1) (sourceB1725 + difference 1 3) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1322) := by
    have ha : (tripleCharges (sourceA1725 + difference 3 1) (sourceB1725 + difference 1 3) sourceC1725) = raw25181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25181; decide +kernel
    rw [ha]
    exact (canonical25181 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1725 + difference 3 2) (sourceB1725 + difference 2 3) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1331) := by
    have ha : (tripleCharges (sourceA1725 + difference 3 2) (sourceB1725 + difference 2 3) sourceC1725) = raw25182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25182; decide +kernel
    rw [ha]
    exact (canonical25182 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1725 + difference 3 4) (sourceB1725 + difference 4 3) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1420) := by
    have ha : (tripleCharges (sourceA1725 + difference 3 4) (sourceB1725 + difference 4 3) sourceC1725) = raw25183 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25183; decide +kernel
    rw [ha]
    exact (canonical25183 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1725 + difference 3 5) (sourceB1725 + difference 5 3) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1411) := by
    have ha : (tripleCharges (sourceA1725 + difference 3 5) (sourceB1725 + difference 5 3) sourceC1725) = raw25184 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25184; decide +kernel
    rw [ha]
    exact (canonical25184 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1725 + difference 4 0) (sourceB1725 + difference 0 4) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 627) := by
    have ha : (tripleCharges (sourceA1725 + difference 4 0) (sourceB1725 + difference 0 4) sourceC1725) = raw25185 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25185; decide +kernel
    rw [ha]
    exact (canonical25185 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1725 + difference 4 1) (sourceB1725 + difference 1 4) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1318) := by
    have ha : (tripleCharges (sourceA1725 + difference 4 1) (sourceB1725 + difference 1 4) sourceC1725) = raw25186 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25186; decide +kernel
    rw [ha]
    exact (canonical25186 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1725 + difference 4 2) (sourceB1725 + difference 2 4) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1328) := by
    have ha : (tripleCharges (sourceA1725 + difference 4 2) (sourceB1725 + difference 2 4) sourceC1725) = raw25187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25187; decide +kernel
    rw [ha]
    exact (canonical25187 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1725 + difference 4 3) (sourceB1725 + difference 3 4) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1391) := by
    have ha : (tripleCharges (sourceA1725 + difference 4 3) (sourceB1725 + difference 3 4) sourceC1725) = raw25188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25188; decide +kernel
    rw [ha]
    exact (canonical25188 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1725 + difference 4 5) (sourceB1725 + difference 5 4) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1410) := by
    have ha : (tripleCharges (sourceA1725 + difference 4 5) (sourceB1725 + difference 5 4) sourceC1725) = raw25189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25189; decide +kernel
    rw [ha]
    exact (canonical25189 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1725 + difference 5 0) (sourceB1725 + difference 0 5) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 626) := by
    have ha : (tripleCharges (sourceA1725 + difference 5 0) (sourceB1725 + difference 0 5) sourceC1725) = raw25190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25190; decide +kernel
    rw [ha]
    exact (canonical25190 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1725 + difference 5 1) (sourceB1725 + difference 1 5) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1317) := by
    have ha : (tripleCharges (sourceA1725 + difference 5 1) (sourceB1725 + difference 1 5) sourceC1725) = raw25191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25191; decide +kernel
    rw [ha]
    exact (canonical25191 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1725 + difference 5 2) (sourceB1725 + difference 2 5) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1327) := by
    have ha : (tripleCharges (sourceA1725 + difference 5 2) (sourceB1725 + difference 2 5) sourceC1725) = raw25192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25192; decide +kernel
    rw [ha]
    exact (canonical25192 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1725 + difference 5 3) (sourceB1725 + difference 3 5) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA1725 + difference 5 3) (sourceB1725 + difference 3 5) sourceC1725) = raw25193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25193; decide +kernel
    rw [ha]
    exact (canonical25193 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1725 + difference 5 4) (sourceB1725 + difference 4 5) sourceC1725) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1413) := by
    have ha : (tripleCharges (sourceA1725 + difference 5 4) (sourceB1725 + difference 4 5) sourceC1725) = raw25194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1725 sourceB1725 sourceC1725 difference raw25194; decide +kernel
    rw [ha]
    exact (canonical25194 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1725 sourceB1725 sourceC1725
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1725, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1726 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1726 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1726 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceForm1726 : Integer.Sparse Master := [(Sum.inr 1504, 1), (Sum.inr 1514, 1), (Sum.inr 1515, 1), (Sum.inr 1517, 1), (Sum.inr 1522, 1), (Sum.inr 1670, 1), (Sum.inr 1671, 1), (Sum.inr 1673, 1), (Sum.inr 1678, 1), (Sum.inr 1703, 1), (Sum.inr 1705, 1), (Sum.inr 1706, 1), (Sum.inr 1720, 1), (Sum.inr 1721, 1), (Sum.inr 1723, 1), (Sum.inr 1724, 3), (Sum.inr 1726, 1), (Sum.inr 1734, 1), (Sum.inr 1736, 1), (Sum.inr 1737, 1), (Sum.inr 1750, 1), (Sum.inr 1751, 1), (Sum.inr 1753, 1), (Sum.inr 2202, 1), (Sum.inr 2260, 1), (Sum.inr 2262, 1), (Sum.inr 2263, 1), (Sum.inr 2291, 1)]

theorem sourceEq1726 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1726 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1726 + difference 0 1) (sourceB1726 + difference 1 0) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA1726 + difference 0 1) (sourceB1726 + difference 1 0) sourceC1726) = raw25195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25195; decide +kernel
    rw [ha]
    exact (canonical25195 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1726 + difference 0 2) (sourceB1726 + difference 2 0) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2202) := by
    have ha : (tripleCharges (sourceA1726 + difference 0 2) (sourceB1726 + difference 2 0) sourceC1726) = raw25196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25196; decide +kernel
    rw [ha]
    exact (canonical25196 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1726 + difference 0 3) (sourceB1726 + difference 3 0) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA1726 + difference 0 3) (sourceB1726 + difference 3 0) sourceC1726) = raw25197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25197; decide +kernel
    rw [ha]
    exact (canonical25197 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1726 + difference 0 4) (sourceB1726 + difference 4 0) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2291) := by
    have ha : (tripleCharges (sourceA1726 + difference 0 4) (sourceB1726 + difference 4 0) sourceC1726) = raw25198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25198; decide +kernel
    rw [ha]
    exact (canonical25198 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1726 + difference 0 5) (sourceB1726 + difference 5 0) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2263) := by
    have ha : (tripleCharges (sourceA1726 + difference 0 5) (sourceB1726 + difference 5 0) sourceC1726) = raw25199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25199; decide +kernel
    rw [ha]
    exact (canonical25199 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1726 + difference 1 0) (sourceB1726 + difference 0 1) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1517) := by
    have ha : (tripleCharges (sourceA1726 + difference 1 0) (sourceB1726 + difference 0 1) sourceC1726) = raw25200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25200; decide +kernel
    rw [ha]
    exact (canonical25200 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1726 + difference 1 2) (sourceB1726 + difference 2 1) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1673) := by
    have ha : (tripleCharges (sourceA1726 + difference 1 2) (sourceB1726 + difference 2 1) sourceC1726) = raw25201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25201; decide +kernel
    rw [ha]
    exact (canonical25201 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1726 + difference 1 3) (sourceB1726 + difference 3 1) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1726 + difference 1 3) (sourceB1726 + difference 3 1) sourceC1726) = raw25202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25202; decide +kernel
    rw [ha]
    exact (canonical25202 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1726 + difference 1 4) (sourceB1726 + difference 4 1) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1753) := by
    have ha : (tripleCharges (sourceA1726 + difference 1 4) (sourceB1726 + difference 4 1) sourceC1726) = raw25203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25203; decide +kernel
    rw [ha]
    exact (canonical25203 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1726 + difference 1 5) (sourceB1726 + difference 5 1) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1726) := by
    have ha : (tripleCharges (sourceA1726 + difference 1 5) (sourceB1726 + difference 5 1) sourceC1726) = raw25204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25204; decide +kernel
    rw [ha]
    exact (canonical25204 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1726 + difference 2 0) (sourceB1726 + difference 0 2) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1504) := by
    have ha : (tripleCharges (sourceA1726 + difference 2 0) (sourceB1726 + difference 0 2) sourceC1726) = raw25205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25205; decide +kernel
    rw [ha]
    exact (canonical25205 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1726 + difference 2 1) (sourceB1726 + difference 1 2) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1703) := by
    have ha : (tripleCharges (sourceA1726 + difference 2 1) (sourceB1726 + difference 1 2) sourceC1726) = raw25206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25206; decide +kernel
    rw [ha]
    exact (canonical25206 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1726 + difference 2 3) (sourceB1726 + difference 3 2) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA1726 + difference 2 3) (sourceB1726 + difference 3 2) sourceC1726) = raw25207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25207; decide +kernel
    rw [ha]
    exact (canonical25207 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1726 + difference 2 4) (sourceB1726 + difference 4 2) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1726 + difference 2 4) (sourceB1726 + difference 4 2) sourceC1726) = raw25208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25208; decide +kernel
    rw [ha]
    exact (canonical25208 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1726 + difference 2 5) (sourceB1726 + difference 5 2) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1726 + difference 2 5) (sourceB1726 + difference 5 2) sourceC1726) = raw25209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25209; decide +kernel
    rw [ha]
    exact (canonical25209 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1726 + difference 3 0) (sourceB1726 + difference 0 3) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1515) := by
    have ha : (tripleCharges (sourceA1726 + difference 3 0) (sourceB1726 + difference 0 3) sourceC1726) = raw25210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25210; decide +kernel
    rw [ha]
    exact (canonical25210 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1726 + difference 3 1) (sourceB1726 + difference 1 3) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1721) := by
    have ha : (tripleCharges (sourceA1726 + difference 3 1) (sourceB1726 + difference 1 3) sourceC1726) = raw25211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25211; decide +kernel
    rw [ha]
    exact (canonical25211 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1726 + difference 3 2) (sourceB1726 + difference 2 3) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1671) := by
    have ha : (tripleCharges (sourceA1726 + difference 3 2) (sourceB1726 + difference 2 3) sourceC1726) = raw25212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25212; decide +kernel
    rw [ha]
    exact (canonical25212 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1726 + difference 3 4) (sourceB1726 + difference 4 3) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1726 + difference 3 4) (sourceB1726 + difference 4 3) sourceC1726) = raw25213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25213; decide +kernel
    rw [ha]
    exact (canonical25213 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1726 + difference 3 5) (sourceB1726 + difference 5 3) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1726 + difference 3 5) (sourceB1726 + difference 5 3) sourceC1726) = raw25214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25214; decide +kernel
    rw [ha]
    exact (canonical25214 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1726 + difference 4 0) (sourceB1726 + difference 0 4) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1522) := by
    have ha : (tripleCharges (sourceA1726 + difference 4 0) (sourceB1726 + difference 0 4) sourceC1726) = raw25215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25215; decide +kernel
    rw [ha]
    exact (canonical25215 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1726 + difference 4 1) (sourceB1726 + difference 1 4) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1734) := by
    have ha : (tripleCharges (sourceA1726 + difference 4 1) (sourceB1726 + difference 1 4) sourceC1726) = raw25216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25216; decide +kernel
    rw [ha]
    exact (canonical25216 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1726 + difference 4 2) (sourceB1726 + difference 2 4) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1678) := by
    have ha : (tripleCharges (sourceA1726 + difference 4 2) (sourceB1726 + difference 2 4) sourceC1726) = raw25217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25217; decide +kernel
    rw [ha]
    exact (canonical25217 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1726 + difference 4 3) (sourceB1726 + difference 3 4) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1726 + difference 4 3) (sourceB1726 + difference 3 4) sourceC1726) = raw25218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25218; decide +kernel
    rw [ha]
    exact (canonical25218 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1726 + difference 4 5) (sourceB1726 + difference 5 4) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1726 + difference 4 5) (sourceB1726 + difference 5 4) sourceC1726) = raw25219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25219; decide +kernel
    rw [ha]
    exact (canonical25219 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1726 + difference 5 0) (sourceB1726 + difference 0 5) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1514) := by
    have ha : (tripleCharges (sourceA1726 + difference 5 0) (sourceB1726 + difference 0 5) sourceC1726) = raw25220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25220; decide +kernel
    rw [ha]
    exact (canonical25220 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1726 + difference 5 1) (sourceB1726 + difference 1 5) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1720) := by
    have ha : (tripleCharges (sourceA1726 + difference 5 1) (sourceB1726 + difference 1 5) sourceC1726) = raw25221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25221; decide +kernel
    rw [ha]
    exact (canonical25221 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1726 + difference 5 2) (sourceB1726 + difference 2 5) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1670) := by
    have ha : (tripleCharges (sourceA1726 + difference 5 2) (sourceB1726 + difference 2 5) sourceC1726) = raw25222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25222; decide +kernel
    rw [ha]
    exact (canonical25222 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1726 + difference 5 3) (sourceB1726 + difference 3 5) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1726 + difference 5 3) (sourceB1726 + difference 3 5) sourceC1726) = raw25223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25223; decide +kernel
    rw [ha]
    exact (canonical25223 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1726 + difference 5 4) (sourceB1726 + difference 4 5) sourceC1726) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1726 + difference 5 4) (sourceB1726 + difference 4 5) sourceC1726) = raw25224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1726 sourceB1726 sourceC1726 difference raw25224; decide +kernel
    rw [ha]
    exact (canonical25224 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1726 sourceB1726 sourceC1726
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1726, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1727 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1727 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceC1727 : Charge := ![3, -1, 0, -1, 0, -1]
def sourceForm1727 : Integer.Sparse Master := [(Sum.inr 578, 1), (Sum.inr 581, 1), (Sum.inr 583, 1), (Sum.inr 586, 1), (Sum.inr 603, 1), (Sum.inr 1041, 1), (Sum.inr 4083, -1)]

theorem sourceEq1727 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1727 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1727 + difference 0 0) (sourceB1727 + difference 0 0) sourceC1727) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1727 + difference 0 0) (sourceB1727 + difference 0 0) sourceC1727) = raw25225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1727 sourceB1727 sourceC1727 difference raw25225; decide +kernel
    rw [ha]
    exact (canonical25225 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1727 + difference 1 0) (sourceB1727 + difference 0 1) sourceC1727) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 603) := by
    have ha : (tripleCharges (sourceA1727 + difference 1 0) (sourceB1727 + difference 0 1) sourceC1727) = raw25226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1727 sourceB1727 sourceC1727 difference raw25226; decide +kernel
    rw [ha]
    exact (canonical25226 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1727 + difference 2 0) (sourceB1727 + difference 0 2) sourceC1727) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 578) := by
    have ha : (tripleCharges (sourceA1727 + difference 2 0) (sourceB1727 + difference 0 2) sourceC1727) = raw25227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1727 sourceB1727 sourceC1727 difference raw25227; decide +kernel
    rw [ha]
    exact (canonical25227 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1727 + difference 3 0) (sourceB1727 + difference 0 3) sourceC1727) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 583) := by
    have ha : (tripleCharges (sourceA1727 + difference 3 0) (sourceB1727 + difference 0 3) sourceC1727) = raw25228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1727 sourceB1727 sourceC1727 difference raw25228; decide +kernel
    rw [ha]
    exact (canonical25228 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1727 + difference 4 0) (sourceB1727 + difference 0 4) sourceC1727) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 586) := by
    have ha : (tripleCharges (sourceA1727 + difference 4 0) (sourceB1727 + difference 0 4) sourceC1727) = raw25229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1727 sourceB1727 sourceC1727 difference raw25229; decide +kernel
    rw [ha]
    exact (canonical25229 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1727 + difference 5 0) (sourceB1727 + difference 0 5) sourceC1727) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 581) := by
    have ha : (tripleCharges (sourceA1727 + difference 5 0) (sourceB1727 + difference 0 5) sourceC1727) = raw25230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1727 sourceB1727 sourceC1727 difference raw25230; decide +kernel
    rw [ha]
    exact (canonical25230 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1727 + sourceB1727) sourceC1727) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1727 + sourceB1727) sourceC1727) = raw25231 := by
      apply Matrix.ext; unfold doubleCharges sourceA1727 sourceB1727 sourceC1727 raw25231; decide +kernel
    rw [ha]
    exact (canonical25231 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1727 sourceB1727 sourceC1727
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1727, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
