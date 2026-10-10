import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical86
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical91
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical105
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical107
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical128
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical158
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical174
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical185
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical186
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical187

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1600 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1600 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceC1600 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceForm1600 : Integer.Sparse Master := [(Sum.inr 580, 1), (Sum.inr 944, 1), (Sum.inr 1021, 2), (Sum.inr 1039, 1), (Sum.inr 1044, 1), (Sum.inr 4083, -1)]

theorem sourceEq1600 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1600 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1600 + difference 1 0) (sourceB1600 + difference 0 1) sourceC1600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 580) := by
    have ha : (tripleCharges (sourceA1600 + difference 1 0) (sourceB1600 + difference 0 1) sourceC1600) = raw23900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1600 sourceB1600 sourceC1600 difference raw23900; decide +kernel
    rw [ha]
    exact (canonical23900 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1600 + difference 1 1) (sourceB1600 + difference 1 1) sourceC1600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA1600 + difference 1 1) (sourceB1600 + difference 1 1) sourceC1600) = raw23901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1600 sourceB1600 sourceC1600 difference raw23901; decide +kernel
    rw [ha]
    exact (canonical23901 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1600 + difference 1 2) (sourceB1600 + difference 2 1) sourceC1600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 944) := by
    have ha : (tripleCharges (sourceA1600 + difference 1 2) (sourceB1600 + difference 2 1) sourceC1600) = raw23902 := by
      apply Matrix.ext; unfold tripleCharges sourceA1600 sourceB1600 sourceC1600 difference raw23902; decide +kernel
    rw [ha]
    exact (canonical23902 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1600 + difference 1 3) (sourceB1600 + difference 3 1) sourceC1600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1600 + difference 1 3) (sourceB1600 + difference 3 1) sourceC1600) = raw11087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1600 sourceB1600 sourceC1600 difference raw11087; decide +kernel
    rw [ha]
    exact (canonical11087 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1600 + difference 1 4) (sourceB1600 + difference 4 1) sourceC1600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA1600 + difference 1 4) (sourceB1600 + difference 4 1) sourceC1600) = raw23903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1600 sourceB1600 sourceC1600 difference raw23903; decide +kernel
    rw [ha]
    exact (canonical23903 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1600 + difference 1 5) (sourceB1600 + difference 5 1) sourceC1600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1039) := by
    have ha : (tripleCharges (sourceA1600 + difference 1 5) (sourceB1600 + difference 5 1) sourceC1600) = raw23904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1600 sourceB1600 sourceC1600 difference raw23904; decide +kernel
    rw [ha]
    exact (canonical23904 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1600 + sourceB1600) sourceC1600) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1600 + sourceB1600) sourceC1600) = raw11086 := by
      apply Matrix.ext; unfold doubleCharges sourceA1600 sourceB1600 sourceC1600 raw11086; decide +kernel
    rw [ha]
    exact (canonical11086 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1600 sourceB1600 sourceC1600
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1600, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1601 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1601 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC1601 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceForm1601 : Integer.Sparse Master := [(Sum.inr 1327, 1), (Sum.inr 1328, 1), (Sum.inr 1330, 1), (Sum.inr 1335, 1), (Sum.inr 1383, 1), (Sum.inr 2924, 1), (Sum.inr 4091, -1)]

theorem sourceEq1601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1601 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1601 + difference 0 1) (sourceB1601 + difference 1 0) sourceC1601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA1601 + difference 0 1) (sourceB1601 + difference 1 0) sourceC1601) = raw23905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1601 sourceB1601 sourceC1601 difference raw23905; decide +kernel
    rw [ha]
    exact (canonical23905 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1601 + difference 1 1) (sourceB1601 + difference 1 1) sourceC1601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1383) := by
    have ha : (tripleCharges (sourceA1601 + difference 1 1) (sourceB1601 + difference 1 1) sourceC1601) = raw23906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1601 sourceB1601 sourceC1601 difference raw23906; decide +kernel
    rw [ha]
    exact (canonical23906 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1601 + difference 2 1) (sourceB1601 + difference 1 2) sourceC1601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1335) := by
    have ha : (tripleCharges (sourceA1601 + difference 2 1) (sourceB1601 + difference 1 2) sourceC1601) = raw23907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1601 sourceB1601 sourceC1601 difference raw23907; decide +kernel
    rw [ha]
    exact (canonical23907 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1601 + difference 3 1) (sourceB1601 + difference 1 3) sourceC1601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1328) := by
    have ha : (tripleCharges (sourceA1601 + difference 3 1) (sourceB1601 + difference 1 3) sourceC1601) = raw23908 := by
      apply Matrix.ext; unfold tripleCharges sourceA1601 sourceB1601 sourceC1601 difference raw23908; decide +kernel
    rw [ha]
    exact (canonical23908 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1601 + difference 4 1) (sourceB1601 + difference 1 4) sourceC1601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1330) := by
    have ha : (tripleCharges (sourceA1601 + difference 4 1) (sourceB1601 + difference 1 4) sourceC1601) = raw23909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1601 sourceB1601 sourceC1601 difference raw23909; decide +kernel
    rw [ha]
    exact (canonical23909 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1601 + difference 5 1) (sourceB1601 + difference 1 5) sourceC1601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1327) := by
    have ha : (tripleCharges (sourceA1601 + difference 5 1) (sourceB1601 + difference 1 5) sourceC1601) = raw23910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1601 sourceB1601 sourceC1601 difference raw23910; decide +kernel
    rw [ha]
    exact (canonical23910 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1601 + sourceB1601) sourceC1601) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1601 + sourceB1601) sourceC1601) = raw23911 := by
      apply Matrix.ext; unfold doubleCharges sourceA1601 sourceB1601 sourceC1601 raw23911; decide +kernel
    rw [ha]
    exact (canonical23911 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1601 sourceB1601 sourceC1601
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1601, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1602 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceB1602 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC1602 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1602 : Integer.Sparse Master := [(Sum.inr 1713, 1), (Sum.inr 2457, 1), (Sum.inr 3278, 1), (Sum.inr 3281, 1), (Sum.inr 3293, 2), (Sum.inr 4069, -1)]

theorem sourceEq1602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1602 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1602 + difference 0 0) (sourceB1602 + difference 0 0) sourceC1602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1602 + difference 0 0) (sourceB1602 + difference 0 0) sourceC1602) = raw23826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1602 sourceB1602 sourceC1602 difference raw23826; decide +kernel
    rw [ha]
    exact (canonical23826 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1602 + difference 0 1) (sourceB1602 + difference 1 0) sourceC1602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1602 + difference 0 1) (sourceB1602 + difference 1 0) sourceC1602) = raw23820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1602 sourceB1602 sourceC1602 difference raw23820; decide +kernel
    rw [ha]
    exact (canonical23820 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1602 + difference 0 2) (sourceB1602 + difference 2 0) sourceC1602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1602 + difference 0 2) (sourceB1602 + difference 2 0) sourceC1602) = raw23912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1602 sourceB1602 sourceC1602 difference raw23912; decide +kernel
    rw [ha]
    exact (canonical23912 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1602 + difference 0 3) (sourceB1602 + difference 3 0) sourceC1602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3278) := by
    have ha : (tripleCharges (sourceA1602 + difference 0 3) (sourceB1602 + difference 3 0) sourceC1602) = raw23913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1602 sourceB1602 sourceC1602 difference raw23913; decide +kernel
    rw [ha]
    exact (canonical23913 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1602 + difference 0 4) (sourceB1602 + difference 4 0) sourceC1602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3281) := by
    have ha : (tripleCharges (sourceA1602 + difference 0 4) (sourceB1602 + difference 4 0) sourceC1602) = raw23887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1602 sourceB1602 sourceC1602 difference raw23887; decide +kernel
    rw [ha]
    exact (canonical23887 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1602 + difference 0 5) (sourceB1602 + difference 5 0) sourceC1602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2457) := by
    have ha : (tripleCharges (sourceA1602 + difference 0 5) (sourceB1602 + difference 5 0) sourceC1602) = raw23914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1602 sourceB1602 sourceC1602 difference raw23914; decide +kernel
    rw [ha]
    exact (canonical23914 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1602 + sourceB1602) sourceC1602) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1602 + sourceB1602) sourceC1602) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1602 sourceB1602 sourceC1602 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1602 sourceB1602 sourceC1602
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1602, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1603 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceB1603 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC1603 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1603 : Integer.Sparse Master := [(Sum.inr 792, 1), (Sum.inr 793, 2), (Sum.inr 803, 1), (Sum.inr 822, 1), (Sum.inr 1713, 1), (Sum.inr 4069, -1)]

theorem sourceEq1603 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1603 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1603 + difference 0 0) (sourceB1603 + difference 0 0) sourceC1603) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1603 + difference 0 0) (sourceB1603 + difference 0 0) sourceC1603) = raw23826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1603 sourceB1603 sourceC1603 difference raw23826; decide +kernel
    rw [ha]
    exact (canonical23826 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1603 + difference 1 0) (sourceB1603 + difference 0 1) sourceC1603) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 793) := by
    have ha : (tripleCharges (sourceA1603 + difference 1 0) (sourceB1603 + difference 0 1) sourceC1603) = raw23915 := by
      apply Matrix.ext; unfold tripleCharges sourceA1603 sourceB1603 sourceC1603 difference raw23915; decide +kernel
    rw [ha]
    exact (canonical23915 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1603 + difference 2 0) (sourceB1603 + difference 0 2) sourceC1603) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 793) := by
    have ha : (tripleCharges (sourceA1603 + difference 2 0) (sourceB1603 + difference 0 2) sourceC1603) = raw23916 := by
      apply Matrix.ext; unfold tripleCharges sourceA1603 sourceB1603 sourceC1603 difference raw23916; decide +kernel
    rw [ha]
    exact (canonical23916 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1603 + difference 3 0) (sourceB1603 + difference 0 3) sourceC1603) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 822) := by
    have ha : (tripleCharges (sourceA1603 + difference 3 0) (sourceB1603 + difference 0 3) sourceC1603) = raw23917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1603 sourceB1603 sourceC1603 difference raw23917; decide +kernel
    rw [ha]
    exact (canonical23917 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1603 + difference 4 0) (sourceB1603 + difference 0 4) sourceC1603) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 792) := by
    have ha : (tripleCharges (sourceA1603 + difference 4 0) (sourceB1603 + difference 0 4) sourceC1603) = raw23918 := by
      apply Matrix.ext; unfold tripleCharges sourceA1603 sourceB1603 sourceC1603 difference raw23918; decide +kernel
    rw [ha]
    exact (canonical23918 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1603 + difference 5 0) (sourceB1603 + difference 0 5) sourceC1603) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 803) := by
    have ha : (tripleCharges (sourceA1603 + difference 5 0) (sourceB1603 + difference 0 5) sourceC1603) = raw23891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1603 sourceB1603 sourceC1603 difference raw23891; decide +kernel
    rw [ha]
    exact (canonical23891 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1603 + sourceB1603) sourceC1603) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1603 + sourceB1603) sourceC1603) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1603 sourceB1603 sourceC1603 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1603 sourceB1603 sourceC1603
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1603, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1604 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceB1604 : Charge := ![3, -1, -1, 0, -1, 0]
def sourceC1604 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1604 : Integer.Sparse Master := [(Sum.inr 822, 1), (Sum.inr 1654, 1), (Sum.inr 1713, 2), (Sum.inr 1737, 2), (Sum.inr 4069, -1)]

theorem sourceEq1604 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1604 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1604 + difference 3 0) (sourceB1604 + difference 0 3) sourceC1604) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 822) := by
    have ha : (tripleCharges (sourceA1604 + difference 3 0) (sourceB1604 + difference 0 3) sourceC1604) = raw23917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1604 sourceB1604 sourceC1604 difference raw23917; decide +kernel
    rw [ha]
    exact (canonical23917 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1604 + difference 3 1) (sourceB1604 + difference 1 3) sourceC1604) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1604 + difference 3 1) (sourceB1604 + difference 1 3) sourceC1604) = raw23824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1604 sourceB1604 sourceC1604 difference raw23824; decide +kernel
    rw [ha]
    exact (canonical23824 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1604 + difference 3 2) (sourceB1604 + difference 2 3) sourceC1604) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1604 + difference 3 2) (sourceB1604 + difference 2 3) sourceC1604) = raw23919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1604 sourceB1604 sourceC1604 difference raw23919; decide +kernel
    rw [ha]
    exact (canonical23919 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1604 + difference 3 3) (sourceB1604 + difference 3 3) sourceC1604) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1604 + difference 3 3) (sourceB1604 + difference 3 3) sourceC1604) = raw23826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1604 sourceB1604 sourceC1604 difference raw23826; decide +kernel
    rw [ha]
    exact (canonical23826 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1604 + difference 3 4) (sourceB1604 + difference 4 3) sourceC1604) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1604 + difference 3 4) (sourceB1604 + difference 4 3) sourceC1604) = raw23895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1604 sourceB1604 sourceC1604 difference raw23895; decide +kernel
    rw [ha]
    exact (canonical23895 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1604 + difference 3 5) (sourceB1604 + difference 5 3) sourceC1604) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1654) := by
    have ha : (tripleCharges (sourceA1604 + difference 3 5) (sourceB1604 + difference 5 3) sourceC1604) = raw23920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1604 sourceB1604 sourceC1604 difference raw23920; decide +kernel
    rw [ha]
    exact (canonical23920 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1604 + sourceB1604) sourceC1604) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1604 + sourceB1604) sourceC1604) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1604 sourceB1604 sourceC1604 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1604 sourceB1604 sourceC1604
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1604, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1605 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1605 : Charge := ![3, -1, -2, 0, 0, 0]
def sourceC1605 : Charge := ![1, 1, 2, -1, -1, -2]
def sourceForm1605 : Integer.Sparse Master := [(Sum.inr 1354, 1), (Sum.inr 2853, 1), (Sum.inr 2908, 1), (Sum.inr 3016, 2), (Sum.inr 3023, 1), (Sum.inr 4090, -1)]

theorem sourceEq1605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1605 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1605 + difference 0 0) (sourceB1605 + difference 0 0) sourceC1605) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1354) := by
    have ha : (tripleCharges (sourceA1605 + difference 0 0) (sourceB1605 + difference 0 0) sourceC1605) = raw23921 := by
      apply Matrix.ext; unfold tripleCharges sourceA1605 sourceB1605 sourceC1605 difference raw23921; decide +kernel
    rw [ha]
    exact (canonical23921 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1605 + difference 0 1) (sourceB1605 + difference 1 0) sourceC1605) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2908) := by
    have ha : (tripleCharges (sourceA1605 + difference 0 1) (sourceB1605 + difference 1 0) sourceC1605) = raw23922 := by
      apply Matrix.ext; unfold tripleCharges sourceA1605 sourceB1605 sourceC1605 difference raw23922; decide +kernel
    rw [ha]
    exact (canonical23922 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1605 + difference 0 2) (sourceB1605 + difference 2 0) sourceC1605) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2853) := by
    have ha : (tripleCharges (sourceA1605 + difference 0 2) (sourceB1605 + difference 2 0) sourceC1605) = raw23923 := by
      apply Matrix.ext; unfold tripleCharges sourceA1605 sourceB1605 sourceC1605 difference raw23923; decide +kernel
    rw [ha]
    exact (canonical23923 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1605 + difference 0 3) (sourceB1605 + difference 3 0) sourceC1605) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA1605 + difference 0 3) (sourceB1605 + difference 3 0) sourceC1605) = raw23924 := by
      apply Matrix.ext; unfold tripleCharges sourceA1605 sourceB1605 sourceC1605 difference raw23924; decide +kernel
    rw [ha]
    exact (canonical23924 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1605 + difference 0 4) (sourceB1605 + difference 4 0) sourceC1605) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA1605 + difference 0 4) (sourceB1605 + difference 4 0) sourceC1605) = raw23925 := by
      apply Matrix.ext; unfold tripleCharges sourceA1605 sourceB1605 sourceC1605 difference raw23925; decide +kernel
    rw [ha]
    exact (canonical23925 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1605 + difference 0 5) (sourceB1605 + difference 5 0) sourceC1605) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA1605 + difference 0 5) (sourceB1605 + difference 5 0) sourceC1605) = raw23926 := by
      apply Matrix.ext; unfold tripleCharges sourceA1605 sourceB1605 sourceC1605 difference raw23926; decide +kernel
    rw [ha]
    exact (canonical23926 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1605 + sourceB1605) sourceC1605) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1605 + sourceB1605) sourceC1605) = raw23927 := by
      apply Matrix.ext; unfold doubleCharges sourceA1605 sourceB1605 sourceC1605 raw23927; decide +kernel
    rw [ha]
    exact (canonical23927 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1605 sourceB1605 sourceC1605
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1605, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1606 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1606 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceC1606 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceForm1606 : Integer.Sparse Master := [(Sum.inr 1125, 1), (Sum.inr 1128, 1), (Sum.inr 1133, 2), (Sum.inr 1234, 1), (Sum.inr 2509, 1), (Sum.inr 4084, -1)]

theorem sourceEq1606 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1606 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1606 + difference 0 1) (sourceB1606 + difference 1 0) sourceC1606) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2509) := by
    have ha : (tripleCharges (sourceA1606 + difference 0 1) (sourceB1606 + difference 1 0) sourceC1606) = raw23928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1606 sourceB1606 sourceC1606 difference raw23928; decide +kernel
    rw [ha]
    exact (canonical23928 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1606 + difference 1 1) (sourceB1606 + difference 1 1) sourceC1606) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1234) := by
    have ha : (tripleCharges (sourceA1606 + difference 1 1) (sourceB1606 + difference 1 1) sourceC1606) = raw23929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1606 sourceB1606 sourceC1606 difference raw23929; decide +kernel
    rw [ha]
    exact (canonical23929 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1606 + difference 2 1) (sourceB1606 + difference 1 2) sourceC1606) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1125) := by
    have ha : (tripleCharges (sourceA1606 + difference 2 1) (sourceB1606 + difference 1 2) sourceC1606) = raw23930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1606 sourceB1606 sourceC1606 difference raw23930; decide +kernel
    rw [ha]
    exact (canonical23930 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1606 + difference 3 1) (sourceB1606 + difference 1 3) sourceC1606) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1133) := by
    have ha : (tripleCharges (sourceA1606 + difference 3 1) (sourceB1606 + difference 1 3) sourceC1606) = raw23931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1606 sourceB1606 sourceC1606 difference raw23931; decide +kernel
    rw [ha]
    exact (canonical23931 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1606 + difference 4 1) (sourceB1606 + difference 1 4) sourceC1606) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1133) := by
    have ha : (tripleCharges (sourceA1606 + difference 4 1) (sourceB1606 + difference 1 4) sourceC1606) = raw22395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1606 sourceB1606 sourceC1606 difference raw22395; decide +kernel
    rw [ha]
    exact (canonical22395 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1606 + difference 5 1) (sourceB1606 + difference 1 5) sourceC1606) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1128) := by
    have ha : (tripleCharges (sourceA1606 + difference 5 1) (sourceB1606 + difference 1 5) sourceC1606) = raw23932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1606 sourceB1606 sourceC1606 difference raw23932; decide +kernel
    rw [ha]
    exact (canonical23932 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1606 + sourceB1606) sourceC1606) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1606 + sourceB1606) sourceC1606) = raw22398 := by
      apply Matrix.ext; unfold doubleCharges sourceA1606 sourceB1606 sourceC1606 raw22398; decide +kernel
    rw [ha]
    exact (canonical22398 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1606 sourceB1606 sourceC1606
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1606, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1607 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1607 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1607 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceForm1607 : Integer.Sparse Master := [(Sum.inr 651, 1), (Sum.inr 1169, 1), (Sum.inr 1270, 3), (Sum.inr 1293, 1), (Sum.inr 4091, -1)]

theorem sourceEq1607 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1607 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1607 + difference 1 0) (sourceB1607 + difference 0 1) sourceC1607) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 651) := by
    have ha : (tripleCharges (sourceA1607 + difference 1 0) (sourceB1607 + difference 0 1) sourceC1607) = raw23933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1607 sourceB1607 sourceC1607 difference raw23933; decide +kernel
    rw [ha]
    exact (canonical23933 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1607 + difference 1 1) (sourceB1607 + difference 1 1) sourceC1607) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA1607 + difference 1 1) (sourceB1607 + difference 1 1) sourceC1607) = raw13564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1607 sourceB1607 sourceC1607 difference raw13564; decide +kernel
    rw [ha]
    exact (canonical13564 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1607 + difference 1 2) (sourceB1607 + difference 2 1) sourceC1607) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1169) := by
    have ha : (tripleCharges (sourceA1607 + difference 1 2) (sourceB1607 + difference 2 1) sourceC1607) = raw23934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1607 sourceB1607 sourceC1607 difference raw23934; decide +kernel
    rw [ha]
    exact (canonical23934 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1607 + difference 1 3) (sourceB1607 + difference 3 1) sourceC1607) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA1607 + difference 1 3) (sourceB1607 + difference 3 1) sourceC1607) = raw23935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1607 sourceB1607 sourceC1607 difference raw23935; decide +kernel
    rw [ha]
    exact (canonical23935 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1607 + difference 1 4) (sourceB1607 + difference 4 1) sourceC1607) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA1607 + difference 1 4) (sourceB1607 + difference 4 1) sourceC1607) = raw23936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1607 sourceB1607 sourceC1607 difference raw23936; decide +kernel
    rw [ha]
    exact (canonical23936 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1607 + difference 1 5) (sourceB1607 + difference 5 1) sourceC1607) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA1607 + difference 1 5) (sourceB1607 + difference 5 1) sourceC1607) = raw13560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1607 sourceB1607 sourceC1607 difference raw13560; decide +kernel
    rw [ha]
    exact (canonical13560 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1607 + sourceB1607) sourceC1607) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1607 + sourceB1607) sourceC1607) = raw13559 := by
      apply Matrix.ext; unfold doubleCharges sourceA1607 sourceB1607 sourceC1607 raw13559; decide +kernel
    rw [ha]
    exact (canonical13559 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1607 sourceB1607 sourceC1607
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1607, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1608 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceB1608 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1608 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1608 : Integer.Sparse Master := [(Sum.inr 1654, 1), (Sum.inr 1656, 2), (Sum.inr 1658, 1), (Sum.inr 1737, 1), (Sum.inr 2702, 1), (Sum.inr 4069, -1)]

theorem sourceEq1608 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1608 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1608 + difference 0 0) (sourceB1608 + difference 0 0) sourceC1608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1608 + difference 0 0) (sourceB1608 + difference 0 0) sourceC1608) = raw23937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1608 sourceB1608 sourceC1608 difference raw23937; decide +kernel
    rw [ha]
    exact (canonical23937 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1608 + difference 0 1) (sourceB1608 + difference 1 0) sourceC1608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1658) := by
    have ha : (tripleCharges (sourceA1608 + difference 0 1) (sourceB1608 + difference 1 0) sourceC1608) = raw23938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1608 sourceB1608 sourceC1608 difference raw23938; decide +kernel
    rw [ha]
    exact (canonical23938 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1608 + difference 0 2) (sourceB1608 + difference 2 0) sourceC1608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1654) := by
    have ha : (tripleCharges (sourceA1608 + difference 0 2) (sourceB1608 + difference 2 0) sourceC1608) = raw23939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1608 sourceB1608 sourceC1608 difference raw23939; decide +kernel
    rw [ha]
    exact (canonical23939 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1608 + difference 0 3) (sourceB1608 + difference 3 0) sourceC1608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1656) := by
    have ha : (tripleCharges (sourceA1608 + difference 0 3) (sourceB1608 + difference 3 0) sourceC1608) = raw23940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1608 sourceB1608 sourceC1608 difference raw23940; decide +kernel
    rw [ha]
    exact (canonical23940 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1608 + difference 0 4) (sourceB1608 + difference 4 0) sourceC1608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1656) := by
    have ha : (tripleCharges (sourceA1608 + difference 0 4) (sourceB1608 + difference 4 0) sourceC1608) = raw23941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1608 sourceB1608 sourceC1608 difference raw23941; decide +kernel
    rw [ha]
    exact (canonical23941 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1608 + difference 0 5) (sourceB1608 + difference 5 0) sourceC1608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1608 + difference 0 5) (sourceB1608 + difference 5 0) sourceC1608) = raw23942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1608 sourceB1608 sourceC1608 difference raw23942; decide +kernel
    rw [ha]
    exact (canonical23942 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1608 + sourceB1608) sourceC1608) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1608 + sourceB1608) sourceC1608) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1608 sourceB1608 sourceC1608 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1608 sourceB1608 sourceC1608
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1608, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1609 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceB1609 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1609 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1609 : Integer.Sparse Master := [(Sum.inr 1710, 1), (Sum.inr 2702, 2), (Sum.inr 2737, 2), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

theorem sourceEq1609 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1609 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1609 + difference 1 0) (sourceB1609 + difference 0 1) sourceC1609) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1609 + difference 1 0) (sourceB1609 + difference 0 1) sourceC1609) = raw23943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1609 sourceB1609 sourceC1609 difference raw23943; decide +kernel
    rw [ha]
    exact (canonical23943 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1609 + difference 1 1) (sourceB1609 + difference 1 1) sourceC1609) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1609 + difference 1 1) (sourceB1609 + difference 1 1) sourceC1609) = raw23937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1609 sourceB1609 sourceC1609 difference raw23937; decide +kernel
    rw [ha]
    exact (canonical23937 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1609 + difference 1 2) (sourceB1609 + difference 2 1) sourceC1609) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1609 + difference 1 2) (sourceB1609 + difference 2 1) sourceC1609) = raw23944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1609 sourceB1609 sourceC1609 difference raw23944; decide +kernel
    rw [ha]
    exact (canonical23944 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1609 + difference 1 3) (sourceB1609 + difference 3 1) sourceC1609) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1609 + difference 1 3) (sourceB1609 + difference 3 1) sourceC1609) = raw23945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1609 sourceB1609 sourceC1609 difference raw23945; decide +kernel
    rw [ha]
    exact (canonical23945 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1609 + difference 1 4) (sourceB1609 + difference 4 1) sourceC1609) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1609 + difference 1 4) (sourceB1609 + difference 4 1) sourceC1609) = raw23946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1609 sourceB1609 sourceC1609 difference raw23946; decide +kernel
    rw [ha]
    exact (canonical23946 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1609 + difference 1 5) (sourceB1609 + difference 5 1) sourceC1609) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3308) := by
    have ha : (tripleCharges (sourceA1609 + difference 1 5) (sourceB1609 + difference 5 1) sourceC1609) = raw23947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1609 sourceB1609 sourceC1609 difference raw23947; decide +kernel
    rw [ha]
    exact (canonical23947 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1609 + sourceB1609) sourceC1609) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1609 + sourceB1609) sourceC1609) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1609 sourceB1609 sourceC1609 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1609 sourceB1609 sourceC1609
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1609, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1610 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceB1610 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1610 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1610 : Integer.Sparse Master := [(Sum.inr 1602, 1), (Sum.inr 2457, 1), (Sum.inr 2466, 1), (Sum.inr 2502, 1), (Sum.inr 2702, 1), (Sum.inr 3293, 1), (Sum.inr 4069, -1)]

theorem sourceEq1610 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1610 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1610 + difference 3 0) (sourceB1610 + difference 0 3) sourceC1610) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1602) := by
    have ha : (tripleCharges (sourceA1610 + difference 3 0) (sourceB1610 + difference 0 3) sourceC1610) = raw23948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1610 sourceB1610 sourceC1610 difference raw23948; decide +kernel
    rw [ha]
    exact (canonical23948 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1610 + difference 3 1) (sourceB1610 + difference 1 3) sourceC1610) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2466) := by
    have ha : (tripleCharges (sourceA1610 + difference 3 1) (sourceB1610 + difference 1 3) sourceC1610) = raw23949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1610 sourceB1610 sourceC1610 difference raw23949; decide +kernel
    rw [ha]
    exact (canonical23949 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1610 + difference 3 2) (sourceB1610 + difference 2 3) sourceC1610) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2457) := by
    have ha : (tripleCharges (sourceA1610 + difference 3 2) (sourceB1610 + difference 2 3) sourceC1610) = raw23950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1610 sourceB1610 sourceC1610 difference raw23950; decide +kernel
    rw [ha]
    exact (canonical23950 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1610 + difference 3 3) (sourceB1610 + difference 3 3) sourceC1610) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1610 + difference 3 3) (sourceB1610 + difference 3 3) sourceC1610) = raw23937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1610 sourceB1610 sourceC1610 difference raw23937; decide +kernel
    rw [ha]
    exact (canonical23937 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1610 + difference 3 4) (sourceB1610 + difference 4 3) sourceC1610) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2502) := by
    have ha : (tripleCharges (sourceA1610 + difference 3 4) (sourceB1610 + difference 4 3) sourceC1610) = raw23951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1610 sourceB1610 sourceC1610 difference raw23951; decide +kernel
    rw [ha]
    exact (canonical23951 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1610 + difference 3 5) (sourceB1610 + difference 5 3) sourceC1610) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1610 + difference 3 5) (sourceB1610 + difference 5 3) sourceC1610) = raw23952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1610 sourceB1610 sourceC1610 difference raw23952; decide +kernel
    rw [ha]
    exact (canonical23952 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1610 + sourceB1610) sourceC1610) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1610 + sourceB1610) sourceC1610) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1610 sourceB1610 sourceC1610 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1610 sourceB1610 sourceC1610
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1610, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1611 : Charge := ![2, -1, 0, -1, -1, 1]
def sourceB1611 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1611 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1611 : Integer.Sparse Master := [(Sum.inr 1737, 1), (Sum.inr 2702, 1), (Sum.inr 3288, 1), (Sum.inr 3293, 2), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

theorem sourceEq1611 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1611 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1611 + difference 0 5) (sourceB1611 + difference 5 0) sourceC1611) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1611 + difference 0 5) (sourceB1611 + difference 5 0) sourceC1611) = raw23942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1611 sourceB1611 sourceC1611 difference raw23942; decide +kernel
    rw [ha]
    exact (canonical23942 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1611 + difference 1 5) (sourceB1611 + difference 5 1) sourceC1611) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3308) := by
    have ha : (tripleCharges (sourceA1611 + difference 1 5) (sourceB1611 + difference 5 1) sourceC1611) = raw23947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1611 sourceB1611 sourceC1611 difference raw23947; decide +kernel
    rw [ha]
    exact (canonical23947 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1611 + difference 2 5) (sourceB1611 + difference 5 2) sourceC1611) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1611 + difference 2 5) (sourceB1611 + difference 5 2) sourceC1611) = raw23953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1611 sourceB1611 sourceC1611 difference raw23953; decide +kernel
    rw [ha]
    exact (canonical23953 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1611 + difference 3 5) (sourceB1611 + difference 5 3) sourceC1611) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1611 + difference 3 5) (sourceB1611 + difference 5 3) sourceC1611) = raw23952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1611 sourceB1611 sourceC1611 difference raw23952; decide +kernel
    rw [ha]
    exact (canonical23952 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1611 + difference 4 5) (sourceB1611 + difference 5 4) sourceC1611) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1611 + difference 4 5) (sourceB1611 + difference 5 4) sourceC1611) = raw23954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1611 sourceB1611 sourceC1611 difference raw23954; decide +kernel
    rw [ha]
    exact (canonical23954 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1611 + difference 5 5) (sourceB1611 + difference 5 5) sourceC1611) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1611 + difference 5 5) (sourceB1611 + difference 5 5) sourceC1611) = raw23937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1611 sourceB1611 sourceC1611 difference raw23937; decide +kernel
    rw [ha]
    exact (canonical23937 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1611 + sourceB1611) sourceC1611) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1611 + sourceB1611) sourceC1611) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1611 sourceB1611 sourceC1611 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1611 sourceB1611 sourceC1611
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1611, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1612 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1612 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceC1612 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceForm1612 : Integer.Sparse Master := [(Sum.inr 1127, 1), (Sum.inr 1132, 1), (Sum.inr 1134, 1), (Sum.inr 1141, 1), (Sum.inr 1237, 1), (Sum.inr 2512, 1), (Sum.inr 4092, -1)]

theorem sourceEq1612 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1612 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1612 + difference 0 1) (sourceB1612 + difference 1 0) sourceC1612) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA1612 + difference 0 1) (sourceB1612 + difference 1 0) sourceC1612) = raw23955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1612 sourceB1612 sourceC1612 difference raw23955; decide +kernel
    rw [ha]
    exact (canonical23955 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1612 + difference 1 1) (sourceB1612 + difference 1 1) sourceC1612) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA1612 + difference 1 1) (sourceB1612 + difference 1 1) sourceC1612) = raw23956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1612 sourceB1612 sourceC1612 difference raw23956; decide +kernel
    rw [ha]
    exact (canonical23956 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1612 + difference 2 1) (sourceB1612 + difference 1 2) sourceC1612) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1127) := by
    have ha : (tripleCharges (sourceA1612 + difference 2 1) (sourceB1612 + difference 1 2) sourceC1612) = raw23957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1612 sourceB1612 sourceC1612 difference raw23957; decide +kernel
    rw [ha]
    exact (canonical23957 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1612 + difference 3 1) (sourceB1612 + difference 1 3) sourceC1612) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1141) := by
    have ha : (tripleCharges (sourceA1612 + difference 3 1) (sourceB1612 + difference 1 3) sourceC1612) = raw23958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1612 sourceB1612 sourceC1612 difference raw23958; decide +kernel
    rw [ha]
    exact (canonical23958 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1612 + difference 4 1) (sourceB1612 + difference 1 4) sourceC1612) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1134) := by
    have ha : (tripleCharges (sourceA1612 + difference 4 1) (sourceB1612 + difference 1 4) sourceC1612) = raw23959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1612 sourceB1612 sourceC1612 difference raw23959; decide +kernel
    rw [ha]
    exact (canonical23959 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1612 + difference 5 1) (sourceB1612 + difference 1 5) sourceC1612) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1132) := by
    have ha : (tripleCharges (sourceA1612 + difference 5 1) (sourceB1612 + difference 1 5) sourceC1612) = raw20245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1612 sourceB1612 sourceC1612 difference raw20245; decide +kernel
    rw [ha]
    exact (canonical20245 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1612 + sourceB1612) sourceC1612) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1612 + sourceB1612) sourceC1612) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA1612 sourceB1612 sourceC1612 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1612 sourceB1612 sourceC1612
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1612, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1613 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1613 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1613 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceForm1613 : Integer.Sparse Master := [(Sum.inr 640, 1), (Sum.inr 1158, 1), (Sum.inr 1240, 1), (Sum.inr 1262, 2), (Sum.inr 1293, 1), (Sum.inr 4091, -1)]

theorem sourceEq1613 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1613 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1613 + difference 1 0) (sourceB1613 + difference 0 1) sourceC1613) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 640) := by
    have ha : (tripleCharges (sourceA1613 + difference 1 0) (sourceB1613 + difference 0 1) sourceC1613) = raw23960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1613 sourceB1613 sourceC1613 difference raw23960; decide +kernel
    rw [ha]
    exact (canonical23960 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1613 + difference 1 1) (sourceB1613 + difference 1 1) sourceC1613) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA1613 + difference 1 1) (sourceB1613 + difference 1 1) sourceC1613) = raw23961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1613 sourceB1613 sourceC1613 difference raw23961; decide +kernel
    rw [ha]
    exact (canonical23961 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1613 + difference 1 2) (sourceB1613 + difference 2 1) sourceC1613) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1158) := by
    have ha : (tripleCharges (sourceA1613 + difference 1 2) (sourceB1613 + difference 2 1) sourceC1613) = raw23962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1613 sourceB1613 sourceC1613 difference raw23962; decide +kernel
    rw [ha]
    exact (canonical23962 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1613 + difference 1 3) (sourceB1613 + difference 3 1) sourceC1613) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA1613 + difference 1 3) (sourceB1613 + difference 3 1) sourceC1613) = raw23963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1613 sourceB1613 sourceC1613 difference raw23963; decide +kernel
    rw [ha]
    exact (canonical23963 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1613 + difference 1 4) (sourceB1613 + difference 4 1) sourceC1613) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1613 + difference 1 4) (sourceB1613 + difference 4 1) sourceC1613) = raw23964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1613 sourceB1613 sourceC1613 difference raw23964; decide +kernel
    rw [ha]
    exact (canonical23964 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1613 + difference 1 5) (sourceB1613 + difference 5 1) sourceC1613) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA1613 + difference 1 5) (sourceB1613 + difference 5 1) sourceC1613) = raw23965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1613 sourceB1613 sourceC1613 difference raw23965; decide +kernel
    rw [ha]
    exact (canonical23965 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1613 + sourceB1613) sourceC1613) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1613 + sourceB1613) sourceC1613) = raw16433 := by
      apply Matrix.ext; unfold doubleCharges sourceA1613 sourceB1613 sourceC1613 raw16433; decide +kernel
    rw [ha]
    exact (canonical16433 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1613 sourceB1613 sourceC1613
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1613, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1614 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceB1614 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1614 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1614 : Integer.Sparse Master := [(Sum.inr 1642, 1), (Sum.inr 1645, 1), (Sum.inr 1646, 1), (Sum.inr 1649, 1), (Sum.inr 1724, 1), (Sum.inr 3294, 1), (Sum.inr 4069, -1)]

theorem sourceEq1614 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1614 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1614 + difference 0 0) (sourceB1614 + difference 0 0) sourceC1614) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1614 + difference 0 0) (sourceB1614 + difference 0 0) sourceC1614) = raw23966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1614 sourceB1614 sourceC1614 difference raw23966; decide +kernel
    rw [ha]
    exact (canonical23966 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1614 + difference 0 1) (sourceB1614 + difference 1 0) sourceC1614) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1649) := by
    have ha : (tripleCharges (sourceA1614 + difference 0 1) (sourceB1614 + difference 1 0) sourceC1614) = raw23967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1614 sourceB1614 sourceC1614 difference raw23967; decide +kernel
    rw [ha]
    exact (canonical23967 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1614 + difference 0 2) (sourceB1614 + difference 2 0) sourceC1614) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1642) := by
    have ha : (tripleCharges (sourceA1614 + difference 0 2) (sourceB1614 + difference 2 0) sourceC1614) = raw23968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1614 sourceB1614 sourceC1614 difference raw23968; decide +kernel
    rw [ha]
    exact (canonical23968 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1614 + difference 0 3) (sourceB1614 + difference 3 0) sourceC1614) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1646) := by
    have ha : (tripleCharges (sourceA1614 + difference 0 3) (sourceB1614 + difference 3 0) sourceC1614) = raw23969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1614 sourceB1614 sourceC1614 difference raw23969; decide +kernel
    rw [ha]
    exact (canonical23969 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1614 + difference 0 4) (sourceB1614 + difference 4 0) sourceC1614) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1614 + difference 0 4) (sourceB1614 + difference 4 0) sourceC1614) = raw23970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1614 sourceB1614 sourceC1614 difference raw23970; decide +kernel
    rw [ha]
    exact (canonical23970 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1614 + difference 0 5) (sourceB1614 + difference 5 0) sourceC1614) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1645) := by
    have ha : (tripleCharges (sourceA1614 + difference 0 5) (sourceB1614 + difference 5 0) sourceC1614) = raw23971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1614 sourceB1614 sourceC1614 difference raw23971; decide +kernel
    rw [ha]
    exact (canonical23971 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1614 + sourceB1614) sourceC1614) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1614 + sourceB1614) sourceC1614) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1614 sourceB1614 sourceC1614 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1614 sourceB1614 sourceC1614
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1614, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1615 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceB1615 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1615 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1615 : Integer.Sparse Master := [(Sum.inr 1598, 1), (Sum.inr 1603, 1), (Sum.inr 1605, 1), (Sum.inr 1623, 1), (Sum.inr 1728, 1), (Sum.inr 3294, 1), (Sum.inr 4069, -1)]

theorem sourceEq1615 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1615 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1615 + difference 0 0) (sourceB1615 + difference 0 0) sourceC1615) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1615 + difference 0 0) (sourceB1615 + difference 0 0) sourceC1615) = raw23966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1615 sourceB1615 sourceC1615 difference raw23966; decide +kernel
    rw [ha]
    exact (canonical23966 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1615 + difference 1 0) (sourceB1615 + difference 0 1) sourceC1615) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1615 + difference 1 0) (sourceB1615 + difference 0 1) sourceC1615) = raw23803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1615 sourceB1615 sourceC1615 difference raw23803; decide +kernel
    rw [ha]
    exact (canonical23803 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1615 + difference 2 0) (sourceB1615 + difference 0 2) sourceC1615) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1598) := by
    have ha : (tripleCharges (sourceA1615 + difference 2 0) (sourceB1615 + difference 0 2) sourceC1615) = raw23830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1615 sourceB1615 sourceC1615 difference raw23830; decide +kernel
    rw [ha]
    exact (canonical23830 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1615 + difference 3 0) (sourceB1615 + difference 0 3) sourceC1615) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1623) := by
    have ha : (tripleCharges (sourceA1615 + difference 3 0) (sourceB1615 + difference 0 3) sourceC1615) = raw23972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1615 sourceB1615 sourceC1615 difference raw23972; decide +kernel
    rw [ha]
    exact (canonical23972 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1615 + difference 4 0) (sourceB1615 + difference 0 4) sourceC1615) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1603) := by
    have ha : (tripleCharges (sourceA1615 + difference 4 0) (sourceB1615 + difference 0 4) sourceC1615) = raw23973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1615 sourceB1615 sourceC1615 difference raw23973; decide +kernel
    rw [ha]
    exact (canonical23973 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1615 + difference 5 0) (sourceB1615 + difference 0 5) sourceC1615) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1605) := by
    have ha : (tripleCharges (sourceA1615 + difference 5 0) (sourceB1615 + difference 0 5) sourceC1615) = raw23974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1615 sourceB1615 sourceC1615 difference raw23974; decide +kernel
    rw [ha]
    exact (canonical23974 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1615 + sourceB1615) sourceC1615) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1615 + sourceB1615) sourceC1615) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1615 sourceB1615 sourceC1615 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1615 sourceB1615 sourceC1615
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1615, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1616 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceB1616 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1616 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1616 : Integer.Sparse Master := [(Sum.inr 1728, 1), (Sum.inr 3294, 2), (Sum.inr 3305, 1), (Sum.inr 3306, 1), (Sum.inr 3309, 1), (Sum.inr 4069, -1)]

theorem sourceEq1616 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1616 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1616 + difference 1 0) (sourceB1616 + difference 0 1) sourceC1616) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1616 + difference 1 0) (sourceB1616 + difference 0 1) sourceC1616) = raw23803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1616 sourceB1616 sourceC1616 difference raw23803; decide +kernel
    rw [ha]
    exact (canonical23803 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1616 + difference 1 1) (sourceB1616 + difference 1 1) sourceC1616) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1616 + difference 1 1) (sourceB1616 + difference 1 1) sourceC1616) = raw23966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1616 sourceB1616 sourceC1616 difference raw23966; decide +kernel
    rw [ha]
    exact (canonical23966 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1616 + difference 1 2) (sourceB1616 + difference 2 1) sourceC1616) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1616 + difference 1 2) (sourceB1616 + difference 2 1) sourceC1616) = raw23975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1616 sourceB1616 sourceC1616 difference raw23975; decide +kernel
    rw [ha]
    exact (canonical23975 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1616 + difference 1 3) (sourceB1616 + difference 3 1) sourceC1616) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3306) := by
    have ha : (tripleCharges (sourceA1616 + difference 1 3) (sourceB1616 + difference 3 1) sourceC1616) = raw23976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1616 sourceB1616 sourceC1616 difference raw23976; decide +kernel
    rw [ha]
    exact (canonical23976 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1616 + difference 1 4) (sourceB1616 + difference 4 1) sourceC1616) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3309) := by
    have ha : (tripleCharges (sourceA1616 + difference 1 4) (sourceB1616 + difference 4 1) sourceC1616) = raw23977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1616 sourceB1616 sourceC1616 difference raw23977; decide +kernel
    rw [ha]
    exact (canonical23977 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1616 + difference 1 5) (sourceB1616 + difference 5 1) sourceC1616) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1616 + difference 1 5) (sourceB1616 + difference 5 1) sourceC1616) = raw23797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1616 sourceB1616 sourceC1616 difference raw23797; decide +kernel
    rw [ha]
    exact (canonical23797 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1616 + sourceB1616) sourceC1616) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1616 + sourceB1616) sourceC1616) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1616 sourceB1616 sourceC1616 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1616 sourceB1616 sourceC1616
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1616, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1617 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceB1617 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1617 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1617 : Integer.Sparse Master := [(Sum.inr 1623, 1), (Sum.inr 3246, 1), (Sum.inr 3282, 1), (Sum.inr 3294, 1), (Sum.inr 3296, 1), (Sum.inr 3299, 1), (Sum.inr 4069, -1)]

theorem sourceEq1617 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1617 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1617 + difference 3 0) (sourceB1617 + difference 0 3) sourceC1617) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1623) := by
    have ha : (tripleCharges (sourceA1617 + difference 3 0) (sourceB1617 + difference 0 3) sourceC1617) = raw23972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1617 sourceB1617 sourceC1617 difference raw23972; decide +kernel
    rw [ha]
    exact (canonical23972 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1617 + difference 3 1) (sourceB1617 + difference 1 3) sourceC1617) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3246) := by
    have ha : (tripleCharges (sourceA1617 + difference 3 1) (sourceB1617 + difference 1 3) sourceC1617) = raw23978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1617 sourceB1617 sourceC1617 difference raw23978; decide +kernel
    rw [ha]
    exact (canonical23978 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1617 + difference 3 2) (sourceB1617 + difference 2 3) sourceC1617) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3282) := by
    have ha : (tripleCharges (sourceA1617 + difference 3 2) (sourceB1617 + difference 2 3) sourceC1617) = raw23979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1617 sourceB1617 sourceC1617 difference raw23979; decide +kernel
    rw [ha]
    exact (canonical23979 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1617 + difference 3 3) (sourceB1617 + difference 3 3) sourceC1617) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1617 + difference 3 3) (sourceB1617 + difference 3 3) sourceC1617) = raw23966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1617 sourceB1617 sourceC1617 difference raw23966; decide +kernel
    rw [ha]
    exact (canonical23966 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1617 + difference 3 4) (sourceB1617 + difference 4 3) sourceC1617) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1617 + difference 3 4) (sourceB1617 + difference 4 3) sourceC1617) = raw23980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1617 sourceB1617 sourceC1617 difference raw23980; decide +kernel
    rw [ha]
    exact (canonical23980 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1617 + difference 3 5) (sourceB1617 + difference 5 3) sourceC1617) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1617 + difference 3 5) (sourceB1617 + difference 5 3) sourceC1617) = raw23981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1617 sourceB1617 sourceC1617 difference raw23981; decide +kernel
    rw [ha]
    exact (canonical23981 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1617 + sourceB1617) sourceC1617) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1617 + sourceB1617) sourceC1617) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1617 sourceB1617 sourceC1617 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1617 sourceB1617 sourceC1617
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1617, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1618 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceB1618 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1618 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1618 : Integer.Sparse Master := [(Sum.inr 1724, 1), (Sum.inr 3290, 1), (Sum.inr 3293, 1), (Sum.inr 3294, 1), (Sum.inr 3299, 1), (Sum.inr 3309, 1), (Sum.inr 4069, -1)]

theorem sourceEq1618 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1618 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1618 + difference 0 4) (sourceB1618 + difference 4 0) sourceC1618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1618 + difference 0 4) (sourceB1618 + difference 4 0) sourceC1618) = raw23970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1618 sourceB1618 sourceC1618 difference raw23970; decide +kernel
    rw [ha]
    exact (canonical23970 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1618 + difference 1 4) (sourceB1618 + difference 4 1) sourceC1618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3309) := by
    have ha : (tripleCharges (sourceA1618 + difference 1 4) (sourceB1618 + difference 4 1) sourceC1618) = raw23977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1618 sourceB1618 sourceC1618 difference raw23977; decide +kernel
    rw [ha]
    exact (canonical23977 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1618 + difference 2 4) (sourceB1618 + difference 4 2) sourceC1618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1618 + difference 2 4) (sourceB1618 + difference 4 2) sourceC1618) = raw23982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1618 sourceB1618 sourceC1618 difference raw23982; decide +kernel
    rw [ha]
    exact (canonical23982 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1618 + difference 3 4) (sourceB1618 + difference 4 3) sourceC1618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1618 + difference 3 4) (sourceB1618 + difference 4 3) sourceC1618) = raw23980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1618 sourceB1618 sourceC1618 difference raw23980; decide +kernel
    rw [ha]
    exact (canonical23980 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1618 + difference 4 4) (sourceB1618 + difference 4 4) sourceC1618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1618 + difference 4 4) (sourceB1618 + difference 4 4) sourceC1618) = raw23966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1618 sourceB1618 sourceC1618 difference raw23966; decide +kernel
    rw [ha]
    exact (canonical23966 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1618 + difference 5 4) (sourceB1618 + difference 4 5) sourceC1618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1618 + difference 5 4) (sourceB1618 + difference 4 5) sourceC1618) = raw23954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1618 sourceB1618 sourceC1618 difference raw23954; decide +kernel
    rw [ha]
    exact (canonical23954 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1618 + sourceB1618) sourceC1618) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1618 + sourceB1618) sourceC1618) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1618 sourceB1618 sourceC1618 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1618 sourceB1618 sourceC1618
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1618, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1619 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceB1619 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1619 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1619 : Integer.Sparse Master := [(Sum.inr 1605, 1), (Sum.inr 3240, 1), (Sum.inr 3278, 1), (Sum.inr 3287, 1), (Sum.inr 3293, 1), (Sum.inr 3294, 1), (Sum.inr 4069, -1)]

theorem sourceEq1619 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1619 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1619 + difference 5 0) (sourceB1619 + difference 0 5) sourceC1619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1605) := by
    have ha : (tripleCharges (sourceA1619 + difference 5 0) (sourceB1619 + difference 0 5) sourceC1619) = raw23974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1619 sourceB1619 sourceC1619 difference raw23974; decide +kernel
    rw [ha]
    exact (canonical23974 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1619 + difference 5 1) (sourceB1619 + difference 1 5) sourceC1619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3240) := by
    have ha : (tripleCharges (sourceA1619 + difference 5 1) (sourceB1619 + difference 1 5) sourceC1619) = raw23983 := by
      apply Matrix.ext; unfold tripleCharges sourceA1619 sourceB1619 sourceC1619 difference raw23983; decide +kernel
    rw [ha]
    exact (canonical23983 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1619 + difference 5 2) (sourceB1619 + difference 2 5) sourceC1619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3278) := by
    have ha : (tripleCharges (sourceA1619 + difference 5 2) (sourceB1619 + difference 2 5) sourceC1619) = raw23984 := by
      apply Matrix.ext; unfold tripleCharges sourceA1619 sourceB1619 sourceC1619 difference raw23984; decide +kernel
    rw [ha]
    exact (canonical23984 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1619 + difference 5 3) (sourceB1619 + difference 3 5) sourceC1619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3287) := by
    have ha : (tripleCharges (sourceA1619 + difference 5 3) (sourceB1619 + difference 3 5) sourceC1619) = raw23985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1619 sourceB1619 sourceC1619 difference raw23985; decide +kernel
    rw [ha]
    exact (canonical23985 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1619 + difference 5 4) (sourceB1619 + difference 4 5) sourceC1619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1619 + difference 5 4) (sourceB1619 + difference 4 5) sourceC1619) = raw23954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1619 sourceB1619 sourceC1619 difference raw23954; decide +kernel
    rw [ha]
    exact (canonical23954 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1619 + difference 5 5) (sourceB1619 + difference 5 5) sourceC1619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1619 + difference 5 5) (sourceB1619 + difference 5 5) sourceC1619) = raw23966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1619 sourceB1619 sourceC1619 difference raw23966; decide +kernel
    rw [ha]
    exact (canonical23966 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1619 + sourceB1619) sourceC1619) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1619 + sourceB1619) sourceC1619) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1619 sourceB1619 sourceC1619 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1619 sourceB1619 sourceC1619
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1619, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1620 : Charge := ![2, -1, 0, -1, 1, -1]
def sourceB1620 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1620 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1620 : Integer.Sparse Master := [(Sum.inr 1645, 1), (Sum.inr 3022, 1), (Sum.inr 3285, 1), (Sum.inr 3294, 1), (Sum.inr 3296, 1), (Sum.inr 3305, 1), (Sum.inr 4069, -1)]

theorem sourceEq1620 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1620 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1620 + difference 0 5) (sourceB1620 + difference 5 0) sourceC1620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1645) := by
    have ha : (tripleCharges (sourceA1620 + difference 0 5) (sourceB1620 + difference 5 0) sourceC1620) = raw23971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1620 sourceB1620 sourceC1620 difference raw23971; decide +kernel
    rw [ha]
    exact (canonical23971 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1620 + difference 1 5) (sourceB1620 + difference 5 1) sourceC1620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1620 + difference 1 5) (sourceB1620 + difference 5 1) sourceC1620) = raw23797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1620 sourceB1620 sourceC1620 difference raw23797; decide +kernel
    rw [ha]
    exact (canonical23797 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1620 + difference 2 5) (sourceB1620 + difference 5 2) sourceC1620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3285) := by
    have ha : (tripleCharges (sourceA1620 + difference 2 5) (sourceB1620 + difference 5 2) sourceC1620) = raw23818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1620 sourceB1620 sourceC1620 difference raw23818; decide +kernel
    rw [ha]
    exact (canonical23818 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1620 + difference 3 5) (sourceB1620 + difference 5 3) sourceC1620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1620 + difference 3 5) (sourceB1620 + difference 5 3) sourceC1620) = raw23981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1620 sourceB1620 sourceC1620 difference raw23981; decide +kernel
    rw [ha]
    exact (canonical23981 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1620 + difference 4 5) (sourceB1620 + difference 5 4) sourceC1620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3022) := by
    have ha : (tripleCharges (sourceA1620 + difference 4 5) (sourceB1620 + difference 5 4) sourceC1620) = raw23794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1620 sourceB1620 sourceC1620 difference raw23794; decide +kernel
    rw [ha]
    exact (canonical23794 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1620 + difference 5 5) (sourceB1620 + difference 5 5) sourceC1620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1620 + difference 5 5) (sourceB1620 + difference 5 5) sourceC1620) = raw23966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1620 sourceB1620 sourceC1620 difference raw23966; decide +kernel
    rw [ha]
    exact (canonical23966 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1620 + sourceB1620) sourceC1620) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1620 + sourceB1620) sourceC1620) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1620 sourceB1620 sourceC1620 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1620 sourceB1620 sourceC1620
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1620, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1621 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1621 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC1621 : Charge := ![2, -1, 0, -1, 2, -2]
def sourceForm1621 : Integer.Sparse Master := [(Sum.inr 1257, 1), (Sum.inr 2565, 1), (Sum.inr 2629, 1), (Sum.inr 2672, 1), (Sum.inr 2748, 1), (Sum.inr 2760, 1), (Sum.inr 4088, -1)]

theorem sourceEq1621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1621 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1621 + difference 0 0) (sourceB1621 + difference 0 0) sourceC1621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1257) := by
    have ha : (tripleCharges (sourceA1621 + difference 0 0) (sourceB1621 + difference 0 0) sourceC1621) = raw23986 := by
      apply Matrix.ext; unfold tripleCharges sourceA1621 sourceB1621 sourceC1621 difference raw23986; decide +kernel
    rw [ha]
    exact (canonical23986 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1621 + difference 0 1) (sourceB1621 + difference 1 0) sourceC1621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2629) := by
    have ha : (tripleCharges (sourceA1621 + difference 0 1) (sourceB1621 + difference 1 0) sourceC1621) = raw23987 := by
      apply Matrix.ext; unfold tripleCharges sourceA1621 sourceB1621 sourceC1621 difference raw23987; decide +kernel
    rw [ha]
    exact (canonical23987 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1621 + difference 0 2) (sourceB1621 + difference 2 0) sourceC1621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2565) := by
    have ha : (tripleCharges (sourceA1621 + difference 0 2) (sourceB1621 + difference 2 0) sourceC1621) = raw23988 := by
      apply Matrix.ext; unfold tripleCharges sourceA1621 sourceB1621 sourceC1621 difference raw23988; decide +kernel
    rw [ha]
    exact (canonical23988 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1621 + difference 0 3) (sourceB1621 + difference 3 0) sourceC1621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2748) := by
    have ha : (tripleCharges (sourceA1621 + difference 0 3) (sourceB1621 + difference 3 0) sourceC1621) = raw23989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1621 sourceB1621 sourceC1621 difference raw23989; decide +kernel
    rw [ha]
    exact (canonical23989 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1621 + difference 0 4) (sourceB1621 + difference 4 0) sourceC1621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA1621 + difference 0 4) (sourceB1621 + difference 4 0) sourceC1621) = raw23990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1621 sourceB1621 sourceC1621 difference raw23990; decide +kernel
    rw [ha]
    exact (canonical23990 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1621 + difference 0 5) (sourceB1621 + difference 5 0) sourceC1621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2760) := by
    have ha : (tripleCharges (sourceA1621 + difference 0 5) (sourceB1621 + difference 5 0) sourceC1621) = raw23991 := by
      apply Matrix.ext; unfold tripleCharges sourceA1621 sourceB1621 sourceC1621 difference raw23991; decide +kernel
    rw [ha]
    exact (canonical23991 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1621 + sourceB1621) sourceC1621) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1621 + sourceB1621) sourceC1621) = raw23992 := by
      apply Matrix.ext; unfold doubleCharges sourceA1621 sourceB1621 sourceC1621 raw23992; decide +kernel
    rw [ha]
    exact (canonical23992 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1621 sourceB1621 sourceC1621
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1621, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1622 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1622 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC1622 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceForm1622 : Integer.Sparse Master := [(Sum.inr 1130, 1), (Sum.inr 1137, 1), (Sum.inr 1138, 1), (Sum.inr 1141, 1), (Sum.inr 1241, 1), (Sum.inr 2515, 1), (Sum.inr 4092, -1)]

theorem sourceEq1622 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1622 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1622 + difference 0 1) (sourceB1622 + difference 1 0) sourceC1622) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA1622 + difference 0 1) (sourceB1622 + difference 1 0) sourceC1622) = raw6233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1622 sourceB1622 sourceC1622 difference raw6233; decide +kernel
    rw [ha]
    exact (canonical6233 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1622 + difference 1 1) (sourceB1622 + difference 1 1) sourceC1622) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA1622 + difference 1 1) (sourceB1622 + difference 1 1) sourceC1622) = raw6225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1622 sourceB1622 sourceC1622 difference raw6225; decide +kernel
    rw [ha]
    exact (canonical6225 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1622 + difference 2 1) (sourceB1622 + difference 1 2) sourceC1622) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1130) := by
    have ha : (tripleCharges (sourceA1622 + difference 2 1) (sourceB1622 + difference 1 2) sourceC1622) = raw23993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1622 sourceB1622 sourceC1622 difference raw23993; decide +kernel
    rw [ha]
    exact (canonical23993 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1622 + difference 3 1) (sourceB1622 + difference 1 3) sourceC1622) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1141) := by
    have ha : (tripleCharges (sourceA1622 + difference 3 1) (sourceB1622 + difference 1 3) sourceC1622) = raw23994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1622 sourceB1622 sourceC1622 difference raw23994; decide +kernel
    rw [ha]
    exact (canonical23994 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1622 + difference 4 1) (sourceB1622 + difference 1 4) sourceC1622) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA1622 + difference 4 1) (sourceB1622 + difference 1 4) sourceC1622) = raw23995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1622 sourceB1622 sourceC1622 difference raw23995; decide +kernel
    rw [ha]
    exact (canonical23995 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1622 + difference 5 1) (sourceB1622 + difference 1 5) sourceC1622) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1137) := by
    have ha : (tripleCharges (sourceA1622 + difference 5 1) (sourceB1622 + difference 1 5) sourceC1622) = raw23996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1622 sourceB1622 sourceC1622 difference raw23996; decide +kernel
    rw [ha]
    exact (canonical23996 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1622 + sourceB1622) sourceC1622) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1622 + sourceB1622) sourceC1622) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA1622 sourceB1622 sourceC1622 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1622 sourceB1622 sourceC1622
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1622, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1623 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1623 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC1623 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceForm1623 : Integer.Sparse Master := [(Sum.inr 638, 1), (Sum.inr 1156, 1), (Sum.inr 1236, 1), (Sum.inr 1261, 1), (Sum.inr 1291, 1), (Sum.inr 1294, 1), (Sum.inr 4092, -1)]

theorem sourceEq1623 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1623 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1623 + difference 1 0) (sourceB1623 + difference 0 1) sourceC1623) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 638) := by
    have ha : (tripleCharges (sourceA1623 + difference 1 0) (sourceB1623 + difference 0 1) sourceC1623) = raw23997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1623 sourceB1623 sourceC1623 difference raw23997; decide +kernel
    rw [ha]
    exact (canonical23997 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1623 + difference 1 1) (sourceB1623 + difference 1 1) sourceC1623) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1261) := by
    have ha : (tripleCharges (sourceA1623 + difference 1 1) (sourceB1623 + difference 1 1) sourceC1623) = raw9582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1623 sourceB1623 sourceC1623 difference raw9582; decide +kernel
    rw [ha]
    exact (canonical9582 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1623 + difference 1 2) (sourceB1623 + difference 2 1) sourceC1623) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1156) := by
    have ha : (tripleCharges (sourceA1623 + difference 1 2) (sourceB1623 + difference 2 1) sourceC1623) = raw23998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1623 sourceB1623 sourceC1623 difference raw23998; decide +kernel
    rw [ha]
    exact (canonical23998 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1623 + difference 1 3) (sourceB1623 + difference 3 1) sourceC1623) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1623 + difference 1 3) (sourceB1623 + difference 3 1) sourceC1623) = raw9580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1623 sourceB1623 sourceC1623 difference raw9580; decide +kernel
    rw [ha]
    exact (canonical9580 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1623 + difference 1 4) (sourceB1623 + difference 4 1) sourceC1623) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1623 + difference 1 4) (sourceB1623 + difference 4 1) sourceC1623) = raw23999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1623 sourceB1623 sourceC1623 difference raw23999; decide +kernel
    rw [ha]
    exact (canonical23999 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1623 + difference 1 5) (sourceB1623 + difference 5 1) sourceC1623) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA1623 + difference 1 5) (sourceB1623 + difference 5 1) sourceC1623) = raw24000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1623 sourceB1623 sourceC1623 difference raw24000; decide +kernel
    rw [ha]
    exact (canonical24000 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1623 + sourceB1623) sourceC1623) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1623 + sourceB1623) sourceC1623) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA1623 sourceB1623 sourceC1623 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1623 sourceB1623 sourceC1623
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1623, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1624 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1624 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC1624 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1624 : Integer.Sparse Master := [(Sum.inr 1635, 1), (Sum.inr 1637, 1), (Sum.inr 1640, 1), (Sum.inr 1645, 1), (Sum.inr 1707, 1), (Sum.inr 3296, 1), (Sum.inr 4069, -1)]

theorem sourceEq1624 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1624 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1624 + difference 0 0) (sourceB1624 + difference 0 0) sourceC1624) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1624 + difference 0 0) (sourceB1624 + difference 0 0) sourceC1624) = raw23981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1624 sourceB1624 sourceC1624 difference raw23981; decide +kernel
    rw [ha]
    exact (canonical23981 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1624 + difference 0 1) (sourceB1624 + difference 1 0) sourceC1624) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1640) := by
    have ha : (tripleCharges (sourceA1624 + difference 0 1) (sourceB1624 + difference 1 0) sourceC1624) = raw24001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1624 sourceB1624 sourceC1624 difference raw24001; decide +kernel
    rw [ha]
    exact (canonical24001 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1624 + difference 0 2) (sourceB1624 + difference 2 0) sourceC1624) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1635) := by
    have ha : (tripleCharges (sourceA1624 + difference 0 2) (sourceB1624 + difference 2 0) sourceC1624) = raw24002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1624 sourceB1624 sourceC1624 difference raw24002; decide +kernel
    rw [ha]
    exact (canonical24002 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1624 + difference 0 3) (sourceB1624 + difference 3 0) sourceC1624) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1645) := by
    have ha : (tripleCharges (sourceA1624 + difference 0 3) (sourceB1624 + difference 3 0) sourceC1624) = raw23971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1624 sourceB1624 sourceC1624 difference raw23971; decide +kernel
    rw [ha]
    exact (canonical23971 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1624 + difference 0 4) (sourceB1624 + difference 4 0) sourceC1624) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1624 + difference 0 4) (sourceB1624 + difference 4 0) sourceC1624) = raw24003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1624 sourceB1624 sourceC1624 difference raw24003; decide +kernel
    rw [ha]
    exact (canonical24003 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1624 + difference 0 5) (sourceB1624 + difference 5 0) sourceC1624) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1637) := by
    have ha : (tripleCharges (sourceA1624 + difference 0 5) (sourceB1624 + difference 5 0) sourceC1624) = raw24004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1624 sourceB1624 sourceC1624 difference raw24004; decide +kernel
    rw [ha]
    exact (canonical24004 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1624 + sourceB1624) sourceC1624) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1624 + sourceB1624) sourceC1624) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1624 sourceB1624 sourceC1624 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1624 sourceB1624 sourceC1624
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1624, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1625 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1625 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC1625 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1625 : Integer.Sparse Master := [(Sum.inr 1607, 1), (Sum.inr 1610, 1), (Sum.inr 1612, 1), (Sum.inr 1623, 1), (Sum.inr 1739, 1), (Sum.inr 3296, 1), (Sum.inr 4069, -1)]

theorem sourceEq1625 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1625 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1625 + difference 0 0) (sourceB1625 + difference 0 0) sourceC1625) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1625 + difference 0 0) (sourceB1625 + difference 0 0) sourceC1625) = raw23981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1625 sourceB1625 sourceC1625 difference raw23981; decide +kernel
    rw [ha]
    exact (canonical23981 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1625 + difference 1 0) (sourceB1625 + difference 0 1) sourceC1625) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1625 + difference 1 0) (sourceB1625 + difference 0 1) sourceC1625) = raw23802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1625 sourceB1625 sourceC1625 difference raw23802; decide +kernel
    rw [ha]
    exact (canonical23802 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1625 + difference 2 0) (sourceB1625 + difference 0 2) sourceC1625) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1607) := by
    have ha : (tripleCharges (sourceA1625 + difference 2 0) (sourceB1625 + difference 0 2) sourceC1625) = raw23823 := by
      apply Matrix.ext; unfold tripleCharges sourceA1625 sourceB1625 sourceC1625 difference raw23823; decide +kernel
    rw [ha]
    exact (canonical23823 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1625 + difference 3 0) (sourceB1625 + difference 0 3) sourceC1625) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1612) := by
    have ha : (tripleCharges (sourceA1625 + difference 3 0) (sourceB1625 + difference 0 3) sourceC1625) = raw24005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1625 sourceB1625 sourceC1625 difference raw24005; decide +kernel
    rw [ha]
    exact (canonical24005 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1625 + difference 4 0) (sourceB1625 + difference 0 4) sourceC1625) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1610) := by
    have ha : (tripleCharges (sourceA1625 + difference 4 0) (sourceB1625 + difference 0 4) sourceC1625) = raw24006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1625 sourceB1625 sourceC1625 difference raw24006; decide +kernel
    rw [ha]
    exact (canonical24006 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1625 + difference 5 0) (sourceB1625 + difference 0 5) sourceC1625) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1623) := by
    have ha : (tripleCharges (sourceA1625 + difference 5 0) (sourceB1625 + difference 0 5) sourceC1625) = raw23972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1625 sourceB1625 sourceC1625 difference raw23972; decide +kernel
    rw [ha]
    exact (canonical23972 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1625 + sourceB1625) sourceC1625) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1625 + sourceB1625) sourceC1625) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1625 sourceB1625 sourceC1625 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1625 sourceB1625 sourceC1625
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1625, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1626 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1626 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC1626 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1626 : Integer.Sparse Master := [(Sum.inr 1739, 1), (Sum.inr 2737, 1), (Sum.inr 3296, 2), (Sum.inr 3305, 1), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

theorem sourceEq1626 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1626 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1626 + difference 1 0) (sourceB1626 + difference 0 1) sourceC1626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1626 + difference 1 0) (sourceB1626 + difference 0 1) sourceC1626) = raw23802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1626 sourceB1626 sourceC1626 difference raw23802; decide +kernel
    rw [ha]
    exact (canonical23802 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1626 + difference 1 1) (sourceB1626 + difference 1 1) sourceC1626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1626 + difference 1 1) (sourceB1626 + difference 1 1) sourceC1626) = raw23981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1626 sourceB1626 sourceC1626 difference raw23981; decide +kernel
    rw [ha]
    exact (canonical23981 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1626 + difference 1 2) (sourceB1626 + difference 2 1) sourceC1626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1626 + difference 1 2) (sourceB1626 + difference 2 1) sourceC1626) = raw24007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1626 sourceB1626 sourceC1626 difference raw24007; decide +kernel
    rw [ha]
    exact (canonical24007 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1626 + difference 1 3) (sourceB1626 + difference 3 1) sourceC1626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1626 + difference 1 3) (sourceB1626 + difference 3 1) sourceC1626) = raw23797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1626 sourceB1626 sourceC1626 difference raw23797; decide +kernel
    rw [ha]
    exact (canonical23797 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1626 + difference 1 4) (sourceB1626 + difference 4 1) sourceC1626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3308) := by
    have ha : (tripleCharges (sourceA1626 + difference 1 4) (sourceB1626 + difference 4 1) sourceC1626) = raw24008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1626 sourceB1626 sourceC1626 difference raw24008; decide +kernel
    rw [ha]
    exact (canonical24008 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1626 + difference 1 5) (sourceB1626 + difference 5 1) sourceC1626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1626 + difference 1 5) (sourceB1626 + difference 5 1) sourceC1626) = raw24009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1626 sourceB1626 sourceC1626 difference raw24009; decide +kernel
    rw [ha]
    exact (canonical24009 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1626 + sourceB1626) sourceC1626) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1626 + sourceB1626) sourceC1626) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1626 sourceB1626 sourceC1626 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1626 sourceB1626 sourceC1626
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1626, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1627 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1627 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC1627 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceForm1627 : Integer.Sparse Master := [(Sum.inr 1707, 1), (Sum.inr 3288, 1), (Sum.inr 3296, 2), (Sum.inr 3299, 1), (Sum.inr 3308, 1), (Sum.inr 4069, -1)]

theorem sourceEq1627 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1627 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1627 + difference 0 4) (sourceB1627 + difference 4 0) sourceC1627) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1627 + difference 0 4) (sourceB1627 + difference 4 0) sourceC1627) = raw24003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1627 sourceB1627 sourceC1627 difference raw24003; decide +kernel
    rw [ha]
    exact (canonical24003 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1627 + difference 1 4) (sourceB1627 + difference 4 1) sourceC1627) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3308) := by
    have ha : (tripleCharges (sourceA1627 + difference 1 4) (sourceB1627 + difference 4 1) sourceC1627) = raw24008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1627 sourceB1627 sourceC1627 difference raw24008; decide +kernel
    rw [ha]
    exact (canonical24008 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1627 + difference 2 4) (sourceB1627 + difference 4 2) sourceC1627) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1627 + difference 2 4) (sourceB1627 + difference 4 2) sourceC1627) = raw24010 := by
      apply Matrix.ext; unfold tripleCharges sourceA1627 sourceB1627 sourceC1627 difference raw24010; decide +kernel
    rw [ha]
    exact (canonical24010 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1627 + difference 3 4) (sourceB1627 + difference 4 3) sourceC1627) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1627 + difference 3 4) (sourceB1627 + difference 4 3) sourceC1627) = raw24011 := by
      apply Matrix.ext; unfold tripleCharges sourceA1627 sourceB1627 sourceC1627 difference raw24011; decide +kernel
    rw [ha]
    exact (canonical24011 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1627 + difference 4 4) (sourceB1627 + difference 4 4) sourceC1627) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1627 + difference 4 4) (sourceB1627 + difference 4 4) sourceC1627) = raw23981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1627 sourceB1627 sourceC1627 difference raw23981; decide +kernel
    rw [ha]
    exact (canonical23981 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1627 + difference 5 4) (sourceB1627 + difference 4 5) sourceC1627) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1627 + difference 5 4) (sourceB1627 + difference 4 5) sourceC1627) = raw23980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1627 sourceB1627 sourceC1627 difference raw23980; decide +kernel
    rw [ha]
    exact (canonical23980 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1627 + sourceB1627) sourceC1627) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1627 + sourceB1627) sourceC1627) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1627 sourceB1627 sourceC1627 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1627 sourceB1627 sourceC1627
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1627, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1628 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1628 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC1628 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceForm1628 : Integer.Sparse Master := [(Sum.inr 1111, 1), (Sum.inr 1113, 2), (Sum.inr 1126, 1), (Sum.inr 1212, 1), (Sum.inr 2479, 1), (Sum.inr 4092, -1)]

theorem sourceEq1628 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1628 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1628 + difference 0 1) (sourceB1628 + difference 1 0) sourceC1628) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2479) := by
    have ha : (tripleCharges (sourceA1628 + difference 0 1) (sourceB1628 + difference 1 0) sourceC1628) = raw11653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1628 sourceB1628 sourceC1628 difference raw11653; decide +kernel
    rw [ha]
    exact (canonical11653 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1628 + difference 1 1) (sourceB1628 + difference 1 1) sourceC1628) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1212) := by
    have ha : (tripleCharges (sourceA1628 + difference 1 1) (sourceB1628 + difference 1 1) sourceC1628) = raw11645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1628 sourceB1628 sourceC1628 difference raw11645; decide +kernel
    rw [ha]
    exact (canonical11645 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1628 + difference 2 1) (sourceB1628 + difference 1 2) sourceC1628) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1126) := by
    have ha : (tripleCharges (sourceA1628 + difference 2 1) (sourceB1628 + difference 1 2) sourceC1628) = raw24012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1628 sourceB1628 sourceC1628 difference raw24012; decide +kernel
    rw [ha]
    exact (canonical24012 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1628 + difference 3 1) (sourceB1628 + difference 1 3) sourceC1628) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1113) := by
    have ha : (tripleCharges (sourceA1628 + difference 3 1) (sourceB1628 + difference 1 3) sourceC1628) = raw24013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1628 sourceB1628 sourceC1628 difference raw24013; decide +kernel
    rw [ha]
    exact (canonical24013 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1628 + difference 4 1) (sourceB1628 + difference 1 4) sourceC1628) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1113) := by
    have ha : (tripleCharges (sourceA1628 + difference 4 1) (sourceB1628 + difference 1 4) sourceC1628) = raw24014 := by
      apply Matrix.ext; unfold tripleCharges sourceA1628 sourceB1628 sourceC1628 difference raw24014; decide +kernel
    rw [ha]
    exact (canonical24014 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1628 + difference 5 1) (sourceB1628 + difference 1 5) sourceC1628) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1111) := by
    have ha : (tripleCharges (sourceA1628 + difference 5 1) (sourceB1628 + difference 1 5) sourceC1628) = raw24015 := by
      apply Matrix.ext; unfold tripleCharges sourceA1628 sourceB1628 sourceC1628 difference raw24015; decide +kernel
    rw [ha]
    exact (canonical24015 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1628 + sourceB1628) sourceC1628) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1628 + sourceB1628) sourceC1628) = raw11640 := by
      apply Matrix.ext; unfold doubleCharges sourceA1628 sourceB1628 sourceC1628 raw11640; decide +kernel
    rw [ha]
    exact (canonical11640 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1628 sourceB1628 sourceC1628
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1628, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1629 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1629 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceC1629 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceForm1629 : Integer.Sparse Master := [(Sum.inr 623, 1), (Sum.inr 1126, 1), (Sum.inr 1212, 1), (Sum.inr 1233, 1), (Sum.inr 1236, 2), (Sum.inr 4092, -1)]

theorem sourceEq1629 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1629 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1629 + difference 2 0) (sourceB1629 + difference 0 2) sourceC1629) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 623) := by
    have ha : (tripleCharges (sourceA1629 + difference 2 0) (sourceB1629 + difference 0 2) sourceC1629) = raw24016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1629 sourceB1629 sourceC1629 difference raw24016; decide +kernel
    rw [ha]
    exact (canonical24016 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1629 + difference 2 1) (sourceB1629 + difference 1 2) sourceC1629) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1126) := by
    have ha : (tripleCharges (sourceA1629 + difference 2 1) (sourceB1629 + difference 1 2) sourceC1629) = raw24012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1629 sourceB1629 sourceC1629 difference raw24012; decide +kernel
    rw [ha]
    exact (canonical24012 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1629 + difference 2 2) (sourceB1629 + difference 2 2) sourceC1629) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1212) := by
    have ha : (tripleCharges (sourceA1629 + difference 2 2) (sourceB1629 + difference 2 2) sourceC1629) = raw11645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1629 sourceB1629 sourceC1629 difference raw11645; decide +kernel
    rw [ha]
    exact (canonical11645 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1629 + difference 2 3) (sourceB1629 + difference 3 2) sourceC1629) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1629 + difference 2 3) (sourceB1629 + difference 3 2) sourceC1629) = raw24017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1629 sourceB1629 sourceC1629 difference raw24017; decide +kernel
    rw [ha]
    exact (canonical24017 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1629 + difference 2 4) (sourceB1629 + difference 4 2) sourceC1629) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1629 + difference 2 4) (sourceB1629 + difference 4 2) sourceC1629) = raw24018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1629 sourceB1629 sourceC1629 difference raw24018; decide +kernel
    rw [ha]
    exact (canonical24018 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1629 + difference 2 5) (sourceB1629 + difference 5 2) sourceC1629) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA1629 + difference 2 5) (sourceB1629 + difference 5 2) sourceC1629) = raw11642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1629 sourceB1629 sourceC1629 difference raw11642; decide +kernel
    rw [ha]
    exact (canonical11642 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1629 + sourceB1629) sourceC1629) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1629 + sourceB1629) sourceC1629) = raw11640 := by
      apply Matrix.ext; unfold doubleCharges sourceA1629 sourceB1629 sourceC1629 raw11640; decide +kernel
    rw [ha]
    exact (canonical11640 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1629 sourceB1629 sourceC1629
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1629, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1630 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1630 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC1630 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceForm1630 : Integer.Sparse Master := [(Sum.inr 629, 1), (Sum.inr 1135, 1), (Sum.inr 1216, 3), (Sum.inr 1235, 1), (Sum.inr 4091, -1)]

theorem sourceEq1630 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1630 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1630 + difference 1 0) (sourceB1630 + difference 0 1) sourceC1630) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 629) := by
    have ha : (tripleCharges (sourceA1630 + difference 1 0) (sourceB1630 + difference 0 1) sourceC1630) = raw24019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1630 sourceB1630 sourceC1630 difference raw24019; decide +kernel
    rw [ha]
    exact (canonical24019 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1630 + difference 1 1) (sourceB1630 + difference 1 1) sourceC1630) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA1630 + difference 1 1) (sourceB1630 + difference 1 1) sourceC1630) = raw24020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1630 sourceB1630 sourceC1630 difference raw24020; decide +kernel
    rw [ha]
    exact (canonical24020 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1630 + difference 1 2) (sourceB1630 + difference 2 1) sourceC1630) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1135) := by
    have ha : (tripleCharges (sourceA1630 + difference 1 2) (sourceB1630 + difference 2 1) sourceC1630) = raw24021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1630 sourceB1630 sourceC1630 difference raw24021; decide +kernel
    rw [ha]
    exact (canonical24021 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1630 + difference 1 3) (sourceB1630 + difference 3 1) sourceC1630) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA1630 + difference 1 3) (sourceB1630 + difference 3 1) sourceC1630) = raw24022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1630 sourceB1630 sourceC1630 difference raw24022; decide +kernel
    rw [ha]
    exact (canonical24022 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1630 + difference 1 4) (sourceB1630 + difference 4 1) sourceC1630) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA1630 + difference 1 4) (sourceB1630 + difference 4 1) sourceC1630) = raw24023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1630 sourceB1630 sourceC1630 difference raw24023; decide +kernel
    rw [ha]
    exact (canonical24023 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1630 + difference 1 5) (sourceB1630 + difference 5 1) sourceC1630) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA1630 + difference 1 5) (sourceB1630 + difference 5 1) sourceC1630) = raw13763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1630 sourceB1630 sourceC1630 difference raw13763; decide +kernel
    rw [ha]
    exact (canonical13763 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1630 + sourceB1630) sourceC1630) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1630 + sourceB1630) sourceC1630) = raw13769 := by
      apply Matrix.ext; unfold doubleCharges sourceA1630 sourceB1630 sourceC1630 raw13769; decide +kernel
    rw [ha]
    exact (canonical13769 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1630 sourceB1630 sourceC1630
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1630, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1631 : Charge := ![-4, 0, 0, 1, 1, 2]
def sourceB1631 : Charge := ![2, 1, -1, 0, 0, -2]
def sourceC1631 : Charge := ![2, -1, 1, -1, -1, 0]
def sourceForm1631 : Integer.Sparse Master := [(Sum.inr 1116, 1), (Sum.inr 1117, 2), (Sum.inr 1135, 1), (Sum.inr 1216, 1), (Sum.inr 2483, 1), (Sum.inr 4091, -1)]

theorem sourceEq1631 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1631 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1631 + difference 0 2) (sourceB1631 + difference 2 0) sourceC1631) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA1631 + difference 0 2) (sourceB1631 + difference 2 0) sourceC1631) = raw24024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1631 sourceB1631 sourceC1631 difference raw24024; decide +kernel
    rw [ha]
    exact (canonical24024 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1631 + difference 1 2) (sourceB1631 + difference 2 1) sourceC1631) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1135) := by
    have ha : (tripleCharges (sourceA1631 + difference 1 2) (sourceB1631 + difference 2 1) sourceC1631) = raw24021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1631 sourceB1631 sourceC1631 difference raw24021; decide +kernel
    rw [ha]
    exact (canonical24021 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1631 + difference 2 2) (sourceB1631 + difference 2 2) sourceC1631) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA1631 + difference 2 2) (sourceB1631 + difference 2 2) sourceC1631) = raw24020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1631 sourceB1631 sourceC1631 difference raw24020; decide +kernel
    rw [ha]
    exact (canonical24020 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1631 + difference 3 2) (sourceB1631 + difference 2 3) sourceC1631) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1117) := by
    have ha : (tripleCharges (sourceA1631 + difference 3 2) (sourceB1631 + difference 2 3) sourceC1631) = raw24025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1631 sourceB1631 sourceC1631 difference raw24025; decide +kernel
    rw [ha]
    exact (canonical24025 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1631 + difference 4 2) (sourceB1631 + difference 2 4) sourceC1631) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1117) := by
    have ha : (tripleCharges (sourceA1631 + difference 4 2) (sourceB1631 + difference 2 4) sourceC1631) = raw24026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1631 sourceB1631 sourceC1631 difference raw24026; decide +kernel
    rw [ha]
    exact (canonical24026 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1631 + difference 5 2) (sourceB1631 + difference 2 5) sourceC1631) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1116) := by
    have ha : (tripleCharges (sourceA1631 + difference 5 2) (sourceB1631 + difference 2 5) sourceC1631) = raw24027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1631 sourceB1631 sourceC1631 difference raw24027; decide +kernel
    rw [ha]
    exact (canonical24027 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1631 + sourceB1631) sourceC1631) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1631 + sourceB1631) sourceC1631) = raw13769 := by
      apply Matrix.ext; unfold doubleCharges sourceA1631 sourceB1631 sourceC1631 raw13769; decide +kernel
    rw [ha]
    exact (canonical13769 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1631 sourceB1631 sourceC1631
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1631, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
