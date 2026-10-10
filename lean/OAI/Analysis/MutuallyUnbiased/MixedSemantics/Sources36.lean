import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical151
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical152
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical153
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical154
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical155

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1152 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1152 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceC1152 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceForm1152 : Integer.Sparse Master := [(Sum.inr 633, 1), (Sum.inr 1115, 2), (Sum.inr 1140, 1), (Sum.inr 1221, 1), (Sum.inr 1242, 1), (Sum.inr 4092, -1)]

theorem sourceEq1152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1152 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1152 + difference 0 1) (sourceB1152 + difference 1 0) sourceC1152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1152 + difference 0 1) (sourceB1152 + difference 1 0) sourceC1152) = raw19466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1152 sourceB1152 sourceC1152 difference raw19466; decide +kernel
    rw [ha]
    exact (canonical19466 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1152 + difference 1 1) (sourceB1152 + difference 1 1) sourceC1152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1152 + difference 1 1) (sourceB1152 + difference 1 1) sourceC1152) = raw19467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1152 sourceB1152 sourceC1152 difference raw19467; decide +kernel
    rw [ha]
    exact (canonical19467 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1152 + difference 2 1) (sourceB1152 + difference 1 2) sourceC1152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1115) := by
    have ha : (tripleCharges (sourceA1152 + difference 2 1) (sourceB1152 + difference 1 2) sourceC1152) = raw19468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1152 sourceB1152 sourceC1152 difference raw19468; decide +kernel
    rw [ha]
    exact (canonical19468 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1152 + difference 3 1) (sourceB1152 + difference 1 3) sourceC1152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1115) := by
    have ha : (tripleCharges (sourceA1152 + difference 3 1) (sourceB1152 + difference 1 3) sourceC1152) = raw19469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1152 sourceB1152 sourceC1152 difference raw19469; decide +kernel
    rw [ha]
    exact (canonical19469 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1152 + difference 4 1) (sourceB1152 + difference 1 4) sourceC1152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1152 + difference 4 1) (sourceB1152 + difference 1 4) sourceC1152) = raw19470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1152 sourceB1152 sourceC1152 difference raw19470; decide +kernel
    rw [ha]
    exact (canonical19470 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1152 + difference 5 1) (sourceB1152 + difference 1 5) sourceC1152) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 633) := by
    have ha : (tripleCharges (sourceA1152 + difference 5 1) (sourceB1152 + difference 1 5) sourceC1152) = raw19471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1152 sourceB1152 sourceC1152 difference raw19471; decide +kernel
    rw [ha]
    exact (canonical19471 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1152 + sourceB1152) sourceC1152) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1152 + sourceB1152) sourceC1152) = raw19472 := by
      apply Matrix.ext; unfold doubleCharges sourceA1152 sourceB1152 sourceC1152 raw19472; decide +kernel
    rw [ha]
    exact (canonical19472 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1152 sourceB1152 sourceC1152
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1152, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1153 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1153 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1153 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1153 : Integer.Sparse Master := [(Sum.inr 1615, 2), (Sum.inr 1620, 1), (Sum.inr 1629, 1), (Sum.inr 1752, 1), (Sum.inr 3298, 1), (Sum.inr 4072, -1)]

theorem sourceEq1153 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1153 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1153 + difference 0 0) (sourceB1153 + difference 0 0) sourceC1153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3298) := by
    have ha : (tripleCharges (sourceA1153 + difference 0 0) (sourceB1153 + difference 0 0) sourceC1153) = raw19473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1153 sourceB1153 sourceC1153 difference raw19473; decide +kernel
    rw [ha]
    exact (canonical19473 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1153 + difference 0 1) (sourceB1153 + difference 1 0) sourceC1153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1629) := by
    have ha : (tripleCharges (sourceA1153 + difference 0 1) (sourceB1153 + difference 1 0) sourceC1153) = raw19474 := by
      apply Matrix.ext; unfold tripleCharges sourceA1153 sourceB1153 sourceC1153 difference raw19474; decide +kernel
    rw [ha]
    exact (canonical19474 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1153 + difference 0 2) (sourceB1153 + difference 2 0) sourceC1153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1615) := by
    have ha : (tripleCharges (sourceA1153 + difference 0 2) (sourceB1153 + difference 2 0) sourceC1153) = raw19475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1153 sourceB1153 sourceC1153 difference raw19475; decide +kernel
    rw [ha]
    exact (canonical19475 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1153 + difference 0 3) (sourceB1153 + difference 3 0) sourceC1153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1615) := by
    have ha : (tripleCharges (sourceA1153 + difference 0 3) (sourceB1153 + difference 3 0) sourceC1153) = raw19476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1153 sourceB1153 sourceC1153 difference raw19476; decide +kernel
    rw [ha]
    exact (canonical19476 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1153 + difference 0 4) (sourceB1153 + difference 4 0) sourceC1153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1153 + difference 0 4) (sourceB1153 + difference 4 0) sourceC1153) = raw19477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1153 sourceB1153 sourceC1153 difference raw19477; decide +kernel
    rw [ha]
    exact (canonical19477 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1153 + difference 0 5) (sourceB1153 + difference 5 0) sourceC1153) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1620) := by
    have ha : (tripleCharges (sourceA1153 + difference 0 5) (sourceB1153 + difference 5 0) sourceC1153) = raw19478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1153 sourceB1153 sourceC1153 difference raw19478; decide +kernel
    rw [ha]
    exact (canonical19478 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1153 + sourceB1153) sourceC1153) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1153 + sourceB1153) sourceC1153) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1153 sourceB1153 sourceC1153 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1153 sourceB1153 sourceC1153
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1153, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1154 : Charge := ![2, -1, 0, 0, 1, -2]
def sourceB1154 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1154 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1154 : Integer.Sparse Master := [(Sum.inr 1752, 2), (Sum.inr 3298, 3), (Sum.inr 3313, 1), (Sum.inr 4072, -1)]

theorem sourceEq1154 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1154 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1154 + difference 1 0) (sourceB1154 + difference 0 1) sourceC1154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1154 + difference 1 0) (sourceB1154 + difference 0 1) sourceC1154) = raw19429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1154 sourceB1154 sourceC1154 difference raw19429; decide +kernel
    rw [ha]
    exact (canonical19429 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1154 + difference 1 1) (sourceB1154 + difference 1 1) sourceC1154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3298) := by
    have ha : (tripleCharges (sourceA1154 + difference 1 1) (sourceB1154 + difference 1 1) sourceC1154) = raw19473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1154 sourceB1154 sourceC1154 difference raw19473; decide +kernel
    rw [ha]
    exact (canonical19473 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1154 + difference 1 2) (sourceB1154 + difference 2 1) sourceC1154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3298) := by
    have ha : (tripleCharges (sourceA1154 + difference 1 2) (sourceB1154 + difference 2 1) sourceC1154) = raw19479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1154 sourceB1154 sourceC1154 difference raw19479; decide +kernel
    rw [ha]
    exact (canonical19479 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1154 + difference 1 3) (sourceB1154 + difference 3 1) sourceC1154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3298) := by
    have ha : (tripleCharges (sourceA1154 + difference 1 3) (sourceB1154 + difference 3 1) sourceC1154) = raw19480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1154 sourceB1154 sourceC1154 difference raw19480; decide +kernel
    rw [ha]
    exact (canonical19480 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1154 + difference 1 4) (sourceB1154 + difference 4 1) sourceC1154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3313) := by
    have ha : (tripleCharges (sourceA1154 + difference 1 4) (sourceB1154 + difference 4 1) sourceC1154) = raw19481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1154 sourceB1154 sourceC1154 difference raw19481; decide +kernel
    rw [ha]
    exact (canonical19481 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1154 + difference 1 5) (sourceB1154 + difference 5 1) sourceC1154) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1154 + difference 1 5) (sourceB1154 + difference 5 1) sourceC1154) = raw19418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1154 sourceB1154 sourceC1154 difference raw19418; decide +kernel
    rw [ha]
    exact (canonical19418 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1154 + sourceB1154) sourceC1154) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1154 + sourceB1154) sourceC1154) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1154 sourceB1154 sourceC1154 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1154 sourceB1154 sourceC1154
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1154, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1155 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1155 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1155 : Charge := ![2, -1, 0, 0, 2, -3]
def sourceForm1155 : Integer.Sparse Master := [(Sum.inr 989, 2), (Sum.inr 994, 1), (Sum.inr 1009, 1), (Sum.inr 1055, 1), (Sum.inr 2218, 1), (Sum.inr 4082, -1)]

theorem sourceEq1155 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1155 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1155 + difference 0 0) (sourceB1155 + difference 0 0) sourceC1155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 994) := by
    have ha : (tripleCharges (sourceA1155 + difference 0 0) (sourceB1155 + difference 0 0) sourceC1155) = raw19482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1155 sourceB1155 sourceC1155 difference raw19482; decide +kernel
    rw [ha]
    exact (canonical19482 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1155 + difference 0 1) (sourceB1155 + difference 1 0) sourceC1155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1055) := by
    have ha : (tripleCharges (sourceA1155 + difference 0 1) (sourceB1155 + difference 1 0) sourceC1155) = raw19483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1155 sourceB1155 sourceC1155 difference raw19483; decide +kernel
    rw [ha]
    exact (canonical19483 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1155 + difference 0 2) (sourceB1155 + difference 2 0) sourceC1155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 989) := by
    have ha : (tripleCharges (sourceA1155 + difference 0 2) (sourceB1155 + difference 2 0) sourceC1155) = raw19484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1155 sourceB1155 sourceC1155 difference raw19484; decide +kernel
    rw [ha]
    exact (canonical19484 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1155 + difference 0 3) (sourceB1155 + difference 3 0) sourceC1155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 989) := by
    have ha : (tripleCharges (sourceA1155 + difference 0 3) (sourceB1155 + difference 3 0) sourceC1155) = raw19485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1155 sourceB1155 sourceC1155 difference raw19485; decide +kernel
    rw [ha]
    exact (canonical19485 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1155 + difference 0 4) (sourceB1155 + difference 4 0) sourceC1155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1009) := by
    have ha : (tripleCharges (sourceA1155 + difference 0 4) (sourceB1155 + difference 4 0) sourceC1155) = raw19486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1155 sourceB1155 sourceC1155 difference raw19486; decide +kernel
    rw [ha]
    exact (canonical19486 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1155 + difference 0 5) (sourceB1155 + difference 5 0) sourceC1155) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1155 + difference 0 5) (sourceB1155 + difference 5 0) sourceC1155) = raw19487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1155 sourceB1155 sourceC1155 difference raw19487; decide +kernel
    rw [ha]
    exact (canonical19487 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1155 + sourceB1155) sourceC1155) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1155 + sourceB1155) sourceC1155) = raw19488 := by
      apply Matrix.ext; unfold doubleCharges sourceA1155 sourceB1155 sourceC1155 raw19488; decide +kernel
    rw [ha]
    exact (canonical19488 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1155 sourceB1155 sourceC1155
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1155, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1156 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1156 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC1156 : Charge := ![2, -1, 0, 0, 2, -3]
def sourceForm1156 : Integer.Sparse Master := [(Sum.inr 994, 1), (Sum.inr 1179, 2), (Sum.inr 1190, 1), (Sum.inr 1258, 1), (Sum.inr 2218, 1), (Sum.inr 4082, -1)]

theorem sourceEq1156 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1156 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1156 + difference 0 5) (sourceB1156 + difference 5 0) sourceC1156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1156 + difference 0 5) (sourceB1156 + difference 5 0) sourceC1156) = raw19487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1156 sourceB1156 sourceC1156 difference raw19487; decide +kernel
    rw [ha]
    exact (canonical19487 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1156 + difference 1 5) (sourceB1156 + difference 5 1) sourceC1156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA1156 + difference 1 5) (sourceB1156 + difference 5 1) sourceC1156) = raw19489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1156 sourceB1156 sourceC1156 difference raw19489; decide +kernel
    rw [ha]
    exact (canonical19489 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1156 + difference 2 5) (sourceB1156 + difference 5 2) sourceC1156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1179) := by
    have ha : (tripleCharges (sourceA1156 + difference 2 5) (sourceB1156 + difference 5 2) sourceC1156) = raw19490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1156 sourceB1156 sourceC1156 difference raw19490; decide +kernel
    rw [ha]
    exact (canonical19490 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1156 + difference 3 5) (sourceB1156 + difference 5 3) sourceC1156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1179) := by
    have ha : (tripleCharges (sourceA1156 + difference 3 5) (sourceB1156 + difference 5 3) sourceC1156) = raw19491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1156 sourceB1156 sourceC1156 difference raw19491; decide +kernel
    rw [ha]
    exact (canonical19491 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1156 + difference 4 5) (sourceB1156 + difference 5 4) sourceC1156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1258) := by
    have ha : (tripleCharges (sourceA1156 + difference 4 5) (sourceB1156 + difference 5 4) sourceC1156) = raw19492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1156 sourceB1156 sourceC1156 difference raw19492; decide +kernel
    rw [ha]
    exact (canonical19492 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1156 + difference 5 5) (sourceB1156 + difference 5 5) sourceC1156) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 994) := by
    have ha : (tripleCharges (sourceA1156 + difference 5 5) (sourceB1156 + difference 5 5) sourceC1156) = raw19482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1156 sourceB1156 sourceC1156 difference raw19482; decide +kernel
    rw [ha]
    exact (canonical19482 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1156 + sourceB1156) sourceC1156) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1156 + sourceB1156) sourceC1156) = raw19488 := by
      apply Matrix.ext; unfold doubleCharges sourceA1156 sourceB1156 sourceC1156 raw19488; decide +kernel
    rw [ha]
    exact (canonical19488 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1156 sourceB1156 sourceC1156
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1156, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1157 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1157 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC1157 : Charge := ![2, -1, 0, 1, 1, -3]
def sourceForm1157 : Integer.Sparse Master := [(Sum.inr 971, 1), (Sum.inr 975, 1), (Sum.inr 982, 2), (Sum.inr 1019, 1), (Sum.inr 2193, 1), (Sum.inr 4080, -1)]

theorem sourceEq1157 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1157 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1157 + difference 0 0) (sourceB1157 + difference 0 0) sourceC1157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 975) := by
    have ha : (tripleCharges (sourceA1157 + difference 0 0) (sourceB1157 + difference 0 0) sourceC1157) = raw19493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1157 sourceB1157 sourceC1157 difference raw19493; decide +kernel
    rw [ha]
    exact (canonical19493 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1157 + difference 0 1) (sourceB1157 + difference 1 0) sourceC1157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1019) := by
    have ha : (tripleCharges (sourceA1157 + difference 0 1) (sourceB1157 + difference 1 0) sourceC1157) = raw19494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1157 sourceB1157 sourceC1157 difference raw19494; decide +kernel
    rw [ha]
    exact (canonical19494 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1157 + difference 0 2) (sourceB1157 + difference 2 0) sourceC1157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 971) := by
    have ha : (tripleCharges (sourceA1157 + difference 0 2) (sourceB1157 + difference 2 0) sourceC1157) = raw19495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1157 sourceB1157 sourceC1157 difference raw19495; decide +kernel
    rw [ha]
    exact (canonical19495 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1157 + difference 0 3) (sourceB1157 + difference 3 0) sourceC1157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1157 + difference 0 3) (sourceB1157 + difference 3 0) sourceC1157) = raw19496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1157 sourceB1157 sourceC1157 difference raw19496; decide +kernel
    rw [ha]
    exact (canonical19496 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1157 + difference 0 4) (sourceB1157 + difference 4 0) sourceC1157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 982) := by
    have ha : (tripleCharges (sourceA1157 + difference 0 4) (sourceB1157 + difference 4 0) sourceC1157) = raw19497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1157 sourceB1157 sourceC1157 difference raw19497; decide +kernel
    rw [ha]
    exact (canonical19497 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1157 + difference 0 5) (sourceB1157 + difference 5 0) sourceC1157) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1157 + difference 0 5) (sourceB1157 + difference 5 0) sourceC1157) = raw19498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1157 sourceB1157 sourceC1157 difference raw19498; decide +kernel
    rw [ha]
    exact (canonical19498 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1157 + sourceB1157) sourceC1157) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1157 + sourceB1157) sourceC1157) = raw19499 := by
      apply Matrix.ext; unfold doubleCharges sourceA1157 sourceB1157 sourceC1157 raw19499; decide +kernel
    rw [ha]
    exact (canonical19499 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1157 sourceB1157 sourceC1157
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1157, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1158 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1158 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC1158 : Charge := ![2, -1, 0, 1, 1, -3]
def sourceForm1158 : Integer.Sparse Master := [(Sum.inr 975, 1), (Sum.inr 1194, 1), (Sum.inr 1202, 1), (Sum.inr 1211, 2), (Sum.inr 2193, 1), (Sum.inr 4080, -1)]

theorem sourceEq1158 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1158 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1158 + difference 0 5) (sourceB1158 + difference 5 0) sourceC1158) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2193) := by
    have ha : (tripleCharges (sourceA1158 + difference 0 5) (sourceB1158 + difference 5 0) sourceC1158) = raw19498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1158 sourceB1158 sourceC1158 difference raw19498; decide +kernel
    rw [ha]
    exact (canonical19498 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1158 + difference 1 5) (sourceB1158 + difference 5 1) sourceC1158) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1202) := by
    have ha : (tripleCharges (sourceA1158 + difference 1 5) (sourceB1158 + difference 5 1) sourceC1158) = raw19500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1158 sourceB1158 sourceC1158 difference raw19500; decide +kernel
    rw [ha]
    exact (canonical19500 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1158 + difference 2 5) (sourceB1158 + difference 5 2) sourceC1158) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1194) := by
    have ha : (tripleCharges (sourceA1158 + difference 2 5) (sourceB1158 + difference 5 2) sourceC1158) = raw19501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1158 sourceB1158 sourceC1158 difference raw19501; decide +kernel
    rw [ha]
    exact (canonical19501 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1158 + difference 3 5) (sourceB1158 + difference 5 3) sourceC1158) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1211) := by
    have ha : (tripleCharges (sourceA1158 + difference 3 5) (sourceB1158 + difference 5 3) sourceC1158) = raw19502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1158 sourceB1158 sourceC1158 difference raw19502; decide +kernel
    rw [ha]
    exact (canonical19502 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1158 + difference 4 5) (sourceB1158 + difference 5 4) sourceC1158) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1211) := by
    have ha : (tripleCharges (sourceA1158 + difference 4 5) (sourceB1158 + difference 5 4) sourceC1158) = raw19503 := by
      apply Matrix.ext; unfold tripleCharges sourceA1158 sourceB1158 sourceC1158 difference raw19503; decide +kernel
    rw [ha]
    exact (canonical19503 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1158 + difference 5 5) (sourceB1158 + difference 5 5) sourceC1158) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 975) := by
    have ha : (tripleCharges (sourceA1158 + difference 5 5) (sourceB1158 + difference 5 5) sourceC1158) = raw19493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1158 sourceB1158 sourceC1158 difference raw19493; decide +kernel
    rw [ha]
    exact (canonical19493 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1158 + sourceB1158) sourceC1158) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1158 + sourceB1158) sourceC1158) = raw19499 := by
      apply Matrix.ext; unfold doubleCharges sourceA1158 sourceB1158 sourceC1158 raw19499; decide +kernel
    rw [ha]
    exact (canonical19499 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1158 sourceB1158 sourceC1158
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1158, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1159 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1159 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1159 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm1159 : Integer.Sparse Master := [(Sum.inr 4187, 8), (Sum.inr 4194, 1), (Sum.inr 4555, 12), (Sum.inr 4625, 8), (Sum.inr 5312, 1)]

theorem sourceEq1159 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1159 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1159 + difference 0 1) (sourceB1159 + difference 1 0) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1159 + difference 0 1) (sourceB1159 + difference 1 0) sourceC1159) = raw5084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw5084; decide +kernel
    rw [ha]
    exact (canonical5084 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1159 + difference 0 2) (sourceB1159 + difference 2 0) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1159 + difference 0 2) (sourceB1159 + difference 2 0) sourceC1159) = raw5085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw5085; decide +kernel
    rw [ha]
    exact (canonical5085 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1159 + difference 0 3) (sourceB1159 + difference 3 0) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1159 + difference 0 3) (sourceB1159 + difference 3 0) sourceC1159) = raw5086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw5086; decide +kernel
    rw [ha]
    exact (canonical5086 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1159 + difference 0 4) (sourceB1159 + difference 4 0) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1159 + difference 0 4) (sourceB1159 + difference 4 0) sourceC1159) = raw5087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw5087; decide +kernel
    rw [ha]
    exact (canonical5087 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1159 + difference 0 5) (sourceB1159 + difference 5 0) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5312) := by
    have ha : (tripleCharges (sourceA1159 + difference 0 5) (sourceB1159 + difference 5 0) sourceC1159) = raw10237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw10237; decide +kernel
    rw [ha]
    exact (canonical10237 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1159 + difference 1 0) (sourceB1159 + difference 0 1) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4187) := by
    have ha : (tripleCharges (sourceA1159 + difference 1 0) (sourceB1159 + difference 0 1) sourceC1159) = raw19504 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19504; decide +kernel
    rw [ha]
    exact (canonical19504 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1159 + difference 1 2) (sourceB1159 + difference 2 1) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4555) := by
    have ha : (tripleCharges (sourceA1159 + difference 1 2) (sourceB1159 + difference 2 1) sourceC1159) = raw19505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19505; decide +kernel
    rw [ha]
    exact (canonical19505 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1159 + difference 1 3) (sourceB1159 + difference 3 1) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4555) := by
    have ha : (tripleCharges (sourceA1159 + difference 1 3) (sourceB1159 + difference 3 1) sourceC1159) = raw19506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19506; decide +kernel
    rw [ha]
    exact (canonical19506 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1159 + difference 1 4) (sourceB1159 + difference 4 1) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4555) := by
    have ha : (tripleCharges (sourceA1159 + difference 1 4) (sourceB1159 + difference 4 1) sourceC1159) = raw19507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19507; decide +kernel
    rw [ha]
    exact (canonical19507 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1159 + difference 1 5) (sourceB1159 + difference 5 1) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1159 + difference 1 5) (sourceB1159 + difference 5 1) sourceC1159) = raw5063 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw5063; decide +kernel
    rw [ha]
    exact (canonical5063 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1159 + difference 2 0) (sourceB1159 + difference 0 2) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4187) := by
    have ha : (tripleCharges (sourceA1159 + difference 2 0) (sourceB1159 + difference 0 2) sourceC1159) = raw19508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19508; decide +kernel
    rw [ha]
    exact (canonical19508 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1159 + difference 2 1) (sourceB1159 + difference 1 2) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4555) := by
    have ha : (tripleCharges (sourceA1159 + difference 2 1) (sourceB1159 + difference 1 2) sourceC1159) = raw19509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19509; decide +kernel
    rw [ha]
    exact (canonical19509 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1159 + difference 2 3) (sourceB1159 + difference 3 2) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4555) := by
    have ha : (tripleCharges (sourceA1159 + difference 2 3) (sourceB1159 + difference 3 2) sourceC1159) = raw19510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19510; decide +kernel
    rw [ha]
    exact (canonical19510 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1159 + difference 2 4) (sourceB1159 + difference 4 2) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4555) := by
    have ha : (tripleCharges (sourceA1159 + difference 2 4) (sourceB1159 + difference 4 2) sourceC1159) = raw19511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19511; decide +kernel
    rw [ha]
    exact (canonical19511 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1159 + difference 2 5) (sourceB1159 + difference 5 2) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1159 + difference 2 5) (sourceB1159 + difference 5 2) sourceC1159) = raw5068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw5068; decide +kernel
    rw [ha]
    exact (canonical5068 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1159 + difference 3 0) (sourceB1159 + difference 0 3) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4187) := by
    have ha : (tripleCharges (sourceA1159 + difference 3 0) (sourceB1159 + difference 0 3) sourceC1159) = raw19512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19512; decide +kernel
    rw [ha]
    exact (canonical19512 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1159 + difference 3 1) (sourceB1159 + difference 1 3) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4555) := by
    have ha : (tripleCharges (sourceA1159 + difference 3 1) (sourceB1159 + difference 1 3) sourceC1159) = raw19513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19513; decide +kernel
    rw [ha]
    exact (canonical19513 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1159 + difference 3 2) (sourceB1159 + difference 2 3) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4555) := by
    have ha : (tripleCharges (sourceA1159 + difference 3 2) (sourceB1159 + difference 2 3) sourceC1159) = raw19514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19514; decide +kernel
    rw [ha]
    exact (canonical19514 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1159 + difference 3 4) (sourceB1159 + difference 4 3) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4555) := by
    have ha : (tripleCharges (sourceA1159 + difference 3 4) (sourceB1159 + difference 4 3) sourceC1159) = raw19515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19515; decide +kernel
    rw [ha]
    exact (canonical19515 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1159 + difference 3 5) (sourceB1159 + difference 5 3) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1159 + difference 3 5) (sourceB1159 + difference 5 3) sourceC1159) = raw5073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw5073; decide +kernel
    rw [ha]
    exact (canonical5073 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1159 + difference 4 0) (sourceB1159 + difference 0 4) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4187) := by
    have ha : (tripleCharges (sourceA1159 + difference 4 0) (sourceB1159 + difference 0 4) sourceC1159) = raw19516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19516; decide +kernel
    rw [ha]
    exact (canonical19516 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1159 + difference 4 1) (sourceB1159 + difference 1 4) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4555) := by
    have ha : (tripleCharges (sourceA1159 + difference 4 1) (sourceB1159 + difference 1 4) sourceC1159) = raw19517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19517; decide +kernel
    rw [ha]
    exact (canonical19517 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1159 + difference 4 2) (sourceB1159 + difference 2 4) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4555) := by
    have ha : (tripleCharges (sourceA1159 + difference 4 2) (sourceB1159 + difference 2 4) sourceC1159) = raw19518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19518; decide +kernel
    rw [ha]
    exact (canonical19518 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1159 + difference 4 3) (sourceB1159 + difference 3 4) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4555) := by
    have ha : (tripleCharges (sourceA1159 + difference 4 3) (sourceB1159 + difference 3 4) sourceC1159) = raw19519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19519; decide +kernel
    rw [ha]
    exact (canonical19519 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1159 + difference 4 5) (sourceB1159 + difference 5 4) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1159 + difference 4 5) (sourceB1159 + difference 5 4) sourceC1159) = raw5078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw5078; decide +kernel
    rw [ha]
    exact (canonical5078 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1159 + difference 5 0) (sourceB1159 + difference 0 5) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4194) := by
    have ha : (tripleCharges (sourceA1159 + difference 5 0) (sourceB1159 + difference 0 5) sourceC1159) = raw19520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19520; decide +kernel
    rw [ha]
    exact (canonical19520 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1159 + difference 5 1) (sourceB1159 + difference 1 5) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4187) := by
    have ha : (tripleCharges (sourceA1159 + difference 5 1) (sourceB1159 + difference 1 5) sourceC1159) = raw19521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19521; decide +kernel
    rw [ha]
    exact (canonical19521 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1159 + difference 5 2) (sourceB1159 + difference 2 5) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4187) := by
    have ha : (tripleCharges (sourceA1159 + difference 5 2) (sourceB1159 + difference 2 5) sourceC1159) = raw19522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19522; decide +kernel
    rw [ha]
    exact (canonical19522 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1159 + difference 5 3) (sourceB1159 + difference 3 5) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4187) := by
    have ha : (tripleCharges (sourceA1159 + difference 5 3) (sourceB1159 + difference 3 5) sourceC1159) = raw19523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19523; decide +kernel
    rw [ha]
    exact (canonical19523 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1159 + difference 5 4) (sourceB1159 + difference 4 5) sourceC1159) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4187) := by
    have ha : (tripleCharges (sourceA1159 + difference 5 4) (sourceB1159 + difference 4 5) sourceC1159) = raw19524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1159 sourceB1159 sourceC1159 difference raw19524; decide +kernel
    rw [ha]
    exact (canonical19524 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1159 sourceB1159 sourceC1159
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1159, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1160 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1160 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1160 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm1160 : Integer.Sparse Master := [(Sum.inr 615, 8), (Sum.inr 622, 1), (Sum.inr 1140, 12), (Sum.inr 1307, 8), (Sum.inr 3126, 1)]

theorem sourceEq1160 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1160 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1160 + difference 0 1) (sourceB1160 + difference 1 0) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1160 + difference 0 1) (sourceB1160 + difference 1 0) sourceC1160) = raw19525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19525; decide +kernel
    rw [ha]
    exact (canonical19525 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1160 + difference 0 2) (sourceB1160 + difference 2 0) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1160 + difference 0 2) (sourceB1160 + difference 2 0) sourceC1160) = raw19526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19526; decide +kernel
    rw [ha]
    exact (canonical19526 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1160 + difference 0 3) (sourceB1160 + difference 3 0) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1160 + difference 0 3) (sourceB1160 + difference 3 0) sourceC1160) = raw19527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19527; decide +kernel
    rw [ha]
    exact (canonical19527 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1160 + difference 0 4) (sourceB1160 + difference 4 0) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1160 + difference 0 4) (sourceB1160 + difference 4 0) sourceC1160) = raw19528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19528; decide +kernel
    rw [ha]
    exact (canonical19528 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1160 + difference 0 5) (sourceB1160 + difference 5 0) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3126) := by
    have ha : (tripleCharges (sourceA1160 + difference 0 5) (sourceB1160 + difference 5 0) sourceC1160) = raw19529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19529; decide +kernel
    rw [ha]
    exact (canonical19529 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1160 + difference 1 0) (sourceB1160 + difference 0 1) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 615) := by
    have ha : (tripleCharges (sourceA1160 + difference 1 0) (sourceB1160 + difference 0 1) sourceC1160) = raw19530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19530; decide +kernel
    rw [ha]
    exact (canonical19530 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1160 + difference 1 2) (sourceB1160 + difference 2 1) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1160 + difference 1 2) (sourceB1160 + difference 2 1) sourceC1160) = raw19531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19531; decide +kernel
    rw [ha]
    exact (canonical19531 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1160 + difference 1 3) (sourceB1160 + difference 3 1) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1160 + difference 1 3) (sourceB1160 + difference 3 1) sourceC1160) = raw19532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19532; decide +kernel
    rw [ha]
    exact (canonical19532 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1160 + difference 1 4) (sourceB1160 + difference 4 1) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1160 + difference 1 4) (sourceB1160 + difference 4 1) sourceC1160) = raw19533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19533; decide +kernel
    rw [ha]
    exact (canonical19533 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1160 + difference 1 5) (sourceB1160 + difference 5 1) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1160 + difference 1 5) (sourceB1160 + difference 5 1) sourceC1160) = raw19534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19534; decide +kernel
    rw [ha]
    exact (canonical19534 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1160 + difference 2 0) (sourceB1160 + difference 0 2) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 615) := by
    have ha : (tripleCharges (sourceA1160 + difference 2 0) (sourceB1160 + difference 0 2) sourceC1160) = raw19535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19535; decide +kernel
    rw [ha]
    exact (canonical19535 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1160 + difference 2 1) (sourceB1160 + difference 1 2) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1160 + difference 2 1) (sourceB1160 + difference 1 2) sourceC1160) = raw19536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19536; decide +kernel
    rw [ha]
    exact (canonical19536 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1160 + difference 2 3) (sourceB1160 + difference 3 2) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1160 + difference 2 3) (sourceB1160 + difference 3 2) sourceC1160) = raw19537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19537; decide +kernel
    rw [ha]
    exact (canonical19537 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1160 + difference 2 4) (sourceB1160 + difference 4 2) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1160 + difference 2 4) (sourceB1160 + difference 4 2) sourceC1160) = raw19538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19538; decide +kernel
    rw [ha]
    exact (canonical19538 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1160 + difference 2 5) (sourceB1160 + difference 5 2) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1160 + difference 2 5) (sourceB1160 + difference 5 2) sourceC1160) = raw19539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19539; decide +kernel
    rw [ha]
    exact (canonical19539 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1160 + difference 3 0) (sourceB1160 + difference 0 3) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 615) := by
    have ha : (tripleCharges (sourceA1160 + difference 3 0) (sourceB1160 + difference 0 3) sourceC1160) = raw19540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19540; decide +kernel
    rw [ha]
    exact (canonical19540 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1160 + difference 3 1) (sourceB1160 + difference 1 3) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1160 + difference 3 1) (sourceB1160 + difference 1 3) sourceC1160) = raw19541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19541; decide +kernel
    rw [ha]
    exact (canonical19541 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1160 + difference 3 2) (sourceB1160 + difference 2 3) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1160 + difference 3 2) (sourceB1160 + difference 2 3) sourceC1160) = raw19542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19542; decide +kernel
    rw [ha]
    exact (canonical19542 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1160 + difference 3 4) (sourceB1160 + difference 4 3) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1160 + difference 3 4) (sourceB1160 + difference 4 3) sourceC1160) = raw19543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19543; decide +kernel
    rw [ha]
    exact (canonical19543 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1160 + difference 3 5) (sourceB1160 + difference 5 3) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1160 + difference 3 5) (sourceB1160 + difference 5 3) sourceC1160) = raw19544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19544; decide +kernel
    rw [ha]
    exact (canonical19544 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1160 + difference 4 0) (sourceB1160 + difference 0 4) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 615) := by
    have ha : (tripleCharges (sourceA1160 + difference 4 0) (sourceB1160 + difference 0 4) sourceC1160) = raw19545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19545; decide +kernel
    rw [ha]
    exact (canonical19545 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1160 + difference 4 1) (sourceB1160 + difference 1 4) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1160 + difference 4 1) (sourceB1160 + difference 1 4) sourceC1160) = raw19546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19546; decide +kernel
    rw [ha]
    exact (canonical19546 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1160 + difference 4 2) (sourceB1160 + difference 2 4) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1160 + difference 4 2) (sourceB1160 + difference 2 4) sourceC1160) = raw19547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19547; decide +kernel
    rw [ha]
    exact (canonical19547 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1160 + difference 4 3) (sourceB1160 + difference 3 4) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1140) := by
    have ha : (tripleCharges (sourceA1160 + difference 4 3) (sourceB1160 + difference 3 4) sourceC1160) = raw19548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19548; decide +kernel
    rw [ha]
    exact (canonical19548 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1160 + difference 4 5) (sourceB1160 + difference 5 4) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1307) := by
    have ha : (tripleCharges (sourceA1160 + difference 4 5) (sourceB1160 + difference 5 4) sourceC1160) = raw19549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19549; decide +kernel
    rw [ha]
    exact (canonical19549 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1160 + difference 5 0) (sourceB1160 + difference 0 5) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 622) := by
    have ha : (tripleCharges (sourceA1160 + difference 5 0) (sourceB1160 + difference 0 5) sourceC1160) = raw19550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19550; decide +kernel
    rw [ha]
    exact (canonical19550 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1160 + difference 5 1) (sourceB1160 + difference 1 5) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 615) := by
    have ha : (tripleCharges (sourceA1160 + difference 5 1) (sourceB1160 + difference 1 5) sourceC1160) = raw19551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19551; decide +kernel
    rw [ha]
    exact (canonical19551 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1160 + difference 5 2) (sourceB1160 + difference 2 5) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 615) := by
    have ha : (tripleCharges (sourceA1160 + difference 5 2) (sourceB1160 + difference 2 5) sourceC1160) = raw19552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19552; decide +kernel
    rw [ha]
    exact (canonical19552 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1160 + difference 5 3) (sourceB1160 + difference 3 5) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 615) := by
    have ha : (tripleCharges (sourceA1160 + difference 5 3) (sourceB1160 + difference 3 5) sourceC1160) = raw19553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19553; decide +kernel
    rw [ha]
    exact (canonical19553 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1160 + difference 5 4) (sourceB1160 + difference 4 5) sourceC1160) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 615) := by
    have ha : (tripleCharges (sourceA1160 + difference 5 4) (sourceB1160 + difference 4 5) sourceC1160) = raw19554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1160 sourceB1160 sourceC1160 difference raw19554; decide +kernel
    rw [ha]
    exact (canonical19554 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1160 sourceB1160 sourceC1160
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1160, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1161 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1161 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1161 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1161 : Integer.Sparse Master := [(Sum.inr 4468, 16), (Sum.inr 4512, 2), (Sum.inr 4594, 12)]

theorem sourceEq1161 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1161 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1161 + difference 0 1) (sourceB1161 + difference 1 0) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 0 1) (sourceB1161 + difference 1 0) sourceC1161) = raw19555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19555; decide +kernel
    rw [ha]
    exact (canonical19555 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1161 + difference 0 2) (sourceB1161 + difference 2 0) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 0 2) (sourceB1161 + difference 2 0) sourceC1161) = raw19556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19556; decide +kernel
    rw [ha]
    exact (canonical19556 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1161 + difference 0 3) (sourceB1161 + difference 3 0) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 0 3) (sourceB1161 + difference 3 0) sourceC1161) = raw19557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19557; decide +kernel
    rw [ha]
    exact (canonical19557 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1161 + difference 0 4) (sourceB1161 + difference 4 0) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 0 4) (sourceB1161 + difference 4 0) sourceC1161) = raw19558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19558; decide +kernel
    rw [ha]
    exact (canonical19558 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1161 + difference 0 5) (sourceB1161 + difference 5 0) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4512) := by
    have ha : (tripleCharges (sourceA1161 + difference 0 5) (sourceB1161 + difference 5 0) sourceC1161) = raw19559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19559; decide +kernel
    rw [ha]
    exact (canonical19559 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1161 + difference 1 0) (sourceB1161 + difference 0 1) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 1 0) (sourceB1161 + difference 0 1) sourceC1161) = raw19560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19560; decide +kernel
    rw [ha]
    exact (canonical19560 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1161 + difference 1 2) (sourceB1161 + difference 2 1) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 1 2) (sourceB1161 + difference 2 1) sourceC1161) = raw19561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19561; decide +kernel
    rw [ha]
    exact (canonical19561 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1161 + difference 1 3) (sourceB1161 + difference 3 1) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 1 3) (sourceB1161 + difference 3 1) sourceC1161) = raw19562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19562; decide +kernel
    rw [ha]
    exact (canonical19562 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1161 + difference 1 4) (sourceB1161 + difference 4 1) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 1 4) (sourceB1161 + difference 4 1) sourceC1161) = raw19563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19563; decide +kernel
    rw [ha]
    exact (canonical19563 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1161 + difference 1 5) (sourceB1161 + difference 5 1) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 1 5) (sourceB1161 + difference 5 1) sourceC1161) = raw19564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19564; decide +kernel
    rw [ha]
    exact (canonical19564 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1161 + difference 2 0) (sourceB1161 + difference 0 2) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 2 0) (sourceB1161 + difference 0 2) sourceC1161) = raw19565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19565; decide +kernel
    rw [ha]
    exact (canonical19565 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1161 + difference 2 1) (sourceB1161 + difference 1 2) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 2 1) (sourceB1161 + difference 1 2) sourceC1161) = raw19566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19566; decide +kernel
    rw [ha]
    exact (canonical19566 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1161 + difference 2 3) (sourceB1161 + difference 3 2) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 2 3) (sourceB1161 + difference 3 2) sourceC1161) = raw19567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19567; decide +kernel
    rw [ha]
    exact (canonical19567 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1161 + difference 2 4) (sourceB1161 + difference 4 2) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 2 4) (sourceB1161 + difference 4 2) sourceC1161) = raw19568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19568; decide +kernel
    rw [ha]
    exact (canonical19568 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1161 + difference 2 5) (sourceB1161 + difference 5 2) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 2 5) (sourceB1161 + difference 5 2) sourceC1161) = raw19569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19569; decide +kernel
    rw [ha]
    exact (canonical19569 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1161 + difference 3 0) (sourceB1161 + difference 0 3) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 3 0) (sourceB1161 + difference 0 3) sourceC1161) = raw19570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19570; decide +kernel
    rw [ha]
    exact (canonical19570 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1161 + difference 3 1) (sourceB1161 + difference 1 3) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 3 1) (sourceB1161 + difference 1 3) sourceC1161) = raw19571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19571; decide +kernel
    rw [ha]
    exact (canonical19571 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1161 + difference 3 2) (sourceB1161 + difference 2 3) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 3 2) (sourceB1161 + difference 2 3) sourceC1161) = raw19572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19572; decide +kernel
    rw [ha]
    exact (canonical19572 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1161 + difference 3 4) (sourceB1161 + difference 4 3) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 3 4) (sourceB1161 + difference 4 3) sourceC1161) = raw19573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19573; decide +kernel
    rw [ha]
    exact (canonical19573 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1161 + difference 3 5) (sourceB1161 + difference 5 3) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 3 5) (sourceB1161 + difference 5 3) sourceC1161) = raw19574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19574; decide +kernel
    rw [ha]
    exact (canonical19574 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1161 + difference 4 0) (sourceB1161 + difference 0 4) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 4 0) (sourceB1161 + difference 0 4) sourceC1161) = raw19575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19575; decide +kernel
    rw [ha]
    exact (canonical19575 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1161 + difference 4 1) (sourceB1161 + difference 1 4) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 4 1) (sourceB1161 + difference 1 4) sourceC1161) = raw19576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19576; decide +kernel
    rw [ha]
    exact (canonical19576 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1161 + difference 4 2) (sourceB1161 + difference 2 4) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 4 2) (sourceB1161 + difference 2 4) sourceC1161) = raw19577 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19577; decide +kernel
    rw [ha]
    exact (canonical19577 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1161 + difference 4 3) (sourceB1161 + difference 3 4) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1161 + difference 4 3) (sourceB1161 + difference 3 4) sourceC1161) = raw19578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19578; decide +kernel
    rw [ha]
    exact (canonical19578 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1161 + difference 4 5) (sourceB1161 + difference 5 4) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 4 5) (sourceB1161 + difference 5 4) sourceC1161) = raw19579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19579; decide +kernel
    rw [ha]
    exact (canonical19579 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1161 + difference 5 0) (sourceB1161 + difference 0 5) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4512) := by
    have ha : (tripleCharges (sourceA1161 + difference 5 0) (sourceB1161 + difference 0 5) sourceC1161) = raw19580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19580; decide +kernel
    rw [ha]
    exact (canonical19580 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1161 + difference 5 1) (sourceB1161 + difference 1 5) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 5 1) (sourceB1161 + difference 1 5) sourceC1161) = raw19581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19581; decide +kernel
    rw [ha]
    exact (canonical19581 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1161 + difference 5 2) (sourceB1161 + difference 2 5) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 5 2) (sourceB1161 + difference 2 5) sourceC1161) = raw19582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19582; decide +kernel
    rw [ha]
    exact (canonical19582 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1161 + difference 5 3) (sourceB1161 + difference 3 5) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 5 3) (sourceB1161 + difference 3 5) sourceC1161) = raw19583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19583; decide +kernel
    rw [ha]
    exact (canonical19583 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1161 + difference 5 4) (sourceB1161 + difference 4 5) sourceC1161) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1161 + difference 5 4) (sourceB1161 + difference 4 5) sourceC1161) = raw19584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1161 sourceB1161 sourceC1161 difference raw19584; decide +kernel
    rw [ha]
    exact (canonical19584 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1161 sourceB1161 sourceC1161
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1161, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1162 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1162 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1162 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1162 : Integer.Sparse Master := [(Sum.inr 1051, 8), (Sum.inr 1096, 1), (Sum.inr 1221, 12), (Sum.inr 1275, 8), (Sum.inr 1456, 1)]

theorem sourceEq1162 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1162 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1162 + difference 0 1) (sourceB1162 + difference 1 0) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1275) := by
    have ha : (tripleCharges (sourceA1162 + difference 0 1) (sourceB1162 + difference 1 0) sourceC1162) = raw19585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19585; decide +kernel
    rw [ha]
    exact (canonical19585 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1162 + difference 0 2) (sourceB1162 + difference 2 0) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1275) := by
    have ha : (tripleCharges (sourceA1162 + difference 0 2) (sourceB1162 + difference 2 0) sourceC1162) = raw19586 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19586; decide +kernel
    rw [ha]
    exact (canonical19586 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1162 + difference 0 3) (sourceB1162 + difference 3 0) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1275) := by
    have ha : (tripleCharges (sourceA1162 + difference 0 3) (sourceB1162 + difference 3 0) sourceC1162) = raw19587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19587; decide +kernel
    rw [ha]
    exact (canonical19587 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1162 + difference 0 4) (sourceB1162 + difference 4 0) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1275) := by
    have ha : (tripleCharges (sourceA1162 + difference 0 4) (sourceB1162 + difference 4 0) sourceC1162) = raw19588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19588; decide +kernel
    rw [ha]
    exact (canonical19588 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1162 + difference 0 5) (sourceB1162 + difference 5 0) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1456) := by
    have ha : (tripleCharges (sourceA1162 + difference 0 5) (sourceB1162 + difference 5 0) sourceC1162) = raw19589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19589; decide +kernel
    rw [ha]
    exact (canonical19589 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1162 + difference 1 0) (sourceB1162 + difference 0 1) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1162 + difference 1 0) (sourceB1162 + difference 0 1) sourceC1162) = raw19590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19590; decide +kernel
    rw [ha]
    exact (canonical19590 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1162 + difference 1 2) (sourceB1162 + difference 2 1) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1162 + difference 1 2) (sourceB1162 + difference 2 1) sourceC1162) = raw19591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19591; decide +kernel
    rw [ha]
    exact (canonical19591 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1162 + difference 1 3) (sourceB1162 + difference 3 1) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1162 + difference 1 3) (sourceB1162 + difference 3 1) sourceC1162) = raw19592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19592; decide +kernel
    rw [ha]
    exact (canonical19592 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1162 + difference 1 4) (sourceB1162 + difference 4 1) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1162 + difference 1 4) (sourceB1162 + difference 4 1) sourceC1162) = raw19593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19593; decide +kernel
    rw [ha]
    exact (canonical19593 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1162 + difference 1 5) (sourceB1162 + difference 5 1) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1275) := by
    have ha : (tripleCharges (sourceA1162 + difference 1 5) (sourceB1162 + difference 5 1) sourceC1162) = raw19594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19594; decide +kernel
    rw [ha]
    exact (canonical19594 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1162 + difference 2 0) (sourceB1162 + difference 0 2) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1162 + difference 2 0) (sourceB1162 + difference 0 2) sourceC1162) = raw19595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19595; decide +kernel
    rw [ha]
    exact (canonical19595 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1162 + difference 2 1) (sourceB1162 + difference 1 2) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1162 + difference 2 1) (sourceB1162 + difference 1 2) sourceC1162) = raw19596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19596; decide +kernel
    rw [ha]
    exact (canonical19596 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1162 + difference 2 3) (sourceB1162 + difference 3 2) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1162 + difference 2 3) (sourceB1162 + difference 3 2) sourceC1162) = raw19597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19597; decide +kernel
    rw [ha]
    exact (canonical19597 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1162 + difference 2 4) (sourceB1162 + difference 4 2) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1162 + difference 2 4) (sourceB1162 + difference 4 2) sourceC1162) = raw19598 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19598; decide +kernel
    rw [ha]
    exact (canonical19598 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1162 + difference 2 5) (sourceB1162 + difference 5 2) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1275) := by
    have ha : (tripleCharges (sourceA1162 + difference 2 5) (sourceB1162 + difference 5 2) sourceC1162) = raw19599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19599; decide +kernel
    rw [ha]
    exact (canonical19599 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1162 + difference 3 0) (sourceB1162 + difference 0 3) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1162 + difference 3 0) (sourceB1162 + difference 0 3) sourceC1162) = raw19600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19600; decide +kernel
    rw [ha]
    exact (canonical19600 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1162 + difference 3 1) (sourceB1162 + difference 1 3) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1162 + difference 3 1) (sourceB1162 + difference 1 3) sourceC1162) = raw19601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19601; decide +kernel
    rw [ha]
    exact (canonical19601 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1162 + difference 3 2) (sourceB1162 + difference 2 3) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1162 + difference 3 2) (sourceB1162 + difference 2 3) sourceC1162) = raw19602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19602; decide +kernel
    rw [ha]
    exact (canonical19602 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1162 + difference 3 4) (sourceB1162 + difference 4 3) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1162 + difference 3 4) (sourceB1162 + difference 4 3) sourceC1162) = raw19603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19603; decide +kernel
    rw [ha]
    exact (canonical19603 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1162 + difference 3 5) (sourceB1162 + difference 5 3) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1275) := by
    have ha : (tripleCharges (sourceA1162 + difference 3 5) (sourceB1162 + difference 5 3) sourceC1162) = raw19604 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19604; decide +kernel
    rw [ha]
    exact (canonical19604 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1162 + difference 4 0) (sourceB1162 + difference 0 4) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1162 + difference 4 0) (sourceB1162 + difference 0 4) sourceC1162) = raw19605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19605; decide +kernel
    rw [ha]
    exact (canonical19605 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1162 + difference 4 1) (sourceB1162 + difference 1 4) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1162 + difference 4 1) (sourceB1162 + difference 1 4) sourceC1162) = raw19606 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19606; decide +kernel
    rw [ha]
    exact (canonical19606 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1162 + difference 4 2) (sourceB1162 + difference 2 4) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1162 + difference 4 2) (sourceB1162 + difference 2 4) sourceC1162) = raw19607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19607; decide +kernel
    rw [ha]
    exact (canonical19607 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1162 + difference 4 3) (sourceB1162 + difference 3 4) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1162 + difference 4 3) (sourceB1162 + difference 3 4) sourceC1162) = raw19608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19608; decide +kernel
    rw [ha]
    exact (canonical19608 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1162 + difference 4 5) (sourceB1162 + difference 5 4) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1275) := by
    have ha : (tripleCharges (sourceA1162 + difference 4 5) (sourceB1162 + difference 5 4) sourceC1162) = raw19609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19609; decide +kernel
    rw [ha]
    exact (canonical19609 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1162 + difference 5 0) (sourceB1162 + difference 0 5) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1096) := by
    have ha : (tripleCharges (sourceA1162 + difference 5 0) (sourceB1162 + difference 0 5) sourceC1162) = raw19610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19610; decide +kernel
    rw [ha]
    exact (canonical19610 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1162 + difference 5 1) (sourceB1162 + difference 1 5) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1162 + difference 5 1) (sourceB1162 + difference 1 5) sourceC1162) = raw19611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19611; decide +kernel
    rw [ha]
    exact (canonical19611 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1162 + difference 5 2) (sourceB1162 + difference 2 5) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1162 + difference 5 2) (sourceB1162 + difference 2 5) sourceC1162) = raw19612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19612; decide +kernel
    rw [ha]
    exact (canonical19612 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1162 + difference 5 3) (sourceB1162 + difference 3 5) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1162 + difference 5 3) (sourceB1162 + difference 3 5) sourceC1162) = raw19613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19613; decide +kernel
    rw [ha]
    exact (canonical19613 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1162 + difference 5 4) (sourceB1162 + difference 4 5) sourceC1162) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1162 + difference 5 4) (sourceB1162 + difference 4 5) sourceC1162) = raw19614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1162 sourceB1162 sourceC1162 difference raw19614; decide +kernel
    rw [ha]
    exact (canonical19614 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1162 sourceB1162 sourceC1162
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1162, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1163 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB1163 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1163 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1163 : Integer.Sparse Master := [(Sum.inr 1752, 4), (Sum.inr 1758, 1), (Sum.inr 3313, 1), (Sum.inr 4072, -1)]

theorem sourceEq1163 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1163 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1163 + difference 0 0) (sourceB1163 + difference 0 0) sourceC1163) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3313) := by
    have ha : (tripleCharges (sourceA1163 + difference 0 0) (sourceB1163 + difference 0 0) sourceC1163) = raw19481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1163 sourceB1163 sourceC1163 difference raw19481; decide +kernel
    rw [ha]
    exact (canonical19481 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1163 + difference 0 1) (sourceB1163 + difference 1 0) sourceC1163) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1163 + difference 0 1) (sourceB1163 + difference 1 0) sourceC1163) = raw19477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1163 sourceB1163 sourceC1163 difference raw19477; decide +kernel
    rw [ha]
    exact (canonical19477 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1163 + difference 0 2) (sourceB1163 + difference 2 0) sourceC1163) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1163 + difference 0 2) (sourceB1163 + difference 2 0) sourceC1163) = raw19615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1163 sourceB1163 sourceC1163 difference raw19615; decide +kernel
    rw [ha]
    exact (canonical19615 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1163 + difference 0 3) (sourceB1163 + difference 3 0) sourceC1163) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1163 + difference 0 3) (sourceB1163 + difference 3 0) sourceC1163) = raw19616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1163 sourceB1163 sourceC1163 difference raw19616; decide +kernel
    rw [ha]
    exact (canonical19616 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1163 + difference 0 4) (sourceB1163 + difference 4 0) sourceC1163) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1163 + difference 0 4) (sourceB1163 + difference 4 0) sourceC1163) = raw19617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1163 sourceB1163 sourceC1163 difference raw19617; decide +kernel
    rw [ha]
    exact (canonical19617 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1163 + difference 0 5) (sourceB1163 + difference 5 0) sourceC1163) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1758) := by
    have ha : (tripleCharges (sourceA1163 + difference 0 5) (sourceB1163 + difference 5 0) sourceC1163) = raw19618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1163 sourceB1163 sourceC1163 difference raw19618; decide +kernel
    rw [ha]
    exact (canonical19618 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1163 + sourceB1163) sourceC1163) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1163 + sourceB1163) sourceC1163) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1163 sourceB1163 sourceC1163 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1163 sourceB1163 sourceC1163
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1163, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1164 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1164 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1164 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm1164 : Integer.Sparse Master := [(Sum.inr 4156, 3), (Sum.inr 4159, 3), (Sum.inr 4163, 1), (Sum.inr 4187, 1), (Sum.inr 4189, 1), (Sum.inr 4330, 6), (Sum.inr 4356, 3), (Sum.inr 4370, 3), (Sum.inr 4460, 3), (Sum.inr 4505, 1), (Sum.inr 4605, 3), (Sum.inr 4621, 1), (Sum.inr 4897, 1)]

theorem sourceEq1164 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1164 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1164 + difference 0 1) (sourceB1164 + difference 1 0) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1164 + difference 0 1) (sourceB1164 + difference 1 0) sourceC1164) = raw5127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw5127; decide +kernel
    rw [ha]
    exact (canonical5127 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1164 + difference 0 2) (sourceB1164 + difference 2 0) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1164 + difference 0 2) (sourceB1164 + difference 2 0) sourceC1164) = raw5128 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw5128; decide +kernel
    rw [ha]
    exact (canonical5128 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1164 + difference 0 3) (sourceB1164 + difference 3 0) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1164 + difference 0 3) (sourceB1164 + difference 3 0) sourceC1164) = raw5129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw5129; decide +kernel
    rw [ha]
    exact (canonical5129 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1164 + difference 0 4) (sourceB1164 + difference 4 0) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA1164 + difference 0 4) (sourceB1164 + difference 4 0) sourceC1164) = raw5130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw5130; decide +kernel
    rw [ha]
    exact (canonical5130 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1164 + difference 0 5) (sourceB1164 + difference 5 0) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA1164 + difference 0 5) (sourceB1164 + difference 5 0) sourceC1164) = raw10259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw10259; decide +kernel
    rw [ha]
    exact (canonical10259 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1164 + difference 1 0) (sourceB1164 + difference 0 1) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4159) := by
    have ha : (tripleCharges (sourceA1164 + difference 1 0) (sourceB1164 + difference 0 1) sourceC1164) = raw19619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19619; decide +kernel
    rw [ha]
    exact (canonical19619 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1164 + difference 1 2) (sourceB1164 + difference 2 1) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1164 + difference 1 2) (sourceB1164 + difference 2 1) sourceC1164) = raw19620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19620; decide +kernel
    rw [ha]
    exact (canonical19620 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1164 + difference 1 3) (sourceB1164 + difference 3 1) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1164 + difference 1 3) (sourceB1164 + difference 3 1) sourceC1164) = raw19621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19621; decide +kernel
    rw [ha]
    exact (canonical19621 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1164 + difference 1 4) (sourceB1164 + difference 4 1) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1164 + difference 1 4) (sourceB1164 + difference 4 1) sourceC1164) = raw19622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19622; decide +kernel
    rw [ha]
    exact (canonical19622 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1164 + difference 1 5) (sourceB1164 + difference 5 1) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1164 + difference 1 5) (sourceB1164 + difference 5 1) sourceC1164) = raw5106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw5106; decide +kernel
    rw [ha]
    exact (canonical5106 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1164 + difference 2 0) (sourceB1164 + difference 0 2) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4159) := by
    have ha : (tripleCharges (sourceA1164 + difference 2 0) (sourceB1164 + difference 0 2) sourceC1164) = raw19623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19623; decide +kernel
    rw [ha]
    exact (canonical19623 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1164 + difference 2 1) (sourceB1164 + difference 1 2) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1164 + difference 2 1) (sourceB1164 + difference 1 2) sourceC1164) = raw19624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19624; decide +kernel
    rw [ha]
    exact (canonical19624 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1164 + difference 2 3) (sourceB1164 + difference 3 2) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1164 + difference 2 3) (sourceB1164 + difference 3 2) sourceC1164) = raw19625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19625; decide +kernel
    rw [ha]
    exact (canonical19625 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1164 + difference 2 4) (sourceB1164 + difference 4 2) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1164 + difference 2 4) (sourceB1164 + difference 4 2) sourceC1164) = raw19626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19626; decide +kernel
    rw [ha]
    exact (canonical19626 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1164 + difference 2 5) (sourceB1164 + difference 5 2) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1164 + difference 2 5) (sourceB1164 + difference 5 2) sourceC1164) = raw5111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw5111; decide +kernel
    rw [ha]
    exact (canonical5111 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1164 + difference 3 0) (sourceB1164 + difference 0 3) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4159) := by
    have ha : (tripleCharges (sourceA1164 + difference 3 0) (sourceB1164 + difference 0 3) sourceC1164) = raw19627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19627; decide +kernel
    rw [ha]
    exact (canonical19627 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1164 + difference 3 1) (sourceB1164 + difference 1 3) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1164 + difference 3 1) (sourceB1164 + difference 1 3) sourceC1164) = raw19628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19628; decide +kernel
    rw [ha]
    exact (canonical19628 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1164 + difference 3 2) (sourceB1164 + difference 2 3) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4330) := by
    have ha : (tripleCharges (sourceA1164 + difference 3 2) (sourceB1164 + difference 2 3) sourceC1164) = raw19629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19629; decide +kernel
    rw [ha]
    exact (canonical19629 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1164 + difference 3 4) (sourceB1164 + difference 4 3) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1164 + difference 3 4) (sourceB1164 + difference 4 3) sourceC1164) = raw19630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19630; decide +kernel
    rw [ha]
    exact (canonical19630 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1164 + difference 3 5) (sourceB1164 + difference 5 3) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4605) := by
    have ha : (tripleCharges (sourceA1164 + difference 3 5) (sourceB1164 + difference 5 3) sourceC1164) = raw5116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw5116; decide +kernel
    rw [ha]
    exact (canonical5116 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1164 + difference 4 0) (sourceB1164 + difference 0 4) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4189) := by
    have ha : (tripleCharges (sourceA1164 + difference 4 0) (sourceB1164 + difference 0 4) sourceC1164) = raw19631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19631; decide +kernel
    rw [ha]
    exact (canonical19631 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1164 + difference 4 1) (sourceB1164 + difference 1 4) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4370) := by
    have ha : (tripleCharges (sourceA1164 + difference 4 1) (sourceB1164 + difference 1 4) sourceC1164) = raw19632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19632; decide +kernel
    rw [ha]
    exact (canonical19632 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1164 + difference 4 2) (sourceB1164 + difference 2 4) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4370) := by
    have ha : (tripleCharges (sourceA1164 + difference 4 2) (sourceB1164 + difference 2 4) sourceC1164) = raw19633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19633; decide +kernel
    rw [ha]
    exact (canonical19633 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1164 + difference 4 3) (sourceB1164 + difference 3 4) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4370) := by
    have ha : (tripleCharges (sourceA1164 + difference 4 3) (sourceB1164 + difference 3 4) sourceC1164) = raw19634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19634; decide +kernel
    rw [ha]
    exact (canonical19634 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1164 + difference 4 5) (sourceB1164 + difference 5 4) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA1164 + difference 4 5) (sourceB1164 + difference 5 4) sourceC1164) = raw5121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw5121; decide +kernel
    rw [ha]
    exact (canonical5121 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1164 + difference 5 0) (sourceB1164 + difference 0 5) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4163) := by
    have ha : (tripleCharges (sourceA1164 + difference 5 0) (sourceB1164 + difference 0 5) sourceC1164) = raw19635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19635; decide +kernel
    rw [ha]
    exact (canonical19635 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1164 + difference 5 1) (sourceB1164 + difference 1 5) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4156) := by
    have ha : (tripleCharges (sourceA1164 + difference 5 1) (sourceB1164 + difference 1 5) sourceC1164) = raw19636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19636; decide +kernel
    rw [ha]
    exact (canonical19636 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1164 + difference 5 2) (sourceB1164 + difference 2 5) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4156) := by
    have ha : (tripleCharges (sourceA1164 + difference 5 2) (sourceB1164 + difference 2 5) sourceC1164) = raw19637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19637; decide +kernel
    rw [ha]
    exact (canonical19637 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1164 + difference 5 3) (sourceB1164 + difference 3 5) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4156) := by
    have ha : (tripleCharges (sourceA1164 + difference 5 3) (sourceB1164 + difference 3 5) sourceC1164) = raw19638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19638; decide +kernel
    rw [ha]
    exact (canonical19638 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1164 + difference 5 4) (sourceB1164 + difference 4 5) sourceC1164) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4187) := by
    have ha : (tripleCharges (sourceA1164 + difference 5 4) (sourceB1164 + difference 4 5) sourceC1164) = raw19639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1164 sourceB1164 sourceC1164 difference raw19639; decide +kernel
    rw [ha]
    exact (canonical19639 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1164 sourceB1164 sourceC1164
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1164, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1165 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1165 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1165 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm1165 : Integer.Sparse Master := [(Sum.inr 587, 3), (Sum.inr 591, 1), (Sum.inr 617, 1), (Sum.inr 633, 3), (Sum.inr 650, 1), (Sum.inr 1118, 6), (Sum.inr 1142, 3), (Sum.inr 1173, 3), (Sum.inr 1271, 3), (Sum.inr 1308, 1), (Sum.inr 1416, 3), (Sum.inr 1450, 1), (Sum.inr 3114, 1)]

theorem sourceEq1165 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1165 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1165 + difference 0 1) (sourceB1165 + difference 1 0) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1165 + difference 0 1) (sourceB1165 + difference 1 0) sourceC1165) = raw19640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19640; decide +kernel
    rw [ha]
    exact (canonical19640 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1165 + difference 0 2) (sourceB1165 + difference 2 0) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1165 + difference 0 2) (sourceB1165 + difference 2 0) sourceC1165) = raw19641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19641; decide +kernel
    rw [ha]
    exact (canonical19641 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1165 + difference 0 3) (sourceB1165 + difference 3 0) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1416) := by
    have ha : (tripleCharges (sourceA1165 + difference 0 3) (sourceB1165 + difference 3 0) sourceC1165) = raw19642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19642; decide +kernel
    rw [ha]
    exact (canonical19642 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1165 + difference 0 4) (sourceB1165 + difference 4 0) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1450) := by
    have ha : (tripleCharges (sourceA1165 + difference 0 4) (sourceB1165 + difference 4 0) sourceC1165) = raw19643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19643; decide +kernel
    rw [ha]
    exact (canonical19643 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1165 + difference 0 5) (sourceB1165 + difference 5 0) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA1165 + difference 0 5) (sourceB1165 + difference 5 0) sourceC1165) = raw10289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw10289; decide +kernel
    rw [ha]
    exact (canonical10289 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1165 + difference 1 0) (sourceB1165 + difference 0 1) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 587) := by
    have ha : (tripleCharges (sourceA1165 + difference 1 0) (sourceB1165 + difference 0 1) sourceC1165) = raw19644 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19644; decide +kernel
    rw [ha]
    exact (canonical19644 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1165 + difference 1 2) (sourceB1165 + difference 2 1) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1165 + difference 1 2) (sourceB1165 + difference 2 1) sourceC1165) = raw19645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19645; decide +kernel
    rw [ha]
    exact (canonical19645 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1165 + difference 1 3) (sourceB1165 + difference 3 1) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1165 + difference 1 3) (sourceB1165 + difference 3 1) sourceC1165) = raw19646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19646; decide +kernel
    rw [ha]
    exact (canonical19646 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1165 + difference 1 4) (sourceB1165 + difference 4 1) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1173) := by
    have ha : (tripleCharges (sourceA1165 + difference 1 4) (sourceB1165 + difference 4 1) sourceC1165) = raw19647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19647; decide +kernel
    rw [ha]
    exact (canonical19647 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1165 + difference 1 5) (sourceB1165 + difference 5 1) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1165 + difference 1 5) (sourceB1165 + difference 5 1) sourceC1165) = raw19648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19648; decide +kernel
    rw [ha]
    exact (canonical19648 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1165 + difference 2 0) (sourceB1165 + difference 0 2) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 587) := by
    have ha : (tripleCharges (sourceA1165 + difference 2 0) (sourceB1165 + difference 0 2) sourceC1165) = raw19649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19649; decide +kernel
    rw [ha]
    exact (canonical19649 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1165 + difference 2 1) (sourceB1165 + difference 1 2) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1165 + difference 2 1) (sourceB1165 + difference 1 2) sourceC1165) = raw19650 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19650; decide +kernel
    rw [ha]
    exact (canonical19650 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1165 + difference 2 3) (sourceB1165 + difference 3 2) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1165 + difference 2 3) (sourceB1165 + difference 3 2) sourceC1165) = raw19651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19651; decide +kernel
    rw [ha]
    exact (canonical19651 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1165 + difference 2 4) (sourceB1165 + difference 4 2) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1173) := by
    have ha : (tripleCharges (sourceA1165 + difference 2 4) (sourceB1165 + difference 4 2) sourceC1165) = raw19652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19652; decide +kernel
    rw [ha]
    exact (canonical19652 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1165 + difference 2 5) (sourceB1165 + difference 5 2) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1165 + difference 2 5) (sourceB1165 + difference 5 2) sourceC1165) = raw19653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19653; decide +kernel
    rw [ha]
    exact (canonical19653 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1165 + difference 3 0) (sourceB1165 + difference 0 3) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 587) := by
    have ha : (tripleCharges (sourceA1165 + difference 3 0) (sourceB1165 + difference 0 3) sourceC1165) = raw19654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19654; decide +kernel
    rw [ha]
    exact (canonical19654 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1165 + difference 3 1) (sourceB1165 + difference 1 3) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1165 + difference 3 1) (sourceB1165 + difference 1 3) sourceC1165) = raw19655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19655; decide +kernel
    rw [ha]
    exact (canonical19655 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1165 + difference 3 2) (sourceB1165 + difference 2 3) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1165 + difference 3 2) (sourceB1165 + difference 2 3) sourceC1165) = raw19656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19656; decide +kernel
    rw [ha]
    exact (canonical19656 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1165 + difference 3 4) (sourceB1165 + difference 4 3) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1173) := by
    have ha : (tripleCharges (sourceA1165 + difference 3 4) (sourceB1165 + difference 4 3) sourceC1165) = raw19657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19657; decide +kernel
    rw [ha]
    exact (canonical19657 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1165 + difference 3 5) (sourceB1165 + difference 5 3) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1271) := by
    have ha : (tripleCharges (sourceA1165 + difference 3 5) (sourceB1165 + difference 5 3) sourceC1165) = raw19658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19658; decide +kernel
    rw [ha]
    exact (canonical19658 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1165 + difference 4 0) (sourceB1165 + difference 0 4) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 617) := by
    have ha : (tripleCharges (sourceA1165 + difference 4 0) (sourceB1165 + difference 0 4) sourceC1165) = raw19659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19659; decide +kernel
    rw [ha]
    exact (canonical19659 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1165 + difference 4 1) (sourceB1165 + difference 1 4) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1142) := by
    have ha : (tripleCharges (sourceA1165 + difference 4 1) (sourceB1165 + difference 1 4) sourceC1165) = raw19660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19660; decide +kernel
    rw [ha]
    exact (canonical19660 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1165 + difference 4 2) (sourceB1165 + difference 2 4) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1142) := by
    have ha : (tripleCharges (sourceA1165 + difference 4 2) (sourceB1165 + difference 2 4) sourceC1165) = raw19661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19661; decide +kernel
    rw [ha]
    exact (canonical19661 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1165 + difference 4 3) (sourceB1165 + difference 3 4) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1142) := by
    have ha : (tripleCharges (sourceA1165 + difference 4 3) (sourceB1165 + difference 3 4) sourceC1165) = raw19662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19662; decide +kernel
    rw [ha]
    exact (canonical19662 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1165 + difference 4 5) (sourceB1165 + difference 5 4) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1308) := by
    have ha : (tripleCharges (sourceA1165 + difference 4 5) (sourceB1165 + difference 5 4) sourceC1165) = raw10285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw10285; decide +kernel
    rw [ha]
    exact (canonical10285 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1165 + difference 5 0) (sourceB1165 + difference 0 5) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 591) := by
    have ha : (tripleCharges (sourceA1165 + difference 5 0) (sourceB1165 + difference 0 5) sourceC1165) = raw19663 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19663; decide +kernel
    rw [ha]
    exact (canonical19663 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1165 + difference 5 1) (sourceB1165 + difference 1 5) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 633) := by
    have ha : (tripleCharges (sourceA1165 + difference 5 1) (sourceB1165 + difference 1 5) sourceC1165) = raw19664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19664; decide +kernel
    rw [ha]
    exact (canonical19664 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1165 + difference 5 2) (sourceB1165 + difference 2 5) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 633) := by
    have ha : (tripleCharges (sourceA1165 + difference 5 2) (sourceB1165 + difference 2 5) sourceC1165) = raw19665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19665; decide +kernel
    rw [ha]
    exact (canonical19665 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1165 + difference 5 3) (sourceB1165 + difference 3 5) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 633) := by
    have ha : (tripleCharges (sourceA1165 + difference 5 3) (sourceB1165 + difference 3 5) sourceC1165) = raw19666 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19666; decide +kernel
    rw [ha]
    exact (canonical19666 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1165 + difference 5 4) (sourceB1165 + difference 4 5) sourceC1165) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 650) := by
    have ha : (tripleCharges (sourceA1165 + difference 5 4) (sourceB1165 + difference 4 5) sourceC1165) = raw19667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1165 sourceB1165 sourceC1165 difference raw19667; decide +kernel
    rw [ha]
    exact (canonical19667 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1165 sourceB1165 sourceC1165
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1165, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1166 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1166 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1166 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm1166 : Integer.Sparse Master := [(Sum.inr 1516, 3), (Sum.inr 1532, 3), (Sum.inr 1534, 1), (Sum.inr 1537, 1), (Sum.inr 1540, 1), (Sum.inr 1672, 6), (Sum.inr 1692, 3), (Sum.inr 1722, 3), (Sum.inr 1725, 3), (Sum.inr 1754, 1), (Sum.inr 2226, 3), (Sum.inr 2289, 1), (Sum.inr 2292, 1)]

theorem sourceEq1166 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1166 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1166 + difference 0 1) (sourceB1166 + difference 1 0) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1166 + difference 0 1) (sourceB1166 + difference 1 0) sourceC1166) = raw5157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw5157; decide +kernel
    rw [ha]
    exact (canonical5157 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1166 + difference 0 2) (sourceB1166 + difference 2 0) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1166 + difference 0 2) (sourceB1166 + difference 2 0) sourceC1166) = raw5158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw5158; decide +kernel
    rw [ha]
    exact (canonical5158 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1166 + difference 0 3) (sourceB1166 + difference 3 0) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1166 + difference 0 3) (sourceB1166 + difference 3 0) sourceC1166) = raw5159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw5159; decide +kernel
    rw [ha]
    exact (canonical5159 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1166 + difference 0 4) (sourceB1166 + difference 4 0) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1754) := by
    have ha : (tripleCharges (sourceA1166 + difference 0 4) (sourceB1166 + difference 4 0) sourceC1166) = raw5160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw5160; decide +kernel
    rw [ha]
    exact (canonical5160 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1166 + difference 0 5) (sourceB1166 + difference 5 0) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2292) := by
    have ha : (tripleCharges (sourceA1166 + difference 0 5) (sourceB1166 + difference 5 0) sourceC1166) = raw10311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw10311; decide +kernel
    rw [ha]
    exact (canonical10311 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1166 + difference 1 0) (sourceB1166 + difference 0 1) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1532) := by
    have ha : (tripleCharges (sourceA1166 + difference 1 0) (sourceB1166 + difference 0 1) sourceC1166) = raw19668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19668; decide +kernel
    rw [ha]
    exact (canonical19668 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1166 + difference 1 2) (sourceB1166 + difference 2 1) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1166 + difference 1 2) (sourceB1166 + difference 2 1) sourceC1166) = raw19669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19669; decide +kernel
    rw [ha]
    exact (canonical19669 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1166 + difference 1 3) (sourceB1166 + difference 3 1) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1166 + difference 1 3) (sourceB1166 + difference 3 1) sourceC1166) = raw19670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19670; decide +kernel
    rw [ha]
    exact (canonical19670 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1166 + difference 1 4) (sourceB1166 + difference 4 1) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA1166 + difference 1 4) (sourceB1166 + difference 4 1) sourceC1166) = raw19671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19671; decide +kernel
    rw [ha]
    exact (canonical19671 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1166 + difference 1 5) (sourceB1166 + difference 5 1) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1166 + difference 1 5) (sourceB1166 + difference 5 1) sourceC1166) = raw5136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw5136; decide +kernel
    rw [ha]
    exact (canonical5136 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1166 + difference 2 0) (sourceB1166 + difference 0 2) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1532) := by
    have ha : (tripleCharges (sourceA1166 + difference 2 0) (sourceB1166 + difference 0 2) sourceC1166) = raw19672 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19672; decide +kernel
    rw [ha]
    exact (canonical19672 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1166 + difference 2 1) (sourceB1166 + difference 1 2) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1166 + difference 2 1) (sourceB1166 + difference 1 2) sourceC1166) = raw19673 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19673; decide +kernel
    rw [ha]
    exact (canonical19673 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1166 + difference 2 3) (sourceB1166 + difference 3 2) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1166 + difference 2 3) (sourceB1166 + difference 3 2) sourceC1166) = raw19674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19674; decide +kernel
    rw [ha]
    exact (canonical19674 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1166 + difference 2 4) (sourceB1166 + difference 4 2) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA1166 + difference 2 4) (sourceB1166 + difference 4 2) sourceC1166) = raw19675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19675; decide +kernel
    rw [ha]
    exact (canonical19675 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1166 + difference 2 5) (sourceB1166 + difference 5 2) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1166 + difference 2 5) (sourceB1166 + difference 5 2) sourceC1166) = raw5141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw5141; decide +kernel
    rw [ha]
    exact (canonical5141 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1166 + difference 3 0) (sourceB1166 + difference 0 3) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1532) := by
    have ha : (tripleCharges (sourceA1166 + difference 3 0) (sourceB1166 + difference 0 3) sourceC1166) = raw19676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19676; decide +kernel
    rw [ha]
    exact (canonical19676 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1166 + difference 3 1) (sourceB1166 + difference 1 3) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1166 + difference 3 1) (sourceB1166 + difference 1 3) sourceC1166) = raw19677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19677; decide +kernel
    rw [ha]
    exact (canonical19677 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1166 + difference 3 2) (sourceB1166 + difference 2 3) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1672) := by
    have ha : (tripleCharges (sourceA1166 + difference 3 2) (sourceB1166 + difference 2 3) sourceC1166) = raw19678 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19678; decide +kernel
    rw [ha]
    exact (canonical19678 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1166 + difference 3 4) (sourceB1166 + difference 4 3) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA1166 + difference 3 4) (sourceB1166 + difference 4 3) sourceC1166) = raw19679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19679; decide +kernel
    rw [ha]
    exact (canonical19679 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1166 + difference 3 5) (sourceB1166 + difference 5 3) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1166 + difference 3 5) (sourceB1166 + difference 5 3) sourceC1166) = raw5146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw5146; decide +kernel
    rw [ha]
    exact (canonical5146 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1166 + difference 4 0) (sourceB1166 + difference 0 4) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1540) := by
    have ha : (tripleCharges (sourceA1166 + difference 4 0) (sourceB1166 + difference 0 4) sourceC1166) = raw19680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19680; decide +kernel
    rw [ha]
    exact (canonical19680 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1166 + difference 4 1) (sourceB1166 + difference 1 4) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1722) := by
    have ha : (tripleCharges (sourceA1166 + difference 4 1) (sourceB1166 + difference 1 4) sourceC1166) = raw19681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19681; decide +kernel
    rw [ha]
    exact (canonical19681 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1166 + difference 4 2) (sourceB1166 + difference 2 4) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1722) := by
    have ha : (tripleCharges (sourceA1166 + difference 4 2) (sourceB1166 + difference 2 4) sourceC1166) = raw19682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19682; decide +kernel
    rw [ha]
    exact (canonical19682 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1166 + difference 4 3) (sourceB1166 + difference 3 4) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1722) := by
    have ha : (tripleCharges (sourceA1166 + difference 4 3) (sourceB1166 + difference 3 4) sourceC1166) = raw19683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19683; decide +kernel
    rw [ha]
    exact (canonical19683 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1166 + difference 4 5) (sourceB1166 + difference 5 4) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA1166 + difference 4 5) (sourceB1166 + difference 5 4) sourceC1166) = raw5151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw5151; decide +kernel
    rw [ha]
    exact (canonical5151 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1166 + difference 5 0) (sourceB1166 + difference 0 5) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1534) := by
    have ha : (tripleCharges (sourceA1166 + difference 5 0) (sourceB1166 + difference 0 5) sourceC1166) = raw19684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19684; decide +kernel
    rw [ha]
    exact (canonical19684 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1166 + difference 5 1) (sourceB1166 + difference 1 5) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1516) := by
    have ha : (tripleCharges (sourceA1166 + difference 5 1) (sourceB1166 + difference 1 5) sourceC1166) = raw19685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19685; decide +kernel
    rw [ha]
    exact (canonical19685 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1166 + difference 5 2) (sourceB1166 + difference 2 5) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1516) := by
    have ha : (tripleCharges (sourceA1166 + difference 5 2) (sourceB1166 + difference 2 5) sourceC1166) = raw19686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19686; decide +kernel
    rw [ha]
    exact (canonical19686 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1166 + difference 5 3) (sourceB1166 + difference 3 5) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1516) := by
    have ha : (tripleCharges (sourceA1166 + difference 5 3) (sourceB1166 + difference 3 5) sourceC1166) = raw19687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19687; decide +kernel
    rw [ha]
    exact (canonical19687 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1166 + difference 5 4) (sourceB1166 + difference 4 5) sourceC1166) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1537) := by
    have ha : (tripleCharges (sourceA1166 + difference 5 4) (sourceB1166 + difference 4 5) sourceC1166) = raw19688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1166 sourceB1166 sourceC1166 difference raw19688; decide +kernel
    rw [ha]
    exact (canonical19688 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1166 sourceB1166 sourceC1166
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1166, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1167 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1167 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1167 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm1167 : Integer.Sparse Master := [(Sum.inr 591, 1), (Sum.inr 628, 3), (Sum.inr 643, 1), (Sum.inr 1051, 1), (Sum.inr 4084, -1)]

theorem sourceEq1167 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1167 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1167 + difference 0 0) (sourceB1167 + difference 0 0) sourceC1167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1167 + difference 0 0) (sourceB1167 + difference 0 0) sourceC1167) = raw5166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1167 sourceB1167 sourceC1167 difference raw5166; decide +kernel
    rw [ha]
    exact (canonical5166 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1167 + difference 1 0) (sourceB1167 + difference 0 1) sourceC1167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 628) := by
    have ha : (tripleCharges (sourceA1167 + difference 1 0) (sourceB1167 + difference 0 1) sourceC1167) = raw19689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1167 sourceB1167 sourceC1167 difference raw19689; decide +kernel
    rw [ha]
    exact (canonical19689 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1167 + difference 2 0) (sourceB1167 + difference 0 2) sourceC1167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 628) := by
    have ha : (tripleCharges (sourceA1167 + difference 2 0) (sourceB1167 + difference 0 2) sourceC1167) = raw19690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1167 sourceB1167 sourceC1167 difference raw19690; decide +kernel
    rw [ha]
    exact (canonical19690 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1167 + difference 3 0) (sourceB1167 + difference 0 3) sourceC1167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 628) := by
    have ha : (tripleCharges (sourceA1167 + difference 3 0) (sourceB1167 + difference 0 3) sourceC1167) = raw19691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1167 sourceB1167 sourceC1167 difference raw19691; decide +kernel
    rw [ha]
    exact (canonical19691 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1167 + difference 4 0) (sourceB1167 + difference 0 4) sourceC1167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 643) := by
    have ha : (tripleCharges (sourceA1167 + difference 4 0) (sourceB1167 + difference 0 4) sourceC1167) = raw19692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1167 sourceB1167 sourceC1167 difference raw19692; decide +kernel
    rw [ha]
    exact (canonical19692 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1167 + difference 5 0) (sourceB1167 + difference 0 5) sourceC1167) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 591) := by
    have ha : (tripleCharges (sourceA1167 + difference 5 0) (sourceB1167 + difference 0 5) sourceC1167) = raw19693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1167 sourceB1167 sourceC1167 difference raw19693; decide +kernel
    rw [ha]
    exact (canonical19693 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1167 + sourceB1167) sourceC1167) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1167 + sourceB1167) sourceC1167) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA1167 sourceB1167 sourceC1167 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1167 sourceB1167 sourceC1167
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1167, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1168 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1168 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1168 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm1168 : Integer.Sparse Master := [(Sum.inr 628, 1), (Sum.inr 908, 2), (Sum.inr 934, 1), (Sum.inr 1051, 1), (Sum.inr 1239, 1), (Sum.inr 4084, -1)]

theorem sourceEq1168 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1168 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1168 + difference 1 0) (sourceB1168 + difference 0 1) sourceC1168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 628) := by
    have ha : (tripleCharges (sourceA1168 + difference 1 0) (sourceB1168 + difference 0 1) sourceC1168) = raw19689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1168 sourceB1168 sourceC1168 difference raw19689; decide +kernel
    rw [ha]
    exact (canonical19689 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1168 + difference 1 1) (sourceB1168 + difference 1 1) sourceC1168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1168 + difference 1 1) (sourceB1168 + difference 1 1) sourceC1168) = raw5166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1168 sourceB1168 sourceC1168 difference raw5166; decide +kernel
    rw [ha]
    exact (canonical5166 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1168 + difference 1 2) (sourceB1168 + difference 2 1) sourceC1168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 908) := by
    have ha : (tripleCharges (sourceA1168 + difference 1 2) (sourceB1168 + difference 2 1) sourceC1168) = raw19694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1168 sourceB1168 sourceC1168 difference raw19694; decide +kernel
    rw [ha]
    exact (canonical19694 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1168 + difference 1 3) (sourceB1168 + difference 3 1) sourceC1168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 908) := by
    have ha : (tripleCharges (sourceA1168 + difference 1 3) (sourceB1168 + difference 3 1) sourceC1168) = raw19695 := by
      apply Matrix.ext; unfold tripleCharges sourceA1168 sourceB1168 sourceC1168 difference raw19695; decide +kernel
    rw [ha]
    exact (canonical19695 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1168 + difference 1 4) (sourceB1168 + difference 4 1) sourceC1168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 934) := by
    have ha : (tripleCharges (sourceA1168 + difference 1 4) (sourceB1168 + difference 4 1) sourceC1168) = raw19696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1168 sourceB1168 sourceC1168 difference raw19696; decide +kernel
    rw [ha]
    exact (canonical19696 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1168 + difference 1 5) (sourceB1168 + difference 5 1) sourceC1168) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1239) := by
    have ha : (tripleCharges (sourceA1168 + difference 1 5) (sourceB1168 + difference 5 1) sourceC1168) = raw5162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1168 sourceB1168 sourceC1168 difference raw5162; decide +kernel
    rw [ha]
    exact (canonical5162 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1168 + sourceB1168) sourceC1168) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1168 + sourceB1168) sourceC1168) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA1168 sourceB1168 sourceC1168 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1168 sourceB1168 sourceC1168
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1168, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1169 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1169 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1169 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm1169 : Integer.Sparse Master := [(Sum.inr 584, 1), (Sum.inr 908, 2), (Sum.inr 948, 1), (Sum.inr 1043, 1), (Sum.inr 1051, 1), (Sum.inr 4084, -1)]

theorem sourceEq1169 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1169 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1169 + difference 0 1) (sourceB1169 + difference 1 0) sourceC1169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1043) := by
    have ha : (tripleCharges (sourceA1169 + difference 0 1) (sourceB1169 + difference 1 0) sourceC1169) = raw5176 := by
      apply Matrix.ext; unfold tripleCharges sourceA1169 sourceB1169 sourceC1169 difference raw5176; decide +kernel
    rw [ha]
    exact (canonical5176 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1169 + difference 1 1) (sourceB1169 + difference 1 1) sourceC1169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1169 + difference 1 1) (sourceB1169 + difference 1 1) sourceC1169) = raw5166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1169 sourceB1169 sourceC1169 difference raw5166; decide +kernel
    rw [ha]
    exact (canonical5166 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1169 + difference 2 1) (sourceB1169 + difference 1 2) sourceC1169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 908) := by
    have ha : (tripleCharges (sourceA1169 + difference 2 1) (sourceB1169 + difference 1 2) sourceC1169) = raw19697 := by
      apply Matrix.ext; unfold tripleCharges sourceA1169 sourceB1169 sourceC1169 difference raw19697; decide +kernel
    rw [ha]
    exact (canonical19697 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1169 + difference 3 1) (sourceB1169 + difference 1 3) sourceC1169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 908) := by
    have ha : (tripleCharges (sourceA1169 + difference 3 1) (sourceB1169 + difference 1 3) sourceC1169) = raw19698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1169 sourceB1169 sourceC1169 difference raw19698; decide +kernel
    rw [ha]
    exact (canonical19698 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1169 + difference 4 1) (sourceB1169 + difference 1 4) sourceC1169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 948) := by
    have ha : (tripleCharges (sourceA1169 + difference 4 1) (sourceB1169 + difference 1 4) sourceC1169) = raw19699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1169 sourceB1169 sourceC1169 difference raw19699; decide +kernel
    rw [ha]
    exact (canonical19699 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1169 + difference 5 1) (sourceB1169 + difference 1 5) sourceC1169) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 584) := by
    have ha : (tripleCharges (sourceA1169 + difference 5 1) (sourceB1169 + difference 1 5) sourceC1169) = raw19700 := by
      apply Matrix.ext; unfold tripleCharges sourceA1169 sourceB1169 sourceC1169 difference raw19700; decide +kernel
    rw [ha]
    exact (canonical19700 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1169 + sourceB1169) sourceC1169) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1169 + sourceB1169) sourceC1169) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA1169 sourceB1169 sourceC1169 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1169 sourceB1169 sourceC1169
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1169, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1170 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1170 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1170 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm1170 : Integer.Sparse Master := [(Sum.inr 643, 1), (Sum.inr 948, 3), (Sum.inr 1051, 1), (Sum.inr 1297, 1), (Sum.inr 4084, -1)]

theorem sourceEq1170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1170 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1170 + difference 4 0) (sourceB1170 + difference 0 4) sourceC1170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 643) := by
    have ha : (tripleCharges (sourceA1170 + difference 4 0) (sourceB1170 + difference 0 4) sourceC1170) = raw19692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1170 sourceB1170 sourceC1170 difference raw19692; decide +kernel
    rw [ha]
    exact (canonical19692 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1170 + difference 4 1) (sourceB1170 + difference 1 4) sourceC1170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 948) := by
    have ha : (tripleCharges (sourceA1170 + difference 4 1) (sourceB1170 + difference 1 4) sourceC1170) = raw19699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1170 sourceB1170 sourceC1170 difference raw19699; decide +kernel
    rw [ha]
    exact (canonical19699 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1170 + difference 4 2) (sourceB1170 + difference 2 4) sourceC1170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 948) := by
    have ha : (tripleCharges (sourceA1170 + difference 4 2) (sourceB1170 + difference 2 4) sourceC1170) = raw19701 := by
      apply Matrix.ext; unfold tripleCharges sourceA1170 sourceB1170 sourceC1170 difference raw19701; decide +kernel
    rw [ha]
    exact (canonical19701 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1170 + difference 4 3) (sourceB1170 + difference 3 4) sourceC1170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 948) := by
    have ha : (tripleCharges (sourceA1170 + difference 4 3) (sourceB1170 + difference 3 4) sourceC1170) = raw19702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1170 sourceB1170 sourceC1170 difference raw19702; decide +kernel
    rw [ha]
    exact (canonical19702 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1170 + difference 4 4) (sourceB1170 + difference 4 4) sourceC1170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1170 + difference 4 4) (sourceB1170 + difference 4 4) sourceC1170) = raw5166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1170 sourceB1170 sourceC1170 difference raw5166; decide +kernel
    rw [ha]
    exact (canonical5166 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1170 + difference 4 5) (sourceB1170 + difference 5 4) sourceC1170) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1297) := by
    have ha : (tripleCharges (sourceA1170 + difference 4 5) (sourceB1170 + difference 5 4) sourceC1170) = raw5165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1170 sourceB1170 sourceC1170 difference raw5165; decide +kernel
    rw [ha]
    exact (canonical5165 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1170 + sourceB1170) sourceC1170) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1170 + sourceB1170) sourceC1170) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA1170 sourceB1170 sourceC1170 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1170 sourceB1170 sourceC1170
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1170, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1171 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1171 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1171 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceForm1171 : Integer.Sparse Master := [(Sum.inr 615, 1), (Sum.inr 934, 3), (Sum.inr 1051, 1), (Sum.inr 1089, 1), (Sum.inr 4084, -1)]

theorem sourceEq1171 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1171 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1171 + difference 0 4) (sourceB1171 + difference 4 0) sourceC1171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1089) := by
    have ha : (tripleCharges (sourceA1171 + difference 0 4) (sourceB1171 + difference 4 0) sourceC1171) = raw19703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1171 sourceB1171 sourceC1171 difference raw19703; decide +kernel
    rw [ha]
    exact (canonical19703 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1171 + difference 1 4) (sourceB1171 + difference 4 1) sourceC1171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 934) := by
    have ha : (tripleCharges (sourceA1171 + difference 1 4) (sourceB1171 + difference 4 1) sourceC1171) = raw19696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1171 sourceB1171 sourceC1171 difference raw19696; decide +kernel
    rw [ha]
    exact (canonical19696 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1171 + difference 2 4) (sourceB1171 + difference 4 2) sourceC1171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 934) := by
    have ha : (tripleCharges (sourceA1171 + difference 2 4) (sourceB1171 + difference 4 2) sourceC1171) = raw19704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1171 sourceB1171 sourceC1171 difference raw19704; decide +kernel
    rw [ha]
    exact (canonical19704 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1171 + difference 3 4) (sourceB1171 + difference 4 3) sourceC1171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 934) := by
    have ha : (tripleCharges (sourceA1171 + difference 3 4) (sourceB1171 + difference 4 3) sourceC1171) = raw19705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1171 sourceB1171 sourceC1171 difference raw19705; decide +kernel
    rw [ha]
    exact (canonical19705 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1171 + difference 4 4) (sourceB1171 + difference 4 4) sourceC1171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1171 + difference 4 4) (sourceB1171 + difference 4 4) sourceC1171) = raw5166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1171 sourceB1171 sourceC1171 difference raw5166; decide +kernel
    rw [ha]
    exact (canonical5166 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1171 + difference 5 4) (sourceB1171 + difference 4 5) sourceC1171) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 615) := by
    have ha : (tripleCharges (sourceA1171 + difference 5 4) (sourceB1171 + difference 4 5) sourceC1171) = raw19706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1171 sourceB1171 sourceC1171 difference raw19706; decide +kernel
    rw [ha]
    exact (canonical19706 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1171 + sourceB1171) sourceC1171) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1171 + sourceB1171) sourceC1171) = raw5167 := by
      apply Matrix.ext; unfold doubleCharges sourceA1171 sourceB1171 sourceC1171 raw5167; decide +kernel
    rw [ha]
    exact (canonical5167 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1171 sourceB1171 sourceC1171
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1171, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1172 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1172 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1172 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm1172 : Integer.Sparse Master := [(Sum.inr 4108, 3), (Sum.inr 4112, 1), (Sum.inr 4134, 1), (Sum.inr 4146, 3), (Sum.inr 4181, 1), (Sum.inr 4293, 6), (Sum.inr 4315, 3), (Sum.inr 4356, 3), (Sum.inr 4463, 3), (Sum.inr 4507, 1), (Sum.inr 4608, 3), (Sum.inr 4625, 1), (Sum.inr 5296, 1)]

theorem sourceEq1172 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1172 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1172 + difference 0 1) (sourceB1172 + difference 1 0) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1172 + difference 0 1) (sourceB1172 + difference 1 0) sourceC1172) = raw4308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw4308; decide +kernel
    rw [ha]
    exact (canonical4308 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1172 + difference 0 2) (sourceB1172 + difference 2 0) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1172 + difference 0 2) (sourceB1172 + difference 2 0) sourceC1172) = raw4309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw4309; decide +kernel
    rw [ha]
    exact (canonical4309 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1172 + difference 0 3) (sourceB1172 + difference 3 0) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1172 + difference 0 3) (sourceB1172 + difference 3 0) sourceC1172) = raw4310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw4310; decide +kernel
    rw [ha]
    exact (canonical4310 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1172 + difference 0 4) (sourceB1172 + difference 4 0) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA1172 + difference 0 4) (sourceB1172 + difference 4 0) sourceC1172) = raw4311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw4311; decide +kernel
    rw [ha]
    exact (canonical4311 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1172 + difference 0 5) (sourceB1172 + difference 5 0) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA1172 + difference 0 5) (sourceB1172 + difference 5 0) sourceC1172) = raw10215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw10215; decide +kernel
    rw [ha]
    exact (canonical10215 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1172 + difference 1 0) (sourceB1172 + difference 0 1) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4146) := by
    have ha : (tripleCharges (sourceA1172 + difference 1 0) (sourceB1172 + difference 0 1) sourceC1172) = raw19707 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19707; decide +kernel
    rw [ha]
    exact (canonical19707 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1172 + difference 1 2) (sourceB1172 + difference 2 1) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4293) := by
    have ha : (tripleCharges (sourceA1172 + difference 1 2) (sourceB1172 + difference 2 1) sourceC1172) = raw19708 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19708; decide +kernel
    rw [ha]
    exact (canonical19708 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1172 + difference 1 3) (sourceB1172 + difference 3 1) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4293) := by
    have ha : (tripleCharges (sourceA1172 + difference 1 3) (sourceB1172 + difference 3 1) sourceC1172) = raw19709 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19709; decide +kernel
    rw [ha]
    exact (canonical19709 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1172 + difference 1 4) (sourceB1172 + difference 4 1) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4315) := by
    have ha : (tripleCharges (sourceA1172 + difference 1 4) (sourceB1172 + difference 4 1) sourceC1172) = raw19710 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19710; decide +kernel
    rw [ha]
    exact (canonical19710 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1172 + difference 1 5) (sourceB1172 + difference 5 1) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1172 + difference 1 5) (sourceB1172 + difference 5 1) sourceC1172) = raw4287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw4287; decide +kernel
    rw [ha]
    exact (canonical4287 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1172 + difference 2 0) (sourceB1172 + difference 0 2) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4146) := by
    have ha : (tripleCharges (sourceA1172 + difference 2 0) (sourceB1172 + difference 0 2) sourceC1172) = raw19711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19711; decide +kernel
    rw [ha]
    exact (canonical19711 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1172 + difference 2 1) (sourceB1172 + difference 1 2) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4293) := by
    have ha : (tripleCharges (sourceA1172 + difference 2 1) (sourceB1172 + difference 1 2) sourceC1172) = raw19712 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19712; decide +kernel
    rw [ha]
    exact (canonical19712 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1172 + difference 2 3) (sourceB1172 + difference 3 2) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4293) := by
    have ha : (tripleCharges (sourceA1172 + difference 2 3) (sourceB1172 + difference 3 2) sourceC1172) = raw19713 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19713; decide +kernel
    rw [ha]
    exact (canonical19713 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1172 + difference 2 4) (sourceB1172 + difference 4 2) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4315) := by
    have ha : (tripleCharges (sourceA1172 + difference 2 4) (sourceB1172 + difference 4 2) sourceC1172) = raw19714 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19714; decide +kernel
    rw [ha]
    exact (canonical19714 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1172 + difference 2 5) (sourceB1172 + difference 5 2) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1172 + difference 2 5) (sourceB1172 + difference 5 2) sourceC1172) = raw4292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw4292; decide +kernel
    rw [ha]
    exact (canonical4292 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1172 + difference 3 0) (sourceB1172 + difference 0 3) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4146) := by
    have ha : (tripleCharges (sourceA1172 + difference 3 0) (sourceB1172 + difference 0 3) sourceC1172) = raw19715 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19715; decide +kernel
    rw [ha]
    exact (canonical19715 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1172 + difference 3 1) (sourceB1172 + difference 1 3) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4293) := by
    have ha : (tripleCharges (sourceA1172 + difference 3 1) (sourceB1172 + difference 1 3) sourceC1172) = raw19716 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19716; decide +kernel
    rw [ha]
    exact (canonical19716 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1172 + difference 3 2) (sourceB1172 + difference 2 3) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4293) := by
    have ha : (tripleCharges (sourceA1172 + difference 3 2) (sourceB1172 + difference 2 3) sourceC1172) = raw19717 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19717; decide +kernel
    rw [ha]
    exact (canonical19717 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1172 + difference 3 4) (sourceB1172 + difference 4 3) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4315) := by
    have ha : (tripleCharges (sourceA1172 + difference 3 4) (sourceB1172 + difference 4 3) sourceC1172) = raw19718 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19718; decide +kernel
    rw [ha]
    exact (canonical19718 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1172 + difference 3 5) (sourceB1172 + difference 5 3) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4608) := by
    have ha : (tripleCharges (sourceA1172 + difference 3 5) (sourceB1172 + difference 5 3) sourceC1172) = raw4297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw4297; decide +kernel
    rw [ha]
    exact (canonical4297 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1172 + difference 4 0) (sourceB1172 + difference 0 4) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4181) := by
    have ha : (tripleCharges (sourceA1172 + difference 4 0) (sourceB1172 + difference 0 4) sourceC1172) = raw19719 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19719; decide +kernel
    rw [ha]
    exact (canonical19719 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1172 + difference 4 1) (sourceB1172 + difference 1 4) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1172 + difference 4 1) (sourceB1172 + difference 1 4) sourceC1172) = raw19720 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19720; decide +kernel
    rw [ha]
    exact (canonical19720 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1172 + difference 4 2) (sourceB1172 + difference 2 4) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1172 + difference 4 2) (sourceB1172 + difference 2 4) sourceC1172) = raw19721 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19721; decide +kernel
    rw [ha]
    exact (canonical19721 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1172 + difference 4 3) (sourceB1172 + difference 3 4) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4356) := by
    have ha : (tripleCharges (sourceA1172 + difference 4 3) (sourceB1172 + difference 3 4) sourceC1172) = raw19722 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19722; decide +kernel
    rw [ha]
    exact (canonical19722 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1172 + difference 4 5) (sourceB1172 + difference 5 4) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4625) := by
    have ha : (tripleCharges (sourceA1172 + difference 4 5) (sourceB1172 + difference 5 4) sourceC1172) = raw4302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw4302; decide +kernel
    rw [ha]
    exact (canonical4302 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1172 + difference 5 0) (sourceB1172 + difference 0 5) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4112) := by
    have ha : (tripleCharges (sourceA1172 + difference 5 0) (sourceB1172 + difference 0 5) sourceC1172) = raw19723 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19723; decide +kernel
    rw [ha]
    exact (canonical19723 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1172 + difference 5 1) (sourceB1172 + difference 1 5) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4108) := by
    have ha : (tripleCharges (sourceA1172 + difference 5 1) (sourceB1172 + difference 1 5) sourceC1172) = raw19724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19724; decide +kernel
    rw [ha]
    exact (canonical19724 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1172 + difference 5 2) (sourceB1172 + difference 2 5) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4108) := by
    have ha : (tripleCharges (sourceA1172 + difference 5 2) (sourceB1172 + difference 2 5) sourceC1172) = raw19725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19725; decide +kernel
    rw [ha]
    exact (canonical19725 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1172 + difference 5 3) (sourceB1172 + difference 3 5) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4108) := by
    have ha : (tripleCharges (sourceA1172 + difference 5 3) (sourceB1172 + difference 3 5) sourceC1172) = raw19726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19726; decide +kernel
    rw [ha]
    exact (canonical19726 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1172 + difference 5 4) (sourceB1172 + difference 4 5) sourceC1172) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4134) := by
    have ha : (tripleCharges (sourceA1172 + difference 5 4) (sourceB1172 + difference 4 5) sourceC1172) = raw19727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1172 sourceB1172 sourceC1172 difference raw19727; decide +kernel
    rw [ha]
    exact (canonical19727 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1172 sourceB1172 sourceC1172
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1172, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1173 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1173 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1173 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm1173 : Integer.Sparse Master := [(Sum.inr 545, 3), (Sum.inr 549, 1), (Sum.inr 564, 1), (Sum.inr 574, 3), (Sum.inr 609, 1), (Sum.inr 871, 6), (Sum.inr 893, 3), (Sum.inr 934, 3), (Sum.inr 1046, 3), (Sum.inr 1091, 1), (Sum.inr 1242, 3), (Sum.inr 1304, 1), (Sum.inr 2770, 1)]

theorem sourceEq1173 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1173 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1173 + difference 0 1) (sourceB1173 + difference 1 0) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1173 + difference 0 1) (sourceB1173 + difference 1 0) sourceC1173) = raw4338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw4338; decide +kernel
    rw [ha]
    exact (canonical4338 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1173 + difference 0 2) (sourceB1173 + difference 2 0) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1173 + difference 0 2) (sourceB1173 + difference 2 0) sourceC1173) = raw4339 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw4339; decide +kernel
    rw [ha]
    exact (canonical4339 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1173 + difference 0 3) (sourceB1173 + difference 3 0) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1173 + difference 0 3) (sourceB1173 + difference 3 0) sourceC1173) = raw4340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw4340; decide +kernel
    rw [ha]
    exact (canonical4340 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1173 + difference 0 4) (sourceB1173 + difference 4 0) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA1173 + difference 0 4) (sourceB1173 + difference 4 0) sourceC1173) = raw4341 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw4341; decide +kernel
    rw [ha]
    exact (canonical4341 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1173 + difference 0 5) (sourceB1173 + difference 5 0) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA1173 + difference 0 5) (sourceB1173 + difference 5 0) sourceC1173) = raw19728 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19728; decide +kernel
    rw [ha]
    exact (canonical19728 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1173 + difference 1 0) (sourceB1173 + difference 0 1) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 574) := by
    have ha : (tripleCharges (sourceA1173 + difference 1 0) (sourceB1173 + difference 0 1) sourceC1173) = raw19729 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19729; decide +kernel
    rw [ha]
    exact (canonical19729 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1173 + difference 1 2) (sourceB1173 + difference 2 1) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 871) := by
    have ha : (tripleCharges (sourceA1173 + difference 1 2) (sourceB1173 + difference 2 1) sourceC1173) = raw19730 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19730; decide +kernel
    rw [ha]
    exact (canonical19730 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1173 + difference 1 3) (sourceB1173 + difference 3 1) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 871) := by
    have ha : (tripleCharges (sourceA1173 + difference 1 3) (sourceB1173 + difference 3 1) sourceC1173) = raw19731 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19731; decide +kernel
    rw [ha]
    exact (canonical19731 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1173 + difference 1 4) (sourceB1173 + difference 4 1) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 893) := by
    have ha : (tripleCharges (sourceA1173 + difference 1 4) (sourceB1173 + difference 4 1) sourceC1173) = raw19732 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19732; decide +kernel
    rw [ha]
    exact (canonical19732 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1173 + difference 1 5) (sourceB1173 + difference 5 1) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1173 + difference 1 5) (sourceB1173 + difference 5 1) sourceC1173) = raw4317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw4317; decide +kernel
    rw [ha]
    exact (canonical4317 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1173 + difference 2 0) (sourceB1173 + difference 0 2) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 574) := by
    have ha : (tripleCharges (sourceA1173 + difference 2 0) (sourceB1173 + difference 0 2) sourceC1173) = raw19733 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19733; decide +kernel
    rw [ha]
    exact (canonical19733 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1173 + difference 2 1) (sourceB1173 + difference 1 2) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 871) := by
    have ha : (tripleCharges (sourceA1173 + difference 2 1) (sourceB1173 + difference 1 2) sourceC1173) = raw19734 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19734; decide +kernel
    rw [ha]
    exact (canonical19734 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1173 + difference 2 3) (sourceB1173 + difference 3 2) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 871) := by
    have ha : (tripleCharges (sourceA1173 + difference 2 3) (sourceB1173 + difference 3 2) sourceC1173) = raw19735 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19735; decide +kernel
    rw [ha]
    exact (canonical19735 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1173 + difference 2 4) (sourceB1173 + difference 4 2) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 893) := by
    have ha : (tripleCharges (sourceA1173 + difference 2 4) (sourceB1173 + difference 4 2) sourceC1173) = raw19736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19736; decide +kernel
    rw [ha]
    exact (canonical19736 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1173 + difference 2 5) (sourceB1173 + difference 5 2) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1173 + difference 2 5) (sourceB1173 + difference 5 2) sourceC1173) = raw4322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw4322; decide +kernel
    rw [ha]
    exact (canonical4322 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1173 + difference 3 0) (sourceB1173 + difference 0 3) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 574) := by
    have ha : (tripleCharges (sourceA1173 + difference 3 0) (sourceB1173 + difference 0 3) sourceC1173) = raw19737 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19737; decide +kernel
    rw [ha]
    exact (canonical19737 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1173 + difference 3 1) (sourceB1173 + difference 1 3) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 871) := by
    have ha : (tripleCharges (sourceA1173 + difference 3 1) (sourceB1173 + difference 1 3) sourceC1173) = raw19738 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19738; decide +kernel
    rw [ha]
    exact (canonical19738 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1173 + difference 3 2) (sourceB1173 + difference 2 3) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 871) := by
    have ha : (tripleCharges (sourceA1173 + difference 3 2) (sourceB1173 + difference 2 3) sourceC1173) = raw19739 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19739; decide +kernel
    rw [ha]
    exact (canonical19739 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1173 + difference 3 4) (sourceB1173 + difference 4 3) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 893) := by
    have ha : (tripleCharges (sourceA1173 + difference 3 4) (sourceB1173 + difference 4 3) sourceC1173) = raw19740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19740; decide +kernel
    rw [ha]
    exact (canonical19740 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1173 + difference 3 5) (sourceB1173 + difference 5 3) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1173 + difference 3 5) (sourceB1173 + difference 5 3) sourceC1173) = raw4327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw4327; decide +kernel
    rw [ha]
    exact (canonical4327 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1173 + difference 4 0) (sourceB1173 + difference 0 4) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 609) := by
    have ha : (tripleCharges (sourceA1173 + difference 4 0) (sourceB1173 + difference 0 4) sourceC1173) = raw19741 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19741; decide +kernel
    rw [ha]
    exact (canonical19741 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1173 + difference 4 1) (sourceB1173 + difference 1 4) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 934) := by
    have ha : (tripleCharges (sourceA1173 + difference 4 1) (sourceB1173 + difference 1 4) sourceC1173) = raw19742 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19742; decide +kernel
    rw [ha]
    exact (canonical19742 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1173 + difference 4 2) (sourceB1173 + difference 2 4) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 934) := by
    have ha : (tripleCharges (sourceA1173 + difference 4 2) (sourceB1173 + difference 2 4) sourceC1173) = raw19743 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19743; decide +kernel
    rw [ha]
    exact (canonical19743 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1173 + difference 4 3) (sourceB1173 + difference 3 4) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 934) := by
    have ha : (tripleCharges (sourceA1173 + difference 4 3) (sourceB1173 + difference 3 4) sourceC1173) = raw19744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19744; decide +kernel
    rw [ha]
    exact (canonical19744 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1173 + difference 4 5) (sourceB1173 + difference 5 4) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1304) := by
    have ha : (tripleCharges (sourceA1173 + difference 4 5) (sourceB1173 + difference 5 4) sourceC1173) = raw4332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw4332; decide +kernel
    rw [ha]
    exact (canonical4332 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1173 + difference 5 0) (sourceB1173 + difference 0 5) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 549) := by
    have ha : (tripleCharges (sourceA1173 + difference 5 0) (sourceB1173 + difference 0 5) sourceC1173) = raw19745 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19745; decide +kernel
    rw [ha]
    exact (canonical19745 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1173 + difference 5 1) (sourceB1173 + difference 1 5) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 545) := by
    have ha : (tripleCharges (sourceA1173 + difference 5 1) (sourceB1173 + difference 1 5) sourceC1173) = raw19746 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19746; decide +kernel
    rw [ha]
    exact (canonical19746 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1173 + difference 5 2) (sourceB1173 + difference 2 5) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 545) := by
    have ha : (tripleCharges (sourceA1173 + difference 5 2) (sourceB1173 + difference 2 5) sourceC1173) = raw19747 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19747; decide +kernel
    rw [ha]
    exact (canonical19747 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1173 + difference 5 3) (sourceB1173 + difference 3 5) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 545) := by
    have ha : (tripleCharges (sourceA1173 + difference 5 3) (sourceB1173 + difference 3 5) sourceC1173) = raw19748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19748; decide +kernel
    rw [ha]
    exact (canonical19748 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1173 + difference 5 4) (sourceB1173 + difference 4 5) sourceC1173) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 564) := by
    have ha : (tripleCharges (sourceA1173 + difference 5 4) (sourceB1173 + difference 4 5) sourceC1173) = raw19749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1173 sourceB1173 sourceC1173 difference raw19749; decide +kernel
    rw [ha]
    exact (canonical19749 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1173 sourceB1173 sourceC1173
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1173, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1174 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1174 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1174 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1174 : Integer.Sparse Master := [(Sum.inr 4257, 3), (Sum.inr 4274, 1), (Sum.inr 4280, 1), (Sum.inr 4394, 6), (Sum.inr 4405, 3), (Sum.inr 4413, 3), (Sum.inr 4445, 3), (Sum.inr 4468, 4), (Sum.inr 4481, 1), (Sum.inr 4512, 1), (Sum.inr 4594, 3), (Sum.inr 4629, 1)]

theorem sourceEq1174 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1174 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1174 + difference 0 1) (sourceB1174 + difference 1 0) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4445) := by
    have ha : (tripleCharges (sourceA1174 + difference 0 1) (sourceB1174 + difference 1 0) sourceC1174) = raw19750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19750; decide +kernel
    rw [ha]
    exact (canonical19750 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1174 + difference 0 2) (sourceB1174 + difference 2 0) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4445) := by
    have ha : (tripleCharges (sourceA1174 + difference 0 2) (sourceB1174 + difference 2 0) sourceC1174) = raw19751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19751; decide +kernel
    rw [ha]
    exact (canonical19751 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1174 + difference 0 3) (sourceB1174 + difference 3 0) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4445) := by
    have ha : (tripleCharges (sourceA1174 + difference 0 3) (sourceB1174 + difference 3 0) sourceC1174) = raw19752 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19752; decide +kernel
    rw [ha]
    exact (canonical19752 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1174 + difference 0 4) (sourceB1174 + difference 4 0) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4481) := by
    have ha : (tripleCharges (sourceA1174 + difference 0 4) (sourceB1174 + difference 4 0) sourceC1174) = raw19753 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19753; decide +kernel
    rw [ha]
    exact (canonical19753 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1174 + difference 0 5) (sourceB1174 + difference 5 0) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1174 + difference 0 5) (sourceB1174 + difference 5 0) sourceC1174) = raw19558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19558; decide +kernel
    rw [ha]
    exact (canonical19558 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1174 + difference 1 0) (sourceB1174 + difference 0 1) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1174 + difference 1 0) (sourceB1174 + difference 0 1) sourceC1174) = raw19754 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19754; decide +kernel
    rw [ha]
    exact (canonical19754 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1174 + difference 1 2) (sourceB1174 + difference 2 1) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4394) := by
    have ha : (tripleCharges (sourceA1174 + difference 1 2) (sourceB1174 + difference 2 1) sourceC1174) = raw19755 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19755; decide +kernel
    rw [ha]
    exact (canonical19755 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1174 + difference 1 3) (sourceB1174 + difference 3 1) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4394) := by
    have ha : (tripleCharges (sourceA1174 + difference 1 3) (sourceB1174 + difference 3 1) sourceC1174) = raw19756 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19756; decide +kernel
    rw [ha]
    exact (canonical19756 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1174 + difference 1 4) (sourceB1174 + difference 4 1) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4413) := by
    have ha : (tripleCharges (sourceA1174 + difference 1 4) (sourceB1174 + difference 4 1) sourceC1174) = raw19757 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19757; decide +kernel
    rw [ha]
    exact (canonical19757 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1174 + difference 1 5) (sourceB1174 + difference 5 1) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1174 + difference 1 5) (sourceB1174 + difference 5 1) sourceC1174) = raw19563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19563; decide +kernel
    rw [ha]
    exact (canonical19563 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1174 + difference 2 0) (sourceB1174 + difference 0 2) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1174 + difference 2 0) (sourceB1174 + difference 0 2) sourceC1174) = raw19758 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19758; decide +kernel
    rw [ha]
    exact (canonical19758 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1174 + difference 2 1) (sourceB1174 + difference 1 2) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4394) := by
    have ha : (tripleCharges (sourceA1174 + difference 2 1) (sourceB1174 + difference 1 2) sourceC1174) = raw19759 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19759; decide +kernel
    rw [ha]
    exact (canonical19759 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1174 + difference 2 3) (sourceB1174 + difference 3 2) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4394) := by
    have ha : (tripleCharges (sourceA1174 + difference 2 3) (sourceB1174 + difference 3 2) sourceC1174) = raw19760 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19760; decide +kernel
    rw [ha]
    exact (canonical19760 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1174 + difference 2 4) (sourceB1174 + difference 4 2) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4413) := by
    have ha : (tripleCharges (sourceA1174 + difference 2 4) (sourceB1174 + difference 4 2) sourceC1174) = raw19761 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19761; decide +kernel
    rw [ha]
    exact (canonical19761 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1174 + difference 2 5) (sourceB1174 + difference 5 2) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1174 + difference 2 5) (sourceB1174 + difference 5 2) sourceC1174) = raw19568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19568; decide +kernel
    rw [ha]
    exact (canonical19568 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1174 + difference 3 0) (sourceB1174 + difference 0 3) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4405) := by
    have ha : (tripleCharges (sourceA1174 + difference 3 0) (sourceB1174 + difference 0 3) sourceC1174) = raw19762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19762; decide +kernel
    rw [ha]
    exact (canonical19762 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1174 + difference 3 1) (sourceB1174 + difference 1 3) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4394) := by
    have ha : (tripleCharges (sourceA1174 + difference 3 1) (sourceB1174 + difference 1 3) sourceC1174) = raw19763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19763; decide +kernel
    rw [ha]
    exact (canonical19763 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1174 + difference 3 2) (sourceB1174 + difference 2 3) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4394) := by
    have ha : (tripleCharges (sourceA1174 + difference 3 2) (sourceB1174 + difference 2 3) sourceC1174) = raw19764 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19764; decide +kernel
    rw [ha]
    exact (canonical19764 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1174 + difference 3 4) (sourceB1174 + difference 4 3) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4413) := by
    have ha : (tripleCharges (sourceA1174 + difference 3 4) (sourceB1174 + difference 4 3) sourceC1174) = raw19765 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19765; decide +kernel
    rw [ha]
    exact (canonical19765 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1174 + difference 3 5) (sourceB1174 + difference 5 3) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4594) := by
    have ha : (tripleCharges (sourceA1174 + difference 3 5) (sourceB1174 + difference 5 3) sourceC1174) = raw19573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19573; decide +kernel
    rw [ha]
    exact (canonical19573 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1174 + difference 4 0) (sourceB1174 + difference 0 4) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4512) := by
    have ha : (tripleCharges (sourceA1174 + difference 4 0) (sourceB1174 + difference 0 4) sourceC1174) = raw19580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19580; decide +kernel
    rw [ha]
    exact (canonical19580 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1174 + difference 4 1) (sourceB1174 + difference 1 4) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1174 + difference 4 1) (sourceB1174 + difference 1 4) sourceC1174) = raw19581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19581; decide +kernel
    rw [ha]
    exact (canonical19581 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1174 + difference 4 2) (sourceB1174 + difference 2 4) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1174 + difference 4 2) (sourceB1174 + difference 2 4) sourceC1174) = raw19582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19582; decide +kernel
    rw [ha]
    exact (canonical19582 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1174 + difference 4 3) (sourceB1174 + difference 3 4) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4468) := by
    have ha : (tripleCharges (sourceA1174 + difference 4 3) (sourceB1174 + difference 3 4) sourceC1174) = raw19583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19583; decide +kernel
    rw [ha]
    exact (canonical19583 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1174 + difference 4 5) (sourceB1174 + difference 5 4) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4629) := by
    have ha : (tripleCharges (sourceA1174 + difference 4 5) (sourceB1174 + difference 5 4) sourceC1174) = raw19766 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19766; decide +kernel
    rw [ha]
    exact (canonical19766 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1174 + difference 5 0) (sourceB1174 + difference 0 5) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4274) := by
    have ha : (tripleCharges (sourceA1174 + difference 5 0) (sourceB1174 + difference 0 5) sourceC1174) = raw19767 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19767; decide +kernel
    rw [ha]
    exact (canonical19767 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1174 + difference 5 1) (sourceB1174 + difference 1 5) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4257) := by
    have ha : (tripleCharges (sourceA1174 + difference 5 1) (sourceB1174 + difference 1 5) sourceC1174) = raw19768 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19768; decide +kernel
    rw [ha]
    exact (canonical19768 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1174 + difference 5 2) (sourceB1174 + difference 2 5) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4257) := by
    have ha : (tripleCharges (sourceA1174 + difference 5 2) (sourceB1174 + difference 2 5) sourceC1174) = raw19769 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19769; decide +kernel
    rw [ha]
    exact (canonical19769 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1174 + difference 5 3) (sourceB1174 + difference 3 5) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4257) := by
    have ha : (tripleCharges (sourceA1174 + difference 5 3) (sourceB1174 + difference 3 5) sourceC1174) = raw19770 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19770; decide +kernel
    rw [ha]
    exact (canonical19770 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1174 + difference 5 4) (sourceB1174 + difference 4 5) sourceC1174) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4280) := by
    have ha : (tripleCharges (sourceA1174 + difference 5 4) (sourceB1174 + difference 4 5) sourceC1174) = raw19771 := by
      apply Matrix.ext; unfold tripleCharges sourceA1174 sourceB1174 sourceC1174 difference raw19771; decide +kernel
    rw [ha]
    exact (canonical19771 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1174 sourceB1174 sourceC1174
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1174, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1175 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1175 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1175 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1175 : Integer.Sparse Master := [(Sum.inr 791, 3), (Sum.inr 817, 1), (Sum.inr 832, 1), (Sum.inr 975, 6), (Sum.inr 986, 3), (Sum.inr 994, 3), (Sum.inr 1027, 3), (Sum.inr 1051, 3), (Sum.inr 1064, 1), (Sum.inr 1096, 1), (Sum.inr 1221, 3), (Sum.inr 1275, 1), (Sum.inr 1313, 1)]

theorem sourceEq1175 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1175 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1175 + difference 0 1) (sourceB1175 + difference 1 0) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1027) := by
    have ha : (tripleCharges (sourceA1175 + difference 0 1) (sourceB1175 + difference 1 0) sourceC1175) = raw19772 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19772; decide +kernel
    rw [ha]
    exact (canonical19772 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1175 + difference 0 2) (sourceB1175 + difference 2 0) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1027) := by
    have ha : (tripleCharges (sourceA1175 + difference 0 2) (sourceB1175 + difference 2 0) sourceC1175) = raw19773 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19773; decide +kernel
    rw [ha]
    exact (canonical19773 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1175 + difference 0 3) (sourceB1175 + difference 3 0) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1027) := by
    have ha : (tripleCharges (sourceA1175 + difference 0 3) (sourceB1175 + difference 3 0) sourceC1175) = raw19774 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19774; decide +kernel
    rw [ha]
    exact (canonical19774 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1175 + difference 0 4) (sourceB1175 + difference 4 0) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1064) := by
    have ha : (tripleCharges (sourceA1175 + difference 0 4) (sourceB1175 + difference 4 0) sourceC1175) = raw19775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19775; decide +kernel
    rw [ha]
    exact (canonical19775 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1175 + difference 0 5) (sourceB1175 + difference 5 0) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1275) := by
    have ha : (tripleCharges (sourceA1175 + difference 0 5) (sourceB1175 + difference 5 0) sourceC1175) = raw19588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19588; decide +kernel
    rw [ha]
    exact (canonical19588 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1175 + difference 1 0) (sourceB1175 + difference 0 1) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 986) := by
    have ha : (tripleCharges (sourceA1175 + difference 1 0) (sourceB1175 + difference 0 1) sourceC1175) = raw19776 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19776; decide +kernel
    rw [ha]
    exact (canonical19776 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1175 + difference 1 2) (sourceB1175 + difference 2 1) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 975) := by
    have ha : (tripleCharges (sourceA1175 + difference 1 2) (sourceB1175 + difference 2 1) sourceC1175) = raw19777 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19777; decide +kernel
    rw [ha]
    exact (canonical19777 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1175 + difference 1 3) (sourceB1175 + difference 3 1) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 975) := by
    have ha : (tripleCharges (sourceA1175 + difference 1 3) (sourceB1175 + difference 3 1) sourceC1175) = raw19778 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19778; decide +kernel
    rw [ha]
    exact (canonical19778 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1175 + difference 1 4) (sourceB1175 + difference 4 1) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 994) := by
    have ha : (tripleCharges (sourceA1175 + difference 1 4) (sourceB1175 + difference 4 1) sourceC1175) = raw19779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19779; decide +kernel
    rw [ha]
    exact (canonical19779 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1175 + difference 1 5) (sourceB1175 + difference 5 1) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1175 + difference 1 5) (sourceB1175 + difference 5 1) sourceC1175) = raw19593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19593; decide +kernel
    rw [ha]
    exact (canonical19593 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1175 + difference 2 0) (sourceB1175 + difference 0 2) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 986) := by
    have ha : (tripleCharges (sourceA1175 + difference 2 0) (sourceB1175 + difference 0 2) sourceC1175) = raw19780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19780; decide +kernel
    rw [ha]
    exact (canonical19780 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1175 + difference 2 1) (sourceB1175 + difference 1 2) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 975) := by
    have ha : (tripleCharges (sourceA1175 + difference 2 1) (sourceB1175 + difference 1 2) sourceC1175) = raw19781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19781; decide +kernel
    rw [ha]
    exact (canonical19781 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1175 + difference 2 3) (sourceB1175 + difference 3 2) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 975) := by
    have ha : (tripleCharges (sourceA1175 + difference 2 3) (sourceB1175 + difference 3 2) sourceC1175) = raw19782 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19782; decide +kernel
    rw [ha]
    exact (canonical19782 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1175 + difference 2 4) (sourceB1175 + difference 4 2) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 994) := by
    have ha : (tripleCharges (sourceA1175 + difference 2 4) (sourceB1175 + difference 4 2) sourceC1175) = raw19783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19783; decide +kernel
    rw [ha]
    exact (canonical19783 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1175 + difference 2 5) (sourceB1175 + difference 5 2) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1175 + difference 2 5) (sourceB1175 + difference 5 2) sourceC1175) = raw19598 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19598; decide +kernel
    rw [ha]
    exact (canonical19598 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1175 + difference 3 0) (sourceB1175 + difference 0 3) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 986) := by
    have ha : (tripleCharges (sourceA1175 + difference 3 0) (sourceB1175 + difference 0 3) sourceC1175) = raw19784 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19784; decide +kernel
    rw [ha]
    exact (canonical19784 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1175 + difference 3 1) (sourceB1175 + difference 1 3) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 975) := by
    have ha : (tripleCharges (sourceA1175 + difference 3 1) (sourceB1175 + difference 1 3) sourceC1175) = raw19785 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19785; decide +kernel
    rw [ha]
    exact (canonical19785 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1175 + difference 3 2) (sourceB1175 + difference 2 3) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 975) := by
    have ha : (tripleCharges (sourceA1175 + difference 3 2) (sourceB1175 + difference 2 3) sourceC1175) = raw19786 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19786; decide +kernel
    rw [ha]
    exact (canonical19786 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1175 + difference 3 4) (sourceB1175 + difference 4 3) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 994) := by
    have ha : (tripleCharges (sourceA1175 + difference 3 4) (sourceB1175 + difference 4 3) sourceC1175) = raw19787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19787; decide +kernel
    rw [ha]
    exact (canonical19787 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1175 + difference 3 5) (sourceB1175 + difference 5 3) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1175 + difference 3 5) (sourceB1175 + difference 5 3) sourceC1175) = raw19603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19603; decide +kernel
    rw [ha]
    exact (canonical19603 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1175 + difference 4 0) (sourceB1175 + difference 0 4) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1096) := by
    have ha : (tripleCharges (sourceA1175 + difference 4 0) (sourceB1175 + difference 0 4) sourceC1175) = raw19610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19610; decide +kernel
    rw [ha]
    exact (canonical19610 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1175 + difference 4 1) (sourceB1175 + difference 1 4) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1175 + difference 4 1) (sourceB1175 + difference 1 4) sourceC1175) = raw19611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19611; decide +kernel
    rw [ha]
    exact (canonical19611 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1175 + difference 4 2) (sourceB1175 + difference 2 4) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1175 + difference 4 2) (sourceB1175 + difference 2 4) sourceC1175) = raw19612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19612; decide +kernel
    rw [ha]
    exact (canonical19612 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1175 + difference 4 3) (sourceB1175 + difference 3 4) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1175 + difference 4 3) (sourceB1175 + difference 3 4) sourceC1175) = raw19613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19613; decide +kernel
    rw [ha]
    exact (canonical19613 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1175 + difference 4 5) (sourceB1175 + difference 5 4) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1313) := by
    have ha : (tripleCharges (sourceA1175 + difference 4 5) (sourceB1175 + difference 5 4) sourceC1175) = raw19788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19788; decide +kernel
    rw [ha]
    exact (canonical19788 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1175 + difference 5 0) (sourceB1175 + difference 0 5) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 817) := by
    have ha : (tripleCharges (sourceA1175 + difference 5 0) (sourceB1175 + difference 0 5) sourceC1175) = raw19789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19789; decide +kernel
    rw [ha]
    exact (canonical19789 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1175 + difference 5 1) (sourceB1175 + difference 1 5) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 791) := by
    have ha : (tripleCharges (sourceA1175 + difference 5 1) (sourceB1175 + difference 1 5) sourceC1175) = raw19790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19790; decide +kernel
    rw [ha]
    exact (canonical19790 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1175 + difference 5 2) (sourceB1175 + difference 2 5) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 791) := by
    have ha : (tripleCharges (sourceA1175 + difference 5 2) (sourceB1175 + difference 2 5) sourceC1175) = raw19791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19791; decide +kernel
    rw [ha]
    exact (canonical19791 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1175 + difference 5 3) (sourceB1175 + difference 3 5) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 791) := by
    have ha : (tripleCharges (sourceA1175 + difference 5 3) (sourceB1175 + difference 3 5) sourceC1175) = raw19792 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19792; decide +kernel
    rw [ha]
    exact (canonical19792 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1175 + difference 5 4) (sourceB1175 + difference 4 5) sourceC1175) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 832) := by
    have ha : (tripleCharges (sourceA1175 + difference 5 4) (sourceB1175 + difference 4 5) sourceC1175) = raw19793 := by
      apply Matrix.ext; unfold tripleCharges sourceA1175 sourceB1175 sourceC1175 difference raw19793; decide +kernel
    rw [ha]
    exact (canonical19793 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1175 sourceB1175 sourceC1175
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1175, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1176 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1176 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1176 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1176 : Integer.Sparse Master := [(Sum.inr 1027, 3), (Sum.inr 1051, 1), (Sum.inr 1064, 1), (Sum.inr 1209, 6), (Sum.inr 1221, 3), (Sum.inr 1227, 3), (Sum.inr 1255, 3), (Sum.inr 1275, 3), (Sum.inr 1285, 1), (Sum.inr 1313, 1), (Sum.inr 1402, 3), (Sum.inr 1432, 1), (Sum.inr 1456, 1)]

theorem sourceEq1176 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1176 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1176 + difference 0 1) (sourceB1176 + difference 1 0) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1027) := by
    have ha : (tripleCharges (sourceA1176 + difference 0 1) (sourceB1176 + difference 1 0) sourceC1176) = raw19794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19794; decide +kernel
    rw [ha]
    exact (canonical19794 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1176 + difference 0 2) (sourceB1176 + difference 2 0) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1027) := by
    have ha : (tripleCharges (sourceA1176 + difference 0 2) (sourceB1176 + difference 2 0) sourceC1176) = raw19795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19795; decide +kernel
    rw [ha]
    exact (canonical19795 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1176 + difference 0 3) (sourceB1176 + difference 3 0) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1027) := by
    have ha : (tripleCharges (sourceA1176 + difference 0 3) (sourceB1176 + difference 3 0) sourceC1176) = raw19796 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19796; decide +kernel
    rw [ha]
    exact (canonical19796 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1176 + difference 0 4) (sourceB1176 + difference 4 0) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1064) := by
    have ha : (tripleCharges (sourceA1176 + difference 0 4) (sourceB1176 + difference 4 0) sourceC1176) = raw19797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19797; decide +kernel
    rw [ha]
    exact (canonical19797 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1176 + difference 0 5) (sourceB1176 + difference 5 0) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1051) := by
    have ha : (tripleCharges (sourceA1176 + difference 0 5) (sourceB1176 + difference 5 0) sourceC1176) = raw19798 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19798; decide +kernel
    rw [ha]
    exact (canonical19798 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1176 + difference 1 0) (sourceB1176 + difference 0 1) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1402) := by
    have ha : (tripleCharges (sourceA1176 + difference 1 0) (sourceB1176 + difference 0 1) sourceC1176) = raw19799 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19799; decide +kernel
    rw [ha]
    exact (canonical19799 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1176 + difference 1 2) (sourceB1176 + difference 2 1) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1209) := by
    have ha : (tripleCharges (sourceA1176 + difference 1 2) (sourceB1176 + difference 2 1) sourceC1176) = raw19800 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19800; decide +kernel
    rw [ha]
    exact (canonical19800 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1176 + difference 1 3) (sourceB1176 + difference 3 1) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1209) := by
    have ha : (tripleCharges (sourceA1176 + difference 1 3) (sourceB1176 + difference 3 1) sourceC1176) = raw19801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19801; decide +kernel
    rw [ha]
    exact (canonical19801 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1176 + difference 1 4) (sourceB1176 + difference 4 1) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1227) := by
    have ha : (tripleCharges (sourceA1176 + difference 1 4) (sourceB1176 + difference 4 1) sourceC1176) = raw19802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19802; decide +kernel
    rw [ha]
    exact (canonical19802 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1176 + difference 1 5) (sourceB1176 + difference 5 1) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1176 + difference 1 5) (sourceB1176 + difference 5 1) sourceC1176) = raw19803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19803; decide +kernel
    rw [ha]
    exact (canonical19803 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1176 + difference 2 0) (sourceB1176 + difference 0 2) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1402) := by
    have ha : (tripleCharges (sourceA1176 + difference 2 0) (sourceB1176 + difference 0 2) sourceC1176) = raw19804 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19804; decide +kernel
    rw [ha]
    exact (canonical19804 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1176 + difference 2 1) (sourceB1176 + difference 1 2) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1209) := by
    have ha : (tripleCharges (sourceA1176 + difference 2 1) (sourceB1176 + difference 1 2) sourceC1176) = raw19805 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19805; decide +kernel
    rw [ha]
    exact (canonical19805 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1176 + difference 2 3) (sourceB1176 + difference 3 2) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1209) := by
    have ha : (tripleCharges (sourceA1176 + difference 2 3) (sourceB1176 + difference 3 2) sourceC1176) = raw19806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19806; decide +kernel
    rw [ha]
    exact (canonical19806 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1176 + difference 2 4) (sourceB1176 + difference 4 2) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1227) := by
    have ha : (tripleCharges (sourceA1176 + difference 2 4) (sourceB1176 + difference 4 2) sourceC1176) = raw19807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19807; decide +kernel
    rw [ha]
    exact (canonical19807 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1176 + difference 2 5) (sourceB1176 + difference 5 2) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1176 + difference 2 5) (sourceB1176 + difference 5 2) sourceC1176) = raw19808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19808; decide +kernel
    rw [ha]
    exact (canonical19808 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1176 + difference 3 0) (sourceB1176 + difference 0 3) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1402) := by
    have ha : (tripleCharges (sourceA1176 + difference 3 0) (sourceB1176 + difference 0 3) sourceC1176) = raw19809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19809; decide +kernel
    rw [ha]
    exact (canonical19809 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1176 + difference 3 1) (sourceB1176 + difference 1 3) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1209) := by
    have ha : (tripleCharges (sourceA1176 + difference 3 1) (sourceB1176 + difference 1 3) sourceC1176) = raw19810 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19810; decide +kernel
    rw [ha]
    exact (canonical19810 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1176 + difference 3 2) (sourceB1176 + difference 2 3) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1209) := by
    have ha : (tripleCharges (sourceA1176 + difference 3 2) (sourceB1176 + difference 2 3) sourceC1176) = raw19811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19811; decide +kernel
    rw [ha]
    exact (canonical19811 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1176 + difference 3 4) (sourceB1176 + difference 4 3) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1227) := by
    have ha : (tripleCharges (sourceA1176 + difference 3 4) (sourceB1176 + difference 4 3) sourceC1176) = raw19812 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19812; decide +kernel
    rw [ha]
    exact (canonical19812 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1176 + difference 3 5) (sourceB1176 + difference 5 3) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1221) := by
    have ha : (tripleCharges (sourceA1176 + difference 3 5) (sourceB1176 + difference 5 3) sourceC1176) = raw19813 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19813; decide +kernel
    rw [ha]
    exact (canonical19813 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1176 + difference 4 0) (sourceB1176 + difference 0 4) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1456) := by
    have ha : (tripleCharges (sourceA1176 + difference 4 0) (sourceB1176 + difference 0 4) sourceC1176) = raw19814 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19814; decide +kernel
    rw [ha]
    exact (canonical19814 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1176 + difference 4 1) (sourceB1176 + difference 1 4) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1275) := by
    have ha : (tripleCharges (sourceA1176 + difference 4 1) (sourceB1176 + difference 1 4) sourceC1176) = raw19815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19815; decide +kernel
    rw [ha]
    exact (canonical19815 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1176 + difference 4 2) (sourceB1176 + difference 2 4) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1275) := by
    have ha : (tripleCharges (sourceA1176 + difference 4 2) (sourceB1176 + difference 2 4) sourceC1176) = raw19816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19816; decide +kernel
    rw [ha]
    exact (canonical19816 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1176 + difference 4 3) (sourceB1176 + difference 3 4) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1275) := by
    have ha : (tripleCharges (sourceA1176 + difference 4 3) (sourceB1176 + difference 3 4) sourceC1176) = raw19817 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19817; decide +kernel
    rw [ha]
    exact (canonical19817 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1176 + difference 4 5) (sourceB1176 + difference 5 4) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1313) := by
    have ha : (tripleCharges (sourceA1176 + difference 4 5) (sourceB1176 + difference 5 4) sourceC1176) = raw19818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19818; decide +kernel
    rw [ha]
    exact (canonical19818 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1176 + difference 5 0) (sourceB1176 + difference 0 5) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1432) := by
    have ha : (tripleCharges (sourceA1176 + difference 5 0) (sourceB1176 + difference 0 5) sourceC1176) = raw19819 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19819; decide +kernel
    rw [ha]
    exact (canonical19819 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1176 + difference 5 1) (sourceB1176 + difference 1 5) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1255) := by
    have ha : (tripleCharges (sourceA1176 + difference 5 1) (sourceB1176 + difference 1 5) sourceC1176) = raw19820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19820; decide +kernel
    rw [ha]
    exact (canonical19820 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1176 + difference 5 2) (sourceB1176 + difference 2 5) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1255) := by
    have ha : (tripleCharges (sourceA1176 + difference 5 2) (sourceB1176 + difference 2 5) sourceC1176) = raw19821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19821; decide +kernel
    rw [ha]
    exact (canonical19821 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1176 + difference 5 3) (sourceB1176 + difference 3 5) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1255) := by
    have ha : (tripleCharges (sourceA1176 + difference 5 3) (sourceB1176 + difference 3 5) sourceC1176) = raw19822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19822; decide +kernel
    rw [ha]
    exact (canonical19822 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1176 + difference 5 4) (sourceB1176 + difference 4 5) sourceC1176) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1285) := by
    have ha : (tripleCharges (sourceA1176 + difference 5 4) (sourceB1176 + difference 4 5) sourceC1176) = raw19823 := by
      apply Matrix.ext; unfold tripleCharges sourceA1176 sourceB1176 sourceC1176 difference raw19823; decide +kernel
    rw [ha]
    exact (canonical19823 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1176 sourceB1176 sourceC1176
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1176, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1177 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB1177 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceC1177 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1177 : Integer.Sparse Master := [(Sum.inr 855, 1), (Sum.inr 1620, 3), (Sum.inr 1752, 1), (Sum.inr 1758, 1), (Sum.inr 4072, -1)]

theorem sourceEq1177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1177 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1177 + difference 0 0) (sourceB1177 + difference 0 0) sourceC1177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1752) := by
    have ha : (tripleCharges (sourceA1177 + difference 0 0) (sourceB1177 + difference 0 0) sourceC1177) = raw19824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1177 sourceB1177 sourceC1177 difference raw19824; decide +kernel
    rw [ha]
    exact (canonical19824 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1177 + difference 1 0) (sourceB1177 + difference 0 1) sourceC1177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1620) := by
    have ha : (tripleCharges (sourceA1177 + difference 1 0) (sourceB1177 + difference 0 1) sourceC1177) = raw19825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1177 sourceB1177 sourceC1177 difference raw19825; decide +kernel
    rw [ha]
    exact (canonical19825 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1177 + difference 2 0) (sourceB1177 + difference 0 2) sourceC1177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1620) := by
    have ha : (tripleCharges (sourceA1177 + difference 2 0) (sourceB1177 + difference 0 2) sourceC1177) = raw19826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1177 sourceB1177 sourceC1177 difference raw19826; decide +kernel
    rw [ha]
    exact (canonical19826 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1177 + difference 3 0) (sourceB1177 + difference 0 3) sourceC1177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1620) := by
    have ha : (tripleCharges (sourceA1177 + difference 3 0) (sourceB1177 + difference 0 3) sourceC1177) = raw19827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1177 sourceB1177 sourceC1177 difference raw19827; decide +kernel
    rw [ha]
    exact (canonical19827 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1177 + difference 4 0) (sourceB1177 + difference 0 4) sourceC1177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1758) := by
    have ha : (tripleCharges (sourceA1177 + difference 4 0) (sourceB1177 + difference 0 4) sourceC1177) = raw19828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1177 sourceB1177 sourceC1177 difference raw19828; decide +kernel
    rw [ha]
    exact (canonical19828 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1177 + difference 5 0) (sourceB1177 + difference 0 5) sourceC1177) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 855) := by
    have ha : (tripleCharges (sourceA1177 + difference 5 0) (sourceB1177 + difference 0 5) sourceC1177) = raw19829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1177 sourceB1177 sourceC1177 difference raw19829; decide +kernel
    rw [ha]
    exact (canonical19829 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1177 + sourceB1177) sourceC1177) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1177 + sourceB1177) sourceC1177) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1177 sourceB1177 sourceC1177 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1177 sourceB1177 sourceC1177
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1177, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1178 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1178 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1178 : Charge := ![2, 0, 0, 0, 2, -4]
def sourceForm1178 : Integer.Sparse Master := [(Sum.inr 826, 3), (Sum.inr 832, 1), (Sum.inr 859, 1), (Sum.inr 1741, 1), (Sum.inr 4071, -1)]

theorem sourceEq1178 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1178 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1178 + difference 0 0) (sourceB1178 + difference 0 0) sourceC1178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 832) := by
    have ha : (tripleCharges (sourceA1178 + difference 0 0) (sourceB1178 + difference 0 0) sourceC1178) = raw19830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1178 sourceB1178 sourceC1178 difference raw19830; decide +kernel
    rw [ha]
    exact (canonical19830 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1178 + difference 0 1) (sourceB1178 + difference 1 0) sourceC1178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 826) := by
    have ha : (tripleCharges (sourceA1178 + difference 0 1) (sourceB1178 + difference 1 0) sourceC1178) = raw19831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1178 sourceB1178 sourceC1178 difference raw19831; decide +kernel
    rw [ha]
    exact (canonical19831 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1178 + difference 0 2) (sourceB1178 + difference 2 0) sourceC1178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 826) := by
    have ha : (tripleCharges (sourceA1178 + difference 0 2) (sourceB1178 + difference 2 0) sourceC1178) = raw19832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1178 sourceB1178 sourceC1178 difference raw19832; decide +kernel
    rw [ha]
    exact (canonical19832 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1178 + difference 0 3) (sourceB1178 + difference 3 0) sourceC1178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 826) := by
    have ha : (tripleCharges (sourceA1178 + difference 0 3) (sourceB1178 + difference 3 0) sourceC1178) = raw19833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1178 sourceB1178 sourceC1178 difference raw19833; decide +kernel
    rw [ha]
    exact (canonical19833 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1178 + difference 0 4) (sourceB1178 + difference 4 0) sourceC1178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 859) := by
    have ha : (tripleCharges (sourceA1178 + difference 0 4) (sourceB1178 + difference 4 0) sourceC1178) = raw19834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1178 sourceB1178 sourceC1178 difference raw19834; decide +kernel
    rw [ha]
    exact (canonical19834 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1178 + difference 0 5) (sourceB1178 + difference 5 0) sourceC1178) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA1178 + difference 0 5) (sourceB1178 + difference 5 0) sourceC1178) = raw19835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1178 sourceB1178 sourceC1178 difference raw19835; decide +kernel
    rw [ha]
    exact (canonical19835 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1178 + sourceB1178) sourceC1178) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1178 + sourceB1178) sourceC1178) = raw19836 := by
      apply Matrix.ext; unfold doubleCharges sourceA1178 sourceB1178 sourceC1178 raw19836; decide +kernel
    rw [ha]
    exact (canonical19836 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1178 sourceB1178 sourceC1178
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1178, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1179 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1179 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1179 : Charge := ![2, 0, 0, 0, 2, -4]
def sourceForm1179 : Integer.Sparse Master := [(Sum.inr 564, 1), (Sum.inr 726, 3), (Sum.inr 832, 1), (Sum.inr 859, 1), (Sum.inr 4071, -1)]

theorem sourceEq1179 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1179 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1179 + difference 0 4) (sourceB1179 + difference 4 0) sourceC1179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 859) := by
    have ha : (tripleCharges (sourceA1179 + difference 0 4) (sourceB1179 + difference 4 0) sourceC1179) = raw19834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1179 sourceB1179 sourceC1179 difference raw19834; decide +kernel
    rw [ha]
    exact (canonical19834 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1179 + difference 1 4) (sourceB1179 + difference 4 1) sourceC1179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 726) := by
    have ha : (tripleCharges (sourceA1179 + difference 1 4) (sourceB1179 + difference 4 1) sourceC1179) = raw19837 := by
      apply Matrix.ext; unfold tripleCharges sourceA1179 sourceB1179 sourceC1179 difference raw19837; decide +kernel
    rw [ha]
    exact (canonical19837 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1179 + difference 2 4) (sourceB1179 + difference 4 2) sourceC1179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 726) := by
    have ha : (tripleCharges (sourceA1179 + difference 2 4) (sourceB1179 + difference 4 2) sourceC1179) = raw19838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1179 sourceB1179 sourceC1179 difference raw19838; decide +kernel
    rw [ha]
    exact (canonical19838 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1179 + difference 3 4) (sourceB1179 + difference 4 3) sourceC1179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 726) := by
    have ha : (tripleCharges (sourceA1179 + difference 3 4) (sourceB1179 + difference 4 3) sourceC1179) = raw19839 := by
      apply Matrix.ext; unfold tripleCharges sourceA1179 sourceB1179 sourceC1179 difference raw19839; decide +kernel
    rw [ha]
    exact (canonical19839 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1179 + difference 4 4) (sourceB1179 + difference 4 4) sourceC1179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 832) := by
    have ha : (tripleCharges (sourceA1179 + difference 4 4) (sourceB1179 + difference 4 4) sourceC1179) = raw19830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1179 sourceB1179 sourceC1179 difference raw19830; decide +kernel
    rw [ha]
    exact (canonical19830 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1179 + difference 5 4) (sourceB1179 + difference 4 5) sourceC1179) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 564) := by
    have ha : (tripleCharges (sourceA1179 + difference 5 4) (sourceB1179 + difference 4 5) sourceC1179) = raw19840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1179 sourceB1179 sourceC1179 difference raw19840; decide +kernel
    rw [ha]
    exact (canonical19840 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1179 + sourceB1179) sourceC1179) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1179 + sourceB1179) sourceC1179) = raw19836 := by
      apply Matrix.ext; unfold doubleCharges sourceA1179 sourceB1179 sourceC1179 raw19836; decide +kernel
    rw [ha]
    exact (canonical19836 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1179 sourceB1179 sourceC1179
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1179, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1180 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1180 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC1180 : Charge := ![2, 0, 0, 0, 2, -4]
def sourceForm1180 : Integer.Sparse Master := [(Sum.inr 832, 1), (Sum.inr 1186, 3), (Sum.inr 1289, 1), (Sum.inr 1741, 1), (Sum.inr 4071, -1)]

theorem sourceEq1180 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1180 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1180 + difference 0 5) (sourceB1180 + difference 5 0) sourceC1180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA1180 + difference 0 5) (sourceB1180 + difference 5 0) sourceC1180) = raw19835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1180 sourceB1180 sourceC1180 difference raw19835; decide +kernel
    rw [ha]
    exact (canonical19835 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1180 + difference 1 5) (sourceB1180 + difference 5 1) sourceC1180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1186) := by
    have ha : (tripleCharges (sourceA1180 + difference 1 5) (sourceB1180 + difference 5 1) sourceC1180) = raw19841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1180 sourceB1180 sourceC1180 difference raw19841; decide +kernel
    rw [ha]
    exact (canonical19841 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1180 + difference 2 5) (sourceB1180 + difference 5 2) sourceC1180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1186) := by
    have ha : (tripleCharges (sourceA1180 + difference 2 5) (sourceB1180 + difference 5 2) sourceC1180) = raw19842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1180 sourceB1180 sourceC1180 difference raw19842; decide +kernel
    rw [ha]
    exact (canonical19842 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1180 + difference 3 5) (sourceB1180 + difference 5 3) sourceC1180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1186) := by
    have ha : (tripleCharges (sourceA1180 + difference 3 5) (sourceB1180 + difference 5 3) sourceC1180) = raw19843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1180 sourceB1180 sourceC1180 difference raw19843; decide +kernel
    rw [ha]
    exact (canonical19843 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1180 + difference 4 5) (sourceB1180 + difference 5 4) sourceC1180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1289) := by
    have ha : (tripleCharges (sourceA1180 + difference 4 5) (sourceB1180 + difference 5 4) sourceC1180) = raw19844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1180 sourceB1180 sourceC1180 difference raw19844; decide +kernel
    rw [ha]
    exact (canonical19844 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1180 + difference 5 5) (sourceB1180 + difference 5 5) sourceC1180) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 832) := by
    have ha : (tripleCharges (sourceA1180 + difference 5 5) (sourceB1180 + difference 5 5) sourceC1180) = raw19830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1180 sourceB1180 sourceC1180 difference raw19830; decide +kernel
    rw [ha]
    exact (canonical19830 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1180 + sourceB1180) sourceC1180) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1180 + sourceB1180) sourceC1180) = raw19836 := by
      apply Matrix.ext; unfold doubleCharges sourceA1180 sourceB1180 sourceC1180 raw19836; decide +kernel
    rw [ha]
    exact (canonical19836 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1180 sourceB1180 sourceC1180
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1180, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1181 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB1181 : Charge := ![2, 0, 0, 0, 2, -4]
def sourceC1181 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceForm1181 : Integer.Sparse Master := [(Sum.inr 565, 1), (Sum.inr 727, 3), (Sum.inr 855, 1), (Sum.inr 862, 1), (Sum.inr 4072, -1)]

theorem sourceEq1181 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1181 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1181 + difference 0 0) (sourceB1181 + difference 0 0) sourceC1181) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 862) := by
    have ha : (tripleCharges (sourceA1181 + difference 0 0) (sourceB1181 + difference 0 0) sourceC1181) = raw19845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1181 sourceB1181 sourceC1181 difference raw19845; decide +kernel
    rw [ha]
    exact (canonical19845 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1181 + difference 1 0) (sourceB1181 + difference 0 1) sourceC1181) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 727) := by
    have ha : (tripleCharges (sourceA1181 + difference 1 0) (sourceB1181 + difference 0 1) sourceC1181) = raw19846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1181 sourceB1181 sourceC1181 difference raw19846; decide +kernel
    rw [ha]
    exact (canonical19846 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1181 + difference 2 0) (sourceB1181 + difference 0 2) sourceC1181) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 727) := by
    have ha : (tripleCharges (sourceA1181 + difference 2 0) (sourceB1181 + difference 0 2) sourceC1181) = raw19847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1181 sourceB1181 sourceC1181 difference raw19847; decide +kernel
    rw [ha]
    exact (canonical19847 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1181 + difference 3 0) (sourceB1181 + difference 0 3) sourceC1181) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 727) := by
    have ha : (tripleCharges (sourceA1181 + difference 3 0) (sourceB1181 + difference 0 3) sourceC1181) = raw19848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1181 sourceB1181 sourceC1181 difference raw19848; decide +kernel
    rw [ha]
    exact (canonical19848 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1181 + difference 4 0) (sourceB1181 + difference 0 4) sourceC1181) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 855) := by
    have ha : (tripleCharges (sourceA1181 + difference 4 0) (sourceB1181 + difference 0 4) sourceC1181) = raw19829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1181 sourceB1181 sourceC1181 difference raw19829; decide +kernel
    rw [ha]
    exact (canonical19829 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1181 + difference 5 0) (sourceB1181 + difference 0 5) sourceC1181) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 565) := by
    have ha : (tripleCharges (sourceA1181 + difference 5 0) (sourceB1181 + difference 0 5) sourceC1181) = raw19849 := by
      apply Matrix.ext; unfold tripleCharges sourceA1181 sourceB1181 sourceC1181 difference raw19849; decide +kernel
    rw [ha]
    exact (canonical19849 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1181 + sourceB1181) sourceC1181) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (doubleCharges (sourceA1181 + sourceB1181) sourceC1181) = raw19420 := by
      apply Matrix.ext; unfold doubleCharges sourceA1181 sourceB1181 sourceC1181 raw19420; decide +kernel
    rw [ha]
    exact (canonical19420 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1181 sourceB1181 sourceC1181
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1181, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1182 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1182 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1182 : Charge := ![2, 0, 0, 1, 1, -4]
def sourceForm1182 : Integer.Sparse Master := [(Sum.inr 785, 2), (Sum.inr 791, 1), (Sum.inr 812, 2), (Sum.inr 1710, 1), (Sum.inr 4069, -1)]

theorem sourceEq1182 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1182 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1182 + difference 0 0) (sourceB1182 + difference 0 0) sourceC1182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 791) := by
    have ha : (tripleCharges (sourceA1182 + difference 0 0) (sourceB1182 + difference 0 0) sourceC1182) = raw19850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1182 sourceB1182 sourceC1182 difference raw19850; decide +kernel
    rw [ha]
    exact (canonical19850 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1182 + difference 0 1) (sourceB1182 + difference 1 0) sourceC1182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 785) := by
    have ha : (tripleCharges (sourceA1182 + difference 0 1) (sourceB1182 + difference 1 0) sourceC1182) = raw19851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1182 sourceB1182 sourceC1182 difference raw19851; decide +kernel
    rw [ha]
    exact (canonical19851 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1182 + difference 0 2) (sourceB1182 + difference 2 0) sourceC1182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 785) := by
    have ha : (tripleCharges (sourceA1182 + difference 0 2) (sourceB1182 + difference 2 0) sourceC1182) = raw19852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1182 sourceB1182 sourceC1182 difference raw19852; decide +kernel
    rw [ha]
    exact (canonical19852 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1182 + difference 0 3) (sourceB1182 + difference 3 0) sourceC1182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 812) := by
    have ha : (tripleCharges (sourceA1182 + difference 0 3) (sourceB1182 + difference 3 0) sourceC1182) = raw19853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1182 sourceB1182 sourceC1182 difference raw19853; decide +kernel
    rw [ha]
    exact (canonical19853 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1182 + difference 0 4) (sourceB1182 + difference 4 0) sourceC1182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 812) := by
    have ha : (tripleCharges (sourceA1182 + difference 0 4) (sourceB1182 + difference 4 0) sourceC1182) = raw19854 := by
      apply Matrix.ext; unfold tripleCharges sourceA1182 sourceB1182 sourceC1182 difference raw19854; decide +kernel
    rw [ha]
    exact (canonical19854 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1182 + difference 0 5) (sourceB1182 + difference 5 0) sourceC1182) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1182 + difference 0 5) (sourceB1182 + difference 5 0) sourceC1182) = raw19855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1182 sourceB1182 sourceC1182 difference raw19855; decide +kernel
    rw [ha]
    exact (canonical19855 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1182 + sourceB1182) sourceC1182) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1182 + sourceB1182) sourceC1182) = raw19856 := by
      apply Matrix.ext; unfold doubleCharges sourceA1182 sourceB1182 sourceC1182 raw19856; decide +kernel
    rw [ha]
    exact (canonical19856 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1182 sourceB1182 sourceC1182
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1182, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1183 : Charge := ![-4, 0, 0, 0, 0, 4]
def sourceB1183 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceC1183 : Charge := ![2, 0, 0, 1, 1, -4]
def sourceForm1183 : Integer.Sparse Master := [(Sum.inr 545, 1), (Sum.inr 705, 2), (Sum.inr 740, 1), (Sum.inr 791, 1), (Sum.inr 812, 1), (Sum.inr 4069, -1)]

theorem sourceEq1183 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1183 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1183 + difference 0 3) (sourceB1183 + difference 3 0) sourceC1183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 812) := by
    have ha : (tripleCharges (sourceA1183 + difference 0 3) (sourceB1183 + difference 3 0) sourceC1183) = raw19853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1183 sourceB1183 sourceC1183 difference raw19853; decide +kernel
    rw [ha]
    exact (canonical19853 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1183 + difference 1 3) (sourceB1183 + difference 3 1) sourceC1183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 705) := by
    have ha : (tripleCharges (sourceA1183 + difference 1 3) (sourceB1183 + difference 3 1) sourceC1183) = raw19857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1183 sourceB1183 sourceC1183 difference raw19857; decide +kernel
    rw [ha]
    exact (canonical19857 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1183 + difference 2 3) (sourceB1183 + difference 3 2) sourceC1183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 705) := by
    have ha : (tripleCharges (sourceA1183 + difference 2 3) (sourceB1183 + difference 3 2) sourceC1183) = raw19858 := by
      apply Matrix.ext; unfold tripleCharges sourceA1183 sourceB1183 sourceC1183 difference raw19858; decide +kernel
    rw [ha]
    exact (canonical19858 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1183 + difference 3 3) (sourceB1183 + difference 3 3) sourceC1183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 791) := by
    have ha : (tripleCharges (sourceA1183 + difference 3 3) (sourceB1183 + difference 3 3) sourceC1183) = raw19850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1183 sourceB1183 sourceC1183 difference raw19850; decide +kernel
    rw [ha]
    exact (canonical19850 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1183 + difference 4 3) (sourceB1183 + difference 3 4) sourceC1183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 740) := by
    have ha : (tripleCharges (sourceA1183 + difference 4 3) (sourceB1183 + difference 3 4) sourceC1183) = raw19859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1183 sourceB1183 sourceC1183 difference raw19859; decide +kernel
    rw [ha]
    exact (canonical19859 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1183 + difference 5 3) (sourceB1183 + difference 3 5) sourceC1183) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 545) := by
    have ha : (tripleCharges (sourceA1183 + difference 5 3) (sourceB1183 + difference 3 5) sourceC1183) = raw19860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1183 sourceB1183 sourceC1183 difference raw19860; decide +kernel
    rw [ha]
    exact (canonical19860 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1183 + sourceB1183) sourceC1183) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1183 + sourceB1183) sourceC1183) = raw19856 := by
      apply Matrix.ext; unfold doubleCharges sourceA1183 sourceB1183 sourceC1183 raw19856; decide +kernel
    rw [ha]
    exact (canonical19856 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1183 sourceB1183 sourceC1183
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1183, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
