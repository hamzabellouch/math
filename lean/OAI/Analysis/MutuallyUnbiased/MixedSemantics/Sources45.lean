import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical157
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical158
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical174
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical175

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1440 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1440 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceC1440 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceForm1440 : Integer.Sparse Master := [(Sum.inr 616, 1), (Sum.inr 935, 2), (Sum.inr 1063, 1), (Sum.inr 1083, 1), (Sum.inr 1087, 1), (Sum.inr 4084, -1)]

theorem sourceEq1440 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1440 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1440 + difference 3 0) (sourceB1440 + difference 0 3) sourceC1440) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 616) := by
    have ha : (tripleCharges (sourceA1440 + difference 3 0) (sourceB1440 + difference 0 3) sourceC1440) = raw22314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1440 sourceB1440 sourceC1440 difference raw22314; decide +kernel
    rw [ha]
    exact (canonical22314 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1440 + difference 3 1) (sourceB1440 + difference 1 3) sourceC1440) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 935) := by
    have ha : (tripleCharges (sourceA1440 + difference 3 1) (sourceB1440 + difference 1 3) sourceC1440) = raw22315 := by
      apply Matrix.ext; unfold tripleCharges sourceA1440 sourceB1440 sourceC1440 difference raw22315; decide +kernel
    rw [ha]
    exact (canonical22315 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1440 + difference 3 2) (sourceB1440 + difference 2 3) sourceC1440) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 935) := by
    have ha : (tripleCharges (sourceA1440 + difference 3 2) (sourceB1440 + difference 2 3) sourceC1440) = raw22316 := by
      apply Matrix.ext; unfold tripleCharges sourceA1440 sourceB1440 sourceC1440 difference raw22316; decide +kernel
    rw [ha]
    exact (canonical22316 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1440 + difference 3 3) (sourceB1440 + difference 3 3) sourceC1440) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1063) := by
    have ha : (tripleCharges (sourceA1440 + difference 3 3) (sourceB1440 + difference 3 3) sourceC1440) = raw22317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1440 sourceB1440 sourceC1440 difference raw22317; decide +kernel
    rw [ha]
    exact (canonical22317 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1440 + difference 3 4) (sourceB1440 + difference 4 3) sourceC1440) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1440 + difference 3 4) (sourceB1440 + difference 4 3) sourceC1440) = raw20141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1440 sourceB1440 sourceC1440 difference raw20141; decide +kernel
    rw [ha]
    exact (canonical20141 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1440 + difference 3 5) (sourceB1440 + difference 5 3) sourceC1440) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1440 + difference 3 5) (sourceB1440 + difference 5 3) sourceC1440) = raw22318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1440 sourceB1440 sourceC1440 difference raw22318; decide +kernel
    rw [ha]
    exact (canonical22318 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1440 + sourceB1440) sourceC1440) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1440 + sourceB1440) sourceC1440) = raw20142 := by
      apply Matrix.ext; unfold doubleCharges sourceA1440 sourceB1440 sourceC1440 raw20142; decide +kernel
    rw [ha]
    exact (canonical20142 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1440 sourceB1440 sourceC1440
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1440, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1441 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1441 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1441 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceForm1441 : Integer.Sparse Master := [(Sum.inr 1318, 2), (Sum.inr 1324, 1), (Sum.inr 1325, 1), (Sum.inr 1375, 1), (Sum.inr 2889, 1), (Sum.inr 4092, -1)]

theorem sourceEq1441 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1441 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1441 + difference 0 3) (sourceB1441 + difference 3 0) sourceC1441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA1441 + difference 0 3) (sourceB1441 + difference 3 0) sourceC1441) = raw8546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1441 sourceB1441 sourceC1441 difference raw8546; decide +kernel
    rw [ha]
    exact (canonical8546 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1441 + difference 1 3) (sourceB1441 + difference 3 1) sourceC1441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1318) := by
    have ha : (tripleCharges (sourceA1441 + difference 1 3) (sourceB1441 + difference 3 1) sourceC1441) = raw22319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1441 sourceB1441 sourceC1441 difference raw22319; decide +kernel
    rw [ha]
    exact (canonical22319 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1441 + difference 2 3) (sourceB1441 + difference 3 2) sourceC1441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1318) := by
    have ha : (tripleCharges (sourceA1441 + difference 2 3) (sourceB1441 + difference 3 2) sourceC1441) = raw22320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1441 sourceB1441 sourceC1441 difference raw22320; decide +kernel
    rw [ha]
    exact (canonical22320 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1441 + difference 3 3) (sourceB1441 + difference 3 3) sourceC1441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1375) := by
    have ha : (tripleCharges (sourceA1441 + difference 3 3) (sourceB1441 + difference 3 3) sourceC1441) = raw8535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1441 sourceB1441 sourceC1441 difference raw8535; decide +kernel
    rw [ha]
    exact (canonical8535 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1441 + difference 4 3) (sourceB1441 + difference 3 4) sourceC1441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1324) := by
    have ha : (tripleCharges (sourceA1441 + difference 4 3) (sourceB1441 + difference 3 4) sourceC1441) = raw22321 := by
      apply Matrix.ext; unfold tripleCharges sourceA1441 sourceB1441 sourceC1441 difference raw22321; decide +kernel
    rw [ha]
    exact (canonical22321 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1441 + difference 5 3) (sourceB1441 + difference 3 5) sourceC1441) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1325) := by
    have ha : (tripleCharges (sourceA1441 + difference 5 3) (sourceB1441 + difference 3 5) sourceC1441) = raw22322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1441 sourceB1441 sourceC1441 difference raw22322; decide +kernel
    rw [ha]
    exact (canonical22322 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1441 + sourceB1441) sourceC1441) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1441 + sourceB1441) sourceC1441) = raw8531 := by
      apply Matrix.ext; unfold doubleCharges sourceA1441 sourceB1441 sourceC1441 raw8531; decide +kernel
    rw [ha]
    exact (canonical8531 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1441 sourceB1441 sourceC1441
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1441, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1442 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB1442 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1442 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1442 : Integer.Sparse Master := [(Sum.inr 1740, 1), (Sum.inr 2409, 1), (Sum.inr 3243, 2), (Sum.inr 3248, 1), (Sum.inr 3301, 1), (Sum.inr 4071, -1)]

theorem sourceEq1442 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1442 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1442 + difference 0 0) (sourceB1442 + difference 0 0) sourceC1442) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA1442 + difference 0 0) (sourceB1442 + difference 0 0) sourceC1442) = raw22323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1442 sourceB1442 sourceC1442 difference raw22323; decide +kernel
    rw [ha]
    exact (canonical22323 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1442 + difference 0 1) (sourceB1442 + difference 1 0) sourceC1442) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3243) := by
    have ha : (tripleCharges (sourceA1442 + difference 0 1) (sourceB1442 + difference 1 0) sourceC1442) = raw22324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1442 sourceB1442 sourceC1442 difference raw22324; decide +kernel
    rw [ha]
    exact (canonical22324 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1442 + difference 0 2) (sourceB1442 + difference 2 0) sourceC1442) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3243) := by
    have ha : (tripleCharges (sourceA1442 + difference 0 2) (sourceB1442 + difference 2 0) sourceC1442) = raw22325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1442 sourceB1442 sourceC1442 difference raw22325; decide +kernel
    rw [ha]
    exact (canonical22325 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1442 + difference 0 3) (sourceB1442 + difference 3 0) sourceC1442) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1442 + difference 0 3) (sourceB1442 + difference 3 0) sourceC1442) = raw22326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1442 sourceB1442 sourceC1442 difference raw22326; decide +kernel
    rw [ha]
    exact (canonical22326 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1442 + difference 0 4) (sourceB1442 + difference 4 0) sourceC1442) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2409) := by
    have ha : (tripleCharges (sourceA1442 + difference 0 4) (sourceB1442 + difference 4 0) sourceC1442) = raw22327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1442 sourceB1442 sourceC1442 difference raw22327; decide +kernel
    rw [ha]
    exact (canonical22327 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1442 + difference 0 5) (sourceB1442 + difference 5 0) sourceC1442) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3248) := by
    have ha : (tripleCharges (sourceA1442 + difference 0 5) (sourceB1442 + difference 5 0) sourceC1442) = raw22328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1442 sourceB1442 sourceC1442 difference raw22328; decide +kernel
    rw [ha]
    exact (canonical22328 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1442 + sourceB1442) sourceC1442) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1442 + sourceB1442) sourceC1442) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1442 sourceB1442 sourceC1442 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1442 sourceB1442 sourceC1442
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1442, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1443 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB1443 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1443 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1443 : Integer.Sparse Master := [(Sum.inr 1736, 2), (Sum.inr 1738, 1), (Sum.inr 1740, 1), (Sum.inr 1751, 1), (Sum.inr 3301, 1), (Sum.inr 4071, -1)]

theorem sourceEq1443 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1443 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1443 + difference 0 3) (sourceB1443 + difference 3 0) sourceC1443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1443 + difference 0 3) (sourceB1443 + difference 3 0) sourceC1443) = raw22326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1443 sourceB1443 sourceC1443 difference raw22326; decide +kernel
    rw [ha]
    exact (canonical22326 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1443 + difference 1 3) (sourceB1443 + difference 3 1) sourceC1443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1443 + difference 1 3) (sourceB1443 + difference 3 1) sourceC1443) = raw22330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1443 sourceB1443 sourceC1443 difference raw22330; decide +kernel
    rw [ha]
    exact (canonical22330 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1443 + difference 2 3) (sourceB1443 + difference 3 2) sourceC1443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1443 + difference 2 3) (sourceB1443 + difference 3 2) sourceC1443) = raw22331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1443 sourceB1443 sourceC1443 difference raw22331; decide +kernel
    rw [ha]
    exact (canonical22331 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1443 + difference 3 3) (sourceB1443 + difference 3 3) sourceC1443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA1443 + difference 3 3) (sourceB1443 + difference 3 3) sourceC1443) = raw22323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1443 sourceB1443 sourceC1443 difference raw22323; decide +kernel
    rw [ha]
    exact (canonical22323 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1443 + difference 4 3) (sourceB1443 + difference 3 4) sourceC1443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1443 + difference 4 3) (sourceB1443 + difference 3 4) sourceC1443) = raw22332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1443 sourceB1443 sourceC1443 difference raw22332; decide +kernel
    rw [ha]
    exact (canonical22332 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1443 + difference 5 3) (sourceB1443 + difference 3 5) sourceC1443) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1443 + difference 5 3) (sourceB1443 + difference 3 5) sourceC1443) = raw22333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1443 sourceB1443 sourceC1443 difference raw22333; decide +kernel
    rw [ha]
    exact (canonical22333 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1443 + sourceB1443) sourceC1443) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1443 + sourceB1443) sourceC1443) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1443 sourceB1443 sourceC1443 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1443 sourceB1443 sourceC1443
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1443, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1444 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB1444 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1444 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1444 : Integer.Sparse Master := [(Sum.inr 858, 1), (Sum.inr 1626, 2), (Sum.inr 1740, 2), (Sum.inr 1751, 1), (Sum.inr 4071, -1)]

theorem sourceEq1444 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1444 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1444 + difference 4 0) (sourceB1444 + difference 0 4) sourceC1444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 858) := by
    have ha : (tripleCharges (sourceA1444 + difference 4 0) (sourceB1444 + difference 0 4) sourceC1444) = raw22334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1444 sourceB1444 sourceC1444 difference raw22334; decide +kernel
    rw [ha]
    exact (canonical22334 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1444 + difference 4 1) (sourceB1444 + difference 1 4) sourceC1444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1626) := by
    have ha : (tripleCharges (sourceA1444 + difference 4 1) (sourceB1444 + difference 1 4) sourceC1444) = raw22335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1444 sourceB1444 sourceC1444 difference raw22335; decide +kernel
    rw [ha]
    exact (canonical22335 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1444 + difference 4 2) (sourceB1444 + difference 2 4) sourceC1444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1626) := by
    have ha : (tripleCharges (sourceA1444 + difference 4 2) (sourceB1444 + difference 2 4) sourceC1444) = raw22336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1444 sourceB1444 sourceC1444 difference raw22336; decide +kernel
    rw [ha]
    exact (canonical22336 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1444 + difference 4 3) (sourceB1444 + difference 3 4) sourceC1444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1444 + difference 4 3) (sourceB1444 + difference 3 4) sourceC1444) = raw22332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1444 sourceB1444 sourceC1444 difference raw22332; decide +kernel
    rw [ha]
    exact (canonical22332 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1444 + difference 4 4) (sourceB1444 + difference 4 4) sourceC1444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA1444 + difference 4 4) (sourceB1444 + difference 4 4) sourceC1444) = raw22323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1444 sourceB1444 sourceC1444 difference raw22323; decide +kernel
    rw [ha]
    exact (canonical22323 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1444 + difference 4 5) (sourceB1444 + difference 5 4) sourceC1444) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA1444 + difference 4 5) (sourceB1444 + difference 5 4) sourceC1444) = raw22337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1444 sourceB1444 sourceC1444 difference raw22337; decide +kernel
    rw [ha]
    exact (canonical22337 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1444 + sourceB1444) sourceC1444) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1444 + sourceB1444) sourceC1444) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1444 sourceB1444 sourceC1444 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1444 sourceB1444 sourceC1444
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1444, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1445 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB1445 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1445 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1445 : Integer.Sparse Master := [(Sum.inr 830, 1), (Sum.inr 1611, 2), (Sum.inr 1660, 1), (Sum.inr 1738, 1), (Sum.inr 1740, 1), (Sum.inr 4071, -1)]

theorem sourceEq1445 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1445 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1445 + difference 5 0) (sourceB1445 + difference 0 5) sourceC1445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 830) := by
    have ha : (tripleCharges (sourceA1445 + difference 5 0) (sourceB1445 + difference 0 5) sourceC1445) = raw22338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1445 sourceB1445 sourceC1445 difference raw22338; decide +kernel
    rw [ha]
    exact (canonical22338 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1445 + difference 5 1) (sourceB1445 + difference 1 5) sourceC1445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1611) := by
    have ha : (tripleCharges (sourceA1445 + difference 5 1) (sourceB1445 + difference 1 5) sourceC1445) = raw22339 := by
      apply Matrix.ext; unfold tripleCharges sourceA1445 sourceB1445 sourceC1445 difference raw22339; decide +kernel
    rw [ha]
    exact (canonical22339 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1445 + difference 5 2) (sourceB1445 + difference 2 5) sourceC1445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1611) := by
    have ha : (tripleCharges (sourceA1445 + difference 5 2) (sourceB1445 + difference 2 5) sourceC1445) = raw22340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1445 sourceB1445 sourceC1445 difference raw22340; decide +kernel
    rw [ha]
    exact (canonical22340 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1445 + difference 5 3) (sourceB1445 + difference 3 5) sourceC1445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1445 + difference 5 3) (sourceB1445 + difference 3 5) sourceC1445) = raw22333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1445 sourceB1445 sourceC1445 difference raw22333; decide +kernel
    rw [ha]
    exact (canonical22333 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1445 + difference 5 4) (sourceB1445 + difference 4 5) sourceC1445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1660) := by
    have ha : (tripleCharges (sourceA1445 + difference 5 4) (sourceB1445 + difference 4 5) sourceC1445) = raw22341 := by
      apply Matrix.ext; unfold tripleCharges sourceA1445 sourceB1445 sourceC1445 difference raw22341; decide +kernel
    rw [ha]
    exact (canonical22341 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1445 + difference 5 5) (sourceB1445 + difference 5 5) sourceC1445) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA1445 + difference 5 5) (sourceB1445 + difference 5 5) sourceC1445) = raw22323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1445 sourceB1445 sourceC1445 difference raw22323; decide +kernel
    rw [ha]
    exact (canonical22323 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1445 + sourceB1445) sourceC1445) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1445 + sourceB1445) sourceC1445) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1445 sourceB1445 sourceC1445 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1445 sourceB1445 sourceC1445
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1445, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1446 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB1446 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC1446 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1446 : Integer.Sparse Master := [(Sum.inr 1732, 2), (Sum.inr 1733, 1), (Sum.inr 1740, 2), (Sum.inr 3248, 1), (Sum.inr 4071, -1)]

theorem sourceEq1446 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1446 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1446 + difference 0 5) (sourceB1446 + difference 5 0) sourceC1446) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3248) := by
    have ha : (tripleCharges (sourceA1446 + difference 0 5) (sourceB1446 + difference 5 0) sourceC1446) = raw22328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1446 sourceB1446 sourceC1446 difference raw22328; decide +kernel
    rw [ha]
    exact (canonical22328 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1446 + difference 1 5) (sourceB1446 + difference 5 1) sourceC1446) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1732) := by
    have ha : (tripleCharges (sourceA1446 + difference 1 5) (sourceB1446 + difference 5 1) sourceC1446) = raw22342 := by
      apply Matrix.ext; unfold tripleCharges sourceA1446 sourceB1446 sourceC1446 difference raw22342; decide +kernel
    rw [ha]
    exact (canonical22342 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1446 + difference 2 5) (sourceB1446 + difference 5 2) sourceC1446) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1732) := by
    have ha : (tripleCharges (sourceA1446 + difference 2 5) (sourceB1446 + difference 5 2) sourceC1446) = raw22343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1446 sourceB1446 sourceC1446 difference raw22343; decide +kernel
    rw [ha]
    exact (canonical22343 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1446 + difference 3 5) (sourceB1446 + difference 5 3) sourceC1446) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1733) := by
    have ha : (tripleCharges (sourceA1446 + difference 3 5) (sourceB1446 + difference 5 3) sourceC1446) = raw22344 := by
      apply Matrix.ext; unfold tripleCharges sourceA1446 sourceB1446 sourceC1446 difference raw22344; decide +kernel
    rw [ha]
    exact (canonical22344 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1446 + difference 4 5) (sourceB1446 + difference 5 4) sourceC1446) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA1446 + difference 4 5) (sourceB1446 + difference 5 4) sourceC1446) = raw22337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1446 sourceB1446 sourceC1446 difference raw22337; decide +kernel
    rw [ha]
    exact (canonical22337 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1446 + difference 5 5) (sourceB1446 + difference 5 5) sourceC1446) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA1446 + difference 5 5) (sourceB1446 + difference 5 5) sourceC1446) = raw22323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1446 sourceB1446 sourceC1446 difference raw22323; decide +kernel
    rw [ha]
    exact (canonical22323 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1446 + sourceB1446) sourceC1446) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1446 + sourceB1446) sourceC1446) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1446 sourceB1446 sourceC1446 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1446 sourceB1446 sourceC1446
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1446, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1447 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1447 : Charge := ![3, 0, 0, -3, 0, 0]
def sourceC1447 : Charge := ![1, 0, 0, 3, -2, -2]
def sourceForm1447 : Integer.Sparse Master := [(Sum.inr 1353, 1), (Sum.inr 2271, 2), (Sum.inr 2280, 2), (Sum.inr 2843, 1), (Sum.inr 4082, -1)]

theorem sourceEq1447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1447 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1447 + difference 0 0) (sourceB1447 + difference 0 0) sourceC1447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1353) := by
    have ha : (tripleCharges (sourceA1447 + difference 0 0) (sourceB1447 + difference 0 0) sourceC1447) = raw22345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1447 sourceB1447 sourceC1447 difference raw22345; decide +kernel
    rw [ha]
    exact (canonical22345 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1447 + difference 0 1) (sourceB1447 + difference 1 0) sourceC1447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2271) := by
    have ha : (tripleCharges (sourceA1447 + difference 0 1) (sourceB1447 + difference 1 0) sourceC1447) = raw22346 := by
      apply Matrix.ext; unfold tripleCharges sourceA1447 sourceB1447 sourceC1447 difference raw22346; decide +kernel
    rw [ha]
    exact (canonical22346 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1447 + difference 0 2) (sourceB1447 + difference 2 0) sourceC1447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2271) := by
    have ha : (tripleCharges (sourceA1447 + difference 0 2) (sourceB1447 + difference 2 0) sourceC1447) = raw22347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1447 sourceB1447 sourceC1447 difference raw22347; decide +kernel
    rw [ha]
    exact (canonical22347 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1447 + difference 0 3) (sourceB1447 + difference 3 0) sourceC1447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2843) := by
    have ha : (tripleCharges (sourceA1447 + difference 0 3) (sourceB1447 + difference 3 0) sourceC1447) = raw22348 := by
      apply Matrix.ext; unfold tripleCharges sourceA1447 sourceB1447 sourceC1447 difference raw22348; decide +kernel
    rw [ha]
    exact (canonical22348 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1447 + difference 0 4) (sourceB1447 + difference 4 0) sourceC1447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2280) := by
    have ha : (tripleCharges (sourceA1447 + difference 0 4) (sourceB1447 + difference 4 0) sourceC1447) = raw22349 := by
      apply Matrix.ext; unfold tripleCharges sourceA1447 sourceB1447 sourceC1447 difference raw22349; decide +kernel
    rw [ha]
    exact (canonical22349 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1447 + difference 0 5) (sourceB1447 + difference 5 0) sourceC1447) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2280) := by
    have ha : (tripleCharges (sourceA1447 + difference 0 5) (sourceB1447 + difference 5 0) sourceC1447) = raw22350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1447 sourceB1447 sourceC1447 difference raw22350; decide +kernel
    rw [ha]
    exact (canonical22350 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1447 + sourceB1447) sourceC1447) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1447 + sourceB1447) sourceC1447) = raw22351 := by
      apply Matrix.ext; unfold doubleCharges sourceA1447 sourceB1447 sourceC1447 raw22351; decide +kernel
    rw [ha]
    exact (canonical22351 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1447 sourceB1447 sourceC1447
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1447, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1448 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1448 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC1448 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceForm1448 : Integer.Sparse Master := [(Sum.inr 586, 1), (Sum.inr 910, 1), (Sum.inr 950, 1), (Sum.inr 1026, 1), (Sum.inr 1041, 1), (Sum.inr 1044, 1), (Sum.inr 4083, -1)]

theorem sourceEq1448 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1448 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1448 + difference 2 0) (sourceB1448 + difference 0 2) sourceC1448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 586) := by
    have ha : (tripleCharges (sourceA1448 + difference 2 0) (sourceB1448 + difference 0 2) sourceC1448) = raw22352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1448 sourceB1448 sourceC1448 difference raw22352; decide +kernel
    rw [ha]
    exact (canonical22352 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1448 + difference 2 1) (sourceB1448 + difference 1 2) sourceC1448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 910) := by
    have ha : (tripleCharges (sourceA1448 + difference 2 1) (sourceB1448 + difference 1 2) sourceC1448) = raw22353 := by
      apply Matrix.ext; unfold tripleCharges sourceA1448 sourceB1448 sourceC1448 difference raw22353; decide +kernel
    rw [ha]
    exact (canonical22353 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1448 + difference 2 2) (sourceB1448 + difference 2 2) sourceC1448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1026) := by
    have ha : (tripleCharges (sourceA1448 + difference 2 2) (sourceB1448 + difference 2 2) sourceC1448) = raw22354 := by
      apply Matrix.ext; unfold tripleCharges sourceA1448 sourceB1448 sourceC1448 difference raw22354; decide +kernel
    rw [ha]
    exact (canonical22354 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1448 + difference 2 3) (sourceB1448 + difference 3 2) sourceC1448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 950) := by
    have ha : (tripleCharges (sourceA1448 + difference 2 3) (sourceB1448 + difference 3 2) sourceC1448) = raw22355 := by
      apply Matrix.ext; unfold tripleCharges sourceA1448 sourceB1448 sourceC1448 difference raw22355; decide +kernel
    rw [ha]
    exact (canonical22355 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1448 + difference 2 4) (sourceB1448 + difference 4 2) sourceC1448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1448 + difference 2 4) (sourceB1448 + difference 4 2) sourceC1448) = raw20195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1448 sourceB1448 sourceC1448 difference raw20195; decide +kernel
    rw [ha]
    exact (canonical20195 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1448 + difference 2 5) (sourceB1448 + difference 5 2) sourceC1448) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1448 + difference 2 5) (sourceB1448 + difference 5 2) sourceC1448) = raw22356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1448 sourceB1448 sourceC1448 difference raw22356; decide +kernel
    rw [ha]
    exact (canonical22356 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1448 + sourceB1448) sourceC1448) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1448 + sourceB1448) sourceC1448) = raw20196 := by
      apply Matrix.ext; unfold doubleCharges sourceA1448 sourceB1448 sourceC1448 raw20196; decide +kernel
    rw [ha]
    exact (canonical20196 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1448 sourceB1448 sourceC1448
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1448, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1449 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1449 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1449 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceForm1449 : Integer.Sparse Master := [(Sum.inr 1328, 1), (Sum.inr 1333, 1), (Sum.inr 1334, 1), (Sum.inr 1338, 1), (Sum.inr 1391, 1), (Sum.inr 2931, 1), (Sum.inr 4091, -1)]

theorem sourceEq1449 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1449 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1449 + difference 0 2) (sourceB1449 + difference 2 0) sourceC1449) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA1449 + difference 0 2) (sourceB1449 + difference 2 0) sourceC1449) = raw9031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1449 sourceB1449 sourceC1449 difference raw9031; decide +kernel
    rw [ha]
    exact (canonical9031 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1449 + difference 1 2) (sourceB1449 + difference 2 1) sourceC1449) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1328) := by
    have ha : (tripleCharges (sourceA1449 + difference 1 2) (sourceB1449 + difference 2 1) sourceC1449) = raw22357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1449 sourceB1449 sourceC1449 difference raw22357; decide +kernel
    rw [ha]
    exact (canonical22357 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1449 + difference 2 2) (sourceB1449 + difference 2 2) sourceC1449) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1391) := by
    have ha : (tripleCharges (sourceA1449 + difference 2 2) (sourceB1449 + difference 2 2) sourceC1449) = raw9017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1449 sourceB1449 sourceC1449 difference raw9017; decide +kernel
    rw [ha]
    exact (canonical9017 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1449 + difference 3 2) (sourceB1449 + difference 2 3) sourceC1449) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1338) := by
    have ha : (tripleCharges (sourceA1449 + difference 3 2) (sourceB1449 + difference 2 3) sourceC1449) = raw22358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1449 sourceB1449 sourceC1449 difference raw22358; decide +kernel
    rw [ha]
    exact (canonical22358 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1449 + difference 4 2) (sourceB1449 + difference 2 4) sourceC1449) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1333) := by
    have ha : (tripleCharges (sourceA1449 + difference 4 2) (sourceB1449 + difference 2 4) sourceC1449) = raw22359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1449 sourceB1449 sourceC1449 difference raw22359; decide +kernel
    rw [ha]
    exact (canonical22359 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1449 + difference 5 2) (sourceB1449 + difference 2 5) sourceC1449) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1334) := by
    have ha : (tripleCharges (sourceA1449 + difference 5 2) (sourceB1449 + difference 2 5) sourceC1449) = raw22360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1449 sourceB1449 sourceC1449 difference raw22360; decide +kernel
    rw [ha]
    exact (canonical22360 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1449 + sourceB1449) sourceC1449) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1449 + sourceB1449) sourceC1449) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA1449 sourceB1449 sourceC1449 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1449 sourceB1449 sourceC1449
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1449, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1450 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB1450 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1450 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1450 : Integer.Sparse Master := [(Sum.inr 1736, 1), (Sum.inr 2397, 1), (Sum.inr 3280, 1), (Sum.inr 3284, 1), (Sum.inr 3301, 2), (Sum.inr 4071, -1)]

theorem sourceEq1450 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1450 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1450 + difference 0 0) (sourceB1450 + difference 0 0) sourceC1450) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1450 + difference 0 0) (sourceB1450 + difference 0 0) sourceC1450) = raw22331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1450 sourceB1450 sourceC1450 difference raw22331; decide +kernel
    rw [ha]
    exact (canonical22331 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1450 + difference 0 1) (sourceB1450 + difference 1 0) sourceC1450) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3280) := by
    have ha : (tripleCharges (sourceA1450 + difference 0 1) (sourceB1450 + difference 1 0) sourceC1450) = raw22361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1450 sourceB1450 sourceC1450 difference raw22361; decide +kernel
    rw [ha]
    exact (canonical22361 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1450 + difference 0 2) (sourceB1450 + difference 2 0) sourceC1450) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1450 + difference 0 2) (sourceB1450 + difference 2 0) sourceC1450) = raw22326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1450 sourceB1450 sourceC1450 difference raw22326; decide +kernel
    rw [ha]
    exact (canonical22326 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1450 + difference 0 3) (sourceB1450 + difference 3 0) sourceC1450) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1450 + difference 0 3) (sourceB1450 + difference 3 0) sourceC1450) = raw22362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1450 sourceB1450 sourceC1450 difference raw22362; decide +kernel
    rw [ha]
    exact (canonical22362 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1450 + difference 0 4) (sourceB1450 + difference 4 0) sourceC1450) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2397) := by
    have ha : (tripleCharges (sourceA1450 + difference 0 4) (sourceB1450 + difference 4 0) sourceC1450) = raw22363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1450 sourceB1450 sourceC1450 difference raw22363; decide +kernel
    rw [ha]
    exact (canonical22363 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1450 + difference 0 5) (sourceB1450 + difference 5 0) sourceC1450) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3284) := by
    have ha : (tripleCharges (sourceA1450 + difference 0 5) (sourceB1450 + difference 5 0) sourceC1450) = raw22364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1450 sourceB1450 sourceC1450 difference raw22364; decide +kernel
    rw [ha]
    exact (canonical22364 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1450 + sourceB1450) sourceC1450) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1450 + sourceB1450) sourceC1450) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1450 sourceB1450 sourceC1450 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1450 sourceB1450 sourceC1450
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1450, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1451 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB1451 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1451 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1451 : Integer.Sparse Master := [(Sum.inr 821, 1), (Sum.inr 823, 1), (Sum.inr 825, 2), (Sum.inr 848, 1), (Sum.inr 1736, 1), (Sum.inr 4071, -1)]

theorem sourceEq1451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1451 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1451 + difference 0 0) (sourceB1451 + difference 0 0) sourceC1451) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1451 + difference 0 0) (sourceB1451 + difference 0 0) sourceC1451) = raw22331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1451 sourceB1451 sourceC1451 difference raw22331; decide +kernel
    rw [ha]
    exact (canonical22331 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1451 + difference 1 0) (sourceB1451 + difference 0 1) sourceC1451) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 821) := by
    have ha : (tripleCharges (sourceA1451 + difference 1 0) (sourceB1451 + difference 0 1) sourceC1451) = raw22365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1451 sourceB1451 sourceC1451 difference raw22365; decide +kernel
    rw [ha]
    exact (canonical22365 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1451 + difference 2 0) (sourceB1451 + difference 0 2) sourceC1451) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 825) := by
    have ha : (tripleCharges (sourceA1451 + difference 2 0) (sourceB1451 + difference 0 2) sourceC1451) = raw22366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1451 sourceB1451 sourceC1451 difference raw22366; decide +kernel
    rw [ha]
    exact (canonical22366 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1451 + difference 3 0) (sourceB1451 + difference 0 3) sourceC1451) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 825) := by
    have ha : (tripleCharges (sourceA1451 + difference 3 0) (sourceB1451 + difference 0 3) sourceC1451) = raw22367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1451 sourceB1451 sourceC1451 difference raw22367; decide +kernel
    rw [ha]
    exact (canonical22367 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1451 + difference 4 0) (sourceB1451 + difference 0 4) sourceC1451) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 848) := by
    have ha : (tripleCharges (sourceA1451 + difference 4 0) (sourceB1451 + difference 0 4) sourceC1451) = raw22368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1451 sourceB1451 sourceC1451 difference raw22368; decide +kernel
    rw [ha]
    exact (canonical22368 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1451 + difference 5 0) (sourceB1451 + difference 0 5) sourceC1451) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 823) := by
    have ha : (tripleCharges (sourceA1451 + difference 5 0) (sourceB1451 + difference 0 5) sourceC1451) = raw22369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1451 sourceB1451 sourceC1451 difference raw22369; decide +kernel
    rw [ha]
    exact (canonical22369 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1451 + sourceB1451) sourceC1451) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1451 + sourceB1451) sourceC1451) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1451 sourceB1451 sourceC1451 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1451 sourceB1451 sourceC1451
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1451, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1452 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB1452 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1452 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1452 : Integer.Sparse Master := [(Sum.inr 848, 1), (Sum.inr 1614, 1), (Sum.inr 1736, 2), (Sum.inr 1751, 2), (Sum.inr 4071, -1)]

theorem sourceEq1452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1452 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1452 + difference 4 0) (sourceB1452 + difference 0 4) sourceC1452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 848) := by
    have ha : (tripleCharges (sourceA1452 + difference 4 0) (sourceB1452 + difference 0 4) sourceC1452) = raw22368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1452 sourceB1452 sourceC1452 difference raw22368; decide +kernel
    rw [ha]
    exact (canonical22368 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1452 + difference 4 1) (sourceB1452 + difference 1 4) sourceC1452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1614) := by
    have ha : (tripleCharges (sourceA1452 + difference 4 1) (sourceB1452 + difference 1 4) sourceC1452) = raw22370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1452 sourceB1452 sourceC1452 difference raw22370; decide +kernel
    rw [ha]
    exact (canonical22370 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1452 + difference 4 2) (sourceB1452 + difference 2 4) sourceC1452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1452 + difference 4 2) (sourceB1452 + difference 2 4) sourceC1452) = raw22332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1452 sourceB1452 sourceC1452 difference raw22332; decide +kernel
    rw [ha]
    exact (canonical22332 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1452 + difference 4 3) (sourceB1452 + difference 3 4) sourceC1452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1452 + difference 4 3) (sourceB1452 + difference 3 4) sourceC1452) = raw22371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1452 sourceB1452 sourceC1452 difference raw22371; decide +kernel
    rw [ha]
    exact (canonical22371 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1452 + difference 4 4) (sourceB1452 + difference 4 4) sourceC1452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1452 + difference 4 4) (sourceB1452 + difference 4 4) sourceC1452) = raw22331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1452 sourceB1452 sourceC1452 difference raw22331; decide +kernel
    rw [ha]
    exact (canonical22331 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1452 + difference 4 5) (sourceB1452 + difference 5 4) sourceC1452) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1452 + difference 4 5) (sourceB1452 + difference 5 4) sourceC1452) = raw22372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1452 sourceB1452 sourceC1452 difference raw22372; decide +kernel
    rw [ha]
    exact (canonical22372 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1452 + sourceB1452) sourceC1452) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1452 + sourceB1452) sourceC1452) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1452 sourceB1452 sourceC1452 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1452 sourceB1452 sourceC1452
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1452, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1453 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB1453 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1453 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1453 : Integer.Sparse Master := [(Sum.inr 823, 1), (Sum.inr 1606, 1), (Sum.inr 1655, 1), (Sum.inr 1736, 1), (Sum.inr 1738, 2), (Sum.inr 4071, -1)]

theorem sourceEq1453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1453 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1453 + difference 5 0) (sourceB1453 + difference 0 5) sourceC1453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 823) := by
    have ha : (tripleCharges (sourceA1453 + difference 5 0) (sourceB1453 + difference 0 5) sourceC1453) = raw22369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1453 sourceB1453 sourceC1453 difference raw22369; decide +kernel
    rw [ha]
    exact (canonical22369 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1453 + difference 5 1) (sourceB1453 + difference 1 5) sourceC1453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1606) := by
    have ha : (tripleCharges (sourceA1453 + difference 5 1) (sourceB1453 + difference 1 5) sourceC1453) = raw22373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1453 sourceB1453 sourceC1453 difference raw22373; decide +kernel
    rw [ha]
    exact (canonical22373 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1453 + difference 5 2) (sourceB1453 + difference 2 5) sourceC1453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1453 + difference 5 2) (sourceB1453 + difference 2 5) sourceC1453) = raw22333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1453 sourceB1453 sourceC1453 difference raw22333; decide +kernel
    rw [ha]
    exact (canonical22333 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1453 + difference 5 3) (sourceB1453 + difference 3 5) sourceC1453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1453 + difference 5 3) (sourceB1453 + difference 3 5) sourceC1453) = raw22374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1453 sourceB1453 sourceC1453 difference raw22374; decide +kernel
    rw [ha]
    exact (canonical22374 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1453 + difference 5 4) (sourceB1453 + difference 4 5) sourceC1453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1655) := by
    have ha : (tripleCharges (sourceA1453 + difference 5 4) (sourceB1453 + difference 4 5) sourceC1453) = raw22375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1453 sourceB1453 sourceC1453 difference raw22375; decide +kernel
    rw [ha]
    exact (canonical22375 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1453 + difference 5 5) (sourceB1453 + difference 5 5) sourceC1453) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1453 + difference 5 5) (sourceB1453 + difference 5 5) sourceC1453) = raw22331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1453 sourceB1453 sourceC1453 difference raw22331; decide +kernel
    rw [ha]
    exact (canonical22331 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1453 + sourceB1453) sourceC1453) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1453 + sourceB1453) sourceC1453) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1453 sourceB1453 sourceC1453 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1453 sourceB1453 sourceC1453
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1453, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1454 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceB1454 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC1454 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1454 : Integer.Sparse Master := [(Sum.inr 1731, 1), (Sum.inr 1732, 2), (Sum.inr 1736, 2), (Sum.inr 3284, 1), (Sum.inr 4071, -1)]

theorem sourceEq1454 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1454 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1454 + difference 0 5) (sourceB1454 + difference 5 0) sourceC1454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3284) := by
    have ha : (tripleCharges (sourceA1454 + difference 0 5) (sourceB1454 + difference 5 0) sourceC1454) = raw22364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1454 sourceB1454 sourceC1454 difference raw22364; decide +kernel
    rw [ha]
    exact (canonical22364 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1454 + difference 1 5) (sourceB1454 + difference 5 1) sourceC1454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1731) := by
    have ha : (tripleCharges (sourceA1454 + difference 1 5) (sourceB1454 + difference 5 1) sourceC1454) = raw22376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1454 sourceB1454 sourceC1454 difference raw22376; decide +kernel
    rw [ha]
    exact (canonical22376 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1454 + difference 2 5) (sourceB1454 + difference 5 2) sourceC1454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1732) := by
    have ha : (tripleCharges (sourceA1454 + difference 2 5) (sourceB1454 + difference 5 2) sourceC1454) = raw22377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1454 sourceB1454 sourceC1454 difference raw22377; decide +kernel
    rw [ha]
    exact (canonical22377 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1454 + difference 3 5) (sourceB1454 + difference 5 3) sourceC1454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1732) := by
    have ha : (tripleCharges (sourceA1454 + difference 3 5) (sourceB1454 + difference 5 3) sourceC1454) = raw22343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1454 sourceB1454 sourceC1454 difference raw22343; decide +kernel
    rw [ha]
    exact (canonical22343 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1454 + difference 4 5) (sourceB1454 + difference 5 4) sourceC1454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1454 + difference 4 5) (sourceB1454 + difference 5 4) sourceC1454) = raw22372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1454 sourceB1454 sourceC1454 difference raw22372; decide +kernel
    rw [ha]
    exact (canonical22372 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1454 + difference 5 5) (sourceB1454 + difference 5 5) sourceC1454) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1736) := by
    have ha : (tripleCharges (sourceA1454 + difference 5 5) (sourceB1454 + difference 5 5) sourceC1454) = raw22331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1454 sourceB1454 sourceC1454 difference raw22331; decide +kernel
    rw [ha]
    exact (canonical22331 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1454 + sourceB1454) sourceC1454) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1454 + sourceB1454) sourceC1454) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1454 sourceB1454 sourceC1454 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1454 sourceB1454 sourceC1454
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1454, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1455 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1455 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC1455 : Charge := ![1, 0, 1, 2, -2, -2]
def sourceForm1455 : Integer.Sparse Master := [(Sum.inr 1356, 1), (Sum.inr 2856, 1), (Sum.inr 2911, 1), (Sum.inr 2970, 1), (Sum.inr 3025, 2), (Sum.inr 4088, -1)]

theorem sourceEq1455 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1455 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1455 + difference 0 0) (sourceB1455 + difference 0 0) sourceC1455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1356) := by
    have ha : (tripleCharges (sourceA1455 + difference 0 0) (sourceB1455 + difference 0 0) sourceC1455) = raw22378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1455 sourceB1455 sourceC1455 difference raw22378; decide +kernel
    rw [ha]
    exact (canonical22378 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1455 + difference 0 1) (sourceB1455 + difference 1 0) sourceC1455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2970) := by
    have ha : (tripleCharges (sourceA1455 + difference 0 1) (sourceB1455 + difference 1 0) sourceC1455) = raw22379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1455 sourceB1455 sourceC1455 difference raw22379; decide +kernel
    rw [ha]
    exact (canonical22379 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1455 + difference 0 2) (sourceB1455 + difference 2 0) sourceC1455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2911) := by
    have ha : (tripleCharges (sourceA1455 + difference 0 2) (sourceB1455 + difference 2 0) sourceC1455) = raw22380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1455 sourceB1455 sourceC1455 difference raw22380; decide +kernel
    rw [ha]
    exact (canonical22380 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1455 + difference 0 3) (sourceB1455 + difference 3 0) sourceC1455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2856) := by
    have ha : (tripleCharges (sourceA1455 + difference 0 3) (sourceB1455 + difference 3 0) sourceC1455) = raw22381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1455 sourceB1455 sourceC1455 difference raw22381; decide +kernel
    rw [ha]
    exact (canonical22381 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1455 + difference 0 4) (sourceB1455 + difference 4 0) sourceC1455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA1455 + difference 0 4) (sourceB1455 + difference 4 0) sourceC1455) = raw22382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1455 sourceB1455 sourceC1455 difference raw22382; decide +kernel
    rw [ha]
    exact (canonical22382 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1455 + difference 0 5) (sourceB1455 + difference 5 0) sourceC1455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA1455 + difference 0 5) (sourceB1455 + difference 5 0) sourceC1455) = raw22383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1455 sourceB1455 sourceC1455 difference raw22383; decide +kernel
    rw [ha]
    exact (canonical22383 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1455 + sourceB1455) sourceC1455) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1455 + sourceB1455) sourceC1455) = raw22384 := by
      apply Matrix.ext; unfold doubleCharges sourceA1455 sourceB1455 sourceC1455 raw22384; decide +kernel
    rw [ha]
    exact (canonical22384 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1455 sourceB1455 sourceC1455
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1455, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1456 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1456 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC1456 : Charge := ![1, 1, 1, 1, -2, -2]
def sourceForm1456 : Integer.Sparse Master := [(Sum.inr 1377, 1), (Sum.inr 2913, 3), (Sum.inr 3059, 2), (Sum.inr 4087, -1)]

theorem sourceEq1456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1456 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1456 + difference 0 0) (sourceB1456 + difference 0 0) sourceC1456) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1377) := by
    have ha : (tripleCharges (sourceA1456 + difference 0 0) (sourceB1456 + difference 0 0) sourceC1456) = raw22385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1456 sourceB1456 sourceC1456 difference raw22385; decide +kernel
    rw [ha]
    exact (canonical22385 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1456 + difference 0 1) (sourceB1456 + difference 1 0) sourceC1456) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2913) := by
    have ha : (tripleCharges (sourceA1456 + difference 0 1) (sourceB1456 + difference 1 0) sourceC1456) = raw22386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1456 sourceB1456 sourceC1456 difference raw22386; decide +kernel
    rw [ha]
    exact (canonical22386 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1456 + difference 0 2) (sourceB1456 + difference 2 0) sourceC1456) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2913) := by
    have ha : (tripleCharges (sourceA1456 + difference 0 2) (sourceB1456 + difference 2 0) sourceC1456) = raw22387 := by
      apply Matrix.ext; unfold tripleCharges sourceA1456 sourceB1456 sourceC1456 difference raw22387; decide +kernel
    rw [ha]
    exact (canonical22387 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1456 + difference 0 3) (sourceB1456 + difference 3 0) sourceC1456) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2913) := by
    have ha : (tripleCharges (sourceA1456 + difference 0 3) (sourceB1456 + difference 3 0) sourceC1456) = raw22388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1456 sourceB1456 sourceC1456 difference raw22388; decide +kernel
    rw [ha]
    exact (canonical22388 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1456 + difference 0 4) (sourceB1456 + difference 4 0) sourceC1456) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3059) := by
    have ha : (tripleCharges (sourceA1456 + difference 0 4) (sourceB1456 + difference 4 0) sourceC1456) = raw22389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1456 sourceB1456 sourceC1456 difference raw22389; decide +kernel
    rw [ha]
    exact (canonical22389 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1456 + difference 0 5) (sourceB1456 + difference 5 0) sourceC1456) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3059) := by
    have ha : (tripleCharges (sourceA1456 + difference 0 5) (sourceB1456 + difference 5 0) sourceC1456) = raw22390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1456 sourceB1456 sourceC1456 difference raw22390; decide +kernel
    rw [ha]
    exact (canonical22390 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1456 + sourceB1456) sourceC1456) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA1456 + sourceB1456) sourceC1456) = raw22391 := by
      apply Matrix.ext; unfold doubleCharges sourceA1456 sourceB1456 sourceC1456 raw22391; decide +kernel
    rw [ha]
    exact (canonical22391 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1456 sourceB1456 sourceC1456
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1456, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1457 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1457 : Charge := ![2, -1, 0, 0, -2, 1]
def sourceC1457 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceForm1457 : Integer.Sparse Master := [(Sum.inr 1133, 2), (Sum.inr 1143, 1), (Sum.inr 1146, 1), (Sum.inr 1245, 1), (Sum.inr 2522, 1), (Sum.inr 4084, -1)]

theorem sourceEq1457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1457 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1457 + difference 0 1) (sourceB1457 + difference 1 0) sourceC1457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA1457 + difference 0 1) (sourceB1457 + difference 1 0) sourceC1457) = raw22392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1457 sourceB1457 sourceC1457 difference raw22392; decide +kernel
    rw [ha]
    exact (canonical22392 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1457 + difference 1 1) (sourceB1457 + difference 1 1) sourceC1457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA1457 + difference 1 1) (sourceB1457 + difference 1 1) sourceC1457) = raw22393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1457 sourceB1457 sourceC1457 difference raw22393; decide +kernel
    rw [ha]
    exact (canonical22393 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1457 + difference 2 1) (sourceB1457 + difference 1 2) sourceC1457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1133) := by
    have ha : (tripleCharges (sourceA1457 + difference 2 1) (sourceB1457 + difference 1 2) sourceC1457) = raw22394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1457 sourceB1457 sourceC1457 difference raw22394; decide +kernel
    rw [ha]
    exact (canonical22394 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1457 + difference 3 1) (sourceB1457 + difference 1 3) sourceC1457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1133) := by
    have ha : (tripleCharges (sourceA1457 + difference 3 1) (sourceB1457 + difference 1 3) sourceC1457) = raw22395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1457 sourceB1457 sourceC1457 difference raw22395; decide +kernel
    rw [ha]
    exact (canonical22395 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1457 + difference 4 1) (sourceB1457 + difference 1 4) sourceC1457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1146) := by
    have ha : (tripleCharges (sourceA1457 + difference 4 1) (sourceB1457 + difference 1 4) sourceC1457) = raw22396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1457 sourceB1457 sourceC1457 difference raw22396; decide +kernel
    rw [ha]
    exact (canonical22396 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1457 + difference 5 1) (sourceB1457 + difference 1 5) sourceC1457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1143) := by
    have ha : (tripleCharges (sourceA1457 + difference 5 1) (sourceB1457 + difference 1 5) sourceC1457) = raw22397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1457 sourceB1457 sourceC1457 difference raw22397; decide +kernel
    rw [ha]
    exact (canonical22397 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1457 + sourceB1457) sourceC1457) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1457 + sourceB1457) sourceC1457) = raw22398 := by
      apply Matrix.ext; unfold doubleCharges sourceA1457 sourceB1457 sourceC1457 raw22398; decide +kernel
    rw [ha]
    exact (canonical22398 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1457 sourceB1457 sourceC1457
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1457, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1458 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1458 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1458 : Charge := ![2, -1, 0, 0, -2, 1]
def sourceForm1458 : Integer.Sparse Master := [(Sum.inr 653, 1), (Sum.inr 1171, 2), (Sum.inr 1273, 1), (Sum.inr 1294, 1), (Sum.inr 1306, 1), (Sum.inr 4092, -1)]

theorem sourceEq1458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1458 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1458 + difference 1 0) (sourceB1458 + difference 0 1) sourceC1458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 653) := by
    have ha : (tripleCharges (sourceA1458 + difference 1 0) (sourceB1458 + difference 0 1) sourceC1458) = raw22399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1458 sourceB1458 sourceC1458 difference raw22399; decide +kernel
    rw [ha]
    exact (canonical22399 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1458 + difference 1 1) (sourceB1458 + difference 1 1) sourceC1458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA1458 + difference 1 1) (sourceB1458 + difference 1 1) sourceC1458) = raw22400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1458 sourceB1458 sourceC1458 difference raw22400; decide +kernel
    rw [ha]
    exact (canonical22400 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1458 + difference 1 2) (sourceB1458 + difference 2 1) sourceC1458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1171) := by
    have ha : (tripleCharges (sourceA1458 + difference 1 2) (sourceB1458 + difference 2 1) sourceC1458) = raw22401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1458 sourceB1458 sourceC1458 difference raw22401; decide +kernel
    rw [ha]
    exact (canonical22401 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1458 + difference 1 3) (sourceB1458 + difference 3 1) sourceC1458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1171) := by
    have ha : (tripleCharges (sourceA1458 + difference 1 3) (sourceB1458 + difference 3 1) sourceC1458) = raw22402 := by
      apply Matrix.ext; unfold tripleCharges sourceA1458 sourceB1458 sourceC1458 difference raw22402; decide +kernel
    rw [ha]
    exact (canonical22402 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1458 + difference 1 4) (sourceB1458 + difference 4 1) sourceC1458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1306) := by
    have ha : (tripleCharges (sourceA1458 + difference 1 4) (sourceB1458 + difference 4 1) sourceC1458) = raw22403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1458 sourceB1458 sourceC1458 difference raw22403; decide +kernel
    rw [ha]
    exact (canonical22403 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1458 + difference 1 5) (sourceB1458 + difference 5 1) sourceC1458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1458 + difference 1 5) (sourceB1458 + difference 5 1) sourceC1458) = raw22404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1458 sourceB1458 sourceC1458 difference raw22404; decide +kernel
    rw [ha]
    exact (canonical22404 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1458 + sourceB1458) sourceC1458) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1458 + sourceB1458) sourceC1458) = raw22405 := by
      apply Matrix.ext; unfold doubleCharges sourceA1458 sourceB1458 sourceC1458 raw22405; decide +kernel
    rw [ha]
    exact (canonical22405 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1458 sourceB1458 sourceC1458
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1458, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1459 : Charge := ![2, -1, 0, 0, -2, 1]
def sourceB1459 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1459 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1459 : Integer.Sparse Master := [(Sum.inr 1655, 2), (Sum.inr 1657, 1), (Sum.inr 1660, 1), (Sum.inr 1738, 1), (Sum.inr 2683, 1), (Sum.inr 4071, -1)]

theorem sourceEq1459 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1459 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1459 + difference 0 0) (sourceB1459 + difference 0 0) sourceC1459) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA1459 + difference 0 0) (sourceB1459 + difference 0 0) sourceC1459) = raw22406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1459 sourceB1459 sourceC1459 difference raw22406; decide +kernel
    rw [ha]
    exact (canonical22406 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1459 + difference 0 1) (sourceB1459 + difference 1 0) sourceC1459) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1660) := by
    have ha : (tripleCharges (sourceA1459 + difference 0 1) (sourceB1459 + difference 1 0) sourceC1459) = raw22407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1459 sourceB1459 sourceC1459 difference raw22407; decide +kernel
    rw [ha]
    exact (canonical22407 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1459 + difference 0 2) (sourceB1459 + difference 2 0) sourceC1459) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1655) := by
    have ha : (tripleCharges (sourceA1459 + difference 0 2) (sourceB1459 + difference 2 0) sourceC1459) = raw22408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1459 sourceB1459 sourceC1459 difference raw22408; decide +kernel
    rw [ha]
    exact (canonical22408 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1459 + difference 0 3) (sourceB1459 + difference 3 0) sourceC1459) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1655) := by
    have ha : (tripleCharges (sourceA1459 + difference 0 3) (sourceB1459 + difference 3 0) sourceC1459) = raw22409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1459 sourceB1459 sourceC1459 difference raw22409; decide +kernel
    rw [ha]
    exact (canonical22409 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1459 + difference 0 4) (sourceB1459 + difference 4 0) sourceC1459) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1657) := by
    have ha : (tripleCharges (sourceA1459 + difference 0 4) (sourceB1459 + difference 4 0) sourceC1459) = raw22410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1459 sourceB1459 sourceC1459 difference raw22410; decide +kernel
    rw [ha]
    exact (canonical22410 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1459 + difference 0 5) (sourceB1459 + difference 5 0) sourceC1459) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1459 + difference 0 5) (sourceB1459 + difference 5 0) sourceC1459) = raw22411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1459 sourceB1459 sourceC1459 difference raw22411; decide +kernel
    rw [ha]
    exact (canonical22411 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1459 + sourceB1459) sourceC1459) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1459 + sourceB1459) sourceC1459) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1459 sourceB1459 sourceC1459 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1459 sourceB1459 sourceC1459
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1459, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1460 : Charge := ![2, -1, 0, 0, -2, 1]
def sourceB1460 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1460 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1460 : Integer.Sparse Master := [(Sum.inr 1741, 1), (Sum.inr 2683, 3), (Sum.inr 2780, 1), (Sum.inr 3311, 1), (Sum.inr 4071, -1)]

theorem sourceEq1460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1460 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1460 + difference 1 0) (sourceB1460 + difference 0 1) sourceC1460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA1460 + difference 1 0) (sourceB1460 + difference 0 1) sourceC1460) = raw22412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1460 sourceB1460 sourceC1460 difference raw22412; decide +kernel
    rw [ha]
    exact (canonical22412 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1460 + difference 1 1) (sourceB1460 + difference 1 1) sourceC1460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA1460 + difference 1 1) (sourceB1460 + difference 1 1) sourceC1460) = raw22406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1460 sourceB1460 sourceC1460 difference raw22406; decide +kernel
    rw [ha]
    exact (canonical22406 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1460 + difference 1 2) (sourceB1460 + difference 2 1) sourceC1460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA1460 + difference 1 2) (sourceB1460 + difference 2 1) sourceC1460) = raw22413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1460 sourceB1460 sourceC1460 difference raw22413; decide +kernel
    rw [ha]
    exact (canonical22413 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1460 + difference 1 3) (sourceB1460 + difference 3 1) sourceC1460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA1460 + difference 1 3) (sourceB1460 + difference 3 1) sourceC1460) = raw22414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1460 sourceB1460 sourceC1460 difference raw22414; decide +kernel
    rw [ha]
    exact (canonical22414 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1460 + difference 1 4) (sourceB1460 + difference 4 1) sourceC1460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2780) := by
    have ha : (tripleCharges (sourceA1460 + difference 1 4) (sourceB1460 + difference 4 1) sourceC1460) = raw22415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1460 sourceB1460 sourceC1460 difference raw22415; decide +kernel
    rw [ha]
    exact (canonical22415 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1460 + difference 1 5) (sourceB1460 + difference 5 1) sourceC1460) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3311) := by
    have ha : (tripleCharges (sourceA1460 + difference 1 5) (sourceB1460 + difference 5 1) sourceC1460) = raw22416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1460 sourceB1460 sourceC1460 difference raw22416; decide +kernel
    rw [ha]
    exact (canonical22416 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1460 + sourceB1460) sourceC1460) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1460 + sourceB1460) sourceC1460) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1460 sourceB1460 sourceC1460 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1460 sourceB1460 sourceC1460
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1460, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1461 : Charge := ![2, -1, 0, 0, -2, 1]
def sourceB1461 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1461 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1461 : Integer.Sparse Master := [(Sum.inr 1627, 1), (Sum.inr 2397, 2), (Sum.inr 2409, 1), (Sum.inr 2683, 1), (Sum.inr 3301, 1), (Sum.inr 4071, -1)]

theorem sourceEq1461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1461 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1461 + difference 4 0) (sourceB1461 + difference 0 4) sourceC1461) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1627) := by
    have ha : (tripleCharges (sourceA1461 + difference 4 0) (sourceB1461 + difference 0 4) sourceC1461) = raw22417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1461 sourceB1461 sourceC1461 difference raw22417; decide +kernel
    rw [ha]
    exact (canonical22417 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1461 + difference 4 1) (sourceB1461 + difference 1 4) sourceC1461) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2409) := by
    have ha : (tripleCharges (sourceA1461 + difference 4 1) (sourceB1461 + difference 1 4) sourceC1461) = raw22418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1461 sourceB1461 sourceC1461 difference raw22418; decide +kernel
    rw [ha]
    exact (canonical22418 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1461 + difference 4 2) (sourceB1461 + difference 2 4) sourceC1461) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2397) := by
    have ha : (tripleCharges (sourceA1461 + difference 4 2) (sourceB1461 + difference 2 4) sourceC1461) = raw22419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1461 sourceB1461 sourceC1461 difference raw22419; decide +kernel
    rw [ha]
    exact (canonical22419 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1461 + difference 4 3) (sourceB1461 + difference 3 4) sourceC1461) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2397) := by
    have ha : (tripleCharges (sourceA1461 + difference 4 3) (sourceB1461 + difference 3 4) sourceC1461) = raw22420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1461 sourceB1461 sourceC1461 difference raw22420; decide +kernel
    rw [ha]
    exact (canonical22420 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1461 + difference 4 4) (sourceB1461 + difference 4 4) sourceC1461) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA1461 + difference 4 4) (sourceB1461 + difference 4 4) sourceC1461) = raw22406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1461 sourceB1461 sourceC1461 difference raw22406; decide +kernel
    rw [ha]
    exact (canonical22406 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1461 + difference 4 5) (sourceB1461 + difference 5 4) sourceC1461) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1461 + difference 4 5) (sourceB1461 + difference 5 4) sourceC1461) = raw22421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1461 sourceB1461 sourceC1461 difference raw22421; decide +kernel
    rw [ha]
    exact (canonical22421 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1461 + sourceB1461) sourceC1461) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1461 + sourceB1461) sourceC1461) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1461 sourceB1461 sourceC1461 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1461 sourceB1461 sourceC1461
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1461, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1462 : Charge := ![2, -1, 0, 0, -2, 1]
def sourceB1462 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1462 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1462 : Integer.Sparse Master := [(Sum.inr 1738, 1), (Sum.inr 2683, 1), (Sum.inr 3295, 2), (Sum.inr 3301, 1), (Sum.inr 3311, 1), (Sum.inr 4071, -1)]

theorem sourceEq1462 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1462 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1462 + difference 0 5) (sourceB1462 + difference 5 0) sourceC1462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1462 + difference 0 5) (sourceB1462 + difference 5 0) sourceC1462) = raw22411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1462 sourceB1462 sourceC1462 difference raw22411; decide +kernel
    rw [ha]
    exact (canonical22411 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1462 + difference 1 5) (sourceB1462 + difference 5 1) sourceC1462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3311) := by
    have ha : (tripleCharges (sourceA1462 + difference 1 5) (sourceB1462 + difference 5 1) sourceC1462) = raw22416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1462 sourceB1462 sourceC1462 difference raw22416; decide +kernel
    rw [ha]
    exact (canonical22416 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1462 + difference 2 5) (sourceB1462 + difference 5 2) sourceC1462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3295) := by
    have ha : (tripleCharges (sourceA1462 + difference 2 5) (sourceB1462 + difference 5 2) sourceC1462) = raw22422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1462 sourceB1462 sourceC1462 difference raw22422; decide +kernel
    rw [ha]
    exact (canonical22422 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1462 + difference 3 5) (sourceB1462 + difference 5 3) sourceC1462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3295) := by
    have ha : (tripleCharges (sourceA1462 + difference 3 5) (sourceB1462 + difference 5 3) sourceC1462) = raw22423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1462 sourceB1462 sourceC1462 difference raw22423; decide +kernel
    rw [ha]
    exact (canonical22423 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1462 + difference 4 5) (sourceB1462 + difference 5 4) sourceC1462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1462 + difference 4 5) (sourceB1462 + difference 5 4) sourceC1462) = raw22421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1462 sourceB1462 sourceC1462 difference raw22421; decide +kernel
    rw [ha]
    exact (canonical22421 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1462 + difference 5 5) (sourceB1462 + difference 5 5) sourceC1462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA1462 + difference 5 5) (sourceB1462 + difference 5 5) sourceC1462) = raw22406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1462 sourceB1462 sourceC1462 difference raw22406; decide +kernel
    rw [ha]
    exact (canonical22406 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1462 + sourceB1462) sourceC1462) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1462 + sourceB1462) sourceC1462) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1462 sourceB1462 sourceC1462 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1462 sourceB1462 sourceC1462
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1462, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1463 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1463 : Charge := ![2, -1, 0, 1, -2, 0]
def sourceC1463 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceForm1463 : Integer.Sparse Master := [(Sum.inr 1113, 1), (Sum.inr 1119, 1), (Sum.inr 1121, 1), (Sum.inr 1138, 1), (Sum.inr 1219, 1), (Sum.inr 2488, 1), (Sum.inr 4092, -1)]

theorem sourceEq1463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1463 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1463 + difference 0 1) (sourceB1463 + difference 1 0) sourceC1463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA1463 + difference 0 1) (sourceB1463 + difference 1 0) sourceC1463) = raw22424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1463 sourceB1463 sourceC1463 difference raw22424; decide +kernel
    rw [ha]
    exact (canonical22424 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1463 + difference 1 1) (sourceB1463 + difference 1 1) sourceC1463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1463 + difference 1 1) (sourceB1463 + difference 1 1) sourceC1463) = raw22425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1463 sourceB1463 sourceC1463 difference raw22425; decide +kernel
    rw [ha]
    exact (canonical22425 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1463 + difference 2 1) (sourceB1463 + difference 1 2) sourceC1463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1113) := by
    have ha : (tripleCharges (sourceA1463 + difference 2 1) (sourceB1463 + difference 1 2) sourceC1463) = raw22426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1463 sourceB1463 sourceC1463 difference raw22426; decide +kernel
    rw [ha]
    exact (canonical22426 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1463 + difference 3 1) (sourceB1463 + difference 1 3) sourceC1463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA1463 + difference 3 1) (sourceB1463 + difference 1 3) sourceC1463) = raw22427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1463 sourceB1463 sourceC1463 difference raw22427; decide +kernel
    rw [ha]
    exact (canonical22427 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1463 + difference 4 1) (sourceB1463 + difference 1 4) sourceC1463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1121) := by
    have ha : (tripleCharges (sourceA1463 + difference 4 1) (sourceB1463 + difference 1 4) sourceC1463) = raw22428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1463 sourceB1463 sourceC1463 difference raw22428; decide +kernel
    rw [ha]
    exact (canonical22428 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1463 + difference 5 1) (sourceB1463 + difference 1 5) sourceC1463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1119) := by
    have ha : (tripleCharges (sourceA1463 + difference 5 1) (sourceB1463 + difference 1 5) sourceC1463) = raw20281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1463 sourceB1463 sourceC1463 difference raw20281; decide +kernel
    rw [ha]
    exact (canonical20281 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1463 + sourceB1463) sourceC1463) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1463 + sourceB1463) sourceC1463) = raw20283 := by
      apply Matrix.ext; unfold doubleCharges sourceA1463 sourceB1463 sourceC1463 raw20283; decide +kernel
    rw [ha]
    exact (canonical20283 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1463 sourceB1463 sourceC1463
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1463, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1464 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1464 : Charge := ![2, -1, 0, 1, -2, 0]
def sourceC1464 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceForm1464 : Integer.Sparse Master := [(Sum.inr 631, 1), (Sum.inr 1138, 1), (Sum.inr 1151, 1), (Sum.inr 1219, 1), (Sum.inr 1236, 1), (Sum.inr 1241, 1), (Sum.inr 4092, -1)]

theorem sourceEq1464 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1464 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1464 + difference 3 0) (sourceB1464 + difference 0 3) sourceC1464) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 631) := by
    have ha : (tripleCharges (sourceA1464 + difference 3 0) (sourceB1464 + difference 0 3) sourceC1464) = raw22429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1464 sourceB1464 sourceC1464 difference raw22429; decide +kernel
    rw [ha]
    exact (canonical22429 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1464 + difference 3 1) (sourceB1464 + difference 1 3) sourceC1464) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA1464 + difference 3 1) (sourceB1464 + difference 1 3) sourceC1464) = raw22427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1464 sourceB1464 sourceC1464 difference raw22427; decide +kernel
    rw [ha]
    exact (canonical22427 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1464 + difference 3 2) (sourceB1464 + difference 2 3) sourceC1464) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1151) := by
    have ha : (tripleCharges (sourceA1464 + difference 3 2) (sourceB1464 + difference 2 3) sourceC1464) = raw22430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1464 sourceB1464 sourceC1464 difference raw22430; decide +kernel
    rw [ha]
    exact (canonical22430 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1464 + difference 3 3) (sourceB1464 + difference 3 3) sourceC1464) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA1464 + difference 3 3) (sourceB1464 + difference 3 3) sourceC1464) = raw22425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1464 sourceB1464 sourceC1464 difference raw22425; decide +kernel
    rw [ha]
    exact (canonical22425 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1464 + difference 3 4) (sourceB1464 + difference 4 3) sourceC1464) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1464 + difference 3 4) (sourceB1464 + difference 4 3) sourceC1464) = raw20287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1464 sourceB1464 sourceC1464 difference raw20287; decide +kernel
    rw [ha]
    exact (canonical20287 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1464 + difference 3 5) (sourceB1464 + difference 5 3) sourceC1464) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA1464 + difference 3 5) (sourceB1464 + difference 5 3) sourceC1464) = raw22431 := by
      apply Matrix.ext; unfold tripleCharges sourceA1464 sourceB1464 sourceC1464 difference raw22431; decide +kernel
    rw [ha]
    exact (canonical22431 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1464 + sourceB1464) sourceC1464) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1464 + sourceB1464) sourceC1464) = raw20283 := by
      apply Matrix.ext; unfold doubleCharges sourceA1464 sourceB1464 sourceC1464 raw20283; decide +kernel
    rw [ha]
    exact (canonical20283 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1464 sourceB1464 sourceC1464
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1464, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1465 : Charge := ![2, -1, 0, 1, -2, 0]
def sourceB1465 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1465 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1465 : Integer.Sparse Master := [(Sum.inr 1606, 1), (Sum.inr 1608, 1), (Sum.inr 1611, 1), (Sum.inr 1618, 1), (Sum.inr 1738, 1), (Sum.inr 3295, 1), (Sum.inr 4071, -1)]

theorem sourceEq1465 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1465 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1465 + difference 0 0) (sourceB1465 + difference 0 0) sourceC1465) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3295) := by
    have ha : (tripleCharges (sourceA1465 + difference 0 0) (sourceB1465 + difference 0 0) sourceC1465) = raw22423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1465 sourceB1465 sourceC1465 difference raw22423; decide +kernel
    rw [ha]
    exact (canonical22423 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1465 + difference 0 1) (sourceB1465 + difference 1 0) sourceC1465) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1611) := by
    have ha : (tripleCharges (sourceA1465 + difference 0 1) (sourceB1465 + difference 1 0) sourceC1465) = raw22432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1465 sourceB1465 sourceC1465 difference raw22432; decide +kernel
    rw [ha]
    exact (canonical22432 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1465 + difference 0 2) (sourceB1465 + difference 2 0) sourceC1465) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1606) := by
    have ha : (tripleCharges (sourceA1465 + difference 0 2) (sourceB1465 + difference 2 0) sourceC1465) = raw22433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1465 sourceB1465 sourceC1465 difference raw22433; decide +kernel
    rw [ha]
    exact (canonical22433 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1465 + difference 0 3) (sourceB1465 + difference 3 0) sourceC1465) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1465 + difference 0 3) (sourceB1465 + difference 3 0) sourceC1465) = raw22411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1465 sourceB1465 sourceC1465 difference raw22411; decide +kernel
    rw [ha]
    exact (canonical22411 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1465 + difference 0 4) (sourceB1465 + difference 4 0) sourceC1465) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1608) := by
    have ha : (tripleCharges (sourceA1465 + difference 0 4) (sourceB1465 + difference 4 0) sourceC1465) = raw22434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1465 sourceB1465 sourceC1465 difference raw22434; decide +kernel
    rw [ha]
    exact (canonical22434 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1465 + difference 0 5) (sourceB1465 + difference 5 0) sourceC1465) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1618) := by
    have ha : (tripleCharges (sourceA1465 + difference 0 5) (sourceB1465 + difference 5 0) sourceC1465) = raw22435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1465 sourceB1465 sourceC1465 difference raw22435; decide +kernel
    rw [ha]
    exact (canonical22435 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1465 + sourceB1465) sourceC1465) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1465 + sourceB1465) sourceC1465) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1465 sourceB1465 sourceC1465 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1465 sourceB1465 sourceC1465
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1465, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1466 : Charge := ![2, -1, 0, 1, -2, 0]
def sourceB1466 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC1466 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1466 : Integer.Sparse Master := [(Sum.inr 1618, 1), (Sum.inr 3243, 1), (Sum.inr 3280, 1), (Sum.inr 3295, 1), (Sum.inr 3297, 1), (Sum.inr 3301, 1), (Sum.inr 4071, -1)]

theorem sourceEq1466 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1466 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1466 + difference 4 0) (sourceB1466 + difference 0 4) sourceC1466) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1618) := by
    have ha : (tripleCharges (sourceA1466 + difference 4 0) (sourceB1466 + difference 0 4) sourceC1466) = raw22436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1466 sourceB1466 sourceC1466 difference raw22436; decide +kernel
    rw [ha]
    exact (canonical22436 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1466 + difference 4 1) (sourceB1466 + difference 1 4) sourceC1466) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3243) := by
    have ha : (tripleCharges (sourceA1466 + difference 4 1) (sourceB1466 + difference 1 4) sourceC1466) = raw22437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1466 sourceB1466 sourceC1466 difference raw22437; decide +kernel
    rw [ha]
    exact (canonical22437 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1466 + difference 4 2) (sourceB1466 + difference 2 4) sourceC1466) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3280) := by
    have ha : (tripleCharges (sourceA1466 + difference 4 2) (sourceB1466 + difference 2 4) sourceC1466) = raw22438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1466 sourceB1466 sourceC1466 difference raw22438; decide +kernel
    rw [ha]
    exact (canonical22438 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1466 + difference 4 3) (sourceB1466 + difference 3 4) sourceC1466) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1466 + difference 4 3) (sourceB1466 + difference 3 4) sourceC1466) = raw22421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1466 sourceB1466 sourceC1466 difference raw22421; decide +kernel
    rw [ha]
    exact (canonical22421 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1466 + difference 4 4) (sourceB1466 + difference 4 4) sourceC1466) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3295) := by
    have ha : (tripleCharges (sourceA1466 + difference 4 4) (sourceB1466 + difference 4 4) sourceC1466) = raw22423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1466 sourceB1466 sourceC1466 difference raw22423; decide +kernel
    rw [ha]
    exact (canonical22423 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1466 + difference 4 5) (sourceB1466 + difference 5 4) sourceC1466) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3297) := by
    have ha : (tripleCharges (sourceA1466 + difference 4 5) (sourceB1466 + difference 5 4) sourceC1466) = raw22439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1466 sourceB1466 sourceC1466 difference raw22439; decide +kernel
    rw [ha]
    exact (canonical22439 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1466 + sourceB1466) sourceC1466) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1466 + sourceB1466) sourceC1466) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1466 sourceB1466 sourceC1466 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1466 sourceB1466 sourceC1466
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1466, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1467 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1467 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC1467 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceForm1467 : Integer.Sparse Master := [(Sum.inr 1114, 1), (Sum.inr 1120, 2), (Sum.inr 1139, 1), (Sum.inr 1220, 1), (Sum.inr 2489, 1), (Sum.inr 4091, -1)]

theorem sourceEq1467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1467 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1467 + difference 0 1) (sourceB1467 + difference 1 0) sourceC1467) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA1467 + difference 0 1) (sourceB1467 + difference 1 0) sourceC1467) = raw22440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1467 sourceB1467 sourceC1467 difference raw22440; decide +kernel
    rw [ha]
    exact (canonical22440 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1467 + difference 1 1) (sourceB1467 + difference 1 1) sourceC1467) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1467 + difference 1 1) (sourceB1467 + difference 1 1) sourceC1467) = raw22441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1467 sourceB1467 sourceC1467 difference raw22441; decide +kernel
    rw [ha]
    exact (canonical22441 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1467 + difference 2 1) (sourceB1467 + difference 1 2) sourceC1467) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1114) := by
    have ha : (tripleCharges (sourceA1467 + difference 2 1) (sourceB1467 + difference 1 2) sourceC1467) = raw22442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1467 sourceB1467 sourceC1467 difference raw22442; decide +kernel
    rw [ha]
    exact (canonical22442 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1467 + difference 3 1) (sourceB1467 + difference 1 3) sourceC1467) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1139) := by
    have ha : (tripleCharges (sourceA1467 + difference 3 1) (sourceB1467 + difference 1 3) sourceC1467) = raw22443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1467 sourceB1467 sourceC1467 difference raw22443; decide +kernel
    rw [ha]
    exact (canonical22443 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1467 + difference 4 1) (sourceB1467 + difference 1 4) sourceC1467) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1120) := by
    have ha : (tripleCharges (sourceA1467 + difference 4 1) (sourceB1467 + difference 1 4) sourceC1467) = raw22444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1467 sourceB1467 sourceC1467 difference raw22444; decide +kernel
    rw [ha]
    exact (canonical22444 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1467 + difference 5 1) (sourceB1467 + difference 1 5) sourceC1467) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1120) := by
    have ha : (tripleCharges (sourceA1467 + difference 5 1) (sourceB1467 + difference 1 5) sourceC1467) = raw22445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1467 sourceB1467 sourceC1467 difference raw22445; decide +kernel
    rw [ha]
    exact (canonical22445 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1467 + sourceB1467) sourceC1467) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1467 + sourceB1467) sourceC1467) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA1467 sourceB1467 sourceC1467 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1467 sourceB1467 sourceC1467
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1467, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1468 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1468 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceC1468 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceForm1468 : Integer.Sparse Master := [(Sum.inr 632, 1), (Sum.inr 1139, 1), (Sum.inr 1152, 1), (Sum.inr 1220, 1), (Sum.inr 1240, 2), (Sum.inr 4091, -1)]

theorem sourceEq1468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1468 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1468 + difference 3 0) (sourceB1468 + difference 0 3) sourceC1468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 632) := by
    have ha : (tripleCharges (sourceA1468 + difference 3 0) (sourceB1468 + difference 0 3) sourceC1468) = raw22446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1468 sourceB1468 sourceC1468 difference raw22446; decide +kernel
    rw [ha]
    exact (canonical22446 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1468 + difference 3 1) (sourceB1468 + difference 1 3) sourceC1468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1139) := by
    have ha : (tripleCharges (sourceA1468 + difference 3 1) (sourceB1468 + difference 1 3) sourceC1468) = raw22443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1468 sourceB1468 sourceC1468 difference raw22443; decide +kernel
    rw [ha]
    exact (canonical22443 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1468 + difference 3 2) (sourceB1468 + difference 2 3) sourceC1468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1152) := by
    have ha : (tripleCharges (sourceA1468 + difference 3 2) (sourceB1468 + difference 2 3) sourceC1468) = raw22447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1468 sourceB1468 sourceC1468 difference raw22447; decide +kernel
    rw [ha]
    exact (canonical22447 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1468 + difference 3 3) (sourceB1468 + difference 3 3) sourceC1468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1220) := by
    have ha : (tripleCharges (sourceA1468 + difference 3 3) (sourceB1468 + difference 3 3) sourceC1468) = raw22441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1468 sourceB1468 sourceC1468 difference raw22441; decide +kernel
    rw [ha]
    exact (canonical22441 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1468 + difference 3 4) (sourceB1468 + difference 4 3) sourceC1468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1468 + difference 3 4) (sourceB1468 + difference 4 3) sourceC1468) = raw22448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1468 sourceB1468 sourceC1468 difference raw22448; decide +kernel
    rw [ha]
    exact (canonical22448 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1468 + difference 3 5) (sourceB1468 + difference 5 3) sourceC1468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1468 + difference 3 5) (sourceB1468 + difference 5 3) sourceC1468) = raw22449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1468 sourceB1468 sourceC1468 difference raw22449; decide +kernel
    rw [ha]
    exact (canonical22449 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1468 + sourceB1468) sourceC1468) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1468 + sourceB1468) sourceC1468) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA1468 sourceB1468 sourceC1468 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1468 sourceB1468 sourceC1468
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1468, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1469 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceB1469 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC1469 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1469 : Integer.Sparse Master := [(Sum.inr 1614, 1), (Sum.inr 1618, 2), (Sum.inr 1626, 1), (Sum.inr 1751, 1), (Sum.inr 3297, 1), (Sum.inr 4071, -1)]

theorem sourceEq1469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1469 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1469 + difference 0 0) (sourceB1469 + difference 0 0) sourceC1469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3297) := by
    have ha : (tripleCharges (sourceA1469 + difference 0 0) (sourceB1469 + difference 0 0) sourceC1469) = raw22439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1469 sourceB1469 sourceC1469 difference raw22439; decide +kernel
    rw [ha]
    exact (canonical22439 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1469 + difference 0 1) (sourceB1469 + difference 1 0) sourceC1469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1626) := by
    have ha : (tripleCharges (sourceA1469 + difference 0 1) (sourceB1469 + difference 1 0) sourceC1469) = raw22450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1469 sourceB1469 sourceC1469 difference raw22450; decide +kernel
    rw [ha]
    exact (canonical22450 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1469 + difference 0 2) (sourceB1469 + difference 2 0) sourceC1469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1614) := by
    have ha : (tripleCharges (sourceA1469 + difference 0 2) (sourceB1469 + difference 2 0) sourceC1469) = raw22451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1469 sourceB1469 sourceC1469 difference raw22451; decide +kernel
    rw [ha]
    exact (canonical22451 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1469 + difference 0 3) (sourceB1469 + difference 3 0) sourceC1469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1469 + difference 0 3) (sourceB1469 + difference 3 0) sourceC1469) = raw22452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1469 sourceB1469 sourceC1469 difference raw22452; decide +kernel
    rw [ha]
    exact (canonical22452 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1469 + difference 0 4) (sourceB1469 + difference 4 0) sourceC1469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1618) := by
    have ha : (tripleCharges (sourceA1469 + difference 0 4) (sourceB1469 + difference 4 0) sourceC1469) = raw22435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1469 sourceB1469 sourceC1469 difference raw22435; decide +kernel
    rw [ha]
    exact (canonical22435 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1469 + difference 0 5) (sourceB1469 + difference 5 0) sourceC1469) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1618) := by
    have ha : (tripleCharges (sourceA1469 + difference 0 5) (sourceB1469 + difference 5 0) sourceC1469) = raw22453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1469 sourceB1469 sourceC1469 difference raw22453; decide +kernel
    rw [ha]
    exact (canonical22453 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1469 + sourceB1469) sourceC1469) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1469 + sourceB1469) sourceC1469) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1469 sourceB1469 sourceC1469 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1469 sourceB1469 sourceC1469
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1469, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1470 : Charge := ![2, -1, 0, 1, -1, -1]
def sourceB1470 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC1470 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1470 : Integer.Sparse Master := [(Sum.inr 1751, 1), (Sum.inr 3297, 2), (Sum.inr 3301, 2), (Sum.inr 3312, 1), (Sum.inr 4071, -1)]

theorem sourceEq1470 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1470 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1470 + difference 1 0) (sourceB1470 + difference 0 1) sourceC1470) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1751) := by
    have ha : (tripleCharges (sourceA1470 + difference 1 0) (sourceB1470 + difference 0 1) sourceC1470) = raw22332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1470 sourceB1470 sourceC1470 difference raw22332; decide +kernel
    rw [ha]
    exact (canonical22332 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1470 + difference 1 1) (sourceB1470 + difference 1 1) sourceC1470) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3297) := by
    have ha : (tripleCharges (sourceA1470 + difference 1 1) (sourceB1470 + difference 1 1) sourceC1470) = raw22439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1470 sourceB1470 sourceC1470 difference raw22439; decide +kernel
    rw [ha]
    exact (canonical22439 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1470 + difference 1 2) (sourceB1470 + difference 2 1) sourceC1470) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3297) := by
    have ha : (tripleCharges (sourceA1470 + difference 1 2) (sourceB1470 + difference 2 1) sourceC1470) = raw22454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1470 sourceB1470 sourceC1470 difference raw22454; decide +kernel
    rw [ha]
    exact (canonical22454 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1470 + difference 1 3) (sourceB1470 + difference 3 1) sourceC1470) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3312) := by
    have ha : (tripleCharges (sourceA1470 + difference 1 3) (sourceB1470 + difference 3 1) sourceC1470) = raw22455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1470 sourceB1470 sourceC1470 difference raw22455; decide +kernel
    rw [ha]
    exact (canonical22455 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1470 + difference 1 4) (sourceB1470 + difference 4 1) sourceC1470) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1470 + difference 1 4) (sourceB1470 + difference 4 1) sourceC1470) = raw22326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1470 sourceB1470 sourceC1470 difference raw22326; decide +kernel
    rw [ha]
    exact (canonical22326 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1470 + difference 1 5) (sourceB1470 + difference 5 1) sourceC1470) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3301) := by
    have ha : (tripleCharges (sourceA1470 + difference 1 5) (sourceB1470 + difference 5 1) sourceC1470) = raw22456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1470 sourceB1470 sourceC1470 difference raw22456; decide +kernel
    rw [ha]
    exact (canonical22456 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1470 + sourceB1470) sourceC1470) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1470 + sourceB1470) sourceC1470) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1470 sourceB1470 sourceC1470 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1470 sourceB1470 sourceC1470
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1470, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1471 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1471 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC1471 : Charge := ![2, -1, 0, 2, -2, -1]
def sourceForm1471 : Integer.Sparse Master := [(Sum.inr 1182, 1), (Sum.inr 2388, 1), (Sum.inr 2533, 1), (Sum.inr 2608, 1), (Sum.inr 2672, 1), (Sum.inr 2673, 1), (Sum.inr 4088, -1)]

theorem sourceEq1471 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1471 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1471 + difference 0 0) (sourceB1471 + difference 0 0) sourceC1471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1182) := by
    have ha : (tripleCharges (sourceA1471 + difference 0 0) (sourceB1471 + difference 0 0) sourceC1471) = raw22457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1471 sourceB1471 sourceC1471 difference raw22457; decide +kernel
    rw [ha]
    exact (canonical22457 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1471 + difference 0 1) (sourceB1471 + difference 1 0) sourceC1471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2608) := by
    have ha : (tripleCharges (sourceA1471 + difference 0 1) (sourceB1471 + difference 1 0) sourceC1471) = raw22458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1471 sourceB1471 sourceC1471 difference raw22458; decide +kernel
    rw [ha]
    exact (canonical22458 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1471 + difference 0 2) (sourceB1471 + difference 2 0) sourceC1471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2533) := by
    have ha : (tripleCharges (sourceA1471 + difference 0 2) (sourceB1471 + difference 2 0) sourceC1471) = raw22459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1471 sourceB1471 sourceC1471 difference raw22459; decide +kernel
    rw [ha]
    exact (canonical22459 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1471 + difference 0 3) (sourceB1471 + difference 3 0) sourceC1471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2388) := by
    have ha : (tripleCharges (sourceA1471 + difference 0 3) (sourceB1471 + difference 3 0) sourceC1471) = raw22460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1471 sourceB1471 sourceC1471 difference raw22460; decide +kernel
    rw [ha]
    exact (canonical22460 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1471 + difference 0 4) (sourceB1471 + difference 4 0) sourceC1471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA1471 + difference 0 4) (sourceB1471 + difference 4 0) sourceC1471) = raw22461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1471 sourceB1471 sourceC1471 difference raw22461; decide +kernel
    rw [ha]
    exact (canonical22461 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1471 + difference 0 5) (sourceB1471 + difference 5 0) sourceC1471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA1471 + difference 0 5) (sourceB1471 + difference 5 0) sourceC1471) = raw22462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1471 sourceB1471 sourceC1471 difference raw22462; decide +kernel
    rw [ha]
    exact (canonical22462 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1471 + sourceB1471) sourceC1471) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1471 + sourceB1471) sourceC1471) = raw22463 := by
      apply Matrix.ext; unfold doubleCharges sourceA1471 sourceB1471 sourceC1471 raw22463; decide +kernel
    rw [ha]
    exact (canonical22463 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1471 sourceB1471 sourceC1471
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1471, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
