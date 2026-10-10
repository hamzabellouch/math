import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical152
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical167
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical175
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical188
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical189
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical198
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical205
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical206
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical207
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical208

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1824 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1824 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceC1824 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceForm1824 : Integer.Sparse Master := [(Sum.inr 597, 1), (Sum.inr 1038, 1), (Sum.inr 1056, 1), (Sum.inr 1079, 3), (Sum.inr 4084, -1)]

theorem sourceEq1824 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1824 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1824 + difference 1 0) (sourceB1824 + difference 0 1) sourceC1824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 597) := by
    have ha : (tripleCharges (sourceA1824 + difference 1 0) (sourceB1824 + difference 0 1) sourceC1824) = raw26375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1824 sourceB1824 sourceC1824 difference raw26375; decide +kernel
    rw [ha]
    exact (canonical26375 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1824 + difference 1 1) (sourceB1824 + difference 1 1) sourceC1824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1038) := by
    have ha : (tripleCharges (sourceA1824 + difference 1 1) (sourceB1824 + difference 1 1) sourceC1824) = raw25426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1824 sourceB1824 sourceC1824 difference raw25426; decide +kernel
    rw [ha]
    exact (canonical25426 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1824 + difference 1 2) (sourceB1824 + difference 2 1) sourceC1824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1824 + difference 1 2) (sourceB1824 + difference 2 1) sourceC1824) = raw25420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1824 sourceB1824 sourceC1824 difference raw25420; decide +kernel
    rw [ha]
    exact (canonical25420 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1824 + difference 1 3) (sourceB1824 + difference 3 1) sourceC1824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1824 + difference 1 3) (sourceB1824 + difference 3 1) sourceC1824) = raw26376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1824 sourceB1824 sourceC1824 difference raw26376; decide +kernel
    rw [ha]
    exact (canonical26376 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1824 + difference 1 4) (sourceB1824 + difference 4 1) sourceC1824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1824 + difference 1 4) (sourceB1824 + difference 4 1) sourceC1824) = raw26377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1824 sourceB1824 sourceC1824 difference raw26377; decide +kernel
    rw [ha]
    exact (canonical26377 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1824 + difference 1 5) (sourceB1824 + difference 5 1) sourceC1824) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1056) := by
    have ha : (tripleCharges (sourceA1824 + difference 1 5) (sourceB1824 + difference 5 1) sourceC1824) = raw26378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1824 sourceB1824 sourceC1824 difference raw26378; decide +kernel
    rw [ha]
    exact (canonical26378 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1824 + sourceB1824) sourceC1824) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1824 + sourceB1824) sourceC1824) = raw21461 := by
      apply Matrix.ext; unfold doubleCharges sourceA1824 sourceB1824 sourceC1824 raw21461; decide +kernel
    rw [ha]
    exact (canonical21461 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1824 sourceB1824 sourceC1824
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1824, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1825 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceB1825 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1825 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1825 : Integer.Sparse Master := [(Sum.inr 1698, 1), (Sum.inr 3286, 3), (Sum.inr 3292, 1), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

theorem sourceEq1825 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1825 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1825 + difference 0 0) (sourceB1825 + difference 0 0) sourceC1825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1698) := by
    have ha : (tripleCharges (sourceA1825 + difference 0 0) (sourceB1825 + difference 0 0) sourceC1825) = raw26371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1825 sourceB1825 sourceC1825 difference raw26371; decide +kernel
    rw [ha]
    exact (canonical26371 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1825 + difference 0 1) (sourceB1825 + difference 1 0) sourceC1825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA1825 + difference 0 1) (sourceB1825 + difference 1 0) sourceC1825) = raw26369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1825 sourceB1825 sourceC1825 difference raw26369; decide +kernel
    rw [ha]
    exact (canonical26369 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1825 + difference 0 2) (sourceB1825 + difference 2 0) sourceC1825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3286) := by
    have ha : (tripleCharges (sourceA1825 + difference 0 2) (sourceB1825 + difference 2 0) sourceC1825) = raw26379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1825 sourceB1825 sourceC1825 difference raw26379; decide +kernel
    rw [ha]
    exact (canonical26379 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1825 + difference 0 3) (sourceB1825 + difference 3 0) sourceC1825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3286) := by
    have ha : (tripleCharges (sourceA1825 + difference 0 3) (sourceB1825 + difference 3 0) sourceC1825) = raw26380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1825 sourceB1825 sourceC1825 difference raw26380; decide +kernel
    rw [ha]
    exact (canonical26380 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1825 + difference 0 4) (sourceB1825 + difference 4 0) sourceC1825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3286) := by
    have ha : (tripleCharges (sourceA1825 + difference 0 4) (sourceB1825 + difference 4 0) sourceC1825) = raw26381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1825 sourceB1825 sourceC1825 difference raw26381; decide +kernel
    rw [ha]
    exact (canonical26381 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1825 + difference 0 5) (sourceB1825 + difference 5 0) sourceC1825) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3292) := by
    have ha : (tripleCharges (sourceA1825 + difference 0 5) (sourceB1825 + difference 5 0) sourceC1825) = raw26382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1825 sourceB1825 sourceC1825 difference raw26382; decide +kernel
    rw [ha]
    exact (canonical26382 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1825 + sourceB1825) sourceC1825) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1825 + sourceB1825) sourceC1825) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1825 sourceB1825 sourceC1825 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1825 sourceB1825 sourceC1825
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1825, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1826 : Charge := ![1, 1, -1, -1, -1, 1]
def sourceB1826 : Charge := ![3, -1, 0, 0, 0, -2]
def sourceC1826 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1826 : Integer.Sparse Master := [(Sum.inr 1698, 1), (Sum.inr 1699, 1), (Sum.inr 1706, 3), (Sum.inr 3292, 1), (Sum.inr 4068, -1)]

theorem sourceEq1826 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1826 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1826 + difference 0 5) (sourceB1826 + difference 5 0) sourceC1826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3292) := by
    have ha : (tripleCharges (sourceA1826 + difference 0 5) (sourceB1826 + difference 5 0) sourceC1826) = raw26382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1826 sourceB1826 sourceC1826 difference raw26382; decide +kernel
    rw [ha]
    exact (canonical26382 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1826 + difference 1 5) (sourceB1826 + difference 5 1) sourceC1826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA1826 + difference 1 5) (sourceB1826 + difference 5 1) sourceC1826) = raw26383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1826 sourceB1826 sourceC1826 difference raw26383; decide +kernel
    rw [ha]
    exact (canonical26383 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1826 + difference 2 5) (sourceB1826 + difference 5 2) sourceC1826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1826 + difference 2 5) (sourceB1826 + difference 5 2) sourceC1826) = raw26384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1826 sourceB1826 sourceC1826 difference raw26384; decide +kernel
    rw [ha]
    exact (canonical26384 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1826 + difference 3 5) (sourceB1826 + difference 5 3) sourceC1826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1826 + difference 3 5) (sourceB1826 + difference 5 3) sourceC1826) = raw26385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1826 sourceB1826 sourceC1826 difference raw26385; decide +kernel
    rw [ha]
    exact (canonical26385 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1826 + difference 4 5) (sourceB1826 + difference 5 4) sourceC1826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1826 + difference 4 5) (sourceB1826 + difference 5 4) sourceC1826) = raw26386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1826 sourceB1826 sourceC1826 difference raw26386; decide +kernel
    rw [ha]
    exact (canonical26386 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1826 + difference 5 5) (sourceB1826 + difference 5 5) sourceC1826) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1698) := by
    have ha : (tripleCharges (sourceA1826 + difference 5 5) (sourceB1826 + difference 5 5) sourceC1826) = raw26371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1826 sourceB1826 sourceC1826 difference raw26371; decide +kernel
    rw [ha]
    exact (canonical26371 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1826 + sourceB1826) sourceC1826) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1826 + sourceB1826) sourceC1826) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1826 sourceB1826 sourceC1826 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1826 sourceB1826 sourceC1826
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1826, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1827 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1827 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC1827 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceForm1827 : Integer.Sparse Master := [(Sum.inr 1316, 3), (Sum.inr 1319, 1), (Sum.inr 1366, 1), (Sum.inr 2880, 1), (Sum.inr 4091, -1)]

theorem sourceEq1827 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1827 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1827 + difference 0 1) (sourceB1827 + difference 1 0) sourceC1827) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2880) := by
    have ha : (tripleCharges (sourceA1827 + difference 0 1) (sourceB1827 + difference 1 0) sourceC1827) = raw26387 := by
      apply Matrix.ext; unfold tripleCharges sourceA1827 sourceB1827 sourceC1827 difference raw26387; decide +kernel
    rw [ha]
    exact (canonical26387 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1827 + difference 1 1) (sourceB1827 + difference 1 1) sourceC1827) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1366) := by
    have ha : (tripleCharges (sourceA1827 + difference 1 1) (sourceB1827 + difference 1 1) sourceC1827) = raw26388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1827 sourceB1827 sourceC1827 difference raw26388; decide +kernel
    rw [ha]
    exact (canonical26388 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1827 + difference 2 1) (sourceB1827 + difference 1 2) sourceC1827) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1316) := by
    have ha : (tripleCharges (sourceA1827 + difference 2 1) (sourceB1827 + difference 1 2) sourceC1827) = raw26389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1827 sourceB1827 sourceC1827 difference raw26389; decide +kernel
    rw [ha]
    exact (canonical26389 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1827 + difference 3 1) (sourceB1827 + difference 1 3) sourceC1827) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1316) := by
    have ha : (tripleCharges (sourceA1827 + difference 3 1) (sourceB1827 + difference 1 3) sourceC1827) = raw26390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1827 sourceB1827 sourceC1827 difference raw26390; decide +kernel
    rw [ha]
    exact (canonical26390 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1827 + difference 4 1) (sourceB1827 + difference 1 4) sourceC1827) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1316) := by
    have ha : (tripleCharges (sourceA1827 + difference 4 1) (sourceB1827 + difference 1 4) sourceC1827) = raw26391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1827 sourceB1827 sourceC1827 difference raw26391; decide +kernel
    rw [ha]
    exact (canonical26391 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1827 + difference 5 1) (sourceB1827 + difference 1 5) sourceC1827) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1319) := by
    have ha : (tripleCharges (sourceA1827 + difference 5 1) (sourceB1827 + difference 1 5) sourceC1827) = raw26392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1827 sourceB1827 sourceC1827 difference raw26392; decide +kernel
    rw [ha]
    exact (canonical26392 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1827 + sourceB1827) sourceC1827) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1827 + sourceB1827) sourceC1827) = raw26393 := by
      apply Matrix.ext; unfold doubleCharges sourceA1827 sourceB1827 sourceC1827 raw26393; decide +kernel
    rw [ha]
    exact (canonical26393 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1827 sourceB1827 sourceC1827
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1827, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1828 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceB1828 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC1828 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1828 : Integer.Sparse Master := [(Sum.inr 1699, 1), (Sum.inr 3239, 3), (Sum.inr 3244, 1), (Sum.inr 3292, 1), (Sum.inr 4068, -1)]

theorem sourceEq1828 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1828 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1828 + difference 0 0) (sourceB1828 + difference 0 0) sourceC1828) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA1828 + difference 0 0) (sourceB1828 + difference 0 0) sourceC1828) = raw26383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1828 sourceB1828 sourceC1828 difference raw26383; decide +kernel
    rw [ha]
    exact (canonical26383 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1828 + difference 0 1) (sourceB1828 + difference 1 0) sourceC1828) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3292) := by
    have ha : (tripleCharges (sourceA1828 + difference 0 1) (sourceB1828 + difference 1 0) sourceC1828) = raw26382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1828 sourceB1828 sourceC1828 difference raw26382; decide +kernel
    rw [ha]
    exact (canonical26382 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1828 + difference 0 2) (sourceB1828 + difference 2 0) sourceC1828) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3239) := by
    have ha : (tripleCharges (sourceA1828 + difference 0 2) (sourceB1828 + difference 2 0) sourceC1828) = raw26394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1828 sourceB1828 sourceC1828 difference raw26394; decide +kernel
    rw [ha]
    exact (canonical26394 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1828 + difference 0 3) (sourceB1828 + difference 3 0) sourceC1828) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3239) := by
    have ha : (tripleCharges (sourceA1828 + difference 0 3) (sourceB1828 + difference 3 0) sourceC1828) = raw26395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1828 sourceB1828 sourceC1828 difference raw26395; decide +kernel
    rw [ha]
    exact (canonical26395 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1828 + difference 0 4) (sourceB1828 + difference 4 0) sourceC1828) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3239) := by
    have ha : (tripleCharges (sourceA1828 + difference 0 4) (sourceB1828 + difference 4 0) sourceC1828) = raw26396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1828 sourceB1828 sourceC1828 difference raw26396; decide +kernel
    rw [ha]
    exact (canonical26396 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1828 + difference 0 5) (sourceB1828 + difference 5 0) sourceC1828) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3244) := by
    have ha : (tripleCharges (sourceA1828 + difference 0 5) (sourceB1828 + difference 5 0) sourceC1828) = raw26397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1828 sourceB1828 sourceC1828 difference raw26397; decide +kernel
    rw [ha]
    exact (canonical26397 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1828 + sourceB1828) sourceC1828) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1828 + sourceB1828) sourceC1828) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1828 sourceB1828 sourceC1828 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1828 sourceB1828 sourceC1828
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1828, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1829 : Charge := ![1, 2, -1, -1, -1, 0]
def sourceB1829 : Charge := ![3, -2, 0, 0, 0, -1]
def sourceC1829 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1829 : Integer.Sparse Master := [(Sum.inr 1696, 1), (Sum.inr 1699, 4), (Sum.inr 3244, 1), (Sum.inr 4068, -1)]

theorem sourceEq1829 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1829 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1829 + difference 0 5) (sourceB1829 + difference 5 0) sourceC1829) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3244) := by
    have ha : (tripleCharges (sourceA1829 + difference 0 5) (sourceB1829 + difference 5 0) sourceC1829) = raw26397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1829 sourceB1829 sourceC1829 difference raw26397; decide +kernel
    rw [ha]
    exact (canonical26397 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1829 + difference 1 5) (sourceB1829 + difference 5 1) sourceC1829) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1696) := by
    have ha : (tripleCharges (sourceA1829 + difference 1 5) (sourceB1829 + difference 5 1) sourceC1829) = raw26398 := by
      apply Matrix.ext; unfold tripleCharges sourceA1829 sourceB1829 sourceC1829 difference raw26398; decide +kernel
    rw [ha]
    exact (canonical26398 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1829 + difference 2 5) (sourceB1829 + difference 5 2) sourceC1829) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA1829 + difference 2 5) (sourceB1829 + difference 5 2) sourceC1829) = raw26399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1829 sourceB1829 sourceC1829 difference raw26399; decide +kernel
    rw [ha]
    exact (canonical26399 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1829 + difference 3 5) (sourceB1829 + difference 5 3) sourceC1829) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA1829 + difference 3 5) (sourceB1829 + difference 5 3) sourceC1829) = raw26400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1829 sourceB1829 sourceC1829 difference raw26400; decide +kernel
    rw [ha]
    exact (canonical26400 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1829 + difference 4 5) (sourceB1829 + difference 5 4) sourceC1829) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA1829 + difference 4 5) (sourceB1829 + difference 5 4) sourceC1829) = raw26401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1829 sourceB1829 sourceC1829 difference raw26401; decide +kernel
    rw [ha]
    exact (canonical26401 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1829 + difference 5 5) (sourceB1829 + difference 5 5) sourceC1829) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA1829 + difference 5 5) (sourceB1829 + difference 5 5) sourceC1829) = raw26383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1829 sourceB1829 sourceC1829 difference raw26383; decide +kernel
    rw [ha]
    exact (canonical26383 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1829 + sourceB1829) sourceC1829) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1829 + sourceB1829) sourceC1829) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1829 sourceB1829 sourceC1829 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1829 sourceB1829 sourceC1829
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1829, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1830 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1830 : Charge := ![3, -3, 0, 0, 0, 0]
def sourceC1830 : Charge := ![1, 3, -1, -1, -1, -1]
def sourceForm1830 : Integer.Sparse Master := [(Sum.inr 1350, 1), (Sum.inr 2234, 4), (Sum.inr 2839, 1), (Sum.inr 4079, -1)]

theorem sourceEq1830 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1830 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1830 + difference 0 0) (sourceB1830 + difference 0 0) sourceC1830) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1350) := by
    have ha : (tripleCharges (sourceA1830 + difference 0 0) (sourceB1830 + difference 0 0) sourceC1830) = raw26402 := by
      apply Matrix.ext; unfold tripleCharges sourceA1830 sourceB1830 sourceC1830 difference raw26402; decide +kernel
    rw [ha]
    exact (canonical26402 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1830 + difference 0 1) (sourceB1830 + difference 1 0) sourceC1830) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2839) := by
    have ha : (tripleCharges (sourceA1830 + difference 0 1) (sourceB1830 + difference 1 0) sourceC1830) = raw26403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1830 sourceB1830 sourceC1830 difference raw26403; decide +kernel
    rw [ha]
    exact (canonical26403 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1830 + difference 0 2) (sourceB1830 + difference 2 0) sourceC1830) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2234) := by
    have ha : (tripleCharges (sourceA1830 + difference 0 2) (sourceB1830 + difference 2 0) sourceC1830) = raw26404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1830 sourceB1830 sourceC1830 difference raw26404; decide +kernel
    rw [ha]
    exact (canonical26404 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1830 + difference 0 3) (sourceB1830 + difference 3 0) sourceC1830) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2234) := by
    have ha : (tripleCharges (sourceA1830 + difference 0 3) (sourceB1830 + difference 3 0) sourceC1830) = raw26405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1830 sourceB1830 sourceC1830 difference raw26405; decide +kernel
    rw [ha]
    exact (canonical26405 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1830 + difference 0 4) (sourceB1830 + difference 4 0) sourceC1830) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2234) := by
    have ha : (tripleCharges (sourceA1830 + difference 0 4) (sourceB1830 + difference 4 0) sourceC1830) = raw26406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1830 sourceB1830 sourceC1830 difference raw26406; decide +kernel
    rw [ha]
    exact (canonical26406 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1830 + difference 0 5) (sourceB1830 + difference 5 0) sourceC1830) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2234) := by
    have ha : (tripleCharges (sourceA1830 + difference 0 5) (sourceB1830 + difference 5 0) sourceC1830) = raw26407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1830 sourceB1830 sourceC1830 difference raw26407; decide +kernel
    rw [ha]
    exact (canonical26407 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1830 + sourceB1830) sourceC1830) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1830 + sourceB1830) sourceC1830) = raw26408 := by
      apply Matrix.ext; unfold doubleCharges sourceA1830 sourceB1830 sourceC1830 raw26408; decide +kernel
    rw [ha]
    exact (canonical26408 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1830 sourceB1830 sourceC1830
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1830, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1831 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1831 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1831 : Charge := ![2, -1, -1, -1, -1, 2]
def sourceForm1831 : Integer.Sparse Master := [(Sum.inr 1256, 1), (Sum.inr 2628, 1), (Sum.inr 2671, 1), (Sum.inr 2747, 3), (Sum.inr 4087, -1)]

theorem sourceEq1831 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1831 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1831 + difference 0 0) (sourceB1831 + difference 0 0) sourceC1831) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1256) := by
    have ha : (tripleCharges (sourceA1831 + difference 0 0) (sourceB1831 + difference 0 0) sourceC1831) = raw26409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1831 sourceB1831 sourceC1831 difference raw26409; decide +kernel
    rw [ha]
    exact (canonical26409 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1831 + difference 0 1) (sourceB1831 + difference 1 0) sourceC1831) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2628) := by
    have ha : (tripleCharges (sourceA1831 + difference 0 1) (sourceB1831 + difference 1 0) sourceC1831) = raw26410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1831 sourceB1831 sourceC1831 difference raw26410; decide +kernel
    rw [ha]
    exact (canonical26410 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1831 + difference 0 2) (sourceB1831 + difference 2 0) sourceC1831) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2747) := by
    have ha : (tripleCharges (sourceA1831 + difference 0 2) (sourceB1831 + difference 2 0) sourceC1831) = raw26411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1831 sourceB1831 sourceC1831 difference raw26411; decide +kernel
    rw [ha]
    exact (canonical26411 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1831 + difference 0 3) (sourceB1831 + difference 3 0) sourceC1831) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2747) := by
    have ha : (tripleCharges (sourceA1831 + difference 0 3) (sourceB1831 + difference 3 0) sourceC1831) = raw26412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1831 sourceB1831 sourceC1831 difference raw26412; decide +kernel
    rw [ha]
    exact (canonical26412 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1831 + difference 0 4) (sourceB1831 + difference 4 0) sourceC1831) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2747) := by
    have ha : (tripleCharges (sourceA1831 + difference 0 4) (sourceB1831 + difference 4 0) sourceC1831) = raw26413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1831 sourceB1831 sourceC1831 difference raw26413; decide +kernel
    rw [ha]
    exact (canonical26413 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1831 + difference 0 5) (sourceB1831 + difference 5 0) sourceC1831) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA1831 + difference 0 5) (sourceB1831 + difference 5 0) sourceC1831) = raw26414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1831 sourceB1831 sourceC1831 difference raw26414; decide +kernel
    rw [ha]
    exact (canonical26414 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1831 + sourceB1831) sourceC1831) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA1831 + sourceB1831) sourceC1831) = raw26415 := by
      apply Matrix.ext; unfold doubleCharges sourceA1831 sourceB1831 sourceC1831 raw26415; decide +kernel
    rw [ha]
    exact (canonical26415 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1831 sourceB1831 sourceC1831
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1831, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1832 : Charge := ![2, -1, -1, -1, -1, 2]
def sourceB1832 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC1832 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1832 : Integer.Sparse Master := [(Sum.inr 1644, 1), (Sum.inr 3057, 1), (Sum.inr 3289, 3), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

theorem sourceEq1832 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1832 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1832 + difference 0 5) (sourceB1832 + difference 5 0) sourceC1832) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1644) := by
    have ha : (tripleCharges (sourceA1832 + difference 0 5) (sourceB1832 + difference 5 0) sourceC1832) = raw26416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1832 sourceB1832 sourceC1832 difference raw26416; decide +kernel
    rw [ha]
    exact (canonical26416 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1832 + difference 1 5) (sourceB1832 + difference 5 1) sourceC1832) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA1832 + difference 1 5) (sourceB1832 + difference 5 1) sourceC1832) = raw26369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1832 sourceB1832 sourceC1832 difference raw26369; decide +kernel
    rw [ha]
    exact (canonical26369 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1832 + difference 2 5) (sourceB1832 + difference 5 2) sourceC1832) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1832 + difference 2 5) (sourceB1832 + difference 5 2) sourceC1832) = raw26417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1832 sourceB1832 sourceC1832 difference raw26417; decide +kernel
    rw [ha]
    exact (canonical26417 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1832 + difference 3 5) (sourceB1832 + difference 5 3) sourceC1832) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1832 + difference 3 5) (sourceB1832 + difference 5 3) sourceC1832) = raw26418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1832 sourceB1832 sourceC1832 difference raw26418; decide +kernel
    rw [ha]
    exact (canonical26418 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1832 + difference 4 5) (sourceB1832 + difference 5 4) sourceC1832) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1832 + difference 4 5) (sourceB1832 + difference 5 4) sourceC1832) = raw26419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1832 sourceB1832 sourceC1832 difference raw26419; decide +kernel
    rw [ha]
    exact (canonical26419 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1832 + difference 5 5) (sourceB1832 + difference 5 5) sourceC1832) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3057) := by
    have ha : (tripleCharges (sourceA1832 + difference 5 5) (sourceB1832 + difference 5 5) sourceC1832) = raw26365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1832 sourceB1832 sourceC1832 difference raw26365; decide +kernel
    rw [ha]
    exact (canonical26365 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1832 + sourceB1832) sourceC1832) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1832 + sourceB1832) sourceC1832) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1832 sourceB1832 sourceC1832 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1832 sourceB1832 sourceC1832
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1832, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1833 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1833 : Charge := ![2, -1, -1, -1, 0, 1]
def sourceC1833 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceForm1833 : Integer.Sparse Master := [(Sum.inr 1126, 1), (Sum.inr 1127, 1), (Sum.inr 1130, 2), (Sum.inr 1233, 1), (Sum.inr 2508, 1), (Sum.inr 4092, -1)]

theorem sourceEq1833 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1833 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1833 + difference 0 1) (sourceB1833 + difference 1 0) sourceC1833) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA1833 + difference 0 1) (sourceB1833 + difference 1 0) sourceC1833) = raw26420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1833 sourceB1833 sourceC1833 difference raw26420; decide +kernel
    rw [ha]
    exact (canonical26420 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1833 + difference 1 1) (sourceB1833 + difference 1 1) sourceC1833) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA1833 + difference 1 1) (sourceB1833 + difference 1 1) sourceC1833) = raw26421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1833 sourceB1833 sourceC1833 difference raw26421; decide +kernel
    rw [ha]
    exact (canonical26421 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1833 + difference 2 1) (sourceB1833 + difference 1 2) sourceC1833) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1130) := by
    have ha : (tripleCharges (sourceA1833 + difference 2 1) (sourceB1833 + difference 1 2) sourceC1833) = raw26422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1833 sourceB1833 sourceC1833 difference raw26422; decide +kernel
    rw [ha]
    exact (canonical26422 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1833 + difference 3 1) (sourceB1833 + difference 1 3) sourceC1833) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1130) := by
    have ha : (tripleCharges (sourceA1833 + difference 3 1) (sourceB1833 + difference 1 3) sourceC1833) = raw26423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1833 sourceB1833 sourceC1833 difference raw26423; decide +kernel
    rw [ha]
    exact (canonical26423 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1833 + difference 4 1) (sourceB1833 + difference 1 4) sourceC1833) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1127) := by
    have ha : (tripleCharges (sourceA1833 + difference 4 1) (sourceB1833 + difference 1 4) sourceC1833) = raw26424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1833 sourceB1833 sourceC1833 difference raw26424; decide +kernel
    rw [ha]
    exact (canonical26424 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1833 + difference 5 1) (sourceB1833 + difference 1 5) sourceC1833) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1126) := by
    have ha : (tripleCharges (sourceA1833 + difference 5 1) (sourceB1833 + difference 1 5) sourceC1833) = raw26425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1833 sourceB1833 sourceC1833 difference raw26425; decide +kernel
    rw [ha]
    exact (canonical26425 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1833 + sourceB1833) sourceC1833) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1833 + sourceB1833) sourceC1833) = raw19472 := by
      apply Matrix.ext; unfold doubleCharges sourceA1833 sourceB1833 sourceC1833 raw19472; decide +kernel
    rw [ha]
    exact (canonical19472 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1833 sourceB1833 sourceC1833
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1833, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1834 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1834 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1834 : Charge := ![2, -1, -1, -1, 0, 1]
def sourceForm1834 : Integer.Sparse Master := [(Sum.inr 637, 1), (Sum.inr 1235, 1), (Sum.inr 1260, 3), (Sum.inr 1293, 1), (Sum.inr 4091, -1)]

theorem sourceEq1834 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1834 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1834 + difference 1 0) (sourceB1834 + difference 0 1) sourceC1834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 637) := by
    have ha : (tripleCharges (sourceA1834 + difference 1 0) (sourceB1834 + difference 0 1) sourceC1834) = raw26426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1834 sourceB1834 sourceC1834 difference raw26426; decide +kernel
    rw [ha]
    exact (canonical26426 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1834 + difference 1 1) (sourceB1834 + difference 1 1) sourceC1834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA1834 + difference 1 1) (sourceB1834 + difference 1 1) sourceC1834) = raw26427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1834 sourceB1834 sourceC1834 difference raw26427; decide +kernel
    rw [ha]
    exact (canonical26427 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1834 + difference 1 2) (sourceB1834 + difference 2 1) sourceC1834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA1834 + difference 1 2) (sourceB1834 + difference 2 1) sourceC1834) = raw26428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1834 sourceB1834 sourceC1834 difference raw26428; decide +kernel
    rw [ha]
    exact (canonical26428 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1834 + difference 1 3) (sourceB1834 + difference 3 1) sourceC1834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA1834 + difference 1 3) (sourceB1834 + difference 3 1) sourceC1834) = raw26429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1834 sourceB1834 sourceC1834 difference raw26429; decide +kernel
    rw [ha]
    exact (canonical26429 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1834 + difference 1 4) (sourceB1834 + difference 4 1) sourceC1834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA1834 + difference 1 4) (sourceB1834 + difference 4 1) sourceC1834) = raw26430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1834 sourceB1834 sourceC1834 difference raw26430; decide +kernel
    rw [ha]
    exact (canonical26430 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1834 + difference 1 5) (sourceB1834 + difference 5 1) sourceC1834) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA1834 + difference 1 5) (sourceB1834 + difference 5 1) sourceC1834) = raw26431 := by
      apply Matrix.ext; unfold tripleCharges sourceA1834 sourceB1834 sourceC1834 difference raw26431; decide +kernel
    rw [ha]
    exact (canonical26431 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1834 + sourceB1834) sourceC1834) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1834 + sourceB1834) sourceC1834) = raw26432 := by
      apply Matrix.ext; unfold doubleCharges sourceA1834 sourceB1834 sourceC1834 raw26432; decide +kernel
    rw [ha]
    exact (canonical26432 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1834 sourceB1834 sourceC1834
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1834, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1835 : Charge := ![2, -1, -1, -1, 0, 1]
def sourceB1835 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1835 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1835 : Integer.Sparse Master := [(Sum.inr 1636, 2), (Sum.inr 1638, 1), (Sum.inr 1644, 1), (Sum.inr 1706, 1), (Sum.inr 3289, 1), (Sum.inr 4068, -1)]

theorem sourceEq1835 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1835 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1835 + difference 0 0) (sourceB1835 + difference 0 0) sourceC1835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1835 + difference 0 0) (sourceB1835 + difference 0 0) sourceC1835) = raw26419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1835 sourceB1835 sourceC1835 difference raw26419; decide +kernel
    rw [ha]
    exact (canonical26419 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1835 + difference 0 1) (sourceB1835 + difference 1 0) sourceC1835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1638) := by
    have ha : (tripleCharges (sourceA1835 + difference 0 1) (sourceB1835 + difference 1 0) sourceC1835) = raw26433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1835 sourceB1835 sourceC1835 difference raw26433; decide +kernel
    rw [ha]
    exact (canonical26433 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1835 + difference 0 2) (sourceB1835 + difference 2 0) sourceC1835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1636) := by
    have ha : (tripleCharges (sourceA1835 + difference 0 2) (sourceB1835 + difference 2 0) sourceC1835) = raw26434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1835 sourceB1835 sourceC1835 difference raw26434; decide +kernel
    rw [ha]
    exact (canonical26434 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1835 + difference 0 3) (sourceB1835 + difference 3 0) sourceC1835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1636) := by
    have ha : (tripleCharges (sourceA1835 + difference 0 3) (sourceB1835 + difference 3 0) sourceC1835) = raw26435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1835 sourceB1835 sourceC1835 difference raw26435; decide +kernel
    rw [ha]
    exact (canonical26435 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1835 + difference 0 4) (sourceB1835 + difference 4 0) sourceC1835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1644) := by
    have ha : (tripleCharges (sourceA1835 + difference 0 4) (sourceB1835 + difference 4 0) sourceC1835) = raw26416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1835 sourceB1835 sourceC1835 difference raw26416; decide +kernel
    rw [ha]
    exact (canonical26416 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1835 + difference 0 5) (sourceB1835 + difference 5 0) sourceC1835) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1835 + difference 0 5) (sourceB1835 + difference 5 0) sourceC1835) = raw26436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1835 sourceB1835 sourceC1835 difference raw26436; decide +kernel
    rw [ha]
    exact (canonical26436 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1835 + sourceB1835) sourceC1835) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1835 + sourceB1835) sourceC1835) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1835 sourceB1835 sourceC1835 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1835 sourceB1835 sourceC1835
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1835, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1836 : Charge := ![2, -1, -1, -1, 0, 1]
def sourceB1836 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1836 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1836 : Integer.Sparse Master := [(Sum.inr 1593, 1), (Sum.inr 1595, 1), (Sum.inr 1600, 2), (Sum.inr 1708, 1), (Sum.inr 3289, 1), (Sum.inr 4068, -1)]

theorem sourceEq1836 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1836 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1836 + difference 0 0) (sourceB1836 + difference 0 0) sourceC1836) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1836 + difference 0 0) (sourceB1836 + difference 0 0) sourceC1836) = raw26419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1836 sourceB1836 sourceC1836 difference raw26419; decide +kernel
    rw [ha]
    exact (canonical26419 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1836 + difference 1 0) (sourceB1836 + difference 0 1) sourceC1836) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1836 + difference 1 0) (sourceB1836 + difference 0 1) sourceC1836) = raw26374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1836 sourceB1836 sourceC1836 difference raw26374; decide +kernel
    rw [ha]
    exact (canonical26374 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1836 + difference 2 0) (sourceB1836 + difference 0 2) sourceC1836) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1600) := by
    have ha : (tripleCharges (sourceA1836 + difference 2 0) (sourceB1836 + difference 0 2) sourceC1836) = raw26437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1836 sourceB1836 sourceC1836 difference raw26437; decide +kernel
    rw [ha]
    exact (canonical26437 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1836 + difference 3 0) (sourceB1836 + difference 0 3) sourceC1836) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1600) := by
    have ha : (tripleCharges (sourceA1836 + difference 3 0) (sourceB1836 + difference 0 3) sourceC1836) = raw26438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1836 sourceB1836 sourceC1836 difference raw26438; decide +kernel
    rw [ha]
    exact (canonical26438 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1836 + difference 4 0) (sourceB1836 + difference 0 4) sourceC1836) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1595) := by
    have ha : (tripleCharges (sourceA1836 + difference 4 0) (sourceB1836 + difference 0 4) sourceC1836) = raw26439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1836 sourceB1836 sourceC1836 difference raw26439; decide +kernel
    rw [ha]
    exact (canonical26439 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1836 + difference 5 0) (sourceB1836 + difference 0 5) sourceC1836) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1593) := by
    have ha : (tripleCharges (sourceA1836 + difference 5 0) (sourceB1836 + difference 0 5) sourceC1836) = raw26440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1836 sourceB1836 sourceC1836 difference raw26440; decide +kernel
    rw [ha]
    exact (canonical26440 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1836 + sourceB1836) sourceC1836) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1836 + sourceB1836) sourceC1836) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1836 sourceB1836 sourceC1836 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1836 sourceB1836 sourceC1836
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1836, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1837 : Charge := ![2, -1, -1, -1, 0, 1]
def sourceB1837 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1837 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1837 : Integer.Sparse Master := [(Sum.inr 1708, 1), (Sum.inr 3289, 1), (Sum.inr 3303, 2), (Sum.inr 3304, 1), (Sum.inr 3307, 1), (Sum.inr 4068, -1)]

theorem sourceEq1837 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1837 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1837 + difference 1 0) (sourceB1837 + difference 0 1) sourceC1837) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1837 + difference 1 0) (sourceB1837 + difference 0 1) sourceC1837) = raw26374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1837 sourceB1837 sourceC1837 difference raw26374; decide +kernel
    rw [ha]
    exact (canonical26374 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1837 + difference 1 1) (sourceB1837 + difference 1 1) sourceC1837) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1837 + difference 1 1) (sourceB1837 + difference 1 1) sourceC1837) = raw26419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1837 sourceB1837 sourceC1837 difference raw26419; decide +kernel
    rw [ha]
    exact (canonical26419 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1837 + difference 1 2) (sourceB1837 + difference 2 1) sourceC1837) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA1837 + difference 1 2) (sourceB1837 + difference 2 1) sourceC1837) = raw26441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1837 sourceB1837 sourceC1837 difference raw26441; decide +kernel
    rw [ha]
    exact (canonical26441 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1837 + difference 1 3) (sourceB1837 + difference 3 1) sourceC1837) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA1837 + difference 1 3) (sourceB1837 + difference 3 1) sourceC1837) = raw26442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1837 sourceB1837 sourceC1837 difference raw26442; decide +kernel
    rw [ha]
    exact (canonical26442 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1837 + difference 1 4) (sourceB1837 + difference 4 1) sourceC1837) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA1837 + difference 1 4) (sourceB1837 + difference 4 1) sourceC1837) = raw26369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1837 sourceB1837 sourceC1837 difference raw26369; decide +kernel
    rw [ha]
    exact (canonical26369 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1837 + difference 1 5) (sourceB1837 + difference 5 1) sourceC1837) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3307) := by
    have ha : (tripleCharges (sourceA1837 + difference 1 5) (sourceB1837 + difference 5 1) sourceC1837) = raw26443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1837 sourceB1837 sourceC1837 difference raw26443; decide +kernel
    rw [ha]
    exact (canonical26443 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1837 + sourceB1837) sourceC1837) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1837 + sourceB1837) sourceC1837) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1837 sourceB1837 sourceC1837 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1837 sourceB1837 sourceC1837
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1837, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1838 : Charge := ![2, -1, -1, -1, 0, 1]
def sourceB1838 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1838 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1838 : Integer.Sparse Master := [(Sum.inr 1600, 1), (Sum.inr 3239, 1), (Sum.inr 3286, 1), (Sum.inr 3289, 2), (Sum.inr 3292, 1), (Sum.inr 4068, -1)]

theorem sourceEq1838 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1838 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1838 + difference 2 0) (sourceB1838 + difference 0 2) sourceC1838) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1600) := by
    have ha : (tripleCharges (sourceA1838 + difference 2 0) (sourceB1838 + difference 0 2) sourceC1838) = raw26437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1838 sourceB1838 sourceC1838 difference raw26437; decide +kernel
    rw [ha]
    exact (canonical26437 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1838 + difference 2 1) (sourceB1838 + difference 1 2) sourceC1838) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3239) := by
    have ha : (tripleCharges (sourceA1838 + difference 2 1) (sourceB1838 + difference 1 2) sourceC1838) = raw26444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1838 sourceB1838 sourceC1838 difference raw26444; decide +kernel
    rw [ha]
    exact (canonical26444 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1838 + difference 2 2) (sourceB1838 + difference 2 2) sourceC1838) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1838 + difference 2 2) (sourceB1838 + difference 2 2) sourceC1838) = raw26419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1838 sourceB1838 sourceC1838 difference raw26419; decide +kernel
    rw [ha]
    exact (canonical26419 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1838 + difference 2 3) (sourceB1838 + difference 3 2) sourceC1838) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3286) := by
    have ha : (tripleCharges (sourceA1838 + difference 2 3) (sourceB1838 + difference 3 2) sourceC1838) = raw26445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1838 sourceB1838 sourceC1838 difference raw26445; decide +kernel
    rw [ha]
    exact (canonical26445 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1838 + difference 2 4) (sourceB1838 + difference 4 2) sourceC1838) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1838 + difference 2 4) (sourceB1838 + difference 4 2) sourceC1838) = raw26417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1838 sourceB1838 sourceC1838 difference raw26417; decide +kernel
    rw [ha]
    exact (canonical26417 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1838 + difference 2 5) (sourceB1838 + difference 5 2) sourceC1838) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3292) := by
    have ha : (tripleCharges (sourceA1838 + difference 2 5) (sourceB1838 + difference 5 2) sourceC1838) = raw26446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1838 sourceB1838 sourceC1838 difference raw26446; decide +kernel
    rw [ha]
    exact (canonical26446 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1838 + sourceB1838) sourceC1838) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1838 + sourceB1838) sourceC1838) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1838 sourceB1838 sourceC1838 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1838 sourceB1838 sourceC1838
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1838, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1839 : Charge := ![2, -1, -1, -1, 0, 1]
def sourceB1839 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC1839 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1839 : Integer.Sparse Master := [(Sum.inr 1706, 1), (Sum.inr 3289, 2), (Sum.inr 3292, 2), (Sum.inr 3307, 1), (Sum.inr 4068, -1)]

theorem sourceEq1839 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1839 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1839 + difference 0 5) (sourceB1839 + difference 5 0) sourceC1839) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1706) := by
    have ha : (tripleCharges (sourceA1839 + difference 0 5) (sourceB1839 + difference 5 0) sourceC1839) = raw26436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1839 sourceB1839 sourceC1839 difference raw26436; decide +kernel
    rw [ha]
    exact (canonical26436 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1839 + difference 1 5) (sourceB1839 + difference 5 1) sourceC1839) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3307) := by
    have ha : (tripleCharges (sourceA1839 + difference 1 5) (sourceB1839 + difference 5 1) sourceC1839) = raw26443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1839 sourceB1839 sourceC1839 difference raw26443; decide +kernel
    rw [ha]
    exact (canonical26443 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1839 + difference 2 5) (sourceB1839 + difference 5 2) sourceC1839) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3292) := by
    have ha : (tripleCharges (sourceA1839 + difference 2 5) (sourceB1839 + difference 5 2) sourceC1839) = raw26446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1839 sourceB1839 sourceC1839 difference raw26446; decide +kernel
    rw [ha]
    exact (canonical26446 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1839 + difference 3 5) (sourceB1839 + difference 5 3) sourceC1839) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3292) := by
    have ha : (tripleCharges (sourceA1839 + difference 3 5) (sourceB1839 + difference 5 3) sourceC1839) = raw26447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1839 sourceB1839 sourceC1839 difference raw26447; decide +kernel
    rw [ha]
    exact (canonical26447 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1839 + difference 4 5) (sourceB1839 + difference 5 4) sourceC1839) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1839 + difference 4 5) (sourceB1839 + difference 5 4) sourceC1839) = raw26448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1839 sourceB1839 sourceC1839 difference raw26448; decide +kernel
    rw [ha]
    exact (canonical26448 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1839 + difference 5 5) (sourceB1839 + difference 5 5) sourceC1839) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1839 + difference 5 5) (sourceB1839 + difference 5 5) sourceC1839) = raw26419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1839 sourceB1839 sourceC1839 difference raw26419; decide +kernel
    rw [ha]
    exact (canonical26419 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1839 + sourceB1839) sourceC1839) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1839 + sourceB1839) sourceC1839) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1839 sourceB1839 sourceC1839 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1839 sourceB1839 sourceC1839
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1839, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1840 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1840 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceC1840 : Charge := ![2, 0, -2, -1, -1, 2]
def sourceForm1840 : Integer.Sparse Master := [(Sum.inr 1286, 1), (Sum.inr 2583, 1), (Sum.inr 2684, 1), (Sum.inr 2748, 1), (Sum.inr 2760, 2), (Sum.inr 4088, -1)]

theorem sourceEq1840 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1840 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1840 + difference 0 0) (sourceB1840 + difference 0 0) sourceC1840) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1286) := by
    have ha : (tripleCharges (sourceA1840 + difference 0 0) (sourceB1840 + difference 0 0) sourceC1840) = raw26449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1840 sourceB1840 sourceC1840 difference raw26449; decide +kernel
    rw [ha]
    exact (canonical26449 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1840 + difference 0 1) (sourceB1840 + difference 1 0) sourceC1840) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2583) := by
    have ha : (tripleCharges (sourceA1840 + difference 0 1) (sourceB1840 + difference 1 0) sourceC1840) = raw26450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1840 sourceB1840 sourceC1840 difference raw26450; decide +kernel
    rw [ha]
    exact (canonical26450 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1840 + difference 0 2) (sourceB1840 + difference 2 0) sourceC1840) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2748) := by
    have ha : (tripleCharges (sourceA1840 + difference 0 2) (sourceB1840 + difference 2 0) sourceC1840) = raw26451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1840 sourceB1840 sourceC1840 difference raw26451; decide +kernel
    rw [ha]
    exact (canonical26451 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1840 + difference 0 3) (sourceB1840 + difference 3 0) sourceC1840) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2760) := by
    have ha : (tripleCharges (sourceA1840 + difference 0 3) (sourceB1840 + difference 3 0) sourceC1840) = raw26452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1840 sourceB1840 sourceC1840 difference raw26452; decide +kernel
    rw [ha]
    exact (canonical26452 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1840 + difference 0 4) (sourceB1840 + difference 4 0) sourceC1840) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2760) := by
    have ha : (tripleCharges (sourceA1840 + difference 0 4) (sourceB1840 + difference 4 0) sourceC1840) = raw26453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1840 sourceB1840 sourceC1840 difference raw26453; decide +kernel
    rw [ha]
    exact (canonical26453 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1840 + difference 0 5) (sourceB1840 + difference 5 0) sourceC1840) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2684) := by
    have ha : (tripleCharges (sourceA1840 + difference 0 5) (sourceB1840 + difference 5 0) sourceC1840) = raw26454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1840 sourceB1840 sourceC1840 difference raw26454; decide +kernel
    rw [ha]
    exact (canonical26454 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1840 + sourceB1840) sourceC1840) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1840 + sourceB1840) sourceC1840) = raw26455 := by
      apply Matrix.ext; unfold doubleCharges sourceA1840 sourceB1840 sourceC1840 raw26455; decide +kernel
    rw [ha]
    exact (canonical26455 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1840 sourceB1840 sourceC1840
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1840, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1841 : Charge := ![2, 0, -2, -1, -1, 2]
def sourceB1841 : Charge := ![2, 0, 1, 0, 0, -3]
def sourceC1841 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1841 : Integer.Sparse Master := [(Sum.inr 1648, 1), (Sum.inr 3072, 1), (Sum.inr 3286, 1), (Sum.inr 3303, 2), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

theorem sourceEq1841 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1841 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1841 + difference 0 5) (sourceB1841 + difference 5 0) sourceC1841) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1648) := by
    have ha : (tripleCharges (sourceA1841 + difference 0 5) (sourceB1841 + difference 5 0) sourceC1841) = raw26456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1841 sourceB1841 sourceC1841 difference raw26456; decide +kernel
    rw [ha]
    exact (canonical26456 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1841 + difference 1 5) (sourceB1841 + difference 5 1) sourceC1841) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3286) := by
    have ha : (tripleCharges (sourceA1841 + difference 1 5) (sourceB1841 + difference 5 1) sourceC1841) = raw26379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1841 sourceB1841 sourceC1841 difference raw26379; decide +kernel
    rw [ha]
    exact (canonical26379 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1841 + difference 2 5) (sourceB1841 + difference 5 2) sourceC1841) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA1841 + difference 2 5) (sourceB1841 + difference 5 2) sourceC1841) = raw26369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1841 sourceB1841 sourceC1841 difference raw26369; decide +kernel
    rw [ha]
    exact (canonical26369 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1841 + difference 3 5) (sourceB1841 + difference 5 3) sourceC1841) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA1841 + difference 3 5) (sourceB1841 + difference 5 3) sourceC1841) = raw26457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1841 sourceB1841 sourceC1841 difference raw26457; decide +kernel
    rw [ha]
    exact (canonical26457 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1841 + difference 4 5) (sourceB1841 + difference 5 4) sourceC1841) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA1841 + difference 4 5) (sourceB1841 + difference 5 4) sourceC1841) = raw26441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1841 sourceB1841 sourceC1841 difference raw26441; decide +kernel
    rw [ha]
    exact (canonical26441 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1841 + difference 5 5) (sourceB1841 + difference 5 5) sourceC1841) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3072) := by
    have ha : (tripleCharges (sourceA1841 + difference 5 5) (sourceB1841 + difference 5 5) sourceC1841) = raw26366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1841 sourceB1841 sourceC1841 difference raw26366; decide +kernel
    rw [ha]
    exact (canonical26366 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1841 + sourceB1841) sourceC1841) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1841 + sourceB1841) sourceC1841) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1841 sourceB1841 sourceC1841 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1841 sourceB1841 sourceC1841
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1841, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1842 : Charge := ![2, 0, -2, -1, 0, 1]
def sourceB1842 : Charge := ![2, 0, 1, 0, -1, -2]
def sourceC1842 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1842 : Integer.Sparse Master := [(Sum.inr 1636, 1), (Sum.inr 1639, 1), (Sum.inr 1641, 1), (Sum.inr 1648, 1), (Sum.inr 1708, 1), (Sum.inr 3303, 1), (Sum.inr 4068, -1)]

theorem sourceEq1842 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1842 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1842 + difference 0 0) (sourceB1842 + difference 0 0) sourceC1842) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA1842 + difference 0 0) (sourceB1842 + difference 0 0) sourceC1842) = raw26441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1842 sourceB1842 sourceC1842 difference raw26441; decide +kernel
    rw [ha]
    exact (canonical26441 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1842 + difference 0 1) (sourceB1842 + difference 1 0) sourceC1842) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1636) := by
    have ha : (tripleCharges (sourceA1842 + difference 0 1) (sourceB1842 + difference 1 0) sourceC1842) = raw26434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1842 sourceB1842 sourceC1842 difference raw26434; decide +kernel
    rw [ha]
    exact (canonical26434 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1842 + difference 0 2) (sourceB1842 + difference 2 0) sourceC1842) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1639) := by
    have ha : (tripleCharges (sourceA1842 + difference 0 2) (sourceB1842 + difference 2 0) sourceC1842) = raw26458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1842 sourceB1842 sourceC1842 difference raw26458; decide +kernel
    rw [ha]
    exact (canonical26458 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1842 + difference 0 3) (sourceB1842 + difference 3 0) sourceC1842) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1641) := by
    have ha : (tripleCharges (sourceA1842 + difference 0 3) (sourceB1842 + difference 3 0) sourceC1842) = raw26459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1842 sourceB1842 sourceC1842 difference raw26459; decide +kernel
    rw [ha]
    exact (canonical26459 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1842 + difference 0 4) (sourceB1842 + difference 4 0) sourceC1842) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1648) := by
    have ha : (tripleCharges (sourceA1842 + difference 0 4) (sourceB1842 + difference 4 0) sourceC1842) = raw26456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1842 sourceB1842 sourceC1842 difference raw26456; decide +kernel
    rw [ha]
    exact (canonical26456 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1842 + difference 0 5) (sourceB1842 + difference 5 0) sourceC1842) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1842 + difference 0 5) (sourceB1842 + difference 5 0) sourceC1842) = raw26460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1842 sourceB1842 sourceC1842 difference raw26460; decide +kernel
    rw [ha]
    exact (canonical26460 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1842 + sourceB1842) sourceC1842) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1842 + sourceB1842) sourceC1842) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1842 sourceB1842 sourceC1842 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1842 sourceB1842 sourceC1842
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1842, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1843 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1843 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC1843 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm1843 : Integer.Sparse Master := [(Sum.inr 4164, 1), (Sum.inr 4165, 3), (Sum.inr 4182, 1), (Sum.inr 4537, 3), (Sum.inr 4550, 1), (Sum.inr 4569, 1), (Sum.inr 4570, 3), (Sum.inr 4618, 3), (Sum.inr 4619, 6), (Sum.inr 4623, 3), (Sum.inr 5166, 1), (Sum.inr 5301, 1), (Sum.inr 5306, 3)]

theorem sourceEq1843 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1843 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1843 + difference 0 1) (sourceB1843 + difference 1 0) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5166) := by
    have ha : (tripleCharges (sourceA1843 + difference 0 1) (sourceB1843 + difference 1 0) sourceC1843) = raw12089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw12089; decide +kernel
    rw [ha]
    exact (canonical12089 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1843 + difference 0 2) (sourceB1843 + difference 2 0) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA1843 + difference 0 2) (sourceB1843 + difference 2 0) sourceC1843) = raw10231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw10231; decide +kernel
    rw [ha]
    exact (canonical10231 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1843 + difference 0 3) (sourceB1843 + difference 3 0) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA1843 + difference 0 3) (sourceB1843 + difference 3 0) sourceC1843) = raw10227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw10227; decide +kernel
    rw [ha]
    exact (canonical10227 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1843 + difference 0 4) (sourceB1843 + difference 4 0) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA1843 + difference 0 4) (sourceB1843 + difference 4 0) sourceC1843) = raw12090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw12090; decide +kernel
    rw [ha]
    exact (canonical12090 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1843 + difference 0 5) (sourceB1843 + difference 5 0) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA1843 + difference 0 5) (sourceB1843 + difference 5 0) sourceC1843) = raw12091 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw12091; decide +kernel
    rw [ha]
    exact (canonical12091 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1843 + difference 1 0) (sourceB1843 + difference 0 1) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4164) := by
    have ha : (tripleCharges (sourceA1843 + difference 1 0) (sourceB1843 + difference 0 1) sourceC1843) = raw26461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw26461; decide +kernel
    rw [ha]
    exact (canonical26461 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1843 + difference 1 2) (sourceB1843 + difference 2 1) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1843 + difference 1 2) (sourceB1843 + difference 2 1) sourceC1843) = raw12084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw12084; decide +kernel
    rw [ha]
    exact (canonical12084 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1843 + difference 1 3) (sourceB1843 + difference 3 1) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1843 + difference 1 3) (sourceB1843 + difference 3 1) sourceC1843) = raw26462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw26462; decide +kernel
    rw [ha]
    exact (canonical26462 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1843 + difference 1 4) (sourceB1843 + difference 4 1) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1843 + difference 1 4) (sourceB1843 + difference 4 1) sourceC1843) = raw26463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw26463; decide +kernel
    rw [ha]
    exact (canonical26463 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1843 + difference 1 5) (sourceB1843 + difference 5 1) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4569) := by
    have ha : (tripleCharges (sourceA1843 + difference 1 5) (sourceB1843 + difference 5 1) sourceC1843) = raw26464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw26464; decide +kernel
    rw [ha]
    exact (canonical26464 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1843 + difference 2 0) (sourceB1843 + difference 0 2) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4165) := by
    have ha : (tripleCharges (sourceA1843 + difference 2 0) (sourceB1843 + difference 0 2) sourceC1843) = raw26465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw26465; decide +kernel
    rw [ha]
    exact (canonical26465 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1843 + difference 2 1) (sourceB1843 + difference 1 2) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4537) := by
    have ha : (tripleCharges (sourceA1843 + difference 2 1) (sourceB1843 + difference 1 2) sourceC1843) = raw26466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw26466; decide +kernel
    rw [ha]
    exact (canonical26466 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1843 + difference 2 3) (sourceB1843 + difference 3 2) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1843 + difference 2 3) (sourceB1843 + difference 3 2) sourceC1843) = raw26467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw26467; decide +kernel
    rw [ha]
    exact (canonical26467 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1843 + difference 2 4) (sourceB1843 + difference 4 2) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1843 + difference 2 4) (sourceB1843 + difference 4 2) sourceC1843) = raw26468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw26468; decide +kernel
    rw [ha]
    exact (canonical26468 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1843 + difference 2 5) (sourceB1843 + difference 5 2) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4570) := by
    have ha : (tripleCharges (sourceA1843 + difference 2 5) (sourceB1843 + difference 5 2) sourceC1843) = raw26469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw26469; decide +kernel
    rw [ha]
    exact (canonical26469 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1843 + difference 3 0) (sourceB1843 + difference 0 3) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4165) := by
    have ha : (tripleCharges (sourceA1843 + difference 3 0) (sourceB1843 + difference 0 3) sourceC1843) = raw26470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw26470; decide +kernel
    rw [ha]
    exact (canonical26470 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1843 + difference 3 1) (sourceB1843 + difference 1 3) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4537) := by
    have ha : (tripleCharges (sourceA1843 + difference 3 1) (sourceB1843 + difference 1 3) sourceC1843) = raw26471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw26471; decide +kernel
    rw [ha]
    exact (canonical26471 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1843 + difference 3 2) (sourceB1843 + difference 2 3) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1843 + difference 3 2) (sourceB1843 + difference 2 3) sourceC1843) = raw12092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw12092; decide +kernel
    rw [ha]
    exact (canonical12092 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1843 + difference 3 4) (sourceB1843 + difference 4 3) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1843 + difference 3 4) (sourceB1843 + difference 4 3) sourceC1843) = raw26472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw26472; decide +kernel
    rw [ha]
    exact (canonical26472 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1843 + difference 3 5) (sourceB1843 + difference 5 3) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4570) := by
    have ha : (tripleCharges (sourceA1843 + difference 3 5) (sourceB1843 + difference 5 3) sourceC1843) = raw26473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw26473; decide +kernel
    rw [ha]
    exact (canonical26473 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1843 + difference 4 0) (sourceB1843 + difference 0 4) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4165) := by
    have ha : (tripleCharges (sourceA1843 + difference 4 0) (sourceB1843 + difference 0 4) sourceC1843) = raw26474 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw26474; decide +kernel
    rw [ha]
    exact (canonical26474 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1843 + difference 4 1) (sourceB1843 + difference 1 4) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4537) := by
    have ha : (tripleCharges (sourceA1843 + difference 4 1) (sourceB1843 + difference 1 4) sourceC1843) = raw26475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw26475; decide +kernel
    rw [ha]
    exact (canonical26475 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1843 + difference 4 2) (sourceB1843 + difference 2 4) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1843 + difference 4 2) (sourceB1843 + difference 2 4) sourceC1843) = raw12097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw12097; decide +kernel
    rw [ha]
    exact (canonical12097 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1843 + difference 4 3) (sourceB1843 + difference 3 4) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA1843 + difference 4 3) (sourceB1843 + difference 3 4) sourceC1843) = raw22478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw22478; decide +kernel
    rw [ha]
    exact (canonical22478 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1843 + difference 4 5) (sourceB1843 + difference 5 4) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4570) := by
    have ha : (tripleCharges (sourceA1843 + difference 4 5) (sourceB1843 + difference 5 4) sourceC1843) = raw26476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw26476; decide +kernel
    rw [ha]
    exact (canonical26476 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1843 + difference 5 0) (sourceB1843 + difference 0 5) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4182) := by
    have ha : (tripleCharges (sourceA1843 + difference 5 0) (sourceB1843 + difference 0 5) sourceC1843) = raw24104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw24104; decide +kernel
    rw [ha]
    exact (canonical24104 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1843 + difference 5 1) (sourceB1843 + difference 1 5) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4550) := by
    have ha : (tripleCharges (sourceA1843 + difference 5 1) (sourceB1843 + difference 1 5) sourceC1843) = raw24105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw24105; decide +kernel
    rw [ha]
    exact (canonical24105 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1843 + difference 5 2) (sourceB1843 + difference 2 5) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1843 + difference 5 2) (sourceB1843 + difference 2 5) sourceC1843) = raw10228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw10228; decide +kernel
    rw [ha]
    exact (canonical10228 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1843 + difference 5 3) (sourceB1843 + difference 3 5) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1843 + difference 5 3) (sourceB1843 + difference 3 5) sourceC1843) = raw10224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw10224; decide +kernel
    rw [ha]
    exact (canonical10224 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1843 + difference 5 4) (sourceB1843 + difference 4 5) sourceC1843) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1843 + difference 5 4) (sourceB1843 + difference 4 5) sourceC1843) = raw24106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1843 sourceB1843 sourceC1843 difference raw24106; decide +kernel
    rw [ha]
    exact (canonical24106 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1843 sourceB1843 sourceC1843
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1843, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1844 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1844 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceC1844 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceForm1844 : Integer.Sparse Master := [(Sum.inr 592, 1), (Sum.inr 593, 3), (Sum.inr 610, 1), (Sum.inr 1122, 3), (Sum.inr 1135, 1), (Sum.inr 1187, 1), (Sum.inr 1188, 3), (Sum.inr 1293, 3), (Sum.inr 1294, 6), (Sum.inr 1305, 3), (Sum.inr 2953, 1), (Sum.inr 3053, 1), (Sum.inr 3120, 3)]

theorem sourceEq1844 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1844 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1844 + difference 0 1) (sourceB1844 + difference 1 0) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2953) := by
    have ha : (tripleCharges (sourceA1844 + difference 0 1) (sourceB1844 + difference 1 0) sourceC1844) = raw12112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw12112; decide +kernel
    rw [ha]
    exact (canonical12112 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1844 + difference 0 2) (sourceB1844 + difference 2 0) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA1844 + difference 0 2) (sourceB1844 + difference 2 0) sourceC1844) = raw24111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw24111; decide +kernel
    rw [ha]
    exact (canonical24111 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1844 + difference 0 3) (sourceB1844 + difference 3 0) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA1844 + difference 0 3) (sourceB1844 + difference 3 0) sourceC1844) = raw12113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw12113; decide +kernel
    rw [ha]
    exact (canonical12113 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1844 + difference 0 4) (sourceB1844 + difference 4 0) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA1844 + difference 0 4) (sourceB1844 + difference 4 0) sourceC1844) = raw12114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw12114; decide +kernel
    rw [ha]
    exact (canonical12114 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1844 + difference 0 5) (sourceB1844 + difference 5 0) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA1844 + difference 0 5) (sourceB1844 + difference 5 0) sourceC1844) = raw12115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw12115; decide +kernel
    rw [ha]
    exact (canonical12115 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1844 + difference 1 0) (sourceB1844 + difference 0 1) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 592) := by
    have ha : (tripleCharges (sourceA1844 + difference 1 0) (sourceB1844 + difference 0 1) sourceC1844) = raw26477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw26477; decide +kernel
    rw [ha]
    exact (canonical26477 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1844 + difference 1 2) (sourceB1844 + difference 2 1) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA1844 + difference 1 2) (sourceB1844 + difference 2 1) sourceC1844) = raw12106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw12106; decide +kernel
    rw [ha]
    exact (canonical12106 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1844 + difference 1 3) (sourceB1844 + difference 3 1) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA1844 + difference 1 3) (sourceB1844 + difference 3 1) sourceC1844) = raw26478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw26478; decide +kernel
    rw [ha]
    exact (canonical26478 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1844 + difference 1 4) (sourceB1844 + difference 4 1) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA1844 + difference 1 4) (sourceB1844 + difference 4 1) sourceC1844) = raw26479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw26479; decide +kernel
    rw [ha]
    exact (canonical26479 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1844 + difference 1 5) (sourceB1844 + difference 5 1) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1187) := by
    have ha : (tripleCharges (sourceA1844 + difference 1 5) (sourceB1844 + difference 5 1) sourceC1844) = raw26480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw26480; decide +kernel
    rw [ha]
    exact (canonical26480 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1844 + difference 2 0) (sourceB1844 + difference 0 2) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 593) := by
    have ha : (tripleCharges (sourceA1844 + difference 2 0) (sourceB1844 + difference 0 2) sourceC1844) = raw26481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw26481; decide +kernel
    rw [ha]
    exact (canonical26481 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1844 + difference 2 1) (sourceB1844 + difference 1 2) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1122) := by
    have ha : (tripleCharges (sourceA1844 + difference 2 1) (sourceB1844 + difference 1 2) sourceC1844) = raw26482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw26482; decide +kernel
    rw [ha]
    exact (canonical26482 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1844 + difference 2 3) (sourceB1844 + difference 3 2) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1844 + difference 2 3) (sourceB1844 + difference 3 2) sourceC1844) = raw26483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw26483; decide +kernel
    rw [ha]
    exact (canonical26483 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1844 + difference 2 4) (sourceB1844 + difference 4 2) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1844 + difference 2 4) (sourceB1844 + difference 4 2) sourceC1844) = raw26484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw26484; decide +kernel
    rw [ha]
    exact (canonical26484 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1844 + difference 2 5) (sourceB1844 + difference 5 2) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1188) := by
    have ha : (tripleCharges (sourceA1844 + difference 2 5) (sourceB1844 + difference 5 2) sourceC1844) = raw26485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw26485; decide +kernel
    rw [ha]
    exact (canonical26485 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1844 + difference 3 0) (sourceB1844 + difference 0 3) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 593) := by
    have ha : (tripleCharges (sourceA1844 + difference 3 0) (sourceB1844 + difference 0 3) sourceC1844) = raw26486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw26486; decide +kernel
    rw [ha]
    exact (canonical26486 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1844 + difference 3 1) (sourceB1844 + difference 1 3) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1122) := by
    have ha : (tripleCharges (sourceA1844 + difference 3 1) (sourceB1844 + difference 1 3) sourceC1844) = raw26487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw26487; decide +kernel
    rw [ha]
    exact (canonical26487 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1844 + difference 3 2) (sourceB1844 + difference 2 3) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1844 + difference 3 2) (sourceB1844 + difference 2 3) sourceC1844) = raw12116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw12116; decide +kernel
    rw [ha]
    exact (canonical12116 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1844 + difference 3 4) (sourceB1844 + difference 4 3) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1844 + difference 3 4) (sourceB1844 + difference 4 3) sourceC1844) = raw26488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw26488; decide +kernel
    rw [ha]
    exact (canonical26488 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1844 + difference 3 5) (sourceB1844 + difference 5 3) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1188) := by
    have ha : (tripleCharges (sourceA1844 + difference 3 5) (sourceB1844 + difference 5 3) sourceC1844) = raw26489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw26489; decide +kernel
    rw [ha]
    exact (canonical26489 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1844 + difference 4 0) (sourceB1844 + difference 0 4) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 593) := by
    have ha : (tripleCharges (sourceA1844 + difference 4 0) (sourceB1844 + difference 0 4) sourceC1844) = raw26490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw26490; decide +kernel
    rw [ha]
    exact (canonical26490 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1844 + difference 4 1) (sourceB1844 + difference 1 4) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1122) := by
    have ha : (tripleCharges (sourceA1844 + difference 4 1) (sourceB1844 + difference 1 4) sourceC1844) = raw26491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw26491; decide +kernel
    rw [ha]
    exact (canonical26491 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1844 + difference 4 2) (sourceB1844 + difference 2 4) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1844 + difference 4 2) (sourceB1844 + difference 2 4) sourceC1844) = raw12121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw12121; decide +kernel
    rw [ha]
    exact (canonical12121 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1844 + difference 4 3) (sourceB1844 + difference 3 4) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1844 + difference 4 3) (sourceB1844 + difference 3 4) sourceC1844) = raw22497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw22497; decide +kernel
    rw [ha]
    exact (canonical22497 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1844 + difference 4 5) (sourceB1844 + difference 5 4) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1188) := by
    have ha : (tripleCharges (sourceA1844 + difference 4 5) (sourceB1844 + difference 5 4) sourceC1844) = raw26492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw26492; decide +kernel
    rw [ha]
    exact (canonical26492 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1844 + difference 5 0) (sourceB1844 + difference 0 5) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 610) := by
    have ha : (tripleCharges (sourceA1844 + difference 5 0) (sourceB1844 + difference 0 5) sourceC1844) = raw24115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw24115; decide +kernel
    rw [ha]
    exact (canonical24115 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1844 + difference 5 1) (sourceB1844 + difference 1 5) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1135) := by
    have ha : (tripleCharges (sourceA1844 + difference 5 1) (sourceB1844 + difference 1 5) sourceC1844) = raw24116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw24116; decide +kernel
    rw [ha]
    exact (canonical24116 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1844 + difference 5 2) (sourceB1844 + difference 2 5) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1844 + difference 5 2) (sourceB1844 + difference 2 5) sourceC1844) = raw12126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw12126; decide +kernel
    rw [ha]
    exact (canonical12126 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1844 + difference 5 3) (sourceB1844 + difference 3 5) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1844 + difference 5 3) (sourceB1844 + difference 3 5) sourceC1844) = raw20374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw20374; decide +kernel
    rw [ha]
    exact (canonical20374 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1844 + difference 5 4) (sourceB1844 + difference 4 5) sourceC1844) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1305) := by
    have ha : (tripleCharges (sourceA1844 + difference 5 4) (sourceB1844 + difference 4 5) sourceC1844) = raw24117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1844 sourceB1844 sourceC1844 difference raw24117; decide +kernel
    rw [ha]
    exact (canonical24117 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1844 sourceB1844 sourceC1844
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1844, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1845 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1845 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1845 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceForm1845 : Integer.Sparse Master := [(Sum.inr 4169, 1), (Sum.inr 4170, 1), (Sum.inr 4173, 3), (Sum.inr 4540, 1), (Sum.inr 4542, 3), (Sum.inr 4599, 3), (Sum.inr 4600, 3), (Sum.inr 4601, 1), (Sum.inr 4603, 6), (Sum.inr 4606, 3), (Sum.inr 5162, 1), (Sum.inr 5273, 1), (Sum.inr 5290, 3)]

theorem sourceEq1845 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1845 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1845 + difference 0 1) (sourceB1845 + difference 1 0) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5162) := by
    have ha : (tripleCharges (sourceA1845 + difference 0 1) (sourceB1845 + difference 1 0) sourceC1845) = raw26493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26493; decide +kernel
    rw [ha]
    exact (canonical26493 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1845 + difference 0 2) (sourceB1845 + difference 2 0) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA1845 + difference 0 2) (sourceB1845 + difference 2 0) sourceC1845) = raw9271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw9271; decide +kernel
    rw [ha]
    exact (canonical9271 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1845 + difference 0 3) (sourceB1845 + difference 3 0) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA1845 + difference 0 3) (sourceB1845 + difference 3 0) sourceC1845) = raw9266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw9266; decide +kernel
    rw [ha]
    exact (canonical9266 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1845 + difference 0 4) (sourceB1845 + difference 4 0) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA1845 + difference 0 4) (sourceB1845 + difference 4 0) sourceC1845) = raw26494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26494; decide +kernel
    rw [ha]
    exact (canonical26494 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1845 + difference 0 5) (sourceB1845 + difference 5 0) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA1845 + difference 0 5) (sourceB1845 + difference 5 0) sourceC1845) = raw26495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26495; decide +kernel
    rw [ha]
    exact (canonical26495 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1845 + difference 1 0) (sourceB1845 + difference 0 1) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4169) := by
    have ha : (tripleCharges (sourceA1845 + difference 1 0) (sourceB1845 + difference 0 1) sourceC1845) = raw26496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26496; decide +kernel
    rw [ha]
    exact (canonical26496 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1845 + difference 1 2) (sourceB1845 + difference 2 1) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1845 + difference 1 2) (sourceB1845 + difference 2 1) sourceC1845) = raw26497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26497; decide +kernel
    rw [ha]
    exact (canonical26497 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1845 + difference 1 3) (sourceB1845 + difference 3 1) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1845 + difference 1 3) (sourceB1845 + difference 3 1) sourceC1845) = raw26498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26498; decide +kernel
    rw [ha]
    exact (canonical26498 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1845 + difference 1 4) (sourceB1845 + difference 4 1) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1845 + difference 1 4) (sourceB1845 + difference 4 1) sourceC1845) = raw26499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26499; decide +kernel
    rw [ha]
    exact (canonical26499 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1845 + difference 1 5) (sourceB1845 + difference 5 1) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1845 + difference 1 5) (sourceB1845 + difference 5 1) sourceC1845) = raw26500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26500; decide +kernel
    rw [ha]
    exact (canonical26500 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1845 + difference 2 0) (sourceB1845 + difference 0 2) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4173) := by
    have ha : (tripleCharges (sourceA1845 + difference 2 0) (sourceB1845 + difference 0 2) sourceC1845) = raw26501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26501; decide +kernel
    rw [ha]
    exact (canonical26501 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1845 + difference 2 1) (sourceB1845 + difference 1 2) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4542) := by
    have ha : (tripleCharges (sourceA1845 + difference 2 1) (sourceB1845 + difference 1 2) sourceC1845) = raw26502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26502; decide +kernel
    rw [ha]
    exact (canonical26502 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1845 + difference 2 3) (sourceB1845 + difference 3 2) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1845 + difference 2 3) (sourceB1845 + difference 3 2) sourceC1845) = raw26503 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26503; decide +kernel
    rw [ha]
    exact (canonical26503 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1845 + difference 2 4) (sourceB1845 + difference 4 2) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1845 + difference 2 4) (sourceB1845 + difference 4 2) sourceC1845) = raw26504 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26504; decide +kernel
    rw [ha]
    exact (canonical26504 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1845 + difference 2 5) (sourceB1845 + difference 5 2) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1845 + difference 2 5) (sourceB1845 + difference 5 2) sourceC1845) = raw26505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26505; decide +kernel
    rw [ha]
    exact (canonical26505 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1845 + difference 3 0) (sourceB1845 + difference 0 3) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4173) := by
    have ha : (tripleCharges (sourceA1845 + difference 3 0) (sourceB1845 + difference 0 3) sourceC1845) = raw26506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26506; decide +kernel
    rw [ha]
    exact (canonical26506 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1845 + difference 3 1) (sourceB1845 + difference 1 3) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4542) := by
    have ha : (tripleCharges (sourceA1845 + difference 3 1) (sourceB1845 + difference 1 3) sourceC1845) = raw26507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26507; decide +kernel
    rw [ha]
    exact (canonical26507 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1845 + difference 3 2) (sourceB1845 + difference 2 3) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1845 + difference 3 2) (sourceB1845 + difference 2 3) sourceC1845) = raw26508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26508; decide +kernel
    rw [ha]
    exact (canonical26508 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1845 + difference 3 4) (sourceB1845 + difference 4 3) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1845 + difference 3 4) (sourceB1845 + difference 4 3) sourceC1845) = raw26509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26509; decide +kernel
    rw [ha]
    exact (canonical26509 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1845 + difference 3 5) (sourceB1845 + difference 5 3) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1845 + difference 3 5) (sourceB1845 + difference 5 3) sourceC1845) = raw26510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26510; decide +kernel
    rw [ha]
    exact (canonical26510 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1845 + difference 4 0) (sourceB1845 + difference 0 4) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4173) := by
    have ha : (tripleCharges (sourceA1845 + difference 4 0) (sourceB1845 + difference 0 4) sourceC1845) = raw26511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26511; decide +kernel
    rw [ha]
    exact (canonical26511 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1845 + difference 4 1) (sourceB1845 + difference 1 4) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4542) := by
    have ha : (tripleCharges (sourceA1845 + difference 4 1) (sourceB1845 + difference 1 4) sourceC1845) = raw26512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26512; decide +kernel
    rw [ha]
    exact (canonical26512 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1845 + difference 4 2) (sourceB1845 + difference 2 4) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1845 + difference 4 2) (sourceB1845 + difference 2 4) sourceC1845) = raw26513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26513; decide +kernel
    rw [ha]
    exact (canonical26513 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1845 + difference 4 3) (sourceB1845 + difference 3 4) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA1845 + difference 4 3) (sourceB1845 + difference 3 4) sourceC1845) = raw26514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26514; decide +kernel
    rw [ha]
    exact (canonical26514 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1845 + difference 4 5) (sourceB1845 + difference 5 4) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1845 + difference 4 5) (sourceB1845 + difference 5 4) sourceC1845) = raw26515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26515; decide +kernel
    rw [ha]
    exact (canonical26515 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1845 + difference 5 0) (sourceB1845 + difference 0 5) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4170) := by
    have ha : (tripleCharges (sourceA1845 + difference 5 0) (sourceB1845 + difference 0 5) sourceC1845) = raw26516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26516; decide +kernel
    rw [ha]
    exact (canonical26516 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1845 + difference 5 1) (sourceB1845 + difference 1 5) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4540) := by
    have ha : (tripleCharges (sourceA1845 + difference 5 1) (sourceB1845 + difference 1 5) sourceC1845) = raw26517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26517; decide +kernel
    rw [ha]
    exact (canonical26517 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1845 + difference 5 2) (sourceB1845 + difference 2 5) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA1845 + difference 5 2) (sourceB1845 + difference 2 5) sourceC1845) = raw9267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw9267; decide +kernel
    rw [ha]
    exact (canonical9267 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1845 + difference 5 3) (sourceB1845 + difference 3 5) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA1845 + difference 5 3) (sourceB1845 + difference 3 5) sourceC1845) = raw9262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw9262; decide +kernel
    rw [ha]
    exact (canonical9262 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1845 + difference 5 4) (sourceB1845 + difference 4 5) sourceC1845) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4600) := by
    have ha : (tripleCharges (sourceA1845 + difference 5 4) (sourceB1845 + difference 4 5) sourceC1845) = raw26518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1845 sourceB1845 sourceC1845 difference raw26518; decide +kernel
    rw [ha]
    exact (canonical26518 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1845 sourceB1845 sourceC1845
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1845, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1846 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1846 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1846 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceForm1846 : Integer.Sparse Master := [(Sum.inr 597, 1), (Sum.inr 598, 1), (Sum.inr 601, 3), (Sum.inr 1125, 1), (Sum.inr 1127, 3), (Sum.inr 1233, 3), (Sum.inr 1234, 3), (Sum.inr 1237, 6), (Sum.inr 1265, 1), (Sum.inr 1266, 3), (Sum.inr 2957, 1), (Sum.inr 3099, 3), (Sum.inr 3111, 1)]

theorem sourceEq1846 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1846 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1846 + difference 0 1) (sourceB1846 + difference 1 0) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2957) := by
    have ha : (tripleCharges (sourceA1846 + difference 0 1) (sourceB1846 + difference 1 0) sourceC1846) = raw26519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26519; decide +kernel
    rw [ha]
    exact (canonical26519 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1846 + difference 0 2) (sourceB1846 + difference 2 0) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA1846 + difference 0 2) (sourceB1846 + difference 2 0) sourceC1846) = raw9301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw9301; decide +kernel
    rw [ha]
    exact (canonical9301 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1846 + difference 0 3) (sourceB1846 + difference 3 0) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA1846 + difference 0 3) (sourceB1846 + difference 3 0) sourceC1846) = raw9296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw9296; decide +kernel
    rw [ha]
    exact (canonical9296 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1846 + difference 0 4) (sourceB1846 + difference 4 0) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA1846 + difference 0 4) (sourceB1846 + difference 4 0) sourceC1846) = raw26520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26520; decide +kernel
    rw [ha]
    exact (canonical26520 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1846 + difference 0 5) (sourceB1846 + difference 5 0) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3111) := by
    have ha : (tripleCharges (sourceA1846 + difference 0 5) (sourceB1846 + difference 5 0) sourceC1846) = raw26521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26521; decide +kernel
    rw [ha]
    exact (canonical26521 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1846 + difference 1 0) (sourceB1846 + difference 0 1) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 597) := by
    have ha : (tripleCharges (sourceA1846 + difference 1 0) (sourceB1846 + difference 0 1) sourceC1846) = raw26522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26522; decide +kernel
    rw [ha]
    exact (canonical26522 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1846 + difference 1 2) (sourceB1846 + difference 2 1) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA1846 + difference 1 2) (sourceB1846 + difference 2 1) sourceC1846) = raw26523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26523; decide +kernel
    rw [ha]
    exact (canonical26523 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1846 + difference 1 3) (sourceB1846 + difference 3 1) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA1846 + difference 1 3) (sourceB1846 + difference 3 1) sourceC1846) = raw26524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26524; decide +kernel
    rw [ha]
    exact (canonical26524 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1846 + difference 1 4) (sourceB1846 + difference 4 1) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA1846 + difference 1 4) (sourceB1846 + difference 4 1) sourceC1846) = raw26525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26525; decide +kernel
    rw [ha]
    exact (canonical26525 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1846 + difference 1 5) (sourceB1846 + difference 5 1) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1265) := by
    have ha : (tripleCharges (sourceA1846 + difference 1 5) (sourceB1846 + difference 5 1) sourceC1846) = raw26526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26526; decide +kernel
    rw [ha]
    exact (canonical26526 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1846 + difference 2 0) (sourceB1846 + difference 0 2) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 601) := by
    have ha : (tripleCharges (sourceA1846 + difference 2 0) (sourceB1846 + difference 0 2) sourceC1846) = raw26527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26527; decide +kernel
    rw [ha]
    exact (canonical26527 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1846 + difference 2 1) (sourceB1846 + difference 1 2) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1127) := by
    have ha : (tripleCharges (sourceA1846 + difference 2 1) (sourceB1846 + difference 1 2) sourceC1846) = raw26528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26528; decide +kernel
    rw [ha]
    exact (canonical26528 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1846 + difference 2 3) (sourceB1846 + difference 3 2) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA1846 + difference 2 3) (sourceB1846 + difference 3 2) sourceC1846) = raw26529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26529; decide +kernel
    rw [ha]
    exact (canonical26529 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1846 + difference 2 4) (sourceB1846 + difference 4 2) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA1846 + difference 2 4) (sourceB1846 + difference 4 2) sourceC1846) = raw26530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26530; decide +kernel
    rw [ha]
    exact (canonical26530 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1846 + difference 2 5) (sourceB1846 + difference 5 2) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1266) := by
    have ha : (tripleCharges (sourceA1846 + difference 2 5) (sourceB1846 + difference 5 2) sourceC1846) = raw26531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26531; decide +kernel
    rw [ha]
    exact (canonical26531 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1846 + difference 3 0) (sourceB1846 + difference 0 3) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 601) := by
    have ha : (tripleCharges (sourceA1846 + difference 3 0) (sourceB1846 + difference 0 3) sourceC1846) = raw26532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26532; decide +kernel
    rw [ha]
    exact (canonical26532 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1846 + difference 3 1) (sourceB1846 + difference 1 3) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1127) := by
    have ha : (tripleCharges (sourceA1846 + difference 3 1) (sourceB1846 + difference 1 3) sourceC1846) = raw26533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26533; decide +kernel
    rw [ha]
    exact (canonical26533 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1846 + difference 3 2) (sourceB1846 + difference 2 3) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA1846 + difference 3 2) (sourceB1846 + difference 2 3) sourceC1846) = raw26534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26534; decide +kernel
    rw [ha]
    exact (canonical26534 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1846 + difference 3 4) (sourceB1846 + difference 4 3) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA1846 + difference 3 4) (sourceB1846 + difference 4 3) sourceC1846) = raw26535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26535; decide +kernel
    rw [ha]
    exact (canonical26535 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1846 + difference 3 5) (sourceB1846 + difference 5 3) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1266) := by
    have ha : (tripleCharges (sourceA1846 + difference 3 5) (sourceB1846 + difference 5 3) sourceC1846) = raw26536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26536; decide +kernel
    rw [ha]
    exact (canonical26536 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1846 + difference 4 0) (sourceB1846 + difference 0 4) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 601) := by
    have ha : (tripleCharges (sourceA1846 + difference 4 0) (sourceB1846 + difference 0 4) sourceC1846) = raw26537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26537; decide +kernel
    rw [ha]
    exact (canonical26537 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1846 + difference 4 1) (sourceB1846 + difference 1 4) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1127) := by
    have ha : (tripleCharges (sourceA1846 + difference 4 1) (sourceB1846 + difference 1 4) sourceC1846) = raw26538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26538; decide +kernel
    rw [ha]
    exact (canonical26538 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1846 + difference 4 2) (sourceB1846 + difference 2 4) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA1846 + difference 4 2) (sourceB1846 + difference 2 4) sourceC1846) = raw26539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26539; decide +kernel
    rw [ha]
    exact (canonical26539 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1846 + difference 4 3) (sourceB1846 + difference 3 4) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA1846 + difference 4 3) (sourceB1846 + difference 3 4) sourceC1846) = raw26540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26540; decide +kernel
    rw [ha]
    exact (canonical26540 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1846 + difference 4 5) (sourceB1846 + difference 5 4) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1266) := by
    have ha : (tripleCharges (sourceA1846 + difference 4 5) (sourceB1846 + difference 5 4) sourceC1846) = raw26541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26541; decide +kernel
    rw [ha]
    exact (canonical26541 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1846 + difference 5 0) (sourceB1846 + difference 0 5) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 598) := by
    have ha : (tripleCharges (sourceA1846 + difference 5 0) (sourceB1846 + difference 0 5) sourceC1846) = raw26542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26542; decide +kernel
    rw [ha]
    exact (canonical26542 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1846 + difference 5 1) (sourceB1846 + difference 1 5) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1125) := by
    have ha : (tripleCharges (sourceA1846 + difference 5 1) (sourceB1846 + difference 1 5) sourceC1846) = raw26543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26543; decide +kernel
    rw [ha]
    exact (canonical26543 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1846 + difference 5 2) (sourceB1846 + difference 2 5) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1234) := by
    have ha : (tripleCharges (sourceA1846 + difference 5 2) (sourceB1846 + difference 2 5) sourceC1846) = raw9297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw9297; decide +kernel
    rw [ha]
    exact (canonical9297 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1846 + difference 5 3) (sourceB1846 + difference 3 5) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1234) := by
    have ha : (tripleCharges (sourceA1846 + difference 5 3) (sourceB1846 + difference 3 5) sourceC1846) = raw9292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw9292; decide +kernel
    rw [ha]
    exact (canonical9292 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1846 + difference 5 4) (sourceB1846 + difference 4 5) sourceC1846) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1234) := by
    have ha : (tripleCharges (sourceA1846 + difference 5 4) (sourceB1846 + difference 4 5) sourceC1846) = raw26544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1846 sourceB1846 sourceC1846 difference raw26544; decide +kernel
    rw [ha]
    exact (canonical26544 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1846 sourceB1846 sourceC1846
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1846, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1847 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1847 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1847 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceForm1847 : Integer.Sparse Master := [(Sum.inr 1502, 1), (Sum.inr 1503, 1), (Sum.inr 1508, 3), (Sum.inr 2688, 1), (Sum.inr 2702, 3), (Sum.inr 3257, 3), (Sum.inr 3289, 3), (Sum.inr 3292, 1), (Sum.inr 3294, 6), (Sum.inr 3299, 3), (Sum.inr 3546, 1), (Sum.inr 3563, 1), (Sum.inr 3581, 3)]

theorem sourceEq1847 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1847 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1847 + difference 0 1) (sourceB1847 + difference 1 0) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3563) := by
    have ha : (tripleCharges (sourceA1847 + difference 0 1) (sourceB1847 + difference 1 0) sourceC1847) = raw26545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26545; decide +kernel
    rw [ha]
    exact (canonical26545 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1847 + difference 0 2) (sourceB1847 + difference 2 0) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA1847 + difference 0 2) (sourceB1847 + difference 2 0) sourceC1847) = raw9331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw9331; decide +kernel
    rw [ha]
    exact (canonical9331 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1847 + difference 0 3) (sourceB1847 + difference 3 0) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA1847 + difference 0 3) (sourceB1847 + difference 3 0) sourceC1847) = raw9326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw9326; decide +kernel
    rw [ha]
    exact (canonical9326 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1847 + difference 0 4) (sourceB1847 + difference 4 0) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA1847 + difference 0 4) (sourceB1847 + difference 4 0) sourceC1847) = raw26546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26546; decide +kernel
    rw [ha]
    exact (canonical26546 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1847 + difference 0 5) (sourceB1847 + difference 5 0) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3546) := by
    have ha : (tripleCharges (sourceA1847 + difference 0 5) (sourceB1847 + difference 5 0) sourceC1847) = raw26547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26547; decide +kernel
    rw [ha]
    exact (canonical26547 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1847 + difference 1 0) (sourceB1847 + difference 0 1) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1502) := by
    have ha : (tripleCharges (sourceA1847 + difference 1 0) (sourceB1847 + difference 0 1) sourceC1847) = raw26548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26548; decide +kernel
    rw [ha]
    exact (canonical26548 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1847 + difference 1 2) (sourceB1847 + difference 2 1) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1847 + difference 1 2) (sourceB1847 + difference 2 1) sourceC1847) = raw26549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26549; decide +kernel
    rw [ha]
    exact (canonical26549 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1847 + difference 1 3) (sourceB1847 + difference 3 1) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1847 + difference 1 3) (sourceB1847 + difference 3 1) sourceC1847) = raw26550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26550; decide +kernel
    rw [ha]
    exact (canonical26550 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1847 + difference 1 4) (sourceB1847 + difference 4 1) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3289) := by
    have ha : (tripleCharges (sourceA1847 + difference 1 4) (sourceB1847 + difference 4 1) sourceC1847) = raw26551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26551; decide +kernel
    rw [ha]
    exact (canonical26551 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1847 + difference 1 5) (sourceB1847 + difference 5 1) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3292) := by
    have ha : (tripleCharges (sourceA1847 + difference 1 5) (sourceB1847 + difference 5 1) sourceC1847) = raw26552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26552; decide +kernel
    rw [ha]
    exact (canonical26552 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1847 + difference 2 0) (sourceB1847 + difference 0 2) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1508) := by
    have ha : (tripleCharges (sourceA1847 + difference 2 0) (sourceB1847 + difference 0 2) sourceC1847) = raw26553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26553; decide +kernel
    rw [ha]
    exact (canonical26553 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1847 + difference 2 1) (sourceB1847 + difference 1 2) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3257) := by
    have ha : (tripleCharges (sourceA1847 + difference 2 1) (sourceB1847 + difference 1 2) sourceC1847) = raw26554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26554; decide +kernel
    rw [ha]
    exact (canonical26554 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1847 + difference 2 3) (sourceB1847 + difference 3 2) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1847 + difference 2 3) (sourceB1847 + difference 3 2) sourceC1847) = raw26555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26555; decide +kernel
    rw [ha]
    exact (canonical26555 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1847 + difference 2 4) (sourceB1847 + difference 4 2) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1847 + difference 2 4) (sourceB1847 + difference 4 2) sourceC1847) = raw26556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26556; decide +kernel
    rw [ha]
    exact (canonical26556 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1847 + difference 2 5) (sourceB1847 + difference 5 2) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1847 + difference 2 5) (sourceB1847 + difference 5 2) sourceC1847) = raw26557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26557; decide +kernel
    rw [ha]
    exact (canonical26557 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1847 + difference 3 0) (sourceB1847 + difference 0 3) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1508) := by
    have ha : (tripleCharges (sourceA1847 + difference 3 0) (sourceB1847 + difference 0 3) sourceC1847) = raw26558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26558; decide +kernel
    rw [ha]
    exact (canonical26558 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1847 + difference 3 1) (sourceB1847 + difference 1 3) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3257) := by
    have ha : (tripleCharges (sourceA1847 + difference 3 1) (sourceB1847 + difference 1 3) sourceC1847) = raw26559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26559; decide +kernel
    rw [ha]
    exact (canonical26559 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1847 + difference 3 2) (sourceB1847 + difference 2 3) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1847 + difference 3 2) (sourceB1847 + difference 2 3) sourceC1847) = raw26560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26560; decide +kernel
    rw [ha]
    exact (canonical26560 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1847 + difference 3 4) (sourceB1847 + difference 4 3) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1847 + difference 3 4) (sourceB1847 + difference 4 3) sourceC1847) = raw26561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26561; decide +kernel
    rw [ha]
    exact (canonical26561 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1847 + difference 3 5) (sourceB1847 + difference 5 3) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1847 + difference 3 5) (sourceB1847 + difference 5 3) sourceC1847) = raw26562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26562; decide +kernel
    rw [ha]
    exact (canonical26562 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1847 + difference 4 0) (sourceB1847 + difference 0 4) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1508) := by
    have ha : (tripleCharges (sourceA1847 + difference 4 0) (sourceB1847 + difference 0 4) sourceC1847) = raw26563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26563; decide +kernel
    rw [ha]
    exact (canonical26563 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1847 + difference 4 1) (sourceB1847 + difference 1 4) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3257) := by
    have ha : (tripleCharges (sourceA1847 + difference 4 1) (sourceB1847 + difference 1 4) sourceC1847) = raw26564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26564; decide +kernel
    rw [ha]
    exact (canonical26564 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1847 + difference 4 2) (sourceB1847 + difference 2 4) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1847 + difference 4 2) (sourceB1847 + difference 2 4) sourceC1847) = raw26565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26565; decide +kernel
    rw [ha]
    exact (canonical26565 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1847 + difference 4 3) (sourceB1847 + difference 3 4) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1847 + difference 4 3) (sourceB1847 + difference 3 4) sourceC1847) = raw26566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26566; decide +kernel
    rw [ha]
    exact (canonical26566 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1847 + difference 4 5) (sourceB1847 + difference 5 4) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1847 + difference 4 5) (sourceB1847 + difference 5 4) sourceC1847) = raw26567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26567; decide +kernel
    rw [ha]
    exact (canonical26567 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1847 + difference 5 0) (sourceB1847 + difference 0 5) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1503) := by
    have ha : (tripleCharges (sourceA1847 + difference 5 0) (sourceB1847 + difference 0 5) sourceC1847) = raw26568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26568; decide +kernel
    rw [ha]
    exact (canonical26568 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1847 + difference 5 1) (sourceB1847 + difference 1 5) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2688) := by
    have ha : (tripleCharges (sourceA1847 + difference 5 1) (sourceB1847 + difference 1 5) sourceC1847) = raw26569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26569; decide +kernel
    rw [ha]
    exact (canonical26569 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1847 + difference 5 2) (sourceB1847 + difference 2 5) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1847 + difference 5 2) (sourceB1847 + difference 2 5) sourceC1847) = raw9327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw9327; decide +kernel
    rw [ha]
    exact (canonical9327 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1847 + difference 5 3) (sourceB1847 + difference 3 5) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1847 + difference 5 3) (sourceB1847 + difference 3 5) sourceC1847) = raw9322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw9322; decide +kernel
    rw [ha]
    exact (canonical9322 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1847 + difference 5 4) (sourceB1847 + difference 4 5) sourceC1847) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1847 + difference 5 4) (sourceB1847 + difference 4 5) sourceC1847) = raw26570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1847 sourceB1847 sourceC1847 difference raw26570; decide +kernel
    rw [ha]
    exact (canonical26570 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1847 sourceB1847 sourceC1847
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1847, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1848 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1848 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1848 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceForm1848 : Integer.Sparse Master := [(Sum.inr 637, 1), (Sum.inr 640, 3), (Sum.inr 651, 1), (Sum.inr 1293, 1), (Sum.inr 4091, -1)]

theorem sourceEq1848 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1848 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1848 + difference 0 0) (sourceB1848 + difference 0 0) sourceC1848) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA1848 + difference 0 0) (sourceB1848 + difference 0 0) sourceC1848) = raw26571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1848 sourceB1848 sourceC1848 difference raw26571; decide +kernel
    rw [ha]
    exact (canonical26571 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1848 + difference 1 0) (sourceB1848 + difference 0 1) sourceC1848) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 637) := by
    have ha : (tripleCharges (sourceA1848 + difference 1 0) (sourceB1848 + difference 0 1) sourceC1848) = raw26572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1848 sourceB1848 sourceC1848 difference raw26572; decide +kernel
    rw [ha]
    exact (canonical26572 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1848 + difference 2 0) (sourceB1848 + difference 0 2) sourceC1848) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 640) := by
    have ha : (tripleCharges (sourceA1848 + difference 2 0) (sourceB1848 + difference 0 2) sourceC1848) = raw26573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1848 sourceB1848 sourceC1848 difference raw26573; decide +kernel
    rw [ha]
    exact (canonical26573 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1848 + difference 3 0) (sourceB1848 + difference 0 3) sourceC1848) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 640) := by
    have ha : (tripleCharges (sourceA1848 + difference 3 0) (sourceB1848 + difference 0 3) sourceC1848) = raw26574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1848 sourceB1848 sourceC1848 difference raw26574; decide +kernel
    rw [ha]
    exact (canonical26574 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1848 + difference 4 0) (sourceB1848 + difference 0 4) sourceC1848) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 640) := by
    have ha : (tripleCharges (sourceA1848 + difference 4 0) (sourceB1848 + difference 0 4) sourceC1848) = raw26575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1848 sourceB1848 sourceC1848 difference raw26575; decide +kernel
    rw [ha]
    exact (canonical26575 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1848 + difference 5 0) (sourceB1848 + difference 0 5) sourceC1848) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 651) := by
    have ha : (tripleCharges (sourceA1848 + difference 5 0) (sourceB1848 + difference 0 5) sourceC1848) = raw26576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1848 sourceB1848 sourceC1848 difference raw26576; decide +kernel
    rw [ha]
    exact (canonical26576 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1848 + sourceB1848) sourceC1848) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1848 + sourceB1848) sourceC1848) = raw9348 := by
      apply Matrix.ext; unfold doubleCharges sourceA1848 sourceB1848 sourceC1848 raw9348; decide +kernel
    rw [ha]
    exact (canonical9348 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1848 sourceB1848 sourceC1848
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1848, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1849 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceB1849 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1849 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1849 : Integer.Sparse Master := [(Sum.inr 4451, 1), (Sum.inr 4455, 1), (Sum.inr 4489, 3), (Sum.inr 4494, 1), (Sum.inr 4495, 3), (Sum.inr 4497, 1), (Sum.inr 4595, 3), (Sum.inr 4598, 1), (Sum.inr 4599, 3), (Sum.inr 4601, 1), (Sum.inr 4613, 3), (Sum.inr 4616, 6), (Sum.inr 4622, 3)]

theorem sourceEq1849 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1849 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1849 + difference 0 1) (sourceB1849 + difference 1 0) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4451) := by
    have ha : (tripleCharges (sourceA1849 + difference 0 1) (sourceB1849 + difference 1 0) sourceC1849) = raw26577 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26577; decide +kernel
    rw [ha]
    exact (canonical26577 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1849 + difference 0 2) (sourceB1849 + difference 2 0) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA1849 + difference 0 2) (sourceB1849 + difference 2 0) sourceC1849) = raw26578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26578; decide +kernel
    rw [ha]
    exact (canonical26578 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1849 + difference 0 3) (sourceB1849 + difference 3 0) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA1849 + difference 0 3) (sourceB1849 + difference 3 0) sourceC1849) = raw26579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26579; decide +kernel
    rw [ha]
    exact (canonical26579 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1849 + difference 0 4) (sourceB1849 + difference 4 0) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4489) := by
    have ha : (tripleCharges (sourceA1849 + difference 0 4) (sourceB1849 + difference 4 0) sourceC1849) = raw26580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26580; decide +kernel
    rw [ha]
    exact (canonical26580 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1849 + difference 0 5) (sourceB1849 + difference 5 0) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1849 + difference 0 5) (sourceB1849 + difference 5 0) sourceC1849) = raw26581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26581; decide +kernel
    rw [ha]
    exact (canonical26581 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1849 + difference 1 0) (sourceB1849 + difference 0 1) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4455) := by
    have ha : (tripleCharges (sourceA1849 + difference 1 0) (sourceB1849 + difference 0 1) sourceC1849) = raw26582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26582; decide +kernel
    rw [ha]
    exact (canonical26582 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1849 + difference 1 2) (sourceB1849 + difference 2 1) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4595) := by
    have ha : (tripleCharges (sourceA1849 + difference 1 2) (sourceB1849 + difference 2 1) sourceC1849) = raw26583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26583; decide +kernel
    rw [ha]
    exact (canonical26583 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1849 + difference 1 3) (sourceB1849 + difference 3 1) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4595) := by
    have ha : (tripleCharges (sourceA1849 + difference 1 3) (sourceB1849 + difference 3 1) sourceC1849) = raw26584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26584; decide +kernel
    rw [ha]
    exact (canonical26584 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1849 + difference 1 4) (sourceB1849 + difference 4 1) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4595) := by
    have ha : (tripleCharges (sourceA1849 + difference 1 4) (sourceB1849 + difference 4 1) sourceC1849) = raw26585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26585; decide +kernel
    rw [ha]
    exact (canonical26585 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1849 + difference 1 5) (sourceB1849 + difference 5 1) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1849 + difference 1 5) (sourceB1849 + difference 5 1) sourceC1849) = raw26586 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26586; decide +kernel
    rw [ha]
    exact (canonical26586 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1849 + difference 2 0) (sourceB1849 + difference 0 2) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1849 + difference 2 0) (sourceB1849 + difference 0 2) sourceC1849) = raw26587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26587; decide +kernel
    rw [ha]
    exact (canonical26587 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1849 + difference 2 1) (sourceB1849 + difference 1 2) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1849 + difference 2 1) (sourceB1849 + difference 1 2) sourceC1849) = raw26588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26588; decide +kernel
    rw [ha]
    exact (canonical26588 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1849 + difference 2 3) (sourceB1849 + difference 3 2) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1849 + difference 2 3) (sourceB1849 + difference 3 2) sourceC1849) = raw26589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26589; decide +kernel
    rw [ha]
    exact (canonical26589 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1849 + difference 2 4) (sourceB1849 + difference 4 2) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1849 + difference 2 4) (sourceB1849 + difference 4 2) sourceC1849) = raw26590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26590; decide +kernel
    rw [ha]
    exact (canonical26590 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1849 + difference 2 5) (sourceB1849 + difference 5 2) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1849 + difference 2 5) (sourceB1849 + difference 5 2) sourceC1849) = raw26591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26591; decide +kernel
    rw [ha]
    exact (canonical26591 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1849 + difference 3 0) (sourceB1849 + difference 0 3) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1849 + difference 3 0) (sourceB1849 + difference 0 3) sourceC1849) = raw26592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26592; decide +kernel
    rw [ha]
    exact (canonical26592 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1849 + difference 3 1) (sourceB1849 + difference 1 3) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1849 + difference 3 1) (sourceB1849 + difference 1 3) sourceC1849) = raw26593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26593; decide +kernel
    rw [ha]
    exact (canonical26593 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1849 + difference 3 2) (sourceB1849 + difference 2 3) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1849 + difference 3 2) (sourceB1849 + difference 2 3) sourceC1849) = raw26594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26594; decide +kernel
    rw [ha]
    exact (canonical26594 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1849 + difference 3 4) (sourceB1849 + difference 4 3) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1849 + difference 3 4) (sourceB1849 + difference 4 3) sourceC1849) = raw26595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26595; decide +kernel
    rw [ha]
    exact (canonical26595 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1849 + difference 3 5) (sourceB1849 + difference 5 3) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1849 + difference 3 5) (sourceB1849 + difference 5 3) sourceC1849) = raw26596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26596; decide +kernel
    rw [ha]
    exact (canonical26596 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1849 + difference 4 0) (sourceB1849 + difference 0 4) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1849 + difference 4 0) (sourceB1849 + difference 0 4) sourceC1849) = raw26597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26597; decide +kernel
    rw [ha]
    exact (canonical26597 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1849 + difference 4 1) (sourceB1849 + difference 1 4) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1849 + difference 4 1) (sourceB1849 + difference 1 4) sourceC1849) = raw26598 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26598; decide +kernel
    rw [ha]
    exact (canonical26598 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1849 + difference 4 2) (sourceB1849 + difference 2 4) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1849 + difference 4 2) (sourceB1849 + difference 2 4) sourceC1849) = raw26599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26599; decide +kernel
    rw [ha]
    exact (canonical26599 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1849 + difference 4 3) (sourceB1849 + difference 3 4) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1849 + difference 4 3) (sourceB1849 + difference 3 4) sourceC1849) = raw26600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26600; decide +kernel
    rw [ha]
    exact (canonical26600 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1849 + difference 4 5) (sourceB1849 + difference 5 4) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1849 + difference 4 5) (sourceB1849 + difference 5 4) sourceC1849) = raw26601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26601; decide +kernel
    rw [ha]
    exact (canonical26601 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1849 + difference 5 0) (sourceB1849 + difference 0 5) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4494) := by
    have ha : (tripleCharges (sourceA1849 + difference 5 0) (sourceB1849 + difference 0 5) sourceC1849) = raw26602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26602; decide +kernel
    rw [ha]
    exact (canonical26602 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1849 + difference 5 1) (sourceB1849 + difference 1 5) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4598) := by
    have ha : (tripleCharges (sourceA1849 + difference 5 1) (sourceB1849 + difference 1 5) sourceC1849) = raw26603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26603; decide +kernel
    rw [ha]
    exact (canonical26603 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1849 + difference 5 2) (sourceB1849 + difference 2 5) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4613) := by
    have ha : (tripleCharges (sourceA1849 + difference 5 2) (sourceB1849 + difference 2 5) sourceC1849) = raw26604 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26604; decide +kernel
    rw [ha]
    exact (canonical26604 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1849 + difference 5 3) (sourceB1849 + difference 3 5) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4613) := by
    have ha : (tripleCharges (sourceA1849 + difference 5 3) (sourceB1849 + difference 3 5) sourceC1849) = raw26605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26605; decide +kernel
    rw [ha]
    exact (canonical26605 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1849 + difference 5 4) (sourceB1849 + difference 4 5) sourceC1849) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4613) := by
    have ha : (tripleCharges (sourceA1849 + difference 5 4) (sourceB1849 + difference 4 5) sourceC1849) = raw26606 := by
      apply Matrix.ext; unfold tripleCharges sourceA1849 sourceB1849 sourceC1849 difference raw26606; decide +kernel
    rw [ha]
    exact (canonical26606 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1849 sourceB1849 sourceC1849
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1849, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1850 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceB1850 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1850 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1850 : Integer.Sparse Master := [(Sum.inr 1034, 1), (Sum.inr 1073, 3), (Sum.inr 1081, 1), (Sum.inr 1228, 3), (Sum.inr 1235, 1), (Sum.inr 1256, 1), (Sum.inr 1260, 3), (Sum.inr 1286, 3), (Sum.inr 1291, 6), (Sum.inr 1299, 3), (Sum.inr 1405, 1), (Sum.inr 1435, 1), (Sum.inr 1441, 3)]

theorem sourceEq1850 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1850 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1850 + difference 0 1) (sourceB1850 + difference 1 0) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1034) := by
    have ha : (tripleCharges (sourceA1850 + difference 0 1) (sourceB1850 + difference 1 0) sourceC1850) = raw26607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26607; decide +kernel
    rw [ha]
    exact (canonical26607 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1850 + difference 0 2) (sourceB1850 + difference 2 0) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1850 + difference 0 2) (sourceB1850 + difference 2 0) sourceC1850) = raw26608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26608; decide +kernel
    rw [ha]
    exact (canonical26608 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1850 + difference 0 3) (sourceB1850 + difference 3 0) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1850 + difference 0 3) (sourceB1850 + difference 3 0) sourceC1850) = raw26609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26609; decide +kernel
    rw [ha]
    exact (canonical26609 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1850 + difference 0 4) (sourceB1850 + difference 4 0) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1073) := by
    have ha : (tripleCharges (sourceA1850 + difference 0 4) (sourceB1850 + difference 4 0) sourceC1850) = raw26610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26610; decide +kernel
    rw [ha]
    exact (canonical26610 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1850 + difference 0 5) (sourceB1850 + difference 5 0) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1081) := by
    have ha : (tripleCharges (sourceA1850 + difference 0 5) (sourceB1850 + difference 5 0) sourceC1850) = raw26611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26611; decide +kernel
    rw [ha]
    exact (canonical26611 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1850 + difference 1 0) (sourceB1850 + difference 0 1) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1405) := by
    have ha : (tripleCharges (sourceA1850 + difference 1 0) (sourceB1850 + difference 0 1) sourceC1850) = raw26612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26612; decide +kernel
    rw [ha]
    exact (canonical26612 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1850 + difference 1 2) (sourceB1850 + difference 2 1) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1228) := by
    have ha : (tripleCharges (sourceA1850 + difference 1 2) (sourceB1850 + difference 2 1) sourceC1850) = raw26613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26613; decide +kernel
    rw [ha]
    exact (canonical26613 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1850 + difference 1 3) (sourceB1850 + difference 3 1) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1228) := by
    have ha : (tripleCharges (sourceA1850 + difference 1 3) (sourceB1850 + difference 3 1) sourceC1850) = raw26614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26614; decide +kernel
    rw [ha]
    exact (canonical26614 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1850 + difference 1 4) (sourceB1850 + difference 4 1) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1228) := by
    have ha : (tripleCharges (sourceA1850 + difference 1 4) (sourceB1850 + difference 4 1) sourceC1850) = raw26615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26615; decide +kernel
    rw [ha]
    exact (canonical26615 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1850 + difference 1 5) (sourceB1850 + difference 5 1) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA1850 + difference 1 5) (sourceB1850 + difference 5 1) sourceC1850) = raw26616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26616; decide +kernel
    rw [ha]
    exact (canonical26616 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1850 + difference 2 0) (sourceB1850 + difference 0 2) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1441) := by
    have ha : (tripleCharges (sourceA1850 + difference 2 0) (sourceB1850 + difference 0 2) sourceC1850) = raw26617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26617; decide +kernel
    rw [ha]
    exact (canonical26617 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1850 + difference 2 1) (sourceB1850 + difference 1 2) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA1850 + difference 2 1) (sourceB1850 + difference 1 2) sourceC1850) = raw26618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26618; decide +kernel
    rw [ha]
    exact (canonical26618 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1850 + difference 2 3) (sourceB1850 + difference 3 2) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA1850 + difference 2 3) (sourceB1850 + difference 3 2) sourceC1850) = raw26619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26619; decide +kernel
    rw [ha]
    exact (canonical26619 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1850 + difference 2 4) (sourceB1850 + difference 4 2) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA1850 + difference 2 4) (sourceB1850 + difference 4 2) sourceC1850) = raw26620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26620; decide +kernel
    rw [ha]
    exact (canonical26620 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1850 + difference 2 5) (sourceB1850 + difference 5 2) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1850 + difference 2 5) (sourceB1850 + difference 5 2) sourceC1850) = raw26621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26621; decide +kernel
    rw [ha]
    exact (canonical26621 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1850 + difference 3 0) (sourceB1850 + difference 0 3) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1441) := by
    have ha : (tripleCharges (sourceA1850 + difference 3 0) (sourceB1850 + difference 0 3) sourceC1850) = raw26622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26622; decide +kernel
    rw [ha]
    exact (canonical26622 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1850 + difference 3 1) (sourceB1850 + difference 1 3) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA1850 + difference 3 1) (sourceB1850 + difference 1 3) sourceC1850) = raw26623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26623; decide +kernel
    rw [ha]
    exact (canonical26623 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1850 + difference 3 2) (sourceB1850 + difference 2 3) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA1850 + difference 3 2) (sourceB1850 + difference 2 3) sourceC1850) = raw26624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26624; decide +kernel
    rw [ha]
    exact (canonical26624 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1850 + difference 3 4) (sourceB1850 + difference 4 3) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA1850 + difference 3 4) (sourceB1850 + difference 4 3) sourceC1850) = raw26625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26625; decide +kernel
    rw [ha]
    exact (canonical26625 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1850 + difference 3 5) (sourceB1850 + difference 5 3) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1850 + difference 3 5) (sourceB1850 + difference 5 3) sourceC1850) = raw26626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26626; decide +kernel
    rw [ha]
    exact (canonical26626 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1850 + difference 4 0) (sourceB1850 + difference 0 4) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1441) := by
    have ha : (tripleCharges (sourceA1850 + difference 4 0) (sourceB1850 + difference 0 4) sourceC1850) = raw26627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26627; decide +kernel
    rw [ha]
    exact (canonical26627 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1850 + difference 4 1) (sourceB1850 + difference 1 4) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1260) := by
    have ha : (tripleCharges (sourceA1850 + difference 4 1) (sourceB1850 + difference 1 4) sourceC1850) = raw26628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26628; decide +kernel
    rw [ha]
    exact (canonical26628 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1850 + difference 4 2) (sourceB1850 + difference 2 4) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA1850 + difference 4 2) (sourceB1850 + difference 2 4) sourceC1850) = raw26629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26629; decide +kernel
    rw [ha]
    exact (canonical26629 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1850 + difference 4 3) (sourceB1850 + difference 3 4) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA1850 + difference 4 3) (sourceB1850 + difference 3 4) sourceC1850) = raw26630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26630; decide +kernel
    rw [ha]
    exact (canonical26630 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1850 + difference 4 5) (sourceB1850 + difference 5 4) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1850 + difference 4 5) (sourceB1850 + difference 5 4) sourceC1850) = raw26631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26631; decide +kernel
    rw [ha]
    exact (canonical26631 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1850 + difference 5 0) (sourceB1850 + difference 0 5) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1435) := by
    have ha : (tripleCharges (sourceA1850 + difference 5 0) (sourceB1850 + difference 0 5) sourceC1850) = raw26632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26632; decide +kernel
    rw [ha]
    exact (canonical26632 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1850 + difference 5 1) (sourceB1850 + difference 1 5) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1256) := by
    have ha : (tripleCharges (sourceA1850 + difference 5 1) (sourceB1850 + difference 1 5) sourceC1850) = raw26633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26633; decide +kernel
    rw [ha]
    exact (canonical26633 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1850 + difference 5 2) (sourceB1850 + difference 2 5) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1286) := by
    have ha : (tripleCharges (sourceA1850 + difference 5 2) (sourceB1850 + difference 2 5) sourceC1850) = raw26634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26634; decide +kernel
    rw [ha]
    exact (canonical26634 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1850 + difference 5 3) (sourceB1850 + difference 3 5) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1286) := by
    have ha : (tripleCharges (sourceA1850 + difference 5 3) (sourceB1850 + difference 3 5) sourceC1850) = raw26635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26635; decide +kernel
    rw [ha]
    exact (canonical26635 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1850 + difference 5 4) (sourceB1850 + difference 4 5) sourceC1850) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1286) := by
    have ha : (tripleCharges (sourceA1850 + difference 5 4) (sourceB1850 + difference 4 5) sourceC1850) = raw26636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1850 sourceB1850 sourceC1850 difference raw26636; decide +kernel
    rw [ha]
    exact (canonical26636 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1850 sourceB1850 sourceC1850
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1850, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1851 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceB1851 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceC1851 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1851 : Integer.Sparse Master := [(Sum.inr 1644, 1), (Sum.inr 1648, 3), (Sum.inr 1726, 1), (Sum.inr 3304, 1), (Sum.inr 4068, -1)]

theorem sourceEq1851 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1851 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1851 + difference 0 0) (sourceB1851 + difference 0 0) sourceC1851) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3304) := by
    have ha : (tripleCharges (sourceA1851 + difference 0 0) (sourceB1851 + difference 0 0) sourceC1851) = raw26369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1851 sourceB1851 sourceC1851 difference raw26369; decide +kernel
    rw [ha]
    exact (canonical26369 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1851 + difference 0 1) (sourceB1851 + difference 1 0) sourceC1851) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1644) := by
    have ha : (tripleCharges (sourceA1851 + difference 0 1) (sourceB1851 + difference 1 0) sourceC1851) = raw26416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1851 sourceB1851 sourceC1851 difference raw26416; decide +kernel
    rw [ha]
    exact (canonical26416 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1851 + difference 0 2) (sourceB1851 + difference 2 0) sourceC1851) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1648) := by
    have ha : (tripleCharges (sourceA1851 + difference 0 2) (sourceB1851 + difference 2 0) sourceC1851) = raw26456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1851 sourceB1851 sourceC1851 difference raw26456; decide +kernel
    rw [ha]
    exact (canonical26456 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1851 + difference 0 3) (sourceB1851 + difference 3 0) sourceC1851) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1648) := by
    have ha : (tripleCharges (sourceA1851 + difference 0 3) (sourceB1851 + difference 3 0) sourceC1851) = raw26637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1851 sourceB1851 sourceC1851 difference raw26637; decide +kernel
    rw [ha]
    exact (canonical26637 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1851 + difference 0 4) (sourceB1851 + difference 4 0) sourceC1851) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1648) := by
    have ha : (tripleCharges (sourceA1851 + difference 0 4) (sourceB1851 + difference 4 0) sourceC1851) = raw26638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1851 sourceB1851 sourceC1851 difference raw26638; decide +kernel
    rw [ha]
    exact (canonical26638 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1851 + difference 0 5) (sourceB1851 + difference 5 0) sourceC1851) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1726) := by
    have ha : (tripleCharges (sourceA1851 + difference 0 5) (sourceB1851 + difference 5 0) sourceC1851) = raw26639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1851 sourceB1851 sourceC1851 difference raw26639; decide +kernel
    rw [ha]
    exact (canonical26639 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1851 + sourceB1851) sourceC1851) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1851 + sourceB1851) sourceC1851) = raw26370 := by
      apply Matrix.ext; unfold doubleCharges sourceA1851 sourceB1851 sourceC1851 raw26370; decide +kernel
    rw [ha]
    exact (canonical26370 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1851 sourceB1851 sourceC1851
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1851, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1852 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1852 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1852 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm1852 : Integer.Sparse Master := [(Sum.inr 4171, 1), (Sum.inr 4172, 2), (Sum.inr 4175, 2), (Sum.inr 4541, 2), (Sum.inr 4544, 2), (Sum.inr 4601, 2), (Sum.inr 4602, 4), (Sum.inr 4606, 2), (Sum.inr 4622, 2), (Sum.inr 4623, 2), (Sum.inr 4624, 4), (Sum.inr 5167, 1), (Sum.inr 5292, 2), (Sum.inr 5307, 2)]

theorem sourceEq1852 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1852 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1852 + difference 0 1) (sourceB1852 + difference 1 0) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA1852 + difference 0 1) (sourceB1852 + difference 1 0) sourceC1852) = raw26640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26640; decide +kernel
    rw [ha]
    exact (canonical26640 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1852 + difference 0 2) (sourceB1852 + difference 2 0) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA1852 + difference 0 2) (sourceB1852 + difference 2 0) sourceC1852) = raw10209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw10209; decide +kernel
    rw [ha]
    exact (canonical10209 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1852 + difference 0 3) (sourceB1852 + difference 3 0) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA1852 + difference 0 3) (sourceB1852 + difference 3 0) sourceC1852) = raw10205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw10205; decide +kernel
    rw [ha]
    exact (canonical10205 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1852 + difference 0 4) (sourceB1852 + difference 4 0) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1852 + difference 0 4) (sourceB1852 + difference 4 0) sourceC1852) = raw26641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26641; decide +kernel
    rw [ha]
    exact (canonical26641 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1852 + difference 0 5) (sourceB1852 + difference 5 0) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA1852 + difference 0 5) (sourceB1852 + difference 5 0) sourceC1852) = raw26642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26642; decide +kernel
    rw [ha]
    exact (canonical26642 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1852 + difference 1 0) (sourceB1852 + difference 0 1) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4171) := by
    have ha : (tripleCharges (sourceA1852 + difference 1 0) (sourceB1852 + difference 0 1) sourceC1852) = raw26643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26643; decide +kernel
    rw [ha]
    exact (canonical26643 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1852 + difference 1 2) (sourceB1852 + difference 2 1) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1852 + difference 1 2) (sourceB1852 + difference 2 1) sourceC1852) = raw24222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw24222; decide +kernel
    rw [ha]
    exact (canonical24222 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1852 + difference 1 3) (sourceB1852 + difference 3 1) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1852 + difference 1 3) (sourceB1852 + difference 3 1) sourceC1852) = raw26644 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26644; decide +kernel
    rw [ha]
    exact (canonical26644 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1852 + difference 1 4) (sourceB1852 + difference 4 1) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1852 + difference 1 4) (sourceB1852 + difference 4 1) sourceC1852) = raw26645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26645; decide +kernel
    rw [ha]
    exact (canonical26645 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1852 + difference 1 5) (sourceB1852 + difference 5 1) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1852 + difference 1 5) (sourceB1852 + difference 5 1) sourceC1852) = raw26646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26646; decide +kernel
    rw [ha]
    exact (canonical26646 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1852 + difference 2 0) (sourceB1852 + difference 0 2) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4172) := by
    have ha : (tripleCharges (sourceA1852 + difference 2 0) (sourceB1852 + difference 0 2) sourceC1852) = raw26647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26647; decide +kernel
    rw [ha]
    exact (canonical26647 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1852 + difference 2 1) (sourceB1852 + difference 1 2) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4541) := by
    have ha : (tripleCharges (sourceA1852 + difference 2 1) (sourceB1852 + difference 1 2) sourceC1852) = raw26648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26648; decide +kernel
    rw [ha]
    exact (canonical26648 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1852 + difference 2 3) (sourceB1852 + difference 3 2) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1852 + difference 2 3) (sourceB1852 + difference 3 2) sourceC1852) = raw26649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26649; decide +kernel
    rw [ha]
    exact (canonical26649 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1852 + difference 2 4) (sourceB1852 + difference 4 2) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1852 + difference 2 4) (sourceB1852 + difference 4 2) sourceC1852) = raw26650 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26650; decide +kernel
    rw [ha]
    exact (canonical26650 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1852 + difference 2 5) (sourceB1852 + difference 5 2) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1852 + difference 2 5) (sourceB1852 + difference 5 2) sourceC1852) = raw26651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26651; decide +kernel
    rw [ha]
    exact (canonical26651 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1852 + difference 3 0) (sourceB1852 + difference 0 3) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4172) := by
    have ha : (tripleCharges (sourceA1852 + difference 3 0) (sourceB1852 + difference 0 3) sourceC1852) = raw26652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26652; decide +kernel
    rw [ha]
    exact (canonical26652 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1852 + difference 3 1) (sourceB1852 + difference 1 3) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4541) := by
    have ha : (tripleCharges (sourceA1852 + difference 3 1) (sourceB1852 + difference 1 3) sourceC1852) = raw26653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26653; decide +kernel
    rw [ha]
    exact (canonical26653 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1852 + difference 3 2) (sourceB1852 + difference 2 3) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4623) := by
    have ha : (tripleCharges (sourceA1852 + difference 3 2) (sourceB1852 + difference 2 3) sourceC1852) = raw24231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw24231; decide +kernel
    rw [ha]
    exact (canonical24231 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1852 + difference 3 4) (sourceB1852 + difference 4 3) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1852 + difference 3 4) (sourceB1852 + difference 4 3) sourceC1852) = raw26654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26654; decide +kernel
    rw [ha]
    exact (canonical26654 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1852 + difference 3 5) (sourceB1852 + difference 5 3) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA1852 + difference 3 5) (sourceB1852 + difference 5 3) sourceC1852) = raw26655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26655; decide +kernel
    rw [ha]
    exact (canonical26655 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1852 + difference 4 0) (sourceB1852 + difference 0 4) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4175) := by
    have ha : (tripleCharges (sourceA1852 + difference 4 0) (sourceB1852 + difference 0 4) sourceC1852) = raw26656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26656; decide +kernel
    rw [ha]
    exact (canonical26656 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1852 + difference 4 1) (sourceB1852 + difference 1 4) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4544) := by
    have ha : (tripleCharges (sourceA1852 + difference 4 1) (sourceB1852 + difference 1 4) sourceC1852) = raw26657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26657; decide +kernel
    rw [ha]
    exact (canonical26657 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1852 + difference 4 2) (sourceB1852 + difference 2 4) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1852 + difference 4 2) (sourceB1852 + difference 2 4) sourceC1852) = raw22580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw22580; decide +kernel
    rw [ha]
    exact (canonical22580 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1852 + difference 4 3) (sourceB1852 + difference 3 4) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1852 + difference 4 3) (sourceB1852 + difference 3 4) sourceC1852) = raw22576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw22576; decide +kernel
    rw [ha]
    exact (canonical22576 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1852 + difference 4 5) (sourceB1852 + difference 5 4) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1852 + difference 4 5) (sourceB1852 + difference 5 4) sourceC1852) = raw26658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw26658; decide +kernel
    rw [ha]
    exact (canonical26658 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1852 + difference 5 0) (sourceB1852 + difference 0 5) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4175) := by
    have ha : (tripleCharges (sourceA1852 + difference 5 0) (sourceB1852 + difference 0 5) sourceC1852) = raw24223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw24223; decide +kernel
    rw [ha]
    exact (canonical24223 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1852 + difference 5 1) (sourceB1852 + difference 1 5) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4544) := by
    have ha : (tripleCharges (sourceA1852 + difference 5 1) (sourceB1852 + difference 1 5) sourceC1852) = raw24224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw24224; decide +kernel
    rw [ha]
    exact (canonical24224 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1852 + difference 5 2) (sourceB1852 + difference 2 5) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1852 + difference 5 2) (sourceB1852 + difference 2 5) sourceC1852) = raw10206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw10206; decide +kernel
    rw [ha]
    exact (canonical10206 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1852 + difference 5 3) (sourceB1852 + difference 3 5) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4624) := by
    have ha : (tripleCharges (sourceA1852 + difference 5 3) (sourceB1852 + difference 3 5) sourceC1852) = raw10202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw10202; decide +kernel
    rw [ha]
    exact (canonical10202 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1852 + difference 5 4) (sourceB1852 + difference 4 5) sourceC1852) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA1852 + difference 5 4) (sourceB1852 + difference 4 5) sourceC1852) = raw24225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1852 sourceB1852 sourceC1852 difference raw24225; decide +kernel
    rw [ha]
    exact (canonical24225 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1852 sourceB1852 sourceC1852
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1852, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1853 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1853 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceC1853 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceForm1853 : Integer.Sparse Master := [(Sum.inr 599, 1), (Sum.inr 600, 2), (Sum.inr 603, 2), (Sum.inr 1126, 2), (Sum.inr 1129, 2), (Sum.inr 1235, 2), (Sum.inr 1236, 4), (Sum.inr 1240, 2), (Sum.inr 1299, 2), (Sum.inr 1300, 2), (Sum.inr 1301, 4), (Sum.inr 2958, 1), (Sum.inr 3100, 2), (Sum.inr 3122, 2)]

theorem sourceEq1853 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1853 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1853 + difference 0 1) (sourceB1853 + difference 1 0) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2958) := by
    have ha : (tripleCharges (sourceA1853 + difference 0 1) (sourceB1853 + difference 1 0) sourceC1853) = raw26659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26659; decide +kernel
    rw [ha]
    exact (canonical26659 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1853 + difference 0 2) (sourceB1853 + difference 2 0) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3122) := by
    have ha : (tripleCharges (sourceA1853 + difference 0 2) (sourceB1853 + difference 2 0) sourceC1853) = raw24234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw24234; decide +kernel
    rw [ha]
    exact (canonical24234 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1853 + difference 0 3) (sourceB1853 + difference 3 0) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3122) := by
    have ha : (tripleCharges (sourceA1853 + difference 0 3) (sourceB1853 + difference 3 0) sourceC1853) = raw26660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26660; decide +kernel
    rw [ha]
    exact (canonical26660 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1853 + difference 0 4) (sourceB1853 + difference 4 0) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA1853 + difference 0 4) (sourceB1853 + difference 4 0) sourceC1853) = raw26661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26661; decide +kernel
    rw [ha]
    exact (canonical26661 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1853 + difference 0 5) (sourceB1853 + difference 5 0) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA1853 + difference 0 5) (sourceB1853 + difference 5 0) sourceC1853) = raw26662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26662; decide +kernel
    rw [ha]
    exact (canonical26662 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1853 + difference 1 0) (sourceB1853 + difference 0 1) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 599) := by
    have ha : (tripleCharges (sourceA1853 + difference 1 0) (sourceB1853 + difference 0 1) sourceC1853) = raw26663 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26663; decide +kernel
    rw [ha]
    exact (canonical26663 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1853 + difference 1 2) (sourceB1853 + difference 2 1) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1853 + difference 1 2) (sourceB1853 + difference 2 1) sourceC1853) = raw24238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw24238; decide +kernel
    rw [ha]
    exact (canonical24238 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1853 + difference 1 3) (sourceB1853 + difference 3 1) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA1853 + difference 1 3) (sourceB1853 + difference 3 1) sourceC1853) = raw26664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26664; decide +kernel
    rw [ha]
    exact (canonical26664 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1853 + difference 1 4) (sourceB1853 + difference 4 1) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA1853 + difference 1 4) (sourceB1853 + difference 4 1) sourceC1853) = raw26665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26665; decide +kernel
    rw [ha]
    exact (canonical26665 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1853 + difference 1 5) (sourceB1853 + difference 5 1) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA1853 + difference 1 5) (sourceB1853 + difference 5 1) sourceC1853) = raw26666 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26666; decide +kernel
    rw [ha]
    exact (canonical26666 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1853 + difference 2 0) (sourceB1853 + difference 0 2) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 600) := by
    have ha : (tripleCharges (sourceA1853 + difference 2 0) (sourceB1853 + difference 0 2) sourceC1853) = raw26667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26667; decide +kernel
    rw [ha]
    exact (canonical26667 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1853 + difference 2 1) (sourceB1853 + difference 1 2) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1126) := by
    have ha : (tripleCharges (sourceA1853 + difference 2 1) (sourceB1853 + difference 1 2) sourceC1853) = raw26668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26668; decide +kernel
    rw [ha]
    exact (canonical26668 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1853 + difference 2 3) (sourceB1853 + difference 3 2) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1300) := by
    have ha : (tripleCharges (sourceA1853 + difference 2 3) (sourceB1853 + difference 3 2) sourceC1853) = raw26669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26669; decide +kernel
    rw [ha]
    exact (canonical26669 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1853 + difference 2 4) (sourceB1853 + difference 4 2) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1853 + difference 2 4) (sourceB1853 + difference 4 2) sourceC1853) = raw26670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26670; decide +kernel
    rw [ha]
    exact (canonical26670 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1853 + difference 2 5) (sourceB1853 + difference 5 2) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1853 + difference 2 5) (sourceB1853 + difference 5 2) sourceC1853) = raw26671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26671; decide +kernel
    rw [ha]
    exact (canonical26671 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1853 + difference 3 0) (sourceB1853 + difference 0 3) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 600) := by
    have ha : (tripleCharges (sourceA1853 + difference 3 0) (sourceB1853 + difference 0 3) sourceC1853) = raw26672 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26672; decide +kernel
    rw [ha]
    exact (canonical26672 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1853 + difference 3 1) (sourceB1853 + difference 1 3) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1126) := by
    have ha : (tripleCharges (sourceA1853 + difference 3 1) (sourceB1853 + difference 1 3) sourceC1853) = raw26673 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26673; decide +kernel
    rw [ha]
    exact (canonical26673 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1853 + difference 3 2) (sourceB1853 + difference 2 3) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1300) := by
    have ha : (tripleCharges (sourceA1853 + difference 3 2) (sourceB1853 + difference 2 3) sourceC1853) = raw24247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw24247; decide +kernel
    rw [ha]
    exact (canonical24247 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1853 + difference 3 4) (sourceB1853 + difference 4 3) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1853 + difference 3 4) (sourceB1853 + difference 4 3) sourceC1853) = raw26674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26674; decide +kernel
    rw [ha]
    exact (canonical26674 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1853 + difference 3 5) (sourceB1853 + difference 5 3) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1853 + difference 3 5) (sourceB1853 + difference 5 3) sourceC1853) = raw26675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26675; decide +kernel
    rw [ha]
    exact (canonical26675 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1853 + difference 4 0) (sourceB1853 + difference 0 4) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 603) := by
    have ha : (tripleCharges (sourceA1853 + difference 4 0) (sourceB1853 + difference 0 4) sourceC1853) = raw26676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26676; decide +kernel
    rw [ha]
    exact (canonical26676 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1853 + difference 4 1) (sourceB1853 + difference 1 4) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1129) := by
    have ha : (tripleCharges (sourceA1853 + difference 4 1) (sourceB1853 + difference 1 4) sourceC1853) = raw26677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26677; decide +kernel
    rw [ha]
    exact (canonical26677 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1853 + difference 4 2) (sourceB1853 + difference 2 4) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1853 + difference 4 2) (sourceB1853 + difference 2 4) sourceC1853) = raw22601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw22601; decide +kernel
    rw [ha]
    exact (canonical22601 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1853 + difference 4 3) (sourceB1853 + difference 3 4) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1853 + difference 4 3) (sourceB1853 + difference 3 4) sourceC1853) = raw22597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw22597; decide +kernel
    rw [ha]
    exact (canonical22597 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1853 + difference 4 5) (sourceB1853 + difference 5 4) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1853 + difference 4 5) (sourceB1853 + difference 5 4) sourceC1853) = raw26678 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw26678; decide +kernel
    rw [ha]
    exact (canonical26678 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1853 + difference 5 0) (sourceB1853 + difference 0 5) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 603) := by
    have ha : (tripleCharges (sourceA1853 + difference 5 0) (sourceB1853 + difference 0 5) sourceC1853) = raw24239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw24239; decide +kernel
    rw [ha]
    exact (canonical24239 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1853 + difference 5 1) (sourceB1853 + difference 1 5) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1129) := by
    have ha : (tripleCharges (sourceA1853 + difference 5 1) (sourceB1853 + difference 1 5) sourceC1853) = raw24240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw24240; decide +kernel
    rw [ha]
    exact (canonical24240 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1853 + difference 5 2) (sourceB1853 + difference 2 5) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1853 + difference 5 2) (sourceB1853 + difference 2 5) sourceC1853) = raw20408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw20408; decide +kernel
    rw [ha]
    exact (canonical20408 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1853 + difference 5 3) (sourceB1853 + difference 3 5) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1301) := by
    have ha : (tripleCharges (sourceA1853 + difference 5 3) (sourceB1853 + difference 3 5) sourceC1853) = raw20404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw20404; decide +kernel
    rw [ha]
    exact (canonical20404 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1853 + difference 5 4) (sourceB1853 + difference 4 5) sourceC1853) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1853 + difference 5 4) (sourceB1853 + difference 4 5) sourceC1853) = raw24241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1853 sourceB1853 sourceC1853 difference raw24241; decide +kernel
    rw [ha]
    exact (canonical24241 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1853 sourceB1853 sourceC1853
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1853, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1854 : Charge := ![2, 0, -1, -1, 0, 0]
def sourceB1854 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceC1854 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceForm1854 : Integer.Sparse Master := [(Sum.inr 4456, 2), (Sum.inr 4495, 4), (Sum.inr 4497, 4), (Sum.inr 4599, 4), (Sum.inr 4601, 4), (Sum.inr 4616, 4), (Sum.inr 4618, 4), (Sum.inr 4622, 4)]

theorem sourceEq1854 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1854 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1854 + difference 0 1) (sourceB1854 + difference 1 0) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1854 + difference 0 1) (sourceB1854 + difference 1 0) sourceC1854) = raw26679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26679; decide +kernel
    rw [ha]
    exact (canonical26679 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1854 + difference 0 2) (sourceB1854 + difference 2 0) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1854 + difference 0 2) (sourceB1854 + difference 2 0) sourceC1854) = raw26680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26680; decide +kernel
    rw [ha]
    exact (canonical26680 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1854 + difference 0 3) (sourceB1854 + difference 3 0) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1854 + difference 0 3) (sourceB1854 + difference 3 0) sourceC1854) = raw26681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26681; decide +kernel
    rw [ha]
    exact (canonical26681 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1854 + difference 0 4) (sourceB1854 + difference 4 0) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1854 + difference 0 4) (sourceB1854 + difference 4 0) sourceC1854) = raw26581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26581; decide +kernel
    rw [ha]
    exact (canonical26581 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1854 + difference 0 5) (sourceB1854 + difference 5 0) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1854 + difference 0 5) (sourceB1854 + difference 5 0) sourceC1854) = raw26682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26682; decide +kernel
    rw [ha]
    exact (canonical26682 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1854 + difference 1 0) (sourceB1854 + difference 0 1) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA1854 + difference 1 0) (sourceB1854 + difference 0 1) sourceC1854) = raw26683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26683; decide +kernel
    rw [ha]
    exact (canonical26683 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1854 + difference 1 2) (sourceB1854 + difference 2 1) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1854 + difference 1 2) (sourceB1854 + difference 2 1) sourceC1854) = raw26684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26684; decide +kernel
    rw [ha]
    exact (canonical26684 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1854 + difference 1 3) (sourceB1854 + difference 3 1) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1854 + difference 1 3) (sourceB1854 + difference 3 1) sourceC1854) = raw26685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26685; decide +kernel
    rw [ha]
    exact (canonical26685 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1854 + difference 1 4) (sourceB1854 + difference 4 1) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1854 + difference 1 4) (sourceB1854 + difference 4 1) sourceC1854) = raw26586 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26586; decide +kernel
    rw [ha]
    exact (canonical26586 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1854 + difference 1 5) (sourceB1854 + difference 5 1) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1854 + difference 1 5) (sourceB1854 + difference 5 1) sourceC1854) = raw26686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26686; decide +kernel
    rw [ha]
    exact (canonical26686 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1854 + difference 2 0) (sourceB1854 + difference 0 2) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1854 + difference 2 0) (sourceB1854 + difference 0 2) sourceC1854) = raw26687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26687; decide +kernel
    rw [ha]
    exact (canonical26687 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1854 + difference 2 1) (sourceB1854 + difference 1 2) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1854 + difference 2 1) (sourceB1854 + difference 1 2) sourceC1854) = raw26688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26688; decide +kernel
    rw [ha]
    exact (canonical26688 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1854 + difference 2 3) (sourceB1854 + difference 3 2) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1854 + difference 2 3) (sourceB1854 + difference 3 2) sourceC1854) = raw26689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26689; decide +kernel
    rw [ha]
    exact (canonical26689 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1854 + difference 2 4) (sourceB1854 + difference 4 2) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1854 + difference 2 4) (sourceB1854 + difference 4 2) sourceC1854) = raw26591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26591; decide +kernel
    rw [ha]
    exact (canonical26591 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1854 + difference 2 5) (sourceB1854 + difference 5 2) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1854 + difference 2 5) (sourceB1854 + difference 5 2) sourceC1854) = raw26690 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26690; decide +kernel
    rw [ha]
    exact (canonical26690 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1854 + difference 3 0) (sourceB1854 + difference 0 3) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4497) := by
    have ha : (tripleCharges (sourceA1854 + difference 3 0) (sourceB1854 + difference 0 3) sourceC1854) = raw26691 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26691; decide +kernel
    rw [ha]
    exact (canonical26691 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1854 + difference 3 1) (sourceB1854 + difference 1 3) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA1854 + difference 3 1) (sourceB1854 + difference 1 3) sourceC1854) = raw26692 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26692; decide +kernel
    rw [ha]
    exact (canonical26692 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1854 + difference 3 2) (sourceB1854 + difference 2 3) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1854 + difference 3 2) (sourceB1854 + difference 2 3) sourceC1854) = raw26693 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26693; decide +kernel
    rw [ha]
    exact (canonical26693 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1854 + difference 3 4) (sourceB1854 + difference 4 3) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1854 + difference 3 4) (sourceB1854 + difference 4 3) sourceC1854) = raw26596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26596; decide +kernel
    rw [ha]
    exact (canonical26596 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1854 + difference 3 5) (sourceB1854 + difference 5 3) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA1854 + difference 3 5) (sourceB1854 + difference 5 3) sourceC1854) = raw26694 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26694; decide +kernel
    rw [ha]
    exact (canonical26694 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1854 + difference 4 0) (sourceB1854 + difference 0 4) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1854 + difference 4 0) (sourceB1854 + difference 0 4) sourceC1854) = raw26695 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26695; decide +kernel
    rw [ha]
    exact (canonical26695 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1854 + difference 4 1) (sourceB1854 + difference 1 4) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1854 + difference 4 1) (sourceB1854 + difference 1 4) sourceC1854) = raw26696 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26696; decide +kernel
    rw [ha]
    exact (canonical26696 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1854 + difference 4 2) (sourceB1854 + difference 2 4) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1854 + difference 4 2) (sourceB1854 + difference 2 4) sourceC1854) = raw26697 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26697; decide +kernel
    rw [ha]
    exact (canonical26697 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1854 + difference 4 3) (sourceB1854 + difference 3 4) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1854 + difference 4 3) (sourceB1854 + difference 3 4) sourceC1854) = raw26698 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26698; decide +kernel
    rw [ha]
    exact (canonical26698 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1854 + difference 4 5) (sourceB1854 + difference 5 4) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1854 + difference 4 5) (sourceB1854 + difference 5 4) sourceC1854) = raw26699 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26699; decide +kernel
    rw [ha]
    exact (canonical26699 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1854 + difference 5 0) (sourceB1854 + difference 0 5) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA1854 + difference 5 0) (sourceB1854 + difference 0 5) sourceC1854) = raw26597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26597; decide +kernel
    rw [ha]
    exact (canonical26597 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1854 + difference 5 1) (sourceB1854 + difference 1 5) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4599) := by
    have ha : (tripleCharges (sourceA1854 + difference 5 1) (sourceB1854 + difference 1 5) sourceC1854) = raw26598 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26598; decide +kernel
    rw [ha]
    exact (canonical26598 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1854 + difference 5 2) (sourceB1854 + difference 2 5) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1854 + difference 5 2) (sourceB1854 + difference 2 5) sourceC1854) = raw26599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26599; decide +kernel
    rw [ha]
    exact (canonical26599 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1854 + difference 5 3) (sourceB1854 + difference 3 5) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA1854 + difference 5 3) (sourceB1854 + difference 3 5) sourceC1854) = raw26600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26600; decide +kernel
    rw [ha]
    exact (canonical26600 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1854 + difference 5 4) (sourceB1854 + difference 4 5) sourceC1854) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4618) := by
    have ha : (tripleCharges (sourceA1854 + difference 5 4) (sourceB1854 + difference 4 5) sourceC1854) = raw26700 := by
      apply Matrix.ext; unfold tripleCharges sourceA1854 sourceB1854 sourceC1854 difference raw26700; decide +kernel
    rw [ha]
    exact (canonical26700 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1854 sourceB1854 sourceC1854
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1854, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1855 : Charge := ![-4, 0, 1, 1, 1, 1]
def sourceB1855 : Charge := ![2, -1, 1, 0, 0, -2]
def sourceC1855 : Charge := ![2, 1, -2, -1, -1, 1]
def sourceForm1855 : Integer.Sparse Master := [(Sum.inr 1228, 1), (Sum.inr 2503, 1), (Sum.inr 2703, 1), (Sum.inr 2718, 2), (Sum.inr 2728, 1), (Sum.inr 4090, -1)]

theorem sourceEq1855 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1855 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1855 + difference 0 0) (sourceB1855 + difference 0 0) sourceC1855) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1228) := by
    have ha : (tripleCharges (sourceA1855 + difference 0 0) (sourceB1855 + difference 0 0) sourceC1855) = raw26701 := by
      apply Matrix.ext; unfold tripleCharges sourceA1855 sourceB1855 sourceC1855 difference raw26701; decide +kernel
    rw [ha]
    exact (canonical26701 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1855 + difference 0 1) (sourceB1855 + difference 1 0) sourceC1855) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2503) := by
    have ha : (tripleCharges (sourceA1855 + difference 0 1) (sourceB1855 + difference 1 0) sourceC1855) = raw26702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1855 sourceB1855 sourceC1855 difference raw26702; decide +kernel
    rw [ha]
    exact (canonical26702 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1855 + difference 0 2) (sourceB1855 + difference 2 0) sourceC1855) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA1855 + difference 0 2) (sourceB1855 + difference 2 0) sourceC1855) = raw26703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1855 sourceB1855 sourceC1855 difference raw26703; decide +kernel
    rw [ha]
    exact (canonical26703 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1855 + difference 0 3) (sourceB1855 + difference 3 0) sourceC1855) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA1855 + difference 0 3) (sourceB1855 + difference 3 0) sourceC1855) = raw26704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1855 sourceB1855 sourceC1855 difference raw26704; decide +kernel
    rw [ha]
    exact (canonical26704 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1855 + difference 0 4) (sourceB1855 + difference 4 0) sourceC1855) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA1855 + difference 0 4) (sourceB1855 + difference 4 0) sourceC1855) = raw26705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1855 sourceB1855 sourceC1855 difference raw26705; decide +kernel
    rw [ha]
    exact (canonical26705 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1855 + difference 0 5) (sourceB1855 + difference 5 0) sourceC1855) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2703) := by
    have ha : (tripleCharges (sourceA1855 + difference 0 5) (sourceB1855 + difference 5 0) sourceC1855) = raw26706 := by
      apply Matrix.ext; unfold tripleCharges sourceA1855 sourceB1855 sourceC1855 difference raw26706; decide +kernel
    rw [ha]
    exact (canonical26706 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1855 + sourceB1855) sourceC1855) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1855 + sourceB1855) sourceC1855) = raw26707 := by
      apply Matrix.ext; unfold doubleCharges sourceA1855 sourceB1855 sourceC1855 raw26707; decide +kernel
    rw [ha]
    exact (canonical26707 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1855 sourceB1855 sourceC1855
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1855, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
