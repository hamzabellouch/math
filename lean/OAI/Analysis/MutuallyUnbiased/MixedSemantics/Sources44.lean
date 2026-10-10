import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical156
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical157
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical159
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical162
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical166
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical168
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical169
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical171
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical172
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical173
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical174

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1408 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1408 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC1408 : Charge := ![4, -2, 0, 0, -1, -1]
def sourceForm1408 : Integer.Sparse Master := [(Sum.inr 824, 2), (Sum.inr 828, 1), (Sum.inr 831, 1), (Sum.inr 856, 1), (Sum.inr 1739, 1), (Sum.inr 4069, -1)]

theorem sourceEq1408 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1408 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1408 + difference 0 5) (sourceB1408 + difference 5 0) sourceC1408) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1408 + difference 0 5) (sourceB1408 + difference 5 0) sourceC1408) = raw22028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1408 sourceB1408 sourceC1408 difference raw22028; decide +kernel
    rw [ha]
    exact (canonical22028 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1408 + difference 1 5) (sourceB1408 + difference 5 1) sourceC1408) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 856) := by
    have ha : (tripleCharges (sourceA1408 + difference 1 5) (sourceB1408 + difference 5 1) sourceC1408) = raw22034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1408 sourceB1408 sourceC1408 difference raw22034; decide +kernel
    rw [ha]
    exact (canonical22034 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1408 + difference 2 5) (sourceB1408 + difference 5 2) sourceC1408) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 824) := by
    have ha : (tripleCharges (sourceA1408 + difference 2 5) (sourceB1408 + difference 5 2) sourceC1408) = raw22035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1408 sourceB1408 sourceC1408 difference raw22035; decide +kernel
    rw [ha]
    exact (canonical22035 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1408 + difference 3 5) (sourceB1408 + difference 5 3) sourceC1408) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 824) := by
    have ha : (tripleCharges (sourceA1408 + difference 3 5) (sourceB1408 + difference 5 3) sourceC1408) = raw22036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1408 sourceB1408 sourceC1408 difference raw22036; decide +kernel
    rw [ha]
    exact (canonical22036 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1408 + difference 4 5) (sourceB1408 + difference 5 4) sourceC1408) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 831) := by
    have ha : (tripleCharges (sourceA1408 + difference 4 5) (sourceB1408 + difference 5 4) sourceC1408) = raw22037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1408 sourceB1408 sourceC1408 difference raw22037; decide +kernel
    rw [ha]
    exact (canonical22037 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1408 + difference 5 5) (sourceB1408 + difference 5 5) sourceC1408) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 828) := by
    have ha : (tripleCharges (sourceA1408 + difference 5 5) (sourceB1408 + difference 5 5) sourceC1408) = raw22023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1408 sourceB1408 sourceC1408 difference raw22023; decide +kernel
    rw [ha]
    exact (canonical22023 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1408 + sourceB1408) sourceC1408) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1408 + sourceB1408) sourceC1408) = raw22029 := by
      apply Matrix.ext; unfold doubleCharges sourceA1408 sourceB1408 sourceC1408 raw22029; decide +kernel
    rw [ha]
    exact (canonical22029 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1408 sourceB1408 sourceC1408
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1408, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1409 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceB1409 : Charge := ![4, -2, 0, 0, -1, -1]
def sourceC1409 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1409 : Integer.Sparse Master := [(Sum.inr 560, 1), (Sum.inr 721, 2), (Sum.inr 815, 1), (Sum.inr 851, 1), (Sum.inr 857, 1), (Sum.inr 4070, -1)]

theorem sourceEq1409 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1409 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1409 + difference 5 0) (sourceB1409 + difference 0 5) sourceC1409) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 560) := by
    have ha : (tripleCharges (sourceA1409 + difference 5 0) (sourceB1409 + difference 0 5) sourceC1409) = raw22038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1409 sourceB1409 sourceC1409 difference raw22038; decide +kernel
    rw [ha]
    exact (canonical22038 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1409 + difference 5 1) (sourceB1409 + difference 1 5) sourceC1409) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 851) := by
    have ha : (tripleCharges (sourceA1409 + difference 5 1) (sourceB1409 + difference 1 5) sourceC1409) = raw21372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1409 sourceB1409 sourceC1409 difference raw21372; decide +kernel
    rw [ha]
    exact (canonical21372 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1409 + difference 5 2) (sourceB1409 + difference 2 5) sourceC1409) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 721) := by
    have ha : (tripleCharges (sourceA1409 + difference 5 2) (sourceB1409 + difference 2 5) sourceC1409) = raw22039 := by
      apply Matrix.ext; unfold tripleCharges sourceA1409 sourceB1409 sourceC1409 difference raw22039; decide +kernel
    rw [ha]
    exact (canonical22039 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1409 + difference 5 3) (sourceB1409 + difference 3 5) sourceC1409) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 721) := by
    have ha : (tripleCharges (sourceA1409 + difference 5 3) (sourceB1409 + difference 3 5) sourceC1409) = raw21609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1409 sourceB1409 sourceC1409 difference raw21609; decide +kernel
    rw [ha]
    exact (canonical21609 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1409 + difference 5 4) (sourceB1409 + difference 4 5) sourceC1409) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 815) := by
    have ha : (tripleCharges (sourceA1409 + difference 5 4) (sourceB1409 + difference 4 5) sourceC1409) = raw22040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1409 sourceB1409 sourceC1409 difference raw22040; decide +kernel
    rw [ha]
    exact (canonical22040 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1409 + difference 5 5) (sourceB1409 + difference 5 5) sourceC1409) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 857) := by
    have ha : (tripleCharges (sourceA1409 + difference 5 5) (sourceB1409 + difference 5 5) sourceC1409) = raw21368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1409 sourceB1409 sourceC1409 difference raw21368; decide +kernel
    rw [ha]
    exact (canonical21368 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1409 + sourceB1409) sourceC1409) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1409 + sourceB1409) sourceC1409) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1409 sourceB1409 sourceC1409 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1409 sourceB1409 sourceC1409
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1409, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1410 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1410 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC1410 : Charge := ![4, -2, 0, 0, 0, -2]
def sourceForm1410 : Integer.Sparse Master := [(Sum.inr 826, 1), (Sum.inr 1608, 2), (Sum.inr 1657, 1), (Sum.inr 1738, 1), (Sum.inr 1741, 1), (Sum.inr 4071, -1)]

theorem sourceEq1410 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1410 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1410 + difference 0 0) (sourceB1410 + difference 0 0) sourceC1410) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 826) := by
    have ha : (tripleCharges (sourceA1410 + difference 0 0) (sourceB1410 + difference 0 0) sourceC1410) = raw22041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1410 sourceB1410 sourceC1410 difference raw22041; decide +kernel
    rw [ha]
    exact (canonical22041 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1410 + difference 0 1) (sourceB1410 + difference 1 0) sourceC1410) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1657) := by
    have ha : (tripleCharges (sourceA1410 + difference 0 1) (sourceB1410 + difference 1 0) sourceC1410) = raw22042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1410 sourceB1410 sourceC1410 difference raw22042; decide +kernel
    rw [ha]
    exact (canonical22042 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1410 + difference 0 2) (sourceB1410 + difference 2 0) sourceC1410) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1608) := by
    have ha : (tripleCharges (sourceA1410 + difference 0 2) (sourceB1410 + difference 2 0) sourceC1410) = raw22043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1410 sourceB1410 sourceC1410 difference raw22043; decide +kernel
    rw [ha]
    exact (canonical22043 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1410 + difference 0 3) (sourceB1410 + difference 3 0) sourceC1410) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1608) := by
    have ha : (tripleCharges (sourceA1410 + difference 0 3) (sourceB1410 + difference 3 0) sourceC1410) = raw22044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1410 sourceB1410 sourceC1410 difference raw22044; decide +kernel
    rw [ha]
    exact (canonical22044 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1410 + difference 0 4) (sourceB1410 + difference 4 0) sourceC1410) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1741) := by
    have ha : (tripleCharges (sourceA1410 + difference 0 4) (sourceB1410 + difference 4 0) sourceC1410) = raw22045 := by
      apply Matrix.ext; unfold tripleCharges sourceA1410 sourceB1410 sourceC1410 difference raw22045; decide +kernel
    rw [ha]
    exact (canonical22045 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1410 + difference 0 5) (sourceB1410 + difference 5 0) sourceC1410) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1410 + difference 0 5) (sourceB1410 + difference 5 0) sourceC1410) = raw22046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1410 sourceB1410 sourceC1410 difference raw22046; decide +kernel
    rw [ha]
    exact (canonical22046 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1410 + sourceB1410) sourceC1410) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1410 + sourceB1410) sourceC1410) = raw22047 := by
      apply Matrix.ext; unfold doubleCharges sourceA1410 sourceB1410 sourceC1410 raw22047; decide +kernel
    rw [ha]
    exact (canonical22047 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1410 sourceB1410 sourceC1410
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1410, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1411 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1411 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC1411 : Charge := ![4, -2, 0, 0, 0, -2]
def sourceForm1411 : Integer.Sparse Master := [(Sum.inr 555, 1), (Sum.inr 715, 2), (Sum.inr 826, 1), (Sum.inr 852, 1), (Sum.inr 859, 1), (Sum.inr 4071, -1)]

theorem sourceEq1411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1411 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1411 + difference 1 0) (sourceB1411 + difference 0 1) sourceC1411) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 555) := by
    have ha : (tripleCharges (sourceA1411 + difference 1 0) (sourceB1411 + difference 0 1) sourceC1411) = raw22048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1411 sourceB1411 sourceC1411 difference raw22048; decide +kernel
    rw [ha]
    exact (canonical22048 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1411 + difference 1 1) (sourceB1411 + difference 1 1) sourceC1411) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 826) := by
    have ha : (tripleCharges (sourceA1411 + difference 1 1) (sourceB1411 + difference 1 1) sourceC1411) = raw22041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1411 sourceB1411 sourceC1411 difference raw22041; decide +kernel
    rw [ha]
    exact (canonical22041 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1411 + difference 1 2) (sourceB1411 + difference 2 1) sourceC1411) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 715) := by
    have ha : (tripleCharges (sourceA1411 + difference 1 2) (sourceB1411 + difference 2 1) sourceC1411) = raw22049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1411 sourceB1411 sourceC1411 difference raw22049; decide +kernel
    rw [ha]
    exact (canonical22049 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1411 + difference 1 3) (sourceB1411 + difference 3 1) sourceC1411) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 715) := by
    have ha : (tripleCharges (sourceA1411 + difference 1 3) (sourceB1411 + difference 3 1) sourceC1411) = raw22050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1411 sourceB1411 sourceC1411 difference raw22050; decide +kernel
    rw [ha]
    exact (canonical22050 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1411 + difference 1 4) (sourceB1411 + difference 4 1) sourceC1411) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 859) := by
    have ha : (tripleCharges (sourceA1411 + difference 1 4) (sourceB1411 + difference 4 1) sourceC1411) = raw22051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1411 sourceB1411 sourceC1411 difference raw22051; decide +kernel
    rw [ha]
    exact (canonical22051 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1411 + difference 1 5) (sourceB1411 + difference 5 1) sourceC1411) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 852) := by
    have ha : (tripleCharges (sourceA1411 + difference 1 5) (sourceB1411 + difference 5 1) sourceC1411) = raw22052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1411 sourceB1411 sourceC1411 difference raw22052; decide +kernel
    rw [ha]
    exact (canonical22052 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1411 + sourceB1411) sourceC1411) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1411 + sourceB1411) sourceC1411) = raw22047 := by
      apply Matrix.ext; unfold doubleCharges sourceA1411 sourceB1411 sourceC1411 raw22047; decide +kernel
    rw [ha]
    exact (canonical22047 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1411 sourceB1411 sourceC1411
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1411, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1412 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1412 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC1412 : Charge := ![4, -2, 0, 0, 0, -2]
def sourceForm1412 : Integer.Sparse Master := [(Sum.inr 823, 2), (Sum.inr 826, 1), (Sum.inr 830, 1), (Sum.inr 852, 1), (Sum.inr 1738, 1), (Sum.inr 4071, -1)]

theorem sourceEq1412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1412 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1412 + difference 0 5) (sourceB1412 + difference 5 0) sourceC1412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1738) := by
    have ha : (tripleCharges (sourceA1412 + difference 0 5) (sourceB1412 + difference 5 0) sourceC1412) = raw22046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1412 sourceB1412 sourceC1412 difference raw22046; decide +kernel
    rw [ha]
    exact (canonical22046 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1412 + difference 1 5) (sourceB1412 + difference 5 1) sourceC1412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 852) := by
    have ha : (tripleCharges (sourceA1412 + difference 1 5) (sourceB1412 + difference 5 1) sourceC1412) = raw22052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1412 sourceB1412 sourceC1412 difference raw22052; decide +kernel
    rw [ha]
    exact (canonical22052 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1412 + difference 2 5) (sourceB1412 + difference 5 2) sourceC1412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 823) := by
    have ha : (tripleCharges (sourceA1412 + difference 2 5) (sourceB1412 + difference 5 2) sourceC1412) = raw22053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1412 sourceB1412 sourceC1412 difference raw22053; decide +kernel
    rw [ha]
    exact (canonical22053 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1412 + difference 3 5) (sourceB1412 + difference 5 3) sourceC1412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 823) := by
    have ha : (tripleCharges (sourceA1412 + difference 3 5) (sourceB1412 + difference 5 3) sourceC1412) = raw22054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1412 sourceB1412 sourceC1412 difference raw22054; decide +kernel
    rw [ha]
    exact (canonical22054 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1412 + difference 4 5) (sourceB1412 + difference 5 4) sourceC1412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 830) := by
    have ha : (tripleCharges (sourceA1412 + difference 4 5) (sourceB1412 + difference 5 4) sourceC1412) = raw22055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1412 sourceB1412 sourceC1412 difference raw22055; decide +kernel
    rw [ha]
    exact (canonical22055 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1412 + difference 5 5) (sourceB1412 + difference 5 5) sourceC1412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 826) := by
    have ha : (tripleCharges (sourceA1412 + difference 5 5) (sourceB1412 + difference 5 5) sourceC1412) = raw22041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1412 sourceB1412 sourceC1412 difference raw22041; decide +kernel
    rw [ha]
    exact (canonical22041 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1412 + sourceB1412) sourceC1412) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1412 + sourceB1412) sourceC1412) = raw22047 := by
      apply Matrix.ext; unfold doubleCharges sourceA1412 sourceB1412 sourceC1412 raw22047; decide +kernel
    rw [ha]
    exact (canonical22047 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1412 sourceB1412 sourceC1412
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1412, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1413 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceB1413 : Charge := ![4, -2, 0, 0, 0, -2]
def sourceC1413 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1413 : Integer.Sparse Master := [(Sum.inr 546, 1), (Sum.inr 706, 2), (Sum.inr 741, 1), (Sum.inr 809, 1), (Sum.inr 815, 1), (Sum.inr 4070, -1)]

theorem sourceEq1413 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1413 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1413 + difference 5 0) (sourceB1413 + difference 0 5) sourceC1413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 546) := by
    have ha : (tripleCharges (sourceA1413 + difference 5 0) (sourceB1413 + difference 0 5) sourceC1413) = raw22056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1413 sourceB1413 sourceC1413 difference raw22056; decide +kernel
    rw [ha]
    exact (canonical22056 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1413 + difference 5 1) (sourceB1413 + difference 1 5) sourceC1413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1413 + difference 5 1) (sourceB1413 + difference 1 5) sourceC1413) = raw21578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1413 sourceB1413 sourceC1413 difference raw21578; decide +kernel
    rw [ha]
    exact (canonical21578 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1413 + difference 5 2) (sourceB1413 + difference 2 5) sourceC1413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 706) := by
    have ha : (tripleCharges (sourceA1413 + difference 5 2) (sourceB1413 + difference 2 5) sourceC1413) = raw22057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1413 sourceB1413 sourceC1413 difference raw22057; decide +kernel
    rw [ha]
    exact (canonical22057 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1413 + difference 5 3) (sourceB1413 + difference 3 5) sourceC1413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 706) := by
    have ha : (tripleCharges (sourceA1413 + difference 5 3) (sourceB1413 + difference 3 5) sourceC1413) = raw21631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1413 sourceB1413 sourceC1413 difference raw21631; decide +kernel
    rw [ha]
    exact (canonical21631 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1413 + difference 5 4) (sourceB1413 + difference 4 5) sourceC1413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 741) := by
    have ha : (tripleCharges (sourceA1413 + difference 5 4) (sourceB1413 + difference 4 5) sourceC1413) = raw21575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1413 sourceB1413 sourceC1413 difference raw21575; decide +kernel
    rw [ha]
    exact (canonical21575 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1413 + difference 5 5) (sourceB1413 + difference 5 5) sourceC1413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 815) := by
    have ha : (tripleCharges (sourceA1413 + difference 5 5) (sourceB1413 + difference 5 5) sourceC1413) = raw22040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1413 sourceB1413 sourceC1413 difference raw22040; decide +kernel
    rw [ha]
    exact (canonical22040 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1413 + sourceB1413) sourceC1413) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1413 + sourceB1413) sourceC1413) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1413 sourceB1413 sourceC1413 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1413 sourceB1413 sourceC1413
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1413, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1414 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1414 : Charge := ![0, 1, 1, 1, 0, -3]
def sourceC1414 : Charge := ![4, -1, -1, -1, -1, 0]
def sourceForm1414 : Integer.Sparse Master := [(Sum.inr 777, 1), (Sum.inr 778, 1), (Sum.inr 786, 3), (Sum.inr 1699, 1), (Sum.inr 4068, -1)]

theorem sourceEq1414 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1414 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1414 + difference 0 5) (sourceB1414 + difference 5 0) sourceC1414) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA1414 + difference 0 5) (sourceB1414 + difference 5 0) sourceC1414) = raw22058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1414 sourceB1414 sourceC1414 difference raw22058; decide +kernel
    rw [ha]
    exact (canonical22058 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1414 + difference 1 5) (sourceB1414 + difference 5 1) sourceC1414) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 786) := by
    have ha : (tripleCharges (sourceA1414 + difference 1 5) (sourceB1414 + difference 5 1) sourceC1414) = raw22059 := by
      apply Matrix.ext; unfold tripleCharges sourceA1414 sourceB1414 sourceC1414 difference raw22059; decide +kernel
    rw [ha]
    exact (canonical22059 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1414 + difference 2 5) (sourceB1414 + difference 5 2) sourceC1414) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 786) := by
    have ha : (tripleCharges (sourceA1414 + difference 2 5) (sourceB1414 + difference 5 2) sourceC1414) = raw22060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1414 sourceB1414 sourceC1414 difference raw22060; decide +kernel
    rw [ha]
    exact (canonical22060 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1414 + difference 3 5) (sourceB1414 + difference 5 3) sourceC1414) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 786) := by
    have ha : (tripleCharges (sourceA1414 + difference 3 5) (sourceB1414 + difference 5 3) sourceC1414) = raw22061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1414 sourceB1414 sourceC1414 difference raw22061; decide +kernel
    rw [ha]
    exact (canonical22061 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1414 + difference 4 5) (sourceB1414 + difference 5 4) sourceC1414) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 778) := by
    have ha : (tripleCharges (sourceA1414 + difference 4 5) (sourceB1414 + difference 5 4) sourceC1414) = raw22062 := by
      apply Matrix.ext; unfold tripleCharges sourceA1414 sourceB1414 sourceC1414 difference raw22062; decide +kernel
    rw [ha]
    exact (canonical22062 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1414 + difference 5 5) (sourceB1414 + difference 5 5) sourceC1414) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 777) := by
    have ha : (tripleCharges (sourceA1414 + difference 5 5) (sourceB1414 + difference 5 5) sourceC1414) = raw22063 := by
      apply Matrix.ext; unfold tripleCharges sourceA1414 sourceB1414 sourceC1414 difference raw22063; decide +kernel
    rw [ha]
    exact (canonical22063 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1414 + sourceB1414) sourceC1414) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1414 + sourceB1414) sourceC1414) = raw22064 := by
      apply Matrix.ext; unfold doubleCharges sourceA1414 sourceB1414 sourceC1414 raw22064; decide +kernel
    rw [ha]
    exact (canonical22064 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1414 sourceB1414 sourceC1414
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1414, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1415 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1415 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC1415 : Charge := ![4, -1, -1, -1, 0, -1]
def sourceForm1415 : Integer.Sparse Master := [(Sum.inr 776, 1), (Sum.inr 778, 1), (Sum.inr 783, 3), (Sum.inr 1698, 1), (Sum.inr 4068, -1)]

theorem sourceEq1415 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1415 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1415 + difference 0 5) (sourceB1415 + difference 5 0) sourceC1415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1698) := by
    have ha : (tripleCharges (sourceA1415 + difference 0 5) (sourceB1415 + difference 5 0) sourceC1415) = raw22065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1415 sourceB1415 sourceC1415 difference raw22065; decide +kernel
    rw [ha]
    exact (canonical22065 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1415 + difference 1 5) (sourceB1415 + difference 5 1) sourceC1415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1415 + difference 1 5) (sourceB1415 + difference 5 1) sourceC1415) = raw22066 := by
      apply Matrix.ext; unfold tripleCharges sourceA1415 sourceB1415 sourceC1415 difference raw22066; decide +kernel
    rw [ha]
    exact (canonical22066 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1415 + difference 2 5) (sourceB1415 + difference 5 2) sourceC1415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1415 + difference 2 5) (sourceB1415 + difference 5 2) sourceC1415) = raw22067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1415 sourceB1415 sourceC1415 difference raw22067; decide +kernel
    rw [ha]
    exact (canonical22067 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1415 + difference 3 5) (sourceB1415 + difference 5 3) sourceC1415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1415 + difference 3 5) (sourceB1415 + difference 5 3) sourceC1415) = raw22068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1415 sourceB1415 sourceC1415 difference raw22068; decide +kernel
    rw [ha]
    exact (canonical22068 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1415 + difference 4 5) (sourceB1415 + difference 5 4) sourceC1415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 778) := by
    have ha : (tripleCharges (sourceA1415 + difference 4 5) (sourceB1415 + difference 5 4) sourceC1415) = raw22069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1415 sourceB1415 sourceC1415 difference raw22069; decide +kernel
    rw [ha]
    exact (canonical22069 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1415 + difference 5 5) (sourceB1415 + difference 5 5) sourceC1415) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 776) := by
    have ha : (tripleCharges (sourceA1415 + difference 5 5) (sourceB1415 + difference 5 5) sourceC1415) = raw22070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1415 sourceB1415 sourceC1415 difference raw22070; decide +kernel
    rw [ha]
    exact (canonical22070 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1415 + sourceB1415) sourceC1415) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1415 + sourceB1415) sourceC1415) = raw22071 := by
      apply Matrix.ext; unfold doubleCharges sourceA1415 sourceB1415 sourceC1415 raw22071; decide +kernel
    rw [ha]
    exact (canonical22071 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1415 sourceB1415 sourceC1415
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1415, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1416 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1416 : Charge := ![0, 1, 1, 0, 1, -3]
def sourceC1416 : Charge := ![4, -1, -1, 0, -2, 0]
def sourceForm1416 : Integer.Sparse Master := [(Sum.inr 784, 1), (Sum.inr 788, 1), (Sum.inr 789, 1), (Sum.inr 811, 2), (Sum.inr 1709, 1), (Sum.inr 4069, -1)]

theorem sourceEq1416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1416 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1416 + difference 0 5) (sourceB1416 + difference 5 0) sourceC1416) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA1416 + difference 0 5) (sourceB1416 + difference 5 0) sourceC1416) = raw22072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1416 sourceB1416 sourceC1416 difference raw22072; decide +kernel
    rw [ha]
    exact (canonical22072 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1416 + difference 1 5) (sourceB1416 + difference 5 1) sourceC1416) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 811) := by
    have ha : (tripleCharges (sourceA1416 + difference 1 5) (sourceB1416 + difference 5 1) sourceC1416) = raw22073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1416 sourceB1416 sourceC1416 difference raw22073; decide +kernel
    rw [ha]
    exact (canonical22073 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1416 + difference 2 5) (sourceB1416 + difference 5 2) sourceC1416) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 811) := by
    have ha : (tripleCharges (sourceA1416 + difference 2 5) (sourceB1416 + difference 5 2) sourceC1416) = raw22074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1416 sourceB1416 sourceC1416 difference raw22074; decide +kernel
    rw [ha]
    exact (canonical22074 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1416 + difference 3 5) (sourceB1416 + difference 5 3) sourceC1416) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 784) := by
    have ha : (tripleCharges (sourceA1416 + difference 3 5) (sourceB1416 + difference 5 3) sourceC1416) = raw22075 := by
      apply Matrix.ext; unfold tripleCharges sourceA1416 sourceB1416 sourceC1416 difference raw22075; decide +kernel
    rw [ha]
    exact (canonical22075 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1416 + difference 4 5) (sourceB1416 + difference 5 4) sourceC1416) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 789) := by
    have ha : (tripleCharges (sourceA1416 + difference 4 5) (sourceB1416 + difference 5 4) sourceC1416) = raw22076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1416 sourceB1416 sourceC1416 difference raw22076; decide +kernel
    rw [ha]
    exact (canonical22076 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1416 + difference 5 5) (sourceB1416 + difference 5 5) sourceC1416) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 788) := by
    have ha : (tripleCharges (sourceA1416 + difference 5 5) (sourceB1416 + difference 5 5) sourceC1416) = raw22077 := by
      apply Matrix.ext; unfold tripleCharges sourceA1416 sourceB1416 sourceC1416 difference raw22077; decide +kernel
    rw [ha]
    exact (canonical22077 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1416 + sourceB1416) sourceC1416) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1416 + sourceB1416) sourceC1416) = raw22078 := by
      apply Matrix.ext; unfold doubleCharges sourceA1416 sourceB1416 sourceC1416 raw22078; decide +kernel
    rw [ha]
    exact (canonical22078 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1416 sourceB1416 sourceC1416
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1416, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1417 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1417 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1417 : Charge := ![4, -1, -1, 0, -1, -1]
def sourceForm1417 : Integer.Sparse Master := [(Sum.inr 787, 1), (Sum.inr 1593, 1), (Sum.inr 1639, 2), (Sum.inr 1700, 1), (Sum.inr 1708, 1), (Sum.inr 4068, -1)]

theorem sourceEq1417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1417 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1417 + difference 0 0) (sourceB1417 + difference 0 0) sourceC1417) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 787) := by
    have ha : (tripleCharges (sourceA1417 + difference 0 0) (sourceB1417 + difference 0 0) sourceC1417) = raw22079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1417 sourceB1417 sourceC1417 difference raw22079; decide +kernel
    rw [ha]
    exact (canonical22079 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1417 + difference 0 1) (sourceB1417 + difference 1 0) sourceC1417) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1639) := by
    have ha : (tripleCharges (sourceA1417 + difference 0 1) (sourceB1417 + difference 1 0) sourceC1417) = raw22080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1417 sourceB1417 sourceC1417 difference raw22080; decide +kernel
    rw [ha]
    exact (canonical22080 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1417 + difference 0 2) (sourceB1417 + difference 2 0) sourceC1417) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1639) := by
    have ha : (tripleCharges (sourceA1417 + difference 0 2) (sourceB1417 + difference 2 0) sourceC1417) = raw22081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1417 sourceB1417 sourceC1417 difference raw22081; decide +kernel
    rw [ha]
    exact (canonical22081 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1417 + difference 0 3) (sourceB1417 + difference 3 0) sourceC1417) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1593) := by
    have ha : (tripleCharges (sourceA1417 + difference 0 3) (sourceB1417 + difference 3 0) sourceC1417) = raw22082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1417 sourceB1417 sourceC1417 difference raw22082; decide +kernel
    rw [ha]
    exact (canonical22082 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1417 + difference 0 4) (sourceB1417 + difference 4 0) sourceC1417) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1700) := by
    have ha : (tripleCharges (sourceA1417 + difference 0 4) (sourceB1417 + difference 4 0) sourceC1417) = raw22083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1417 sourceB1417 sourceC1417 difference raw22083; decide +kernel
    rw [ha]
    exact (canonical22083 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1417 + difference 0 5) (sourceB1417 + difference 5 0) sourceC1417) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1417 + difference 0 5) (sourceB1417 + difference 5 0) sourceC1417) = raw22084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1417 sourceB1417 sourceC1417 difference raw22084; decide +kernel
    rw [ha]
    exact (canonical22084 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1417 + sourceB1417) sourceC1417) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1417 + sourceB1417) sourceC1417) = raw22085 := by
      apply Matrix.ext; unfold doubleCharges sourceA1417 sourceB1417 sourceC1417 raw22085; decide +kernel
    rw [ha]
    exact (canonical22085 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1417 sourceB1417 sourceC1417
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1417, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1418 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1418 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1418 : Charge := ![4, -1, -1, 0, -1, -1]
def sourceForm1418 : Integer.Sparse Master := [(Sum.inr 542, 1), (Sum.inr 702, 1), (Sum.inr 737, 1), (Sum.inr 787, 2), (Sum.inr 810, 1), (Sum.inr 4068, -1)]

theorem sourceEq1418 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1418 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1418 + difference 1 0) (sourceB1418 + difference 0 1) sourceC1418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 542) := by
    have ha : (tripleCharges (sourceA1418 + difference 1 0) (sourceB1418 + difference 0 1) sourceC1418) = raw22086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1418 sourceB1418 sourceC1418 difference raw22086; decide +kernel
    rw [ha]
    exact (canonical22086 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1418 + difference 1 1) (sourceB1418 + difference 1 1) sourceC1418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 787) := by
    have ha : (tripleCharges (sourceA1418 + difference 1 1) (sourceB1418 + difference 1 1) sourceC1418) = raw22079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1418 sourceB1418 sourceC1418 difference raw22079; decide +kernel
    rw [ha]
    exact (canonical22079 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1418 + difference 1 2) (sourceB1418 + difference 2 1) sourceC1418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 737) := by
    have ha : (tripleCharges (sourceA1418 + difference 1 2) (sourceB1418 + difference 2 1) sourceC1418) = raw22087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1418 sourceB1418 sourceC1418 difference raw22087; decide +kernel
    rw [ha]
    exact (canonical22087 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1418 + difference 1 3) (sourceB1418 + difference 3 1) sourceC1418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 702) := by
    have ha : (tripleCharges (sourceA1418 + difference 1 3) (sourceB1418 + difference 3 1) sourceC1418) = raw22088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1418 sourceB1418 sourceC1418 difference raw22088; decide +kernel
    rw [ha]
    exact (canonical22088 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1418 + difference 1 4) (sourceB1418 + difference 4 1) sourceC1418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 787) := by
    have ha : (tripleCharges (sourceA1418 + difference 1 4) (sourceB1418 + difference 4 1) sourceC1418) = raw22089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1418 sourceB1418 sourceC1418 difference raw22089; decide +kernel
    rw [ha]
    exact (canonical22089 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1418 + difference 1 5) (sourceB1418 + difference 5 1) sourceC1418) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 810) := by
    have ha : (tripleCharges (sourceA1418 + difference 1 5) (sourceB1418 + difference 5 1) sourceC1418) = raw22090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1418 sourceB1418 sourceC1418 difference raw22090; decide +kernel
    rw [ha]
    exact (canonical22090 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1418 + sourceB1418) sourceC1418) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1418 + sourceB1418) sourceC1418) = raw22085 := by
      apply Matrix.ext; unfold doubleCharges sourceA1418 sourceB1418 sourceC1418 raw22085; decide +kernel
    rw [ha]
    exact (canonical22085 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1418 sourceB1418 sourceC1418
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1418, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1419 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1419 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1419 : Charge := ![4, -1, -1, 0, -1, -1]
def sourceForm1419 : Integer.Sparse Master := [(Sum.inr 783, 1), (Sum.inr 787, 1), (Sum.inr 790, 1), (Sum.inr 810, 2), (Sum.inr 1708, 1), (Sum.inr 4068, -1)]

theorem sourceEq1419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1419 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1419 + difference 0 5) (sourceB1419 + difference 5 0) sourceC1419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1419 + difference 0 5) (sourceB1419 + difference 5 0) sourceC1419) = raw22084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1419 sourceB1419 sourceC1419 difference raw22084; decide +kernel
    rw [ha]
    exact (canonical22084 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1419 + difference 1 5) (sourceB1419 + difference 5 1) sourceC1419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 810) := by
    have ha : (tripleCharges (sourceA1419 + difference 1 5) (sourceB1419 + difference 5 1) sourceC1419) = raw22090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1419 sourceB1419 sourceC1419 difference raw22090; decide +kernel
    rw [ha]
    exact (canonical22090 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1419 + difference 2 5) (sourceB1419 + difference 5 2) sourceC1419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 810) := by
    have ha : (tripleCharges (sourceA1419 + difference 2 5) (sourceB1419 + difference 5 2) sourceC1419) = raw22091 := by
      apply Matrix.ext; unfold tripleCharges sourceA1419 sourceB1419 sourceC1419 difference raw22091; decide +kernel
    rw [ha]
    exact (canonical22091 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1419 + difference 3 5) (sourceB1419 + difference 5 3) sourceC1419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 783) := by
    have ha : (tripleCharges (sourceA1419 + difference 3 5) (sourceB1419 + difference 5 3) sourceC1419) = raw22092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1419 sourceB1419 sourceC1419 difference raw22092; decide +kernel
    rw [ha]
    exact (canonical22092 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1419 + difference 4 5) (sourceB1419 + difference 5 4) sourceC1419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 790) := by
    have ha : (tripleCharges (sourceA1419 + difference 4 5) (sourceB1419 + difference 5 4) sourceC1419) = raw22093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1419 sourceB1419 sourceC1419 difference raw22093; decide +kernel
    rw [ha]
    exact (canonical22093 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1419 + difference 5 5) (sourceB1419 + difference 5 5) sourceC1419) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 787) := by
    have ha : (tripleCharges (sourceA1419 + difference 5 5) (sourceB1419 + difference 5 5) sourceC1419) = raw22079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1419 sourceB1419 sourceC1419 difference raw22079; decide +kernel
    rw [ha]
    exact (canonical22079 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1419 + sourceB1419) sourceC1419) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1419 + sourceB1419) sourceC1419) = raw22085 := by
      apply Matrix.ext; unfold doubleCharges sourceA1419 sourceB1419 sourceC1419 raw22085; decide +kernel
    rw [ha]
    exact (canonical22085 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1419 sourceB1419 sourceC1419
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1419, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1420 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB1420 : Charge := ![4, -1, -1, 0, -1, -1]
def sourceC1420 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1420 : Integer.Sparse Master := [(Sum.inr 551, 1), (Sum.inr 709, 1), (Sum.inr 804, 1), (Sum.inr 847, 1), (Sum.inr 851, 2), (Sum.inr 4070, -1)]

theorem sourceEq1420 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1420 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1420 + difference 5 0) (sourceB1420 + difference 0 5) sourceC1420) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 551) := by
    have ha : (tripleCharges (sourceA1420 + difference 5 0) (sourceB1420 + difference 0 5) sourceC1420) = raw22094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1420 sourceB1420 sourceC1420 difference raw22094; decide +kernel
    rw [ha]
    exact (canonical22094 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1420 + difference 5 1) (sourceB1420 + difference 1 5) sourceC1420) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 851) := by
    have ha : (tripleCharges (sourceA1420 + difference 5 1) (sourceB1420 + difference 1 5) sourceC1420) = raw22095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1420 sourceB1420 sourceC1420 difference raw22095; decide +kernel
    rw [ha]
    exact (canonical22095 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1420 + difference 5 2) (sourceB1420 + difference 2 5) sourceC1420) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 851) := by
    have ha : (tripleCharges (sourceA1420 + difference 5 2) (sourceB1420 + difference 2 5) sourceC1420) = raw21372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1420 sourceB1420 sourceC1420 difference raw21372; decide +kernel
    rw [ha]
    exact (canonical21372 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1420 + difference 5 3) (sourceB1420 + difference 3 5) sourceC1420) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 709) := by
    have ha : (tripleCharges (sourceA1420 + difference 5 3) (sourceB1420 + difference 3 5) sourceC1420) = raw21610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1420 sourceB1420 sourceC1420 difference raw21610; decide +kernel
    rw [ha]
    exact (canonical21610 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1420 + difference 5 4) (sourceB1420 + difference 4 5) sourceC1420) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 804) := by
    have ha : (tripleCharges (sourceA1420 + difference 5 4) (sourceB1420 + difference 4 5) sourceC1420) = raw22096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1420 sourceB1420 sourceC1420 difference raw22096; decide +kernel
    rw [ha]
    exact (canonical22096 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1420 + difference 5 5) (sourceB1420 + difference 5 5) sourceC1420) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 847) := by
    have ha : (tripleCharges (sourceA1420 + difference 5 5) (sourceB1420 + difference 5 5) sourceC1420) = raw21369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1420 sourceB1420 sourceC1420 difference raw21369; decide +kernel
    rw [ha]
    exact (canonical21369 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1420 + sourceB1420) sourceC1420) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1420 + sourceB1420) sourceC1420) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1420 sourceB1420 sourceC1420 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1420 sourceB1420 sourceC1420
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1420, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1421 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1421 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1421 : Charge := ![4, -1, -1, 0, 0, -2]
def sourceForm1421 : Integer.Sparse Master := [(Sum.inr 785, 1), (Sum.inr 1592, 1), (Sum.inr 1637, 2), (Sum.inr 1707, 1), (Sum.inr 1710, 1), (Sum.inr 4069, -1)]

theorem sourceEq1421 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1421 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1421 + difference 0 0) (sourceB1421 + difference 0 0) sourceC1421) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 785) := by
    have ha : (tripleCharges (sourceA1421 + difference 0 0) (sourceB1421 + difference 0 0) sourceC1421) = raw22097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1421 sourceB1421 sourceC1421 difference raw22097; decide +kernel
    rw [ha]
    exact (canonical22097 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1421 + difference 0 1) (sourceB1421 + difference 1 0) sourceC1421) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1637) := by
    have ha : (tripleCharges (sourceA1421 + difference 0 1) (sourceB1421 + difference 1 0) sourceC1421) = raw22098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1421 sourceB1421 sourceC1421 difference raw22098; decide +kernel
    rw [ha]
    exact (canonical22098 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1421 + difference 0 2) (sourceB1421 + difference 2 0) sourceC1421) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1637) := by
    have ha : (tripleCharges (sourceA1421 + difference 0 2) (sourceB1421 + difference 2 0) sourceC1421) = raw22099 := by
      apply Matrix.ext; unfold tripleCharges sourceA1421 sourceB1421 sourceC1421 difference raw22099; decide +kernel
    rw [ha]
    exact (canonical22099 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1421 + difference 0 3) (sourceB1421 + difference 3 0) sourceC1421) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1592) := by
    have ha : (tripleCharges (sourceA1421 + difference 0 3) (sourceB1421 + difference 3 0) sourceC1421) = raw22100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1421 sourceB1421 sourceC1421 difference raw22100; decide +kernel
    rw [ha]
    exact (canonical22100 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1421 + difference 0 4) (sourceB1421 + difference 4 0) sourceC1421) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1421 + difference 0 4) (sourceB1421 + difference 4 0) sourceC1421) = raw22101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1421 sourceB1421 sourceC1421 difference raw22101; decide +kernel
    rw [ha]
    exact (canonical22101 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1421 + difference 0 5) (sourceB1421 + difference 5 0) sourceC1421) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1421 + difference 0 5) (sourceB1421 + difference 5 0) sourceC1421) = raw22102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1421 sourceB1421 sourceC1421 difference raw22102; decide +kernel
    rw [ha]
    exact (canonical22102 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1421 + sourceB1421) sourceC1421) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1421 + sourceB1421) sourceC1421) = raw22103 := by
      apply Matrix.ext; unfold doubleCharges sourceA1421 sourceB1421 sourceC1421 raw22103; decide +kernel
    rw [ha]
    exact (canonical22103 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1421 sourceB1421 sourceC1421
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1421, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1422 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1422 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1422 : Charge := ![4, -1, -1, 0, 0, -2]
def sourceForm1422 : Integer.Sparse Master := [(Sum.inr 538, 1), (Sum.inr 699, 1), (Sum.inr 733, 1), (Sum.inr 785, 1), (Sum.inr 806, 1), (Sum.inr 812, 1), (Sum.inr 4069, -1)]

theorem sourceEq1422 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1422 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1422 + difference 1 0) (sourceB1422 + difference 0 1) sourceC1422) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 538) := by
    have ha : (tripleCharges (sourceA1422 + difference 1 0) (sourceB1422 + difference 0 1) sourceC1422) = raw22104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1422 sourceB1422 sourceC1422 difference raw22104; decide +kernel
    rw [ha]
    exact (canonical22104 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1422 + difference 1 1) (sourceB1422 + difference 1 1) sourceC1422) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 785) := by
    have ha : (tripleCharges (sourceA1422 + difference 1 1) (sourceB1422 + difference 1 1) sourceC1422) = raw22097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1422 sourceB1422 sourceC1422 difference raw22097; decide +kernel
    rw [ha]
    exact (canonical22097 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1422 + difference 1 2) (sourceB1422 + difference 2 1) sourceC1422) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 733) := by
    have ha : (tripleCharges (sourceA1422 + difference 1 2) (sourceB1422 + difference 2 1) sourceC1422) = raw22105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1422 sourceB1422 sourceC1422 difference raw22105; decide +kernel
    rw [ha]
    exact (canonical22105 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1422 + difference 1 3) (sourceB1422 + difference 3 1) sourceC1422) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 699) := by
    have ha : (tripleCharges (sourceA1422 + difference 1 3) (sourceB1422 + difference 3 1) sourceC1422) = raw22106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1422 sourceB1422 sourceC1422 difference raw22106; decide +kernel
    rw [ha]
    exact (canonical22106 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1422 + difference 1 4) (sourceB1422 + difference 4 1) sourceC1422) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 812) := by
    have ha : (tripleCharges (sourceA1422 + difference 1 4) (sourceB1422 + difference 4 1) sourceC1422) = raw22107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1422 sourceB1422 sourceC1422 difference raw22107; decide +kernel
    rw [ha]
    exact (canonical22107 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1422 + difference 1 5) (sourceB1422 + difference 5 1) sourceC1422) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1422 + difference 1 5) (sourceB1422 + difference 5 1) sourceC1422) = raw22108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1422 sourceB1422 sourceC1422 difference raw22108; decide +kernel
    rw [ha]
    exact (canonical22108 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1422 + sourceB1422) sourceC1422) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1422 + sourceB1422) sourceC1422) = raw22103 := by
      apply Matrix.ext; unfold doubleCharges sourceA1422 sourceB1422 sourceC1422 raw22103; decide +kernel
    rw [ha]
    exact (canonical22103 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1422 sourceB1422 sourceC1422
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1422, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1423 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1423 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1423 : Charge := ![4, -1, -1, 0, 0, -2]
def sourceForm1423 : Integer.Sparse Master := [(Sum.inr 782, 1), (Sum.inr 785, 1), (Sum.inr 789, 1), (Sum.inr 806, 2), (Sum.inr 1707, 1), (Sum.inr 4069, -1)]

theorem sourceEq1423 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1423 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1423 + difference 0 5) (sourceB1423 + difference 5 0) sourceC1423) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1423 + difference 0 5) (sourceB1423 + difference 5 0) sourceC1423) = raw22102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1423 sourceB1423 sourceC1423 difference raw22102; decide +kernel
    rw [ha]
    exact (canonical22102 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1423 + difference 1 5) (sourceB1423 + difference 5 1) sourceC1423) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1423 + difference 1 5) (sourceB1423 + difference 5 1) sourceC1423) = raw22108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1423 sourceB1423 sourceC1423 difference raw22108; decide +kernel
    rw [ha]
    exact (canonical22108 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1423 + difference 2 5) (sourceB1423 + difference 5 2) sourceC1423) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1423 + difference 2 5) (sourceB1423 + difference 5 2) sourceC1423) = raw22109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1423 sourceB1423 sourceC1423 difference raw22109; decide +kernel
    rw [ha]
    exact (canonical22109 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1423 + difference 3 5) (sourceB1423 + difference 5 3) sourceC1423) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 782) := by
    have ha : (tripleCharges (sourceA1423 + difference 3 5) (sourceB1423 + difference 5 3) sourceC1423) = raw22110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1423 sourceB1423 sourceC1423 difference raw22110; decide +kernel
    rw [ha]
    exact (canonical22110 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1423 + difference 4 5) (sourceB1423 + difference 5 4) sourceC1423) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 789) := by
    have ha : (tripleCharges (sourceA1423 + difference 4 5) (sourceB1423 + difference 5 4) sourceC1423) = raw22111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1423 sourceB1423 sourceC1423 difference raw22111; decide +kernel
    rw [ha]
    exact (canonical22111 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1423 + difference 5 5) (sourceB1423 + difference 5 5) sourceC1423) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 785) := by
    have ha : (tripleCharges (sourceA1423 + difference 5 5) (sourceB1423 + difference 5 5) sourceC1423) = raw22097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1423 sourceB1423 sourceC1423 difference raw22097; decide +kernel
    rw [ha]
    exact (canonical22097 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1423 + sourceB1423) sourceC1423) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1423 + sourceB1423) sourceC1423) = raw22103 := by
      apply Matrix.ext; unfold doubleCharges sourceA1423 sourceB1423 sourceC1423 raw22103; decide +kernel
    rw [ha]
    exact (canonical22103 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1423 sourceB1423 sourceC1423
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1423, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1424 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceB1424 : Charge := ![4, -1, -1, 0, 0, -2]
def sourceC1424 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1424 : Integer.Sparse Master := [(Sum.inr 536, 1), (Sum.inr 698, 1), (Sum.inr 731, 1), (Sum.inr 804, 1), (Sum.inr 809, 2), (Sum.inr 4070, -1)]

theorem sourceEq1424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1424 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1424 + difference 5 0) (sourceB1424 + difference 0 5) sourceC1424) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 536) := by
    have ha : (tripleCharges (sourceA1424 + difference 5 0) (sourceB1424 + difference 0 5) sourceC1424) = raw22112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1424 sourceB1424 sourceC1424 difference raw22112; decide +kernel
    rw [ha]
    exact (canonical22112 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1424 + difference 5 1) (sourceB1424 + difference 1 5) sourceC1424) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1424 + difference 5 1) (sourceB1424 + difference 1 5) sourceC1424) = raw22113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1424 sourceB1424 sourceC1424 difference raw22113; decide +kernel
    rw [ha]
    exact (canonical22113 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1424 + difference 5 2) (sourceB1424 + difference 2 5) sourceC1424) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 809) := by
    have ha : (tripleCharges (sourceA1424 + difference 5 2) (sourceB1424 + difference 2 5) sourceC1424) = raw21578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1424 sourceB1424 sourceC1424 difference raw21578; decide +kernel
    rw [ha]
    exact (canonical21578 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1424 + difference 5 3) (sourceB1424 + difference 3 5) sourceC1424) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 698) := by
    have ha : (tripleCharges (sourceA1424 + difference 5 3) (sourceB1424 + difference 3 5) sourceC1424) = raw21632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1424 sourceB1424 sourceC1424 difference raw21632; decide +kernel
    rw [ha]
    exact (canonical21632 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1424 + difference 5 4) (sourceB1424 + difference 4 5) sourceC1424) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 731) := by
    have ha : (tripleCharges (sourceA1424 + difference 5 4) (sourceB1424 + difference 4 5) sourceC1424) = raw21576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1424 sourceB1424 sourceC1424 difference raw21576; decide +kernel
    rw [ha]
    exact (canonical21576 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1424 + difference 5 5) (sourceB1424 + difference 5 5) sourceC1424) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 804) := by
    have ha : (tripleCharges (sourceA1424 + difference 5 5) (sourceB1424 + difference 5 5) sourceC1424) = raw22096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1424 sourceB1424 sourceC1424 difference raw22096; decide +kernel
    rw [ha]
    exact (canonical22096 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1424 + sourceB1424) sourceC1424) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1424 + sourceB1424) sourceC1424) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1424 sourceB1424 sourceC1424 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1424 sourceB1424 sourceC1424
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1424, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1425 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1425 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC1425 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceForm1425 : Integer.Sparse Master := [(Sum.inr 813, 1), (Sum.inr 1603, 2), (Sum.inr 1651, 1), (Sum.inr 1716, 1), (Sum.inr 1728, 1), (Sum.inr 4069, -1)]

theorem sourceEq1425 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1425 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1425 + difference 0 0) (sourceB1425 + difference 0 0) sourceC1425) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 813) := by
    have ha : (tripleCharges (sourceA1425 + difference 0 0) (sourceB1425 + difference 0 0) sourceC1425) = raw22114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1425 sourceB1425 sourceC1425 difference raw22114; decide +kernel
    rw [ha]
    exact (canonical22114 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1425 + difference 0 1) (sourceB1425 + difference 1 0) sourceC1425) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1651) := by
    have ha : (tripleCharges (sourceA1425 + difference 0 1) (sourceB1425 + difference 1 0) sourceC1425) = raw22115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1425 sourceB1425 sourceC1425 difference raw22115; decide +kernel
    rw [ha]
    exact (canonical22115 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1425 + difference 0 2) (sourceB1425 + difference 2 0) sourceC1425) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1603) := by
    have ha : (tripleCharges (sourceA1425 + difference 0 2) (sourceB1425 + difference 2 0) sourceC1425) = raw22116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1425 sourceB1425 sourceC1425 difference raw22116; decide +kernel
    rw [ha]
    exact (canonical22116 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1425 + difference 0 3) (sourceB1425 + difference 3 0) sourceC1425) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1603) := by
    have ha : (tripleCharges (sourceA1425 + difference 0 3) (sourceB1425 + difference 3 0) sourceC1425) = raw22117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1425 sourceB1425 sourceC1425 difference raw22117; decide +kernel
    rw [ha]
    exact (canonical22117 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1425 + difference 0 4) (sourceB1425 + difference 4 0) sourceC1425) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1425 + difference 0 4) (sourceB1425 + difference 4 0) sourceC1425) = raw22118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1425 sourceB1425 sourceC1425 difference raw22118; decide +kernel
    rw [ha]
    exact (canonical22118 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1425 + difference 0 5) (sourceB1425 + difference 5 0) sourceC1425) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1425 + difference 0 5) (sourceB1425 + difference 5 0) sourceC1425) = raw22119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1425 sourceB1425 sourceC1425 difference raw22119; decide +kernel
    rw [ha]
    exact (canonical22119 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1425 + sourceB1425) sourceC1425) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1425 + sourceB1425) sourceC1425) = raw22120 := by
      apply Matrix.ext; unfold doubleCharges sourceA1425 sourceB1425 sourceC1425 raw22120; decide +kernel
    rw [ha]
    exact (canonical22120 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1425 sourceB1425 sourceC1425
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1425, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1426 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1426 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC1426 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceForm1426 : Integer.Sparse Master := [(Sum.inr 548, 1), (Sum.inr 708, 2), (Sum.inr 743, 1), (Sum.inr 813, 1), (Sum.inr 816, 1), (Sum.inr 4069, -1)]

theorem sourceEq1426 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1426 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1426 + difference 4 0) (sourceB1426 + difference 0 4) sourceC1426) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 548) := by
    have ha : (tripleCharges (sourceA1426 + difference 4 0) (sourceB1426 + difference 0 4) sourceC1426) = raw22121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1426 sourceB1426 sourceC1426 difference raw22121; decide +kernel
    rw [ha]
    exact (canonical22121 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1426 + difference 4 1) (sourceB1426 + difference 1 4) sourceC1426) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 743) := by
    have ha : (tripleCharges (sourceA1426 + difference 4 1) (sourceB1426 + difference 1 4) sourceC1426) = raw22122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1426 sourceB1426 sourceC1426 difference raw22122; decide +kernel
    rw [ha]
    exact (canonical22122 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1426 + difference 4 2) (sourceB1426 + difference 2 4) sourceC1426) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 708) := by
    have ha : (tripleCharges (sourceA1426 + difference 4 2) (sourceB1426 + difference 2 4) sourceC1426) = raw22123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1426 sourceB1426 sourceC1426 difference raw22123; decide +kernel
    rw [ha]
    exact (canonical22123 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1426 + difference 4 3) (sourceB1426 + difference 3 4) sourceC1426) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 708) := by
    have ha : (tripleCharges (sourceA1426 + difference 4 3) (sourceB1426 + difference 3 4) sourceC1426) = raw22124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1426 sourceB1426 sourceC1426 difference raw22124; decide +kernel
    rw [ha]
    exact (canonical22124 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1426 + difference 4 4) (sourceB1426 + difference 4 4) sourceC1426) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 813) := by
    have ha : (tripleCharges (sourceA1426 + difference 4 4) (sourceB1426 + difference 4 4) sourceC1426) = raw22114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1426 sourceB1426 sourceC1426 difference raw22114; decide +kernel
    rw [ha]
    exact (canonical22114 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1426 + difference 4 5) (sourceB1426 + difference 5 4) sourceC1426) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 816) := by
    have ha : (tripleCharges (sourceA1426 + difference 4 5) (sourceB1426 + difference 5 4) sourceC1426) = raw22125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1426 sourceB1426 sourceC1426 difference raw22125; decide +kernel
    rw [ha]
    exact (canonical22125 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1426 + sourceB1426) sourceC1426) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1426 + sourceB1426) sourceC1426) = raw22120 := by
      apply Matrix.ext; unfold doubleCharges sourceA1426 sourceB1426 sourceC1426 raw22120; decide +kernel
    rw [ha]
    exact (canonical22120 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1426 sourceB1426 sourceC1426
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1426, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1427 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1427 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceC1427 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceForm1427 : Integer.Sparse Master := [(Sum.inr 807, 2), (Sum.inr 813, 1), (Sum.inr 816, 1), (Sum.inr 856, 1), (Sum.inr 1728, 1), (Sum.inr 4069, -1)]

theorem sourceEq1427 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1427 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1427 + difference 0 5) (sourceB1427 + difference 5 0) sourceC1427) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1427 + difference 0 5) (sourceB1427 + difference 5 0) sourceC1427) = raw22119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1427 sourceB1427 sourceC1427 difference raw22119; decide +kernel
    rw [ha]
    exact (canonical22119 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1427 + difference 1 5) (sourceB1427 + difference 5 1) sourceC1427) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 856) := by
    have ha : (tripleCharges (sourceA1427 + difference 1 5) (sourceB1427 + difference 5 1) sourceC1427) = raw22126 := by
      apply Matrix.ext; unfold tripleCharges sourceA1427 sourceB1427 sourceC1427 difference raw22126; decide +kernel
    rw [ha]
    exact (canonical22126 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1427 + difference 2 5) (sourceB1427 + difference 5 2) sourceC1427) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 807) := by
    have ha : (tripleCharges (sourceA1427 + difference 2 5) (sourceB1427 + difference 5 2) sourceC1427) = raw22127 := by
      apply Matrix.ext; unfold tripleCharges sourceA1427 sourceB1427 sourceC1427 difference raw22127; decide +kernel
    rw [ha]
    exact (canonical22127 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1427 + difference 3 5) (sourceB1427 + difference 5 3) sourceC1427) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 807) := by
    have ha : (tripleCharges (sourceA1427 + difference 3 5) (sourceB1427 + difference 5 3) sourceC1427) = raw22128 := by
      apply Matrix.ext; unfold tripleCharges sourceA1427 sourceB1427 sourceC1427 difference raw22128; decide +kernel
    rw [ha]
    exact (canonical22128 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1427 + difference 4 5) (sourceB1427 + difference 5 4) sourceC1427) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 816) := by
    have ha : (tripleCharges (sourceA1427 + difference 4 5) (sourceB1427 + difference 5 4) sourceC1427) = raw22125 := by
      apply Matrix.ext; unfold tripleCharges sourceA1427 sourceB1427 sourceC1427 difference raw22125; decide +kernel
    rw [ha]
    exact (canonical22125 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1427 + difference 5 5) (sourceB1427 + difference 5 5) sourceC1427) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 813) := by
    have ha : (tripleCharges (sourceA1427 + difference 5 5) (sourceB1427 + difference 5 5) sourceC1427) = raw22114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1427 sourceB1427 sourceC1427 difference raw22114; decide +kernel
    rw [ha]
    exact (canonical22114 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1427 + sourceB1427) sourceC1427) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1427 + sourceB1427) sourceC1427) = raw22120 := by
      apply Matrix.ext; unfold doubleCharges sourceA1427 sourceB1427 sourceC1427 raw22120; decide +kernel
    rw [ha]
    exact (canonical22120 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1427 sourceB1427 sourceC1427
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1427, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1428 : Charge := ![0, 1, 0, 0, 1, -2]
def sourceB1428 : Charge := ![4, -1, 0, 0, -2, -1]
def sourceC1428 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1428 : Integer.Sparse Master := [(Sum.inr 556, 1), (Sum.inr 716, 2), (Sum.inr 851, 1), (Sum.inr 853, 1), (Sum.inr 863, 1), (Sum.inr 4070, -1)]

theorem sourceEq1428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1428 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1428 + difference 5 0) (sourceB1428 + difference 0 5) sourceC1428) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 556) := by
    have ha : (tripleCharges (sourceA1428 + difference 5 0) (sourceB1428 + difference 0 5) sourceC1428) = raw22129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1428 sourceB1428 sourceC1428 difference raw22129; decide +kernel
    rw [ha]
    exact (canonical22129 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1428 + difference 5 1) (sourceB1428 + difference 1 5) sourceC1428) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 863) := by
    have ha : (tripleCharges (sourceA1428 + difference 5 1) (sourceB1428 + difference 1 5) sourceC1428) = raw21914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1428 sourceB1428 sourceC1428 difference raw21914; decide +kernel
    rw [ha]
    exact (canonical21914 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1428 + difference 5 2) (sourceB1428 + difference 2 5) sourceC1428) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 716) := by
    have ha : (tripleCharges (sourceA1428 + difference 5 2) (sourceB1428 + difference 2 5) sourceC1428) = raw22130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1428 sourceB1428 sourceC1428 difference raw22130; decide +kernel
    rw [ha]
    exact (canonical22130 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1428 + difference 5 3) (sourceB1428 + difference 3 5) sourceC1428) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 716) := by
    have ha : (tripleCharges (sourceA1428 + difference 5 3) (sourceB1428 + difference 3 5) sourceC1428) = raw21611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1428 sourceB1428 sourceC1428 difference raw21611; decide +kernel
    rw [ha]
    exact (canonical21611 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1428 + difference 5 4) (sourceB1428 + difference 4 5) sourceC1428) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 851) := by
    have ha : (tripleCharges (sourceA1428 + difference 5 4) (sourceB1428 + difference 4 5) sourceC1428) = raw21372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1428 sourceB1428 sourceC1428 difference raw21372; decide +kernel
    rw [ha]
    exact (canonical21372 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1428 + difference 5 5) (sourceB1428 + difference 5 5) sourceC1428) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 853) := by
    have ha : (tripleCharges (sourceA1428 + difference 5 5) (sourceB1428 + difference 5 5) sourceC1428) = raw21371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1428 sourceB1428 sourceC1428 difference raw21371; decide +kernel
    rw [ha]
    exact (canonical21371 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1428 + sourceB1428) sourceC1428) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1428 + sourceB1428) sourceC1428) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1428 sourceB1428 sourceC1428 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1428 sourceB1428 sourceC1428
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1428, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1429 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1429 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1429 : Charge := ![4, -1, 0, 0, -1, -2]
def sourceForm1429 : Integer.Sparse Master := [(Sum.inr 4069, 1), (Sum.inr 4101, 2), (Sum.inr 4108, 1), (Sum.inr 4110, 1), (Sum.inr 4127, 1), (Sum.inr 4196, 2), (Sum.inr 4202, 2), (Sum.inr 4204, 2), (Sum.inr 4218, 2), (Sum.inr 4233, 2), (Sum.inr 4240, 1), (Sum.inr 4242, 1), (Sum.inr 4251, 2), (Sum.inr 4257, 1), (Sum.inr 4264, 2), (Sum.inr 4269, 1), (Sum.inr 4273, 1), (Sum.inr 4418, 2), (Sum.inr 4490, 1), (Sum.inr 4496, 1), (Sum.inr 4498, 1)]

theorem sourceEq1429 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1429 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1429 + difference 0 1) (sourceB1429 + difference 1 0) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA1429 + difference 0 1) (sourceB1429 + difference 1 0) sourceC1429) = raw22131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22131; decide +kernel
    rw [ha]
    exact (canonical22131 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1429 + difference 0 2) (sourceB1429 + difference 2 0) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1429 + difference 0 2) (sourceB1429 + difference 2 0) sourceC1429) = raw22132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22132; decide +kernel
    rw [ha]
    exact (canonical22132 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1429 + difference 0 3) (sourceB1429 + difference 3 0) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4418) := by
    have ha : (tripleCharges (sourceA1429 + difference 0 3) (sourceB1429 + difference 3 0) sourceC1429) = raw22133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22133; decide +kernel
    rw [ha]
    exact (canonical22133 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1429 + difference 0 4) (sourceB1429 + difference 4 0) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1429 + difference 0 4) (sourceB1429 + difference 4 0) sourceC1429) = raw22134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22134; decide +kernel
    rw [ha]
    exact (canonical22134 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1429 + difference 0 5) (sourceB1429 + difference 5 0) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1429 + difference 0 5) (sourceB1429 + difference 5 0) sourceC1429) = raw22135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22135; decide +kernel
    rw [ha]
    exact (canonical22135 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1429 + difference 1 0) (sourceB1429 + difference 0 1) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4127) := by
    have ha : (tripleCharges (sourceA1429 + difference 1 0) (sourceB1429 + difference 0 1) sourceC1429) = raw22136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22136; decide +kernel
    rw [ha]
    exact (canonical22136 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1429 + difference 1 2) (sourceB1429 + difference 2 1) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4218) := by
    have ha : (tripleCharges (sourceA1429 + difference 1 2) (sourceB1429 + difference 2 1) sourceC1429) = raw22137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22137; decide +kernel
    rw [ha]
    exact (canonical22137 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1429 + difference 1 3) (sourceB1429 + difference 3 1) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4218) := by
    have ha : (tripleCharges (sourceA1429 + difference 1 3) (sourceB1429 + difference 3 1) sourceC1429) = raw22138 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22138; decide +kernel
    rw [ha]
    exact (canonical22138 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1429 + difference 1 4) (sourceB1429 + difference 4 1) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1429 + difference 1 4) (sourceB1429 + difference 4 1) sourceC1429) = raw22139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22139; decide +kernel
    rw [ha]
    exact (canonical22139 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1429 + difference 1 5) (sourceB1429 + difference 5 1) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1429 + difference 1 5) (sourceB1429 + difference 5 1) sourceC1429) = raw22140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22140; decide +kernel
    rw [ha]
    exact (canonical22140 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1429 + difference 2 0) (sourceB1429 + difference 0 2) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4101) := by
    have ha : (tripleCharges (sourceA1429 + difference 2 0) (sourceB1429 + difference 0 2) sourceC1429) = raw22141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22141; decide +kernel
    rw [ha]
    exact (canonical22141 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1429 + difference 2 1) (sourceB1429 + difference 1 2) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4233) := by
    have ha : (tripleCharges (sourceA1429 + difference 2 1) (sourceB1429 + difference 1 2) sourceC1429) = raw22142 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22142; decide +kernel
    rw [ha]
    exact (canonical22142 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1429 + difference 2 3) (sourceB1429 + difference 3 2) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4196) := by
    have ha : (tripleCharges (sourceA1429 + difference 2 3) (sourceB1429 + difference 3 2) sourceC1429) = raw22143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22143; decide +kernel
    rw [ha]
    exact (canonical22143 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1429 + difference 2 4) (sourceB1429 + difference 4 2) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA1429 + difference 2 4) (sourceB1429 + difference 4 2) sourceC1429) = raw22144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22144; decide +kernel
    rw [ha]
    exact (canonical22144 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1429 + difference 2 5) (sourceB1429 + difference 5 2) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4264) := by
    have ha : (tripleCharges (sourceA1429 + difference 2 5) (sourceB1429 + difference 5 2) sourceC1429) = raw22145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22145; decide +kernel
    rw [ha]
    exact (canonical22145 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1429 + difference 3 0) (sourceB1429 + difference 0 3) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4101) := by
    have ha : (tripleCharges (sourceA1429 + difference 3 0) (sourceB1429 + difference 0 3) sourceC1429) = raw22146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22146; decide +kernel
    rw [ha]
    exact (canonical22146 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1429 + difference 3 1) (sourceB1429 + difference 1 3) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4233) := by
    have ha : (tripleCharges (sourceA1429 + difference 3 1) (sourceB1429 + difference 1 3) sourceC1429) = raw22147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22147; decide +kernel
    rw [ha]
    exact (canonical22147 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1429 + difference 3 2) (sourceB1429 + difference 2 3) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4196) := by
    have ha : (tripleCharges (sourceA1429 + difference 3 2) (sourceB1429 + difference 2 3) sourceC1429) = raw22148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22148; decide +kernel
    rw [ha]
    exact (canonical22148 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1429 + difference 3 4) (sourceB1429 + difference 4 3) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA1429 + difference 3 4) (sourceB1429 + difference 4 3) sourceC1429) = raw22149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22149; decide +kernel
    rw [ha]
    exact (canonical22149 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1429 + difference 3 5) (sourceB1429 + difference 5 3) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4264) := by
    have ha : (tripleCharges (sourceA1429 + difference 3 5) (sourceB1429 + difference 5 3) sourceC1429) = raw22150 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22150; decide +kernel
    rw [ha]
    exact (canonical22150 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1429 + difference 4 0) (sourceB1429 + difference 0 4) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4110) := by
    have ha : (tripleCharges (sourceA1429 + difference 4 0) (sourceB1429 + difference 0 4) sourceC1429) = raw22151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22151; decide +kernel
    rw [ha]
    exact (canonical22151 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1429 + difference 4 1) (sourceB1429 + difference 1 4) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4242) := by
    have ha : (tripleCharges (sourceA1429 + difference 4 1) (sourceB1429 + difference 1 4) sourceC1429) = raw22152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22152; decide +kernel
    rw [ha]
    exact (canonical22152 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1429 + difference 4 2) (sourceB1429 + difference 2 4) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4204) := by
    have ha : (tripleCharges (sourceA1429 + difference 4 2) (sourceB1429 + difference 2 4) sourceC1429) = raw22153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22153; decide +kernel
    rw [ha]
    exact (canonical22153 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1429 + difference 4 3) (sourceB1429 + difference 3 4) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4204) := by
    have ha : (tripleCharges (sourceA1429 + difference 4 3) (sourceB1429 + difference 3 4) sourceC1429) = raw22154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22154; decide +kernel
    rw [ha]
    exact (canonical22154 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1429 + difference 4 5) (sourceB1429 + difference 5 4) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1429 + difference 4 5) (sourceB1429 + difference 5 4) sourceC1429) = raw22155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22155; decide +kernel
    rw [ha]
    exact (canonical22155 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1429 + difference 5 0) (sourceB1429 + difference 0 5) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4108) := by
    have ha : (tripleCharges (sourceA1429 + difference 5 0) (sourceB1429 + difference 0 5) sourceC1429) = raw22156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22156; decide +kernel
    rw [ha]
    exact (canonical22156 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1429 + difference 5 1) (sourceB1429 + difference 1 5) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4240) := by
    have ha : (tripleCharges (sourceA1429 + difference 5 1) (sourceB1429 + difference 1 5) sourceC1429) = raw22157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22157; decide +kernel
    rw [ha]
    exact (canonical22157 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1429 + difference 5 2) (sourceB1429 + difference 2 5) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4202) := by
    have ha : (tripleCharges (sourceA1429 + difference 5 2) (sourceB1429 + difference 2 5) sourceC1429) = raw22158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22158; decide +kernel
    rw [ha]
    exact (canonical22158 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1429 + difference 5 3) (sourceB1429 + difference 3 5) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4202) := by
    have ha : (tripleCharges (sourceA1429 + difference 5 3) (sourceB1429 + difference 3 5) sourceC1429) = raw22159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22159; decide +kernel
    rw [ha]
    exact (canonical22159 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1429 + difference 5 4) (sourceB1429 + difference 4 5) sourceC1429) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4257) := by
    have ha : (tripleCharges (sourceA1429 + difference 5 4) (sourceB1429 + difference 4 5) sourceC1429) = raw22160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1429 sourceB1429 sourceC1429 difference raw22160; decide +kernel
    rw [ha]
    exact (canonical22160 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1429 sourceB1429 sourceC1429
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1429, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1430 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1430 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1430 : Charge := ![4, -1, 0, 0, -1, -2]
def sourceForm1430 : Integer.Sparse Master := [(Sum.inr 663, 2), (Sum.inr 683, 1), (Sum.inr 684, 1), (Sum.inr 688, 1), (Sum.inr 748, 2), (Sum.inr 762, 2), (Sum.inr 763, 2), (Sum.inr 767, 2), (Sum.inr 799, 2), (Sum.inr 804, 2), (Sum.inr 806, 2), (Sum.inr 842, 1), (Sum.inr 843, 1), (Sum.inr 849, 1), (Sum.inr 851, 1), (Sum.inr 852, 1), (Sum.inr 999, 2), (Sum.inr 1074, 1), (Sum.inr 1080, 1), (Sum.inr 1082, 1), (Sum.inr 4069, 1)]

theorem sourceEq1430 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1430 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1430 + difference 0 1) (sourceB1430 + difference 1 0) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1074) := by
    have ha : (tripleCharges (sourceA1430 + difference 0 1) (sourceB1430 + difference 1 0) sourceC1430) = raw22161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22161; decide +kernel
    rw [ha]
    exact (canonical22161 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1430 + difference 0 2) (sourceB1430 + difference 2 0) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 999) := by
    have ha : (tripleCharges (sourceA1430 + difference 0 2) (sourceB1430 + difference 2 0) sourceC1430) = raw22162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22162; decide +kernel
    rw [ha]
    exact (canonical22162 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1430 + difference 0 3) (sourceB1430 + difference 3 0) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 999) := by
    have ha : (tripleCharges (sourceA1430 + difference 0 3) (sourceB1430 + difference 3 0) sourceC1430) = raw22163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22163; decide +kernel
    rw [ha]
    exact (canonical22163 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1430 + difference 0 4) (sourceB1430 + difference 4 0) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1080) := by
    have ha : (tripleCharges (sourceA1430 + difference 0 4) (sourceB1430 + difference 4 0) sourceC1430) = raw22164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22164; decide +kernel
    rw [ha]
    exact (canonical22164 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1430 + difference 0 5) (sourceB1430 + difference 5 0) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1082) := by
    have ha : (tripleCharges (sourceA1430 + difference 0 5) (sourceB1430 + difference 5 0) sourceC1430) = raw22165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22165; decide +kernel
    rw [ha]
    exact (canonical22165 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1430 + difference 1 0) (sourceB1430 + difference 0 1) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 688) := by
    have ha : (tripleCharges (sourceA1430 + difference 1 0) (sourceB1430 + difference 0 1) sourceC1430) = raw22166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22166; decide +kernel
    rw [ha]
    exact (canonical22166 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1430 + difference 1 2) (sourceB1430 + difference 2 1) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 767) := by
    have ha : (tripleCharges (sourceA1430 + difference 1 2) (sourceB1430 + difference 2 1) sourceC1430) = raw22167 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22167; decide +kernel
    rw [ha]
    exact (canonical22167 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1430 + difference 1 3) (sourceB1430 + difference 3 1) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 767) := by
    have ha : (tripleCharges (sourceA1430 + difference 1 3) (sourceB1430 + difference 3 1) sourceC1430) = raw22168 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22168; decide +kernel
    rw [ha]
    exact (canonical22168 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1430 + difference 1 4) (sourceB1430 + difference 4 1) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 851) := by
    have ha : (tripleCharges (sourceA1430 + difference 1 4) (sourceB1430 + difference 4 1) sourceC1430) = raw22169 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22169; decide +kernel
    rw [ha]
    exact (canonical22169 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1430 + difference 1 5) (sourceB1430 + difference 5 1) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1430 + difference 1 5) (sourceB1430 + difference 5 1) sourceC1430) = raw22170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22170; decide +kernel
    rw [ha]
    exact (canonical22170 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1430 + difference 2 0) (sourceB1430 + difference 0 2) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 663) := by
    have ha : (tripleCharges (sourceA1430 + difference 2 0) (sourceB1430 + difference 0 2) sourceC1430) = raw22171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22171; decide +kernel
    rw [ha]
    exact (canonical22171 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1430 + difference 2 1) (sourceB1430 + difference 1 2) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 799) := by
    have ha : (tripleCharges (sourceA1430 + difference 2 1) (sourceB1430 + difference 1 2) sourceC1430) = raw22172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22172; decide +kernel
    rw [ha]
    exact (canonical22172 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1430 + difference 2 3) (sourceB1430 + difference 3 2) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 748) := by
    have ha : (tripleCharges (sourceA1430 + difference 2 3) (sourceB1430 + difference 3 2) sourceC1430) = raw22173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22173; decide +kernel
    rw [ha]
    exact (canonical22173 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1430 + difference 2 4) (sourceB1430 + difference 4 2) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 804) := by
    have ha : (tripleCharges (sourceA1430 + difference 2 4) (sourceB1430 + difference 4 2) sourceC1430) = raw22174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22174; decide +kernel
    rw [ha]
    exact (canonical22174 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1430 + difference 2 5) (sourceB1430 + difference 5 2) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1430 + difference 2 5) (sourceB1430 + difference 5 2) sourceC1430) = raw22175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22175; decide +kernel
    rw [ha]
    exact (canonical22175 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1430 + difference 3 0) (sourceB1430 + difference 0 3) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 663) := by
    have ha : (tripleCharges (sourceA1430 + difference 3 0) (sourceB1430 + difference 0 3) sourceC1430) = raw22176 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22176; decide +kernel
    rw [ha]
    exact (canonical22176 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1430 + difference 3 1) (sourceB1430 + difference 1 3) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 799) := by
    have ha : (tripleCharges (sourceA1430 + difference 3 1) (sourceB1430 + difference 1 3) sourceC1430) = raw22177 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22177; decide +kernel
    rw [ha]
    exact (canonical22177 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1430 + difference 3 2) (sourceB1430 + difference 2 3) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 748) := by
    have ha : (tripleCharges (sourceA1430 + difference 3 2) (sourceB1430 + difference 2 3) sourceC1430) = raw22178 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22178; decide +kernel
    rw [ha]
    exact (canonical22178 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1430 + difference 3 4) (sourceB1430 + difference 4 3) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 804) := by
    have ha : (tripleCharges (sourceA1430 + difference 3 4) (sourceB1430 + difference 4 3) sourceC1430) = raw22179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22179; decide +kernel
    rw [ha]
    exact (canonical22179 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1430 + difference 3 5) (sourceB1430 + difference 5 3) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1430 + difference 3 5) (sourceB1430 + difference 5 3) sourceC1430) = raw22180 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22180; decide +kernel
    rw [ha]
    exact (canonical22180 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1430 + difference 4 0) (sourceB1430 + difference 0 4) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 684) := by
    have ha : (tripleCharges (sourceA1430 + difference 4 0) (sourceB1430 + difference 0 4) sourceC1430) = raw22181 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22181; decide +kernel
    rw [ha]
    exact (canonical22181 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1430 + difference 4 1) (sourceB1430 + difference 1 4) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 843) := by
    have ha : (tripleCharges (sourceA1430 + difference 4 1) (sourceB1430 + difference 1 4) sourceC1430) = raw22182 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22182; decide +kernel
    rw [ha]
    exact (canonical22182 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1430 + difference 4 2) (sourceB1430 + difference 2 4) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 763) := by
    have ha : (tripleCharges (sourceA1430 + difference 4 2) (sourceB1430 + difference 2 4) sourceC1430) = raw22183 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22183; decide +kernel
    rw [ha]
    exact (canonical22183 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1430 + difference 4 3) (sourceB1430 + difference 3 4) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 763) := by
    have ha : (tripleCharges (sourceA1430 + difference 4 3) (sourceB1430 + difference 3 4) sourceC1430) = raw22184 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22184; decide +kernel
    rw [ha]
    exact (canonical22184 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1430 + difference 4 5) (sourceB1430 + difference 5 4) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 852) := by
    have ha : (tripleCharges (sourceA1430 + difference 4 5) (sourceB1430 + difference 5 4) sourceC1430) = raw22185 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22185; decide +kernel
    rw [ha]
    exact (canonical22185 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1430 + difference 5 0) (sourceB1430 + difference 0 5) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 683) := by
    have ha : (tripleCharges (sourceA1430 + difference 5 0) (sourceB1430 + difference 0 5) sourceC1430) = raw22186 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22186; decide +kernel
    rw [ha]
    exact (canonical22186 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1430 + difference 5 1) (sourceB1430 + difference 1 5) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 842) := by
    have ha : (tripleCharges (sourceA1430 + difference 5 1) (sourceB1430 + difference 1 5) sourceC1430) = raw22187 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22187; decide +kernel
    rw [ha]
    exact (canonical22187 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1430 + difference 5 2) (sourceB1430 + difference 2 5) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 762) := by
    have ha : (tripleCharges (sourceA1430 + difference 5 2) (sourceB1430 + difference 2 5) sourceC1430) = raw22188 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22188; decide +kernel
    rw [ha]
    exact (canonical22188 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1430 + difference 5 3) (sourceB1430 + difference 3 5) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 762) := by
    have ha : (tripleCharges (sourceA1430 + difference 5 3) (sourceB1430 + difference 3 5) sourceC1430) = raw22189 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22189; decide +kernel
    rw [ha]
    exact (canonical22189 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1430 + difference 5 4) (sourceB1430 + difference 4 5) sourceC1430) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 849) := by
    have ha : (tripleCharges (sourceA1430 + difference 5 4) (sourceB1430 + difference 4 5) sourceC1430) = raw22190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1430 sourceB1430 sourceC1430 difference raw22190; decide +kernel
    rw [ha]
    exact (canonical22190 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1430 sourceB1430 sourceC1430
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1430, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1431 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1431 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1431 : Charge := ![4, -1, 0, 0, -1, -2]
def sourceForm1431 : Integer.Sparse Master := [(Sum.inr 812, 1), (Sum.inr 1602, 2), (Sum.inr 1650, 1), (Sum.inr 1710, 1), (Sum.inr 1727, 1), (Sum.inr 4069, -1)]

theorem sourceEq1431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1431 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1431 + difference 0 0) (sourceB1431 + difference 0 0) sourceC1431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 812) := by
    have ha : (tripleCharges (sourceA1431 + difference 0 0) (sourceB1431 + difference 0 0) sourceC1431) = raw22191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1431 sourceB1431 sourceC1431 difference raw22191; decide +kernel
    rw [ha]
    exact (canonical22191 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1431 + difference 0 1) (sourceB1431 + difference 1 0) sourceC1431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1650) := by
    have ha : (tripleCharges (sourceA1431 + difference 0 1) (sourceB1431 + difference 1 0) sourceC1431) = raw22192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1431 sourceB1431 sourceC1431 difference raw22192; decide +kernel
    rw [ha]
    exact (canonical22192 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1431 + difference 0 2) (sourceB1431 + difference 2 0) sourceC1431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1602) := by
    have ha : (tripleCharges (sourceA1431 + difference 0 2) (sourceB1431 + difference 2 0) sourceC1431) = raw22193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1431 sourceB1431 sourceC1431 difference raw22193; decide +kernel
    rw [ha]
    exact (canonical22193 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1431 + difference 0 3) (sourceB1431 + difference 3 0) sourceC1431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1602) := by
    have ha : (tripleCharges (sourceA1431 + difference 0 3) (sourceB1431 + difference 3 0) sourceC1431) = raw22194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1431 sourceB1431 sourceC1431 difference raw22194; decide +kernel
    rw [ha]
    exact (canonical22194 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1431 + difference 0 4) (sourceB1431 + difference 4 0) sourceC1431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1431 + difference 0 4) (sourceB1431 + difference 4 0) sourceC1431) = raw22195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1431 sourceB1431 sourceC1431 difference raw22195; decide +kernel
    rw [ha]
    exact (canonical22195 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1431 + difference 0 5) (sourceB1431 + difference 5 0) sourceC1431) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1431 + difference 0 5) (sourceB1431 + difference 5 0) sourceC1431) = raw22196 := by
      apply Matrix.ext; unfold tripleCharges sourceA1431 sourceB1431 sourceC1431 difference raw22196; decide +kernel
    rw [ha]
    exact (canonical22196 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1431 + sourceB1431) sourceC1431) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1431 + sourceB1431) sourceC1431) = raw22197 := by
      apply Matrix.ext; unfold doubleCharges sourceA1431 sourceB1431 sourceC1431 raw22197; decide +kernel
    rw [ha]
    exact (canonical22197 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1431 sourceB1431 sourceC1431
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1431, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1432 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1432 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1432 : Charge := ![4, -1, 0, 0, -1, -2]
def sourceForm1432 : Integer.Sparse Master := [(Sum.inr 538, 2), (Sum.inr 545, 1), (Sum.inr 547, 1), (Sum.inr 558, 1), (Sum.inr 812, 1), (Sum.inr 4069, -1)]

theorem sourceEq1432 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1432 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1432 + difference 0 0) (sourceB1432 + difference 0 0) sourceC1432) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 812) := by
    have ha : (tripleCharges (sourceA1432 + difference 0 0) (sourceB1432 + difference 0 0) sourceC1432) = raw22191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1432 sourceB1432 sourceC1432 difference raw22191; decide +kernel
    rw [ha]
    exact (canonical22191 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1432 + difference 1 0) (sourceB1432 + difference 0 1) sourceC1432) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 558) := by
    have ha : (tripleCharges (sourceA1432 + difference 1 0) (sourceB1432 + difference 0 1) sourceC1432) = raw22198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1432 sourceB1432 sourceC1432 difference raw22198; decide +kernel
    rw [ha]
    exact (canonical22198 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1432 + difference 2 0) (sourceB1432 + difference 0 2) sourceC1432) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 538) := by
    have ha : (tripleCharges (sourceA1432 + difference 2 0) (sourceB1432 + difference 0 2) sourceC1432) = raw22199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1432 sourceB1432 sourceC1432 difference raw22199; decide +kernel
    rw [ha]
    exact (canonical22199 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1432 + difference 3 0) (sourceB1432 + difference 0 3) sourceC1432) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 538) := by
    have ha : (tripleCharges (sourceA1432 + difference 3 0) (sourceB1432 + difference 0 3) sourceC1432) = raw22200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1432 sourceB1432 sourceC1432 difference raw22200; decide +kernel
    rw [ha]
    exact (canonical22200 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1432 + difference 4 0) (sourceB1432 + difference 0 4) sourceC1432) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 547) := by
    have ha : (tripleCharges (sourceA1432 + difference 4 0) (sourceB1432 + difference 0 4) sourceC1432) = raw22201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1432 sourceB1432 sourceC1432 difference raw22201; decide +kernel
    rw [ha]
    exact (canonical22201 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1432 + difference 5 0) (sourceB1432 + difference 0 5) sourceC1432) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 545) := by
    have ha : (tripleCharges (sourceA1432 + difference 5 0) (sourceB1432 + difference 0 5) sourceC1432) = raw22202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1432 sourceB1432 sourceC1432 difference raw22202; decide +kernel
    rw [ha]
    exact (canonical22202 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1432 + sourceB1432) sourceC1432) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1432 + sourceB1432) sourceC1432) = raw22197 := by
      apply Matrix.ext; unfold doubleCharges sourceA1432 sourceB1432 sourceC1432 raw22197; decide +kernel
    rw [ha]
    exact (canonical22197 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1432 sourceB1432 sourceC1432
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1432, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1433 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1433 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceC1433 : Charge := ![4, -1, 0, 0, -1, -2]
def sourceForm1433 : Integer.Sparse Master := [(Sum.inr 733, 2), (Sum.inr 740, 1), (Sum.inr 742, 1), (Sum.inr 812, 1), (Sum.inr 1650, 1), (Sum.inr 4069, -1)]

theorem sourceEq1433 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1433 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1433 + difference 0 1) (sourceB1433 + difference 1 0) sourceC1433) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1650) := by
    have ha : (tripleCharges (sourceA1433 + difference 0 1) (sourceB1433 + difference 1 0) sourceC1433) = raw22192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1433 sourceB1433 sourceC1433 difference raw22192; decide +kernel
    rw [ha]
    exact (canonical22192 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1433 + difference 1 1) (sourceB1433 + difference 1 1) sourceC1433) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 812) := by
    have ha : (tripleCharges (sourceA1433 + difference 1 1) (sourceB1433 + difference 1 1) sourceC1433) = raw22191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1433 sourceB1433 sourceC1433 difference raw22191; decide +kernel
    rw [ha]
    exact (canonical22191 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1433 + difference 2 1) (sourceB1433 + difference 1 2) sourceC1433) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 733) := by
    have ha : (tripleCharges (sourceA1433 + difference 2 1) (sourceB1433 + difference 1 2) sourceC1433) = raw22203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1433 sourceB1433 sourceC1433 difference raw22203; decide +kernel
    rw [ha]
    exact (canonical22203 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1433 + difference 3 1) (sourceB1433 + difference 1 3) sourceC1433) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 733) := by
    have ha : (tripleCharges (sourceA1433 + difference 3 1) (sourceB1433 + difference 1 3) sourceC1433) = raw22204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1433 sourceB1433 sourceC1433 difference raw22204; decide +kernel
    rw [ha]
    exact (canonical22204 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1433 + difference 4 1) (sourceB1433 + difference 1 4) sourceC1433) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 742) := by
    have ha : (tripleCharges (sourceA1433 + difference 4 1) (sourceB1433 + difference 1 4) sourceC1433) = raw22205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1433 sourceB1433 sourceC1433 difference raw22205; decide +kernel
    rw [ha]
    exact (canonical22205 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1433 + difference 5 1) (sourceB1433 + difference 1 5) sourceC1433) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 740) := by
    have ha : (tripleCharges (sourceA1433 + difference 5 1) (sourceB1433 + difference 1 5) sourceC1433) = raw22206 := by
      apply Matrix.ext; unfold tripleCharges sourceA1433 sourceB1433 sourceC1433 difference raw22206; decide +kernel
    rw [ha]
    exact (canonical22206 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1433 + sourceB1433) sourceC1433) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1433 + sourceB1433) sourceC1433) = raw22197 := by
      apply Matrix.ext; unfold doubleCharges sourceA1433 sourceB1433 sourceC1433 raw22197; decide +kernel
    rw [ha]
    exact (canonical22197 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1433 sourceB1433 sourceC1433
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1433, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1434 : Charge := ![0, 1, 0, 0, 0, -1]
def sourceB1434 : Charge := ![4, -1, 0, 0, -1, -2]
def sourceC1434 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1434 : Integer.Sparse Master := [(Sum.inr 4070, 1), (Sum.inr 4114, 2), (Sum.inr 4120, 1), (Sum.inr 4122, 1), (Sum.inr 4129, 1), (Sum.inr 4206, 2), (Sum.inr 4211, 2), (Sum.inr 4213, 2), (Sum.inr 4220, 2), (Sum.inr 4251, 2), (Sum.inr 4253, 2), (Sum.inr 4266, 1), (Sum.inr 4269, 2), (Sum.inr 4270, 1), (Sum.inr 4272, 1), (Sum.inr 4276, 1), (Sum.inr 4284, 1), (Sum.inr 4401, 2), (Sum.inr 4460, 1), (Sum.inr 4463, 1), (Sum.inr 4505, 1)]

theorem sourceEq1434 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1434 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1434 + difference 0 1) (sourceB1434 + difference 1 0) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA1434 + difference 0 1) (sourceB1434 + difference 1 0) sourceC1434) = raw20434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw20434; decide +kernel
    rw [ha]
    exact (canonical20434 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1434 + difference 0 2) (sourceB1434 + difference 2 0) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA1434 + difference 0 2) (sourceB1434 + difference 2 0) sourceC1434) = raw21314 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw21314; decide +kernel
    rw [ha]
    exact (canonical21314 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1434 + difference 0 3) (sourceB1434 + difference 3 0) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4401) := by
    have ha : (tripleCharges (sourceA1434 + difference 0 3) (sourceB1434 + difference 3 0) sourceC1434) = raw20795 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw20795; decide +kernel
    rw [ha]
    exact (canonical20795 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1434 + difference 0 4) (sourceB1434 + difference 4 0) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1434 + difference 0 4) (sourceB1434 + difference 4 0) sourceC1434) = raw20419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw20419; decide +kernel
    rw [ha]
    exact (canonical20419 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1434 + difference 0 5) (sourceB1434 + difference 5 0) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA1434 + difference 0 5) (sourceB1434 + difference 5 0) sourceC1434) = raw21530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw21530; decide +kernel
    rw [ha]
    exact (canonical21530 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1434 + difference 1 0) (sourceB1434 + difference 0 1) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4129) := by
    have ha : (tripleCharges (sourceA1434 + difference 1 0) (sourceB1434 + difference 0 1) sourceC1434) = raw22207 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw22207; decide +kernel
    rw [ha]
    exact (canonical22207 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1434 + difference 1 2) (sourceB1434 + difference 2 1) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4220) := by
    have ha : (tripleCharges (sourceA1434 + difference 1 2) (sourceB1434 + difference 2 1) sourceC1434) = raw22208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw22208; decide +kernel
    rw [ha]
    exact (canonical22208 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1434 + difference 1 3) (sourceB1434 + difference 3 1) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4220) := by
    have ha : (tripleCharges (sourceA1434 + difference 1 3) (sourceB1434 + difference 3 1) sourceC1434) = raw22209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw22209; decide +kernel
    rw [ha]
    exact (canonical22209 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1434 + difference 1 4) (sourceB1434 + difference 4 1) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4272) := by
    have ha : (tripleCharges (sourceA1434 + difference 1 4) (sourceB1434 + difference 4 1) sourceC1434) = raw21520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw21520; decide +kernel
    rw [ha]
    exact (canonical21520 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1434 + difference 1 5) (sourceB1434 + difference 5 1) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4276) := by
    have ha : (tripleCharges (sourceA1434 + difference 1 5) (sourceB1434 + difference 5 1) sourceC1434) = raw21293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw21293; decide +kernel
    rw [ha]
    exact (canonical21293 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1434 + difference 2 0) (sourceB1434 + difference 0 2) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4114) := by
    have ha : (tripleCharges (sourceA1434 + difference 2 0) (sourceB1434 + difference 0 2) sourceC1434) = raw22210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw22210; decide +kernel
    rw [ha]
    exact (canonical22210 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1434 + difference 2 1) (sourceB1434 + difference 1 2) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1434 + difference 2 1) (sourceB1434 + difference 1 2) sourceC1434) = raw22211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw22211; decide +kernel
    rw [ha]
    exact (canonical22211 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1434 + difference 2 3) (sourceB1434 + difference 3 2) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4206) := by
    have ha : (tripleCharges (sourceA1434 + difference 2 3) (sourceB1434 + difference 3 2) sourceC1434) = raw22212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw22212; decide +kernel
    rw [ha]
    exact (canonical22212 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1434 + difference 2 4) (sourceB1434 + difference 4 2) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA1434 + difference 2 4) (sourceB1434 + difference 4 2) sourceC1434) = raw21524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw21524; decide +kernel
    rw [ha]
    exact (canonical21524 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1434 + difference 2 5) (sourceB1434 + difference 5 2) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4253) := by
    have ha : (tripleCharges (sourceA1434 + difference 2 5) (sourceB1434 + difference 5 2) sourceC1434) = raw21298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw21298; decide +kernel
    rw [ha]
    exact (canonical21298 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1434 + difference 3 0) (sourceB1434 + difference 0 3) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4114) := by
    have ha : (tripleCharges (sourceA1434 + difference 3 0) (sourceB1434 + difference 0 3) sourceC1434) = raw22213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw22213; decide +kernel
    rw [ha]
    exact (canonical22213 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1434 + difference 3 1) (sourceB1434 + difference 1 3) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1434 + difference 3 1) (sourceB1434 + difference 1 3) sourceC1434) = raw22214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw22214; decide +kernel
    rw [ha]
    exact (canonical22214 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1434 + difference 3 2) (sourceB1434 + difference 2 3) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4206) := by
    have ha : (tripleCharges (sourceA1434 + difference 3 2) (sourceB1434 + difference 2 3) sourceC1434) = raw22215 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw22215; decide +kernel
    rw [ha]
    exact (canonical22215 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1434 + difference 3 4) (sourceB1434 + difference 4 3) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA1434 + difference 3 4) (sourceB1434 + difference 4 3) sourceC1434) = raw21527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw21527; decide +kernel
    rw [ha]
    exact (canonical21527 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1434 + difference 3 5) (sourceB1434 + difference 5 3) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4253) := by
    have ha : (tripleCharges (sourceA1434 + difference 3 5) (sourceB1434 + difference 5 3) sourceC1434) = raw21303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw21303; decide +kernel
    rw [ha]
    exact (canonical21303 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1434 + difference 4 0) (sourceB1434 + difference 0 4) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4122) := by
    have ha : (tripleCharges (sourceA1434 + difference 4 0) (sourceB1434 + difference 0 4) sourceC1434) = raw22216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw22216; decide +kernel
    rw [ha]
    exact (canonical22216 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1434 + difference 4 1) (sourceB1434 + difference 1 4) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4284) := by
    have ha : (tripleCharges (sourceA1434 + difference 4 1) (sourceB1434 + difference 1 4) sourceC1434) = raw21749 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw21749; decide +kernel
    rw [ha]
    exact (canonical21749 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1434 + difference 4 2) (sourceB1434 + difference 2 4) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4213) := by
    have ha : (tripleCharges (sourceA1434 + difference 4 2) (sourceB1434 + difference 2 4) sourceC1434) = raw22217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw22217; decide +kernel
    rw [ha]
    exact (canonical22217 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1434 + difference 4 3) (sourceB1434 + difference 3 4) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4213) := by
    have ha : (tripleCharges (sourceA1434 + difference 4 3) (sourceB1434 + difference 3 4) sourceC1434) = raw22218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw22218; decide +kernel
    rw [ha]
    exact (canonical22218 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1434 + difference 4 5) (sourceB1434 + difference 5 4) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA1434 + difference 4 5) (sourceB1434 + difference 5 4) sourceC1434) = raw21308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw21308; decide +kernel
    rw [ha]
    exact (canonical21308 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1434 + difference 5 0) (sourceB1434 + difference 0 5) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4120) := by
    have ha : (tripleCharges (sourceA1434 + difference 5 0) (sourceB1434 + difference 0 5) sourceC1434) = raw22219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw22219; decide +kernel
    rw [ha]
    exact (canonical22219 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1434 + difference 5 1) (sourceB1434 + difference 1 5) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1434 + difference 5 1) (sourceB1434 + difference 1 5) sourceC1434) = raw21991 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw21991; decide +kernel
    rw [ha]
    exact (canonical21991 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1434 + difference 5 2) (sourceB1434 + difference 2 5) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4211) := by
    have ha : (tripleCharges (sourceA1434 + difference 5 2) (sourceB1434 + difference 2 5) sourceC1434) = raw22220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw22220; decide +kernel
    rw [ha]
    exact (canonical22220 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1434 + difference 5 3) (sourceB1434 + difference 3 5) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4211) := by
    have ha : (tripleCharges (sourceA1434 + difference 5 3) (sourceB1434 + difference 3 5) sourceC1434) = raw21985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw21985; decide +kernel
    rw [ha]
    exact (canonical21985 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1434 + difference 5 4) (sourceB1434 + difference 4 5) sourceC1434) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4266) := by
    have ha : (tripleCharges (sourceA1434 + difference 5 4) (sourceB1434 + difference 4 5) sourceC1434) = raw21531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1434 sourceB1434 sourceC1434 difference raw21531; decide +kernel
    rw [ha]
    exact (canonical21531 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1434 sourceB1434 sourceC1434
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1434, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1435 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1435 : Charge := ![0, 1, 0, 0, -1, 0]
def sourceC1435 : Charge := ![4, -1, 0, 0, 0, -3]
def sourceForm1435 : Integer.Sparse Master := [(Sum.inr 4070, 1), (Sum.inr 4099, 2), (Sum.inr 4103, 1), (Sum.inr 4109, 1), (Sum.inr 4120, 1), (Sum.inr 4195, 2), (Sum.inr 4198, 2), (Sum.inr 4203, 2), (Sum.inr 4211, 2), (Sum.inr 4231, 2), (Sum.inr 4235, 1), (Sum.inr 4241, 1), (Sum.inr 4251, 2), (Sum.inr 4266, 2), (Sum.inr 4269, 1), (Sum.inr 4272, 1), (Sum.inr 4274, 1), (Sum.inr 4398, 2), (Sum.inr 4454, 1), (Sum.inr 4460, 1), (Sum.inr 4501, 1)]

theorem sourceEq1435 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1435 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1435 + difference 0 1) (sourceB1435 + difference 1 0) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4454) := by
    have ha : (tripleCharges (sourceA1435 + difference 0 1) (sourceB1435 + difference 1 0) sourceC1435) = raw22221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22221; decide +kernel
    rw [ha]
    exact (canonical22221 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1435 + difference 0 2) (sourceB1435 + difference 2 0) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA1435 + difference 0 2) (sourceB1435 + difference 2 0) sourceC1435) = raw22222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22222; decide +kernel
    rw [ha]
    exact (canonical22222 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1435 + difference 0 3) (sourceB1435 + difference 3 0) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4398) := by
    have ha : (tripleCharges (sourceA1435 + difference 0 3) (sourceB1435 + difference 3 0) sourceC1435) = raw22223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22223; decide +kernel
    rw [ha]
    exact (canonical22223 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1435 + difference 0 4) (sourceB1435 + difference 4 0) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1435 + difference 0 4) (sourceB1435 + difference 4 0) sourceC1435) = raw22224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22224; decide +kernel
    rw [ha]
    exact (canonical22224 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1435 + difference 0 5) (sourceB1435 + difference 5 0) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4460) := by
    have ha : (tripleCharges (sourceA1435 + difference 0 5) (sourceB1435 + difference 5 0) sourceC1435) = raw22225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22225; decide +kernel
    rw [ha]
    exact (canonical22225 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1435 + difference 1 0) (sourceB1435 + difference 0 1) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4120) := by
    have ha : (tripleCharges (sourceA1435 + difference 1 0) (sourceB1435 + difference 0 1) sourceC1435) = raw22226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22226; decide +kernel
    rw [ha]
    exact (canonical22226 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1435 + difference 1 2) (sourceB1435 + difference 2 1) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4211) := by
    have ha : (tripleCharges (sourceA1435 + difference 1 2) (sourceB1435 + difference 2 1) sourceC1435) = raw22227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22227; decide +kernel
    rw [ha]
    exact (canonical22227 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1435 + difference 1 3) (sourceB1435 + difference 3 1) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4211) := by
    have ha : (tripleCharges (sourceA1435 + difference 1 3) (sourceB1435 + difference 3 1) sourceC1435) = raw22228 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22228; decide +kernel
    rw [ha]
    exact (canonical22228 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1435 + difference 1 4) (sourceB1435 + difference 4 1) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1435 + difference 1 4) (sourceB1435 + difference 4 1) sourceC1435) = raw22229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22229; decide +kernel
    rw [ha]
    exact (canonical22229 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1435 + difference 1 5) (sourceB1435 + difference 5 1) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1435 + difference 1 5) (sourceB1435 + difference 5 1) sourceC1435) = raw22230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22230; decide +kernel
    rw [ha]
    exact (canonical22230 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1435 + difference 2 0) (sourceB1435 + difference 0 2) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4099) := by
    have ha : (tripleCharges (sourceA1435 + difference 2 0) (sourceB1435 + difference 0 2) sourceC1435) = raw22231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22231; decide +kernel
    rw [ha]
    exact (canonical22231 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1435 + difference 2 1) (sourceB1435 + difference 1 2) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4231) := by
    have ha : (tripleCharges (sourceA1435 + difference 2 1) (sourceB1435 + difference 1 2) sourceC1435) = raw22232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22232; decide +kernel
    rw [ha]
    exact (canonical22232 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1435 + difference 2 3) (sourceB1435 + difference 3 2) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4195) := by
    have ha : (tripleCharges (sourceA1435 + difference 2 3) (sourceB1435 + difference 3 2) sourceC1435) = raw22233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22233; decide +kernel
    rw [ha]
    exact (canonical22233 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1435 + difference 2 4) (sourceB1435 + difference 4 2) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4266) := by
    have ha : (tripleCharges (sourceA1435 + difference 2 4) (sourceB1435 + difference 4 2) sourceC1435) = raw22234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22234; decide +kernel
    rw [ha]
    exact (canonical22234 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1435 + difference 2 5) (sourceB1435 + difference 5 2) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA1435 + difference 2 5) (sourceB1435 + difference 5 2) sourceC1435) = raw22235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22235; decide +kernel
    rw [ha]
    exact (canonical22235 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1435 + difference 3 0) (sourceB1435 + difference 0 3) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4099) := by
    have ha : (tripleCharges (sourceA1435 + difference 3 0) (sourceB1435 + difference 0 3) sourceC1435) = raw22236 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22236; decide +kernel
    rw [ha]
    exact (canonical22236 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1435 + difference 3 1) (sourceB1435 + difference 1 3) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4231) := by
    have ha : (tripleCharges (sourceA1435 + difference 3 1) (sourceB1435 + difference 1 3) sourceC1435) = raw22237 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22237; decide +kernel
    rw [ha]
    exact (canonical22237 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1435 + difference 3 2) (sourceB1435 + difference 2 3) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4195) := by
    have ha : (tripleCharges (sourceA1435 + difference 3 2) (sourceB1435 + difference 2 3) sourceC1435) = raw22238 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22238; decide +kernel
    rw [ha]
    exact (canonical22238 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1435 + difference 3 4) (sourceB1435 + difference 4 3) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4266) := by
    have ha : (tripleCharges (sourceA1435 + difference 3 4) (sourceB1435 + difference 4 3) sourceC1435) = raw22239 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22239; decide +kernel
    rw [ha]
    exact (canonical22239 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1435 + difference 3 5) (sourceB1435 + difference 5 3) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4251) := by
    have ha : (tripleCharges (sourceA1435 + difference 3 5) (sourceB1435 + difference 5 3) sourceC1435) = raw22240 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22240; decide +kernel
    rw [ha]
    exact (canonical22240 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1435 + difference 4 0) (sourceB1435 + difference 0 4) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4109) := by
    have ha : (tripleCharges (sourceA1435 + difference 4 0) (sourceB1435 + difference 0 4) sourceC1435) = raw22241 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22241; decide +kernel
    rw [ha]
    exact (canonical22241 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1435 + difference 4 1) (sourceB1435 + difference 1 4) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4241) := by
    have ha : (tripleCharges (sourceA1435 + difference 4 1) (sourceB1435 + difference 1 4) sourceC1435) = raw22242 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22242; decide +kernel
    rw [ha]
    exact (canonical22242 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1435 + difference 4 2) (sourceB1435 + difference 2 4) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4203) := by
    have ha : (tripleCharges (sourceA1435 + difference 4 2) (sourceB1435 + difference 2 4) sourceC1435) = raw22243 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22243; decide +kernel
    rw [ha]
    exact (canonical22243 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1435 + difference 4 3) (sourceB1435 + difference 3 4) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4203) := by
    have ha : (tripleCharges (sourceA1435 + difference 4 3) (sourceB1435 + difference 3 4) sourceC1435) = raw22244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22244; decide +kernel
    rw [ha]
    exact (canonical22244 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1435 + difference 4 5) (sourceB1435 + difference 5 4) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4272) := by
    have ha : (tripleCharges (sourceA1435 + difference 4 5) (sourceB1435 + difference 5 4) sourceC1435) = raw22245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22245; decide +kernel
    rw [ha]
    exact (canonical22245 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1435 + difference 5 0) (sourceB1435 + difference 0 5) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4103) := by
    have ha : (tripleCharges (sourceA1435 + difference 5 0) (sourceB1435 + difference 0 5) sourceC1435) = raw22246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22246; decide +kernel
    rw [ha]
    exact (canonical22246 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1435 + difference 5 1) (sourceB1435 + difference 1 5) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4235) := by
    have ha : (tripleCharges (sourceA1435 + difference 5 1) (sourceB1435 + difference 1 5) sourceC1435) = raw22247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22247; decide +kernel
    rw [ha]
    exact (canonical22247 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1435 + difference 5 2) (sourceB1435 + difference 2 5) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4198) := by
    have ha : (tripleCharges (sourceA1435 + difference 5 2) (sourceB1435 + difference 2 5) sourceC1435) = raw22248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22248; decide +kernel
    rw [ha]
    exact (canonical22248 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1435 + difference 5 3) (sourceB1435 + difference 3 5) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4198) := by
    have ha : (tripleCharges (sourceA1435 + difference 5 3) (sourceB1435 + difference 3 5) sourceC1435) = raw22249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22249; decide +kernel
    rw [ha]
    exact (canonical22249 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1435 + difference 5 4) (sourceB1435 + difference 4 5) sourceC1435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4274) := by
    have ha : (tripleCharges (sourceA1435 + difference 5 4) (sourceB1435 + difference 4 5) sourceC1435) = raw22250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1435 sourceB1435 sourceC1435 difference raw22250; decide +kernel
    rw [ha]
    exact (canonical22250 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1435 sourceB1435 sourceC1435
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1435, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1436 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1436 : Charge := ![0, 0, 0, 0, 2, -2]
def sourceC1436 : Charge := ![4, 0, 0, 0, -3, -1]
def sourceForm1436 : Integer.Sparse Master := [(Sum.inr 566, 1), (Sum.inr 729, 3), (Sum.inr 860, 1), (Sum.inr 863, 1), (Sum.inr 4070, -1)]

theorem sourceEq1436 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1436 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1436 + difference 4 0) (sourceB1436 + difference 0 4) sourceC1436) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 566) := by
    have ha : (tripleCharges (sourceA1436 + difference 4 0) (sourceB1436 + difference 0 4) sourceC1436) = raw22251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1436 sourceB1436 sourceC1436 difference raw22251; decide +kernel
    rw [ha]
    exact (canonical22251 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1436 + difference 4 1) (sourceB1436 + difference 1 4) sourceC1436) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 729) := by
    have ha : (tripleCharges (sourceA1436 + difference 4 1) (sourceB1436 + difference 1 4) sourceC1436) = raw22252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1436 sourceB1436 sourceC1436 difference raw22252; decide +kernel
    rw [ha]
    exact (canonical22252 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1436 + difference 4 2) (sourceB1436 + difference 2 4) sourceC1436) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 729) := by
    have ha : (tripleCharges (sourceA1436 + difference 4 2) (sourceB1436 + difference 2 4) sourceC1436) = raw22253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1436 sourceB1436 sourceC1436 difference raw22253; decide +kernel
    rw [ha]
    exact (canonical22253 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1436 + difference 4 3) (sourceB1436 + difference 3 4) sourceC1436) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 729) := by
    have ha : (tripleCharges (sourceA1436 + difference 4 3) (sourceB1436 + difference 3 4) sourceC1436) = raw22254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1436 sourceB1436 sourceC1436 difference raw22254; decide +kernel
    rw [ha]
    exact (canonical22254 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1436 + difference 4 4) (sourceB1436 + difference 4 4) sourceC1436) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 860) := by
    have ha : (tripleCharges (sourceA1436 + difference 4 4) (sourceB1436 + difference 4 4) sourceC1436) = raw22255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1436 sourceB1436 sourceC1436 difference raw22255; decide +kernel
    rw [ha]
    exact (canonical22255 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1436 + difference 4 5) (sourceB1436 + difference 5 4) sourceC1436) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 863) := by
    have ha : (tripleCharges (sourceA1436 + difference 4 5) (sourceB1436 + difference 5 4) sourceC1436) = raw22256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1436 sourceB1436 sourceC1436 difference raw22256; decide +kernel
    rw [ha]
    exact (canonical22256 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1436 + sourceB1436) sourceC1436) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1436 + sourceB1436) sourceC1436) = raw22257 := by
      apply Matrix.ext; unfold doubleCharges sourceA1436 sourceB1436 sourceC1436 raw22257; decide +kernel
    rw [ha]
    exact (canonical22257 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1436 sourceB1436 sourceC1436
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1436, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1437 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1437 : Charge := ![0, 0, 0, 0, 1, -1]
def sourceC1437 : Charge := ![4, 0, 0, 0, -2, -2]
def sourceForm1437 : Integer.Sparse Master := [(Sum.inr 4071, 1), (Sum.inr 4121, 3), (Sum.inr 4134, 1), (Sum.inr 4137, 1), (Sum.inr 4212, 6), (Sum.inr 4225, 3), (Sum.inr 4228, 3), (Sum.inr 4272, 3), (Sum.inr 4273, 3), (Sum.inr 4280, 1), (Sum.inr 4431, 3), (Sum.inr 4510, 1), (Sum.inr 4511, 1)]

theorem sourceEq1437 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1437 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1437 + difference 0 1) (sourceB1437 + difference 1 0) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA1437 + difference 0 1) (sourceB1437 + difference 1 0) sourceC1437) = raw22258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22258; decide +kernel
    rw [ha]
    exact (canonical22258 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1437 + difference 0 2) (sourceB1437 + difference 2 0) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA1437 + difference 0 2) (sourceB1437 + difference 2 0) sourceC1437) = raw22259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22259; decide +kernel
    rw [ha]
    exact (canonical22259 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1437 + difference 0 3) (sourceB1437 + difference 3 0) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA1437 + difference 0 3) (sourceB1437 + difference 3 0) sourceC1437) = raw22260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22260; decide +kernel
    rw [ha]
    exact (canonical22260 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1437 + difference 0 4) (sourceB1437 + difference 4 0) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA1437 + difference 0 4) (sourceB1437 + difference 4 0) sourceC1437) = raw22261 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22261; decide +kernel
    rw [ha]
    exact (canonical22261 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1437 + difference 0 5) (sourceB1437 + difference 5 0) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1437 + difference 0 5) (sourceB1437 + difference 5 0) sourceC1437) = raw22262 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22262; decide +kernel
    rw [ha]
    exact (canonical22262 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1437 + difference 1 0) (sourceB1437 + difference 0 1) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4121) := by
    have ha : (tripleCharges (sourceA1437 + difference 1 0) (sourceB1437 + difference 0 1) sourceC1437) = raw22263 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22263; decide +kernel
    rw [ha]
    exact (canonical22263 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1437 + difference 1 2) (sourceB1437 + difference 2 1) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4212) := by
    have ha : (tripleCharges (sourceA1437 + difference 1 2) (sourceB1437 + difference 2 1) sourceC1437) = raw22264 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22264; decide +kernel
    rw [ha]
    exact (canonical22264 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1437 + difference 1 3) (sourceB1437 + difference 3 1) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4212) := by
    have ha : (tripleCharges (sourceA1437 + difference 1 3) (sourceB1437 + difference 3 1) sourceC1437) = raw22265 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22265; decide +kernel
    rw [ha]
    exact (canonical22265 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1437 + difference 1 4) (sourceB1437 + difference 4 1) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4272) := by
    have ha : (tripleCharges (sourceA1437 + difference 1 4) (sourceB1437 + difference 4 1) sourceC1437) = raw22266 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22266; decide +kernel
    rw [ha]
    exact (canonical22266 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1437 + difference 1 5) (sourceB1437 + difference 5 1) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1437 + difference 1 5) (sourceB1437 + difference 5 1) sourceC1437) = raw22267 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22267; decide +kernel
    rw [ha]
    exact (canonical22267 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1437 + difference 2 0) (sourceB1437 + difference 0 2) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4121) := by
    have ha : (tripleCharges (sourceA1437 + difference 2 0) (sourceB1437 + difference 0 2) sourceC1437) = raw22268 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22268; decide +kernel
    rw [ha]
    exact (canonical22268 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1437 + difference 2 1) (sourceB1437 + difference 1 2) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4212) := by
    have ha : (tripleCharges (sourceA1437 + difference 2 1) (sourceB1437 + difference 1 2) sourceC1437) = raw22269 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22269; decide +kernel
    rw [ha]
    exact (canonical22269 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1437 + difference 2 3) (sourceB1437 + difference 3 2) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4212) := by
    have ha : (tripleCharges (sourceA1437 + difference 2 3) (sourceB1437 + difference 3 2) sourceC1437) = raw22270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22270; decide +kernel
    rw [ha]
    exact (canonical22270 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1437 + difference 2 4) (sourceB1437 + difference 4 2) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4272) := by
    have ha : (tripleCharges (sourceA1437 + difference 2 4) (sourceB1437 + difference 4 2) sourceC1437) = raw22271 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22271; decide +kernel
    rw [ha]
    exact (canonical22271 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1437 + difference 2 5) (sourceB1437 + difference 5 2) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1437 + difference 2 5) (sourceB1437 + difference 5 2) sourceC1437) = raw22272 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22272; decide +kernel
    rw [ha]
    exact (canonical22272 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1437 + difference 3 0) (sourceB1437 + difference 0 3) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4121) := by
    have ha : (tripleCharges (sourceA1437 + difference 3 0) (sourceB1437 + difference 0 3) sourceC1437) = raw22273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22273; decide +kernel
    rw [ha]
    exact (canonical22273 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1437 + difference 3 1) (sourceB1437 + difference 1 3) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4212) := by
    have ha : (tripleCharges (sourceA1437 + difference 3 1) (sourceB1437 + difference 1 3) sourceC1437) = raw22274 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22274; decide +kernel
    rw [ha]
    exact (canonical22274 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1437 + difference 3 2) (sourceB1437 + difference 2 3) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4212) := by
    have ha : (tripleCharges (sourceA1437 + difference 3 2) (sourceB1437 + difference 2 3) sourceC1437) = raw22275 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22275; decide +kernel
    rw [ha]
    exact (canonical22275 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1437 + difference 3 4) (sourceB1437 + difference 4 3) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4272) := by
    have ha : (tripleCharges (sourceA1437 + difference 3 4) (sourceB1437 + difference 4 3) sourceC1437) = raw22276 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22276; decide +kernel
    rw [ha]
    exact (canonical22276 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1437 + difference 3 5) (sourceB1437 + difference 5 3) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1437 + difference 3 5) (sourceB1437 + difference 5 3) sourceC1437) = raw22277 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22277; decide +kernel
    rw [ha]
    exact (canonical22277 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1437 + difference 4 0) (sourceB1437 + difference 0 4) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4137) := by
    have ha : (tripleCharges (sourceA1437 + difference 4 0) (sourceB1437 + difference 0 4) sourceC1437) = raw22278 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22278; decide +kernel
    rw [ha]
    exact (canonical22278 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1437 + difference 4 1) (sourceB1437 + difference 1 4) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4228) := by
    have ha : (tripleCharges (sourceA1437 + difference 4 1) (sourceB1437 + difference 1 4) sourceC1437) = raw22279 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22279; decide +kernel
    rw [ha]
    exact (canonical22279 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1437 + difference 4 2) (sourceB1437 + difference 2 4) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4228) := by
    have ha : (tripleCharges (sourceA1437 + difference 4 2) (sourceB1437 + difference 2 4) sourceC1437) = raw22280 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22280; decide +kernel
    rw [ha]
    exact (canonical22280 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1437 + difference 4 3) (sourceB1437 + difference 3 4) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4228) := by
    have ha : (tripleCharges (sourceA1437 + difference 4 3) (sourceB1437 + difference 3 4) sourceC1437) = raw22281 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22281; decide +kernel
    rw [ha]
    exact (canonical22281 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1437 + difference 4 5) (sourceB1437 + difference 5 4) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (tripleCharges (sourceA1437 + difference 4 5) (sourceB1437 + difference 5 4) sourceC1437) = raw22282 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22282; decide +kernel
    rw [ha]
    exact (canonical22282 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1437 + difference 5 0) (sourceB1437 + difference 0 5) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4134) := by
    have ha : (tripleCharges (sourceA1437 + difference 5 0) (sourceB1437 + difference 0 5) sourceC1437) = raw22283 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22283; decide +kernel
    rw [ha]
    exact (canonical22283 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1437 + difference 5 1) (sourceB1437 + difference 1 5) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4225) := by
    have ha : (tripleCharges (sourceA1437 + difference 5 1) (sourceB1437 + difference 1 5) sourceC1437) = raw22284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22284; decide +kernel
    rw [ha]
    exact (canonical22284 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1437 + difference 5 2) (sourceB1437 + difference 2 5) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4225) := by
    have ha : (tripleCharges (sourceA1437 + difference 5 2) (sourceB1437 + difference 2 5) sourceC1437) = raw22285 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22285; decide +kernel
    rw [ha]
    exact (canonical22285 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1437 + difference 5 3) (sourceB1437 + difference 3 5) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4225) := by
    have ha : (tripleCharges (sourceA1437 + difference 5 3) (sourceB1437 + difference 3 5) sourceC1437) = raw22286 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22286; decide +kernel
    rw [ha]
    exact (canonical22286 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1437 + difference 5 4) (sourceB1437 + difference 4 5) sourceC1437) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4280) := by
    have ha : (tripleCharges (sourceA1437 + difference 5 4) (sourceB1437 + difference 4 5) sourceC1437) = raw22287 := by
      apply Matrix.ext; unfold tripleCharges sourceA1437 sourceB1437 sourceC1437 difference raw22287; decide +kernel
    rw [ha]
    exact (canonical22287 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1437 sourceB1437 sourceC1437
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1437, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1438 : Charge := ![0, 0, 0, 0, 1, -1]
def sourceB1438 : Charge := ![4, 0, 0, 0, -2, -2]
def sourceC1438 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceForm1438 : Integer.Sparse Master := [(Sum.inr 4070, 1), (Sum.inr 4122, 3), (Sum.inr 4136, 1), (Sum.inr 4138, 1), (Sum.inr 4213, 6), (Sum.inr 4227, 3), (Sum.inr 4229, 3), (Sum.inr 4269, 3), (Sum.inr 4270, 3), (Sum.inr 4285, 1), (Sum.inr 4428, 3), (Sum.inr 4505, 1), (Sum.inr 4507, 1)]

theorem sourceEq1438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1438 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1438 + difference 0 1) (sourceB1438 + difference 1 0) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA1438 + difference 0 1) (sourceB1438 + difference 1 0) sourceC1438) = raw21750 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21750; decide +kernel
    rw [ha]
    exact (canonical21750 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1438 + difference 0 2) (sourceB1438 + difference 2 0) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA1438 + difference 0 2) (sourceB1438 + difference 2 0) sourceC1438) = raw21751 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21751; decide +kernel
    rw [ha]
    exact (canonical21751 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1438 + difference 0 3) (sourceB1438 + difference 3 0) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA1438 + difference 0 3) (sourceB1438 + difference 3 0) sourceC1438) = raw20803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw20803; decide +kernel
    rw [ha]
    exact (canonical20803 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1438 + difference 0 4) (sourceB1438 + difference 4 0) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA1438 + difference 0 4) (sourceB1438 + difference 4 0) sourceC1438) = raw20434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw20434; decide +kernel
    rw [ha]
    exact (canonical20434 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1438 + difference 0 5) (sourceB1438 + difference 5 0) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA1438 + difference 0 5) (sourceB1438 + difference 5 0) sourceC1438) = raw21309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21309; decide +kernel
    rw [ha]
    exact (canonical21309 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1438 + difference 1 0) (sourceB1438 + difference 0 1) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4122) := by
    have ha : (tripleCharges (sourceA1438 + difference 1 0) (sourceB1438 + difference 0 1) sourceC1438) = raw22216 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22216; decide +kernel
    rw [ha]
    exact (canonical22216 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1438 + difference 1 2) (sourceB1438 + difference 2 1) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4213) := by
    have ha : (tripleCharges (sourceA1438 + difference 1 2) (sourceB1438 + difference 2 1) sourceC1438) = raw22217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22217; decide +kernel
    rw [ha]
    exact (canonical22217 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1438 + difference 1 3) (sourceB1438 + difference 3 1) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4213) := by
    have ha : (tripleCharges (sourceA1438 + difference 1 3) (sourceB1438 + difference 3 1) sourceC1438) = raw22218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22218; decide +kernel
    rw [ha]
    exact (canonical22218 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1438 + difference 1 4) (sourceB1438 + difference 4 1) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1438 + difference 1 4) (sourceB1438 + difference 4 1) sourceC1438) = raw21313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21313; decide +kernel
    rw [ha]
    exact (canonical21313 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1438 + difference 1 5) (sourceB1438 + difference 5 1) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA1438 + difference 1 5) (sourceB1438 + difference 5 1) sourceC1438) = raw21308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21308; decide +kernel
    rw [ha]
    exact (canonical21308 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1438 + difference 2 0) (sourceB1438 + difference 0 2) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4122) := by
    have ha : (tripleCharges (sourceA1438 + difference 2 0) (sourceB1438 + difference 0 2) sourceC1438) = raw22288 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22288; decide +kernel
    rw [ha]
    exact (canonical22288 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1438 + difference 2 1) (sourceB1438 + difference 1 2) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4213) := by
    have ha : (tripleCharges (sourceA1438 + difference 2 1) (sourceB1438 + difference 1 2) sourceC1438) = raw22289 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22289; decide +kernel
    rw [ha]
    exact (canonical22289 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1438 + difference 2 3) (sourceB1438 + difference 3 2) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4213) := by
    have ha : (tripleCharges (sourceA1438 + difference 2 3) (sourceB1438 + difference 3 2) sourceC1438) = raw22290 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22290; decide +kernel
    rw [ha]
    exact (canonical22290 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1438 + difference 2 4) (sourceB1438 + difference 4 2) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1438 + difference 2 4) (sourceB1438 + difference 4 2) sourceC1438) = raw22211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22211; decide +kernel
    rw [ha]
    exact (canonical22211 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1438 + difference 2 5) (sourceB1438 + difference 5 2) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA1438 + difference 2 5) (sourceB1438 + difference 5 2) sourceC1438) = raw21736 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21736; decide +kernel
    rw [ha]
    exact (canonical21736 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1438 + difference 3 0) (sourceB1438 + difference 0 3) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4122) := by
    have ha : (tripleCharges (sourceA1438 + difference 3 0) (sourceB1438 + difference 0 3) sourceC1438) = raw22291 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22291; decide +kernel
    rw [ha]
    exact (canonical22291 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1438 + difference 3 1) (sourceB1438 + difference 1 3) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4213) := by
    have ha : (tripleCharges (sourceA1438 + difference 3 1) (sourceB1438 + difference 1 3) sourceC1438) = raw22292 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22292; decide +kernel
    rw [ha]
    exact (canonical22292 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1438 + difference 3 2) (sourceB1438 + difference 2 3) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4213) := by
    have ha : (tripleCharges (sourceA1438 + difference 3 2) (sourceB1438 + difference 2 3) sourceC1438) = raw22293 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22293; decide +kernel
    rw [ha]
    exact (canonical22293 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1438 + difference 3 4) (sourceB1438 + difference 4 3) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4269) := by
    have ha : (tripleCharges (sourceA1438 + difference 3 4) (sourceB1438 + difference 4 3) sourceC1438) = raw22214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22214; decide +kernel
    rw [ha]
    exact (canonical22214 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1438 + difference 3 5) (sourceB1438 + difference 5 3) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4270) := by
    have ha : (tripleCharges (sourceA1438 + difference 3 5) (sourceB1438 + difference 5 3) sourceC1438) = raw21740 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21740; decide +kernel
    rw [ha]
    exact (canonical21740 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1438 + difference 4 0) (sourceB1438 + difference 0 4) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4138) := by
    have ha : (tripleCharges (sourceA1438 + difference 4 0) (sourceB1438 + difference 0 4) sourceC1438) = raw22294 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22294; decide +kernel
    rw [ha]
    exact (canonical22294 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1438 + difference 4 1) (sourceB1438 + difference 1 4) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4229) := by
    have ha : (tripleCharges (sourceA1438 + difference 4 1) (sourceB1438 + difference 1 4) sourceC1438) = raw22295 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22295; decide +kernel
    rw [ha]
    exact (canonical22295 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1438 + difference 4 2) (sourceB1438 + difference 2 4) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4229) := by
    have ha : (tripleCharges (sourceA1438 + difference 4 2) (sourceB1438 + difference 2 4) sourceC1438) = raw22296 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22296; decide +kernel
    rw [ha]
    exact (canonical22296 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1438 + difference 4 3) (sourceB1438 + difference 3 4) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4229) := by
    have ha : (tripleCharges (sourceA1438 + difference 4 3) (sourceB1438 + difference 3 4) sourceC1438) = raw22297 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22297; decide +kernel
    rw [ha]
    exact (canonical22297 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1438 + difference 4 5) (sourceB1438 + difference 5 4) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4285) := by
    have ha : (tripleCharges (sourceA1438 + difference 4 5) (sourceB1438 + difference 5 4) sourceC1438) = raw21744 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21744; decide +kernel
    rw [ha]
    exact (canonical21744 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1438 + difference 5 0) (sourceB1438 + difference 0 5) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4136) := by
    have ha : (tripleCharges (sourceA1438 + difference 5 0) (sourceB1438 + difference 0 5) sourceC1438) = raw22298 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22298; decide +kernel
    rw [ha]
    exact (canonical22298 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1438 + difference 5 1) (sourceB1438 + difference 1 5) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4227) := by
    have ha : (tripleCharges (sourceA1438 + difference 5 1) (sourceB1438 + difference 1 5) sourceC1438) = raw22299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22299; decide +kernel
    rw [ha]
    exact (canonical22299 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1438 + difference 5 2) (sourceB1438 + difference 2 5) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4227) := by
    have ha : (tripleCharges (sourceA1438 + difference 5 2) (sourceB1438 + difference 2 5) sourceC1438) = raw22300 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw22300; decide +kernel
    rw [ha]
    exact (canonical22300 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1438 + difference 5 3) (sourceB1438 + difference 3 5) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4227) := by
    have ha : (tripleCharges (sourceA1438 + difference 5 3) (sourceB1438 + difference 3 5) sourceC1438) = raw21994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21994; decide +kernel
    rw [ha]
    exact (canonical21994 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1438 + difference 5 4) (sourceB1438 + difference 4 5) sourceC1438) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1438 + difference 5 4) (sourceB1438 + difference 4 5) sourceC1438) = raw21991 := by
      apply Matrix.ext; unfold tripleCharges sourceA1438 sourceB1438 sourceC1438 difference raw21991; decide +kernel
    rw [ha]
    exact (canonical21991 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1438 sourceB1438 sourceC1438
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1438, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1439 : Charge := ![-4, 0, 0, 0, 1, 3]
def sourceB1439 : Charge := ![4, 0, 0, 0, -1, -3]
def sourceC1439 : Charge := ![0, 0, 0, 0, 0, 0]
def sourceForm1439 : Integer.Sparse Master := [(Sum.inr 4058, 3), (Sum.inr 4060, 1), (Sum.inr 4061, 1), (Sum.inr 4064, 6), (Sum.inr 4066, 3), (Sum.inr 4067, 3), (Sum.inr 4069, 3), (Sum.inr 4070, 3), (Sum.inr 4071, 1), (Sum.inr 4072, 1), (Sum.inr 4081, 3), (Sum.inr 4084, 1), (Sum.inr 4085, 1)]

theorem sourceEq1439 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1439 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1439 + difference 0 1) (sourceB1439 + difference 1 0) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA1439 + difference 0 1) (sourceB1439 + difference 1 0) sourceC1439) = raw5210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw5210; decide +kernel
    rw [ha]
    exact (canonical5210 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1439 + difference 0 2) (sourceB1439 + difference 2 0) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA1439 + difference 0 2) (sourceB1439 + difference 2 0) sourceC1439) = raw5211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw5211; decide +kernel
    rw [ha]
    exact (canonical5211 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1439 + difference 0 3) (sourceB1439 + difference 3 0) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (tripleCharges (sourceA1439 + difference 0 3) (sourceB1439 + difference 3 0) sourceC1439) = raw5212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw5212; decide +kernel
    rw [ha]
    exact (canonical5212 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1439 + difference 0 4) (sourceB1439 + difference 4 0) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (tripleCharges (sourceA1439 + difference 0 4) (sourceB1439 + difference 4 0) sourceC1439) = raw2934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw2934; decide +kernel
    rw [ha]
    exact (canonical2934 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1439 + difference 0 5) (sourceB1439 + difference 5 0) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1439 + difference 0 5) (sourceB1439 + difference 5 0) sourceC1439) = raw2929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw2929; decide +kernel
    rw [ha]
    exact (canonical2929 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1439 + difference 1 0) (sourceB1439 + difference 0 1) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (tripleCharges (sourceA1439 + difference 1 0) (sourceB1439 + difference 0 1) sourceC1439) = raw22301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22301; decide +kernel
    rw [ha]
    exact (canonical22301 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1439 + difference 1 2) (sourceB1439 + difference 2 1) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA1439 + difference 1 2) (sourceB1439 + difference 2 1) sourceC1439) = raw22302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22302; decide +kernel
    rw [ha]
    exact (canonical22302 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1439 + difference 1 3) (sourceB1439 + difference 3 1) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA1439 + difference 1 3) (sourceB1439 + difference 3 1) sourceC1439) = raw22303 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22303; decide +kernel
    rw [ha]
    exact (canonical22303 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1439 + difference 1 4) (sourceB1439 + difference 4 1) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1439 + difference 1 4) (sourceB1439 + difference 4 1) sourceC1439) = raw5197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw5197; decide +kernel
    rw [ha]
    exact (canonical5197 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1439 + difference 1 5) (sourceB1439 + difference 5 1) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1439 + difference 1 5) (sourceB1439 + difference 5 1) sourceC1439) = raw11531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw11531; decide +kernel
    rw [ha]
    exact (canonical11531 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1439 + difference 2 0) (sourceB1439 + difference 0 2) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (tripleCharges (sourceA1439 + difference 2 0) (sourceB1439 + difference 0 2) sourceC1439) = raw22304 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22304; decide +kernel
    rw [ha]
    exact (canonical22304 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1439 + difference 2 1) (sourceB1439 + difference 1 2) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA1439 + difference 2 1) (sourceB1439 + difference 1 2) sourceC1439) = raw22305 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22305; decide +kernel
    rw [ha]
    exact (canonical22305 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1439 + difference 2 3) (sourceB1439 + difference 3 2) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA1439 + difference 2 3) (sourceB1439 + difference 3 2) sourceC1439) = raw22306 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22306; decide +kernel
    rw [ha]
    exact (canonical22306 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1439 + difference 2 4) (sourceB1439 + difference 4 2) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1439 + difference 2 4) (sourceB1439 + difference 4 2) sourceC1439) = raw5201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw5201; decide +kernel
    rw [ha]
    exact (canonical5201 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1439 + difference 2 5) (sourceB1439 + difference 5 2) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1439 + difference 2 5) (sourceB1439 + difference 5 2) sourceC1439) = raw11534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw11534; decide +kernel
    rw [ha]
    exact (canonical11534 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1439 + difference 3 0) (sourceB1439 + difference 0 3) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (tripleCharges (sourceA1439 + difference 3 0) (sourceB1439 + difference 0 3) sourceC1439) = raw22307 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22307; decide +kernel
    rw [ha]
    exact (canonical22307 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1439 + difference 3 1) (sourceB1439 + difference 1 3) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA1439 + difference 3 1) (sourceB1439 + difference 1 3) sourceC1439) = raw22308 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22308; decide +kernel
    rw [ha]
    exact (canonical22308 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1439 + difference 3 2) (sourceB1439 + difference 2 3) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (tripleCharges (sourceA1439 + difference 3 2) (sourceB1439 + difference 2 3) sourceC1439) = raw22309 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22309; decide +kernel
    rw [ha]
    exact (canonical22309 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1439 + difference 3 4) (sourceB1439 + difference 4 3) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (tripleCharges (sourceA1439 + difference 3 4) (sourceB1439 + difference 4 3) sourceC1439) = raw5205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw5205; decide +kernel
    rw [ha]
    exact (canonical5205 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1439 + difference 3 5) (sourceB1439 + difference 5 3) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (tripleCharges (sourceA1439 + difference 3 5) (sourceB1439 + difference 5 3) sourceC1439) = raw11537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw11537; decide +kernel
    rw [ha]
    exact (canonical11537 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1439 + difference 4 0) (sourceB1439 + difference 0 4) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (tripleCharges (sourceA1439 + difference 4 0) (sourceB1439 + difference 0 4) sourceC1439) = raw22310 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22310; decide +kernel
    rw [ha]
    exact (canonical22310 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1439 + difference 4 1) (sourceB1439 + difference 1 4) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA1439 + difference 4 1) (sourceB1439 + difference 1 4) sourceC1439) = raw22311 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22311; decide +kernel
    rw [ha]
    exact (canonical22311 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1439 + difference 4 2) (sourceB1439 + difference 2 4) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA1439 + difference 4 2) (sourceB1439 + difference 2 4) sourceC1439) = raw22312 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22312; decide +kernel
    rw [ha]
    exact (canonical22312 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1439 + difference 4 3) (sourceB1439 + difference 3 4) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (tripleCharges (sourceA1439 + difference 4 3) (sourceB1439 + difference 3 4) sourceC1439) = raw22313 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw22313; decide +kernel
    rw [ha]
    exact (canonical22313 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1439 + difference 4 5) (sourceB1439 + difference 5 4) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (tripleCharges (sourceA1439 + difference 4 5) (sourceB1439 + difference 5 4) sourceC1439) = raw11540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw11540; decide +kernel
    rw [ha]
    exact (canonical11540 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1439 + difference 5 0) (sourceB1439 + difference 0 5) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (tripleCharges (sourceA1439 + difference 5 0) (sourceB1439 + difference 0 5) sourceC1439) = raw20079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw20079; decide +kernel
    rw [ha]
    exact (canonical20079 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1439 + difference 5 1) (sourceB1439 + difference 1 5) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1439 + difference 5 1) (sourceB1439 + difference 1 5) sourceC1439) = raw20080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw20080; decide +kernel
    rw [ha]
    exact (canonical20080 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1439 + difference 5 2) (sourceB1439 + difference 2 5) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1439 + difference 5 2) (sourceB1439 + difference 2 5) sourceC1439) = raw20081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw20081; decide +kernel
    rw [ha]
    exact (canonical20081 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1439 + difference 5 3) (sourceB1439 + difference 3 5) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (tripleCharges (sourceA1439 + difference 5 3) (sourceB1439 + difference 3 5) sourceC1439) = raw20082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw20082; decide +kernel
    rw [ha]
    exact (canonical20082 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1439 + difference 5 4) (sourceB1439 + difference 4 5) sourceC1439) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4072) := by
    have ha : (tripleCharges (sourceA1439 + difference 5 4) (sourceB1439 + difference 4 5) sourceC1439) = raw5213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1439 sourceB1439 sourceC1439 difference raw5213; decide +kernel
    rw [ha]
    exact (canonical5213 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1439 sourceB1439 sourceC1439
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1439, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
