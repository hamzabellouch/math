import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical89
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical90
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical151
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical156
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical168
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical169
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical171
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical172
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical174
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical175
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical176
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical177
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical178
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical180
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical181
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical182
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical183
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical184
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical185

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA1536 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1536 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC1536 : Charge := ![3, -1, 0, 1, -2, -1]
def sourceForm1536 : Integer.Sparse Master := [(Sum.inr 573, 1), (Sum.inr 889, 1), (Sum.inr 901, 1), (Sum.inr 985, 1), (Sum.inr 1004, 1), (Sum.inr 1005, 1), (Sum.inr 4080, -1)]

theorem sourceEq1536 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1536 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1536 + difference 1 0) (sourceB1536 + difference 0 1) sourceC1536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 573) := by
    have ha : (tripleCharges (sourceA1536 + difference 1 0) (sourceB1536 + difference 0 1) sourceC1536) = raw23319 := by
      apply Matrix.ext; unfold tripleCharges sourceA1536 sourceB1536 sourceC1536 difference raw23319; decide +kernel
    rw [ha]
    exact (canonical23319 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1536 + difference 1 1) (sourceB1536 + difference 1 1) sourceC1536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1536 + difference 1 1) (sourceB1536 + difference 1 1) sourceC1536) = raw21590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1536 sourceB1536 sourceC1536 difference raw21590; decide +kernel
    rw [ha]
    exact (canonical21590 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1536 + difference 1 2) (sourceB1536 + difference 2 1) sourceC1536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 901) := by
    have ha : (tripleCharges (sourceA1536 + difference 1 2) (sourceB1536 + difference 2 1) sourceC1536) = raw23320 := by
      apply Matrix.ext; unfold tripleCharges sourceA1536 sourceB1536 sourceC1536 difference raw23320; decide +kernel
    rw [ha]
    exact (canonical23320 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1536 + difference 1 3) (sourceB1536 + difference 3 1) sourceC1536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 889) := by
    have ha : (tripleCharges (sourceA1536 + difference 1 3) (sourceB1536 + difference 3 1) sourceC1536) = raw23321 := by
      apply Matrix.ext; unfold tripleCharges sourceA1536 sourceB1536 sourceC1536 difference raw23321; decide +kernel
    rw [ha]
    exact (canonical23321 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1536 + difference 1 4) (sourceB1536 + difference 4 1) sourceC1536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1005) := by
    have ha : (tripleCharges (sourceA1536 + difference 1 4) (sourceB1536 + difference 4 1) sourceC1536) = raw21587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1536 sourceB1536 sourceC1536 difference raw21587; decide +kernel
    rw [ha]
    exact (canonical21587 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1536 + difference 1 5) (sourceB1536 + difference 5 1) sourceC1536) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1004) := by
    have ha : (tripleCharges (sourceA1536 + difference 1 5) (sourceB1536 + difference 5 1) sourceC1536) = raw23322 := by
      apply Matrix.ext; unfold tripleCharges sourceA1536 sourceB1536 sourceC1536 difference raw23322; decide +kernel
    rw [ha]
    exact (canonical23322 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1536 + sourceB1536) sourceC1536) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1536 + sourceB1536) sourceC1536) = raw21586 := by
      apply Matrix.ext; unfold doubleCharges sourceA1536 sourceB1536 sourceC1536 raw21586; decide +kernel
    rw [ha]
    exact (canonical21586 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1536 sourceB1536 sourceC1536
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1536, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1537 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1537 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceC1537 : Charge := ![3, -1, 0, 1, -2, -1]
def sourceForm1537 : Integer.Sparse Master := [(Sum.inr 866, 1), (Sum.inr 873, 1), (Sum.inr 874, 1), (Sum.inr 889, 1), (Sum.inr 985, 1), (Sum.inr 1918, 1), (Sum.inr 4080, -1)]

theorem sourceEq1537 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1537 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1537 + difference 0 3) (sourceB1537 + difference 3 0) sourceC1537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1918) := by
    have ha : (tripleCharges (sourceA1537 + difference 0 3) (sourceB1537 + difference 3 0) sourceC1537) = raw23317 := by
      apply Matrix.ext; unfold tripleCharges sourceA1537 sourceB1537 sourceC1537 difference raw23317; decide +kernel
    rw [ha]
    exact (canonical23317 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1537 + difference 1 3) (sourceB1537 + difference 3 1) sourceC1537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 889) := by
    have ha : (tripleCharges (sourceA1537 + difference 1 3) (sourceB1537 + difference 3 1) sourceC1537) = raw23321 := by
      apply Matrix.ext; unfold tripleCharges sourceA1537 sourceB1537 sourceC1537 difference raw23321; decide +kernel
    rw [ha]
    exact (canonical23321 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1537 + difference 2 3) (sourceB1537 + difference 3 2) sourceC1537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 866) := by
    have ha : (tripleCharges (sourceA1537 + difference 2 3) (sourceB1537 + difference 3 2) sourceC1537) = raw23323 := by
      apply Matrix.ext; unfold tripleCharges sourceA1537 sourceB1537 sourceC1537 difference raw23323; decide +kernel
    rw [ha]
    exact (canonical23323 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1537 + difference 3 3) (sourceB1537 + difference 3 3) sourceC1537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 985) := by
    have ha : (tripleCharges (sourceA1537 + difference 3 3) (sourceB1537 + difference 3 3) sourceC1537) = raw21590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1537 sourceB1537 sourceC1537 difference raw21590; decide +kernel
    rw [ha]
    exact (canonical21590 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1537 + difference 4 3) (sourceB1537 + difference 3 4) sourceC1537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 873) := by
    have ha : (tripleCharges (sourceA1537 + difference 4 3) (sourceB1537 + difference 3 4) sourceC1537) = raw23324 := by
      apply Matrix.ext; unfold tripleCharges sourceA1537 sourceB1537 sourceC1537 difference raw23324; decide +kernel
    rw [ha]
    exact (canonical23324 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1537 + difference 5 3) (sourceB1537 + difference 3 5) sourceC1537) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 874) := by
    have ha : (tripleCharges (sourceA1537 + difference 5 3) (sourceB1537 + difference 3 5) sourceC1537) = raw23325 := by
      apply Matrix.ext; unfold tripleCharges sourceA1537 sourceB1537 sourceC1537 difference raw23325; decide +kernel
    rw [ha]
    exact (canonical23325 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1537 + sourceB1537) sourceC1537) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1537 + sourceB1537) sourceC1537) = raw21586 := by
      apply Matrix.ext; unfold doubleCharges sourceA1537 sourceB1537 sourceC1537 raw21586; decide +kernel
    rw [ha]
    exact (canonical21586 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1537 sourceB1537 sourceC1537
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1537, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1538 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB1538 : Charge := ![3, -1, 0, 1, -2, -1]
def sourceC1538 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1538 : Integer.Sparse Master := [(Sum.inr 710, 1), (Sum.inr 715, 1), (Sum.inr 717, 1), (Sum.inr 724, 1), (Sum.inr 852, 1), (Sum.inr 1618, 1), (Sum.inr 4071, -1)]

theorem sourceEq1538 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1538 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1538 + difference 0 0) (sourceB1538 + difference 0 0) sourceC1538) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1618) := by
    have ha : (tripleCharges (sourceA1538 + difference 0 0) (sourceB1538 + difference 0 0) sourceC1538) = raw23326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1538 sourceB1538 sourceC1538 difference raw23326; decide +kernel
    rw [ha]
    exact (canonical23326 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1538 + difference 1 0) (sourceB1538 + difference 0 1) sourceC1538) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 724) := by
    have ha : (tripleCharges (sourceA1538 + difference 1 0) (sourceB1538 + difference 0 1) sourceC1538) = raw23327 := by
      apply Matrix.ext; unfold tripleCharges sourceA1538 sourceB1538 sourceC1538 difference raw23327; decide +kernel
    rw [ha]
    exact (canonical23327 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1538 + difference 2 0) (sourceB1538 + difference 0 2) sourceC1538) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 710) := by
    have ha : (tripleCharges (sourceA1538 + difference 2 0) (sourceB1538 + difference 0 2) sourceC1538) = raw23328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1538 sourceB1538 sourceC1538 difference raw23328; decide +kernel
    rw [ha]
    exact (canonical23328 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1538 + difference 3 0) (sourceB1538 + difference 0 3) sourceC1538) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 852) := by
    have ha : (tripleCharges (sourceA1538 + difference 3 0) (sourceB1538 + difference 0 3) sourceC1538) = raw23329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1538 sourceB1538 sourceC1538 difference raw23329; decide +kernel
    rw [ha]
    exact (canonical23329 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1538 + difference 4 0) (sourceB1538 + difference 0 4) sourceC1538) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 715) := by
    have ha : (tripleCharges (sourceA1538 + difference 4 0) (sourceB1538 + difference 0 4) sourceC1538) = raw23330 := by
      apply Matrix.ext; unfold tripleCharges sourceA1538 sourceB1538 sourceC1538 difference raw23330; decide +kernel
    rw [ha]
    exact (canonical23330 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1538 + difference 5 0) (sourceB1538 + difference 0 5) sourceC1538) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 717) := by
    have ha : (tripleCharges (sourceA1538 + difference 5 0) (sourceB1538 + difference 0 5) sourceC1538) = raw23331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1538 sourceB1538 sourceC1538 difference raw23331; decide +kernel
    rw [ha]
    exact (canonical23331 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1538 + sourceB1538) sourceC1538) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1538 + sourceB1538) sourceC1538) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1538 sourceB1538 sourceC1538 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1538 sourceB1538 sourceC1538
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1538, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1539 : Charge := ![1, 1, 0, -1, 0, -1]
def sourceB1539 : Charge := ![3, -1, 0, 1, -2, -1]
def sourceC1539 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1539 : Integer.Sparse Master := [(Sum.inr 717, 1), (Sum.inr 1544, 1), (Sum.inr 1581, 1), (Sum.inr 1618, 2), (Sum.inr 1631, 1), (Sum.inr 4071, -1)]

theorem sourceEq1539 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1539 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1539 + difference 5 0) (sourceB1539 + difference 0 5) sourceC1539) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 717) := by
    have ha : (tripleCharges (sourceA1539 + difference 5 0) (sourceB1539 + difference 0 5) sourceC1539) = raw23331 := by
      apply Matrix.ext; unfold tripleCharges sourceA1539 sourceB1539 sourceC1539 difference raw23331; decide +kernel
    rw [ha]
    exact (canonical23331 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1539 + difference 5 1) (sourceB1539 + difference 1 5) sourceC1539) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1631) := by
    have ha : (tripleCharges (sourceA1539 + difference 5 1) (sourceB1539 + difference 1 5) sourceC1539) = raw22861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1539 sourceB1539 sourceC1539 difference raw22861; decide +kernel
    rw [ha]
    exact (canonical22861 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1539 + difference 5 2) (sourceB1539 + difference 2 5) sourceC1539) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1581) := by
    have ha : (tripleCharges (sourceA1539 + difference 5 2) (sourceB1539 + difference 2 5) sourceC1539) = raw22880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1539 sourceB1539 sourceC1539 difference raw22880; decide +kernel
    rw [ha]
    exact (canonical22880 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1539 + difference 5 3) (sourceB1539 + difference 3 5) sourceC1539) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1544) := by
    have ha : (tripleCharges (sourceA1539 + difference 5 3) (sourceB1539 + difference 3 5) sourceC1539) = raw22859 := by
      apply Matrix.ext; unfold tripleCharges sourceA1539 sourceB1539 sourceC1539 difference raw22859; decide +kernel
    rw [ha]
    exact (canonical22859 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1539 + difference 5 4) (sourceB1539 + difference 4 5) sourceC1539) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1618) := by
    have ha : (tripleCharges (sourceA1539 + difference 5 4) (sourceB1539 + difference 4 5) sourceC1539) = raw23332 := by
      apply Matrix.ext; unfold tripleCharges sourceA1539 sourceB1539 sourceC1539 difference raw23332; decide +kernel
    rw [ha]
    exact (canonical23332 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1539 + difference 5 5) (sourceB1539 + difference 5 5) sourceC1539) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1618) := by
    have ha : (tripleCharges (sourceA1539 + difference 5 5) (sourceB1539 + difference 5 5) sourceC1539) = raw23326 := by
      apply Matrix.ext; unfold tripleCharges sourceA1539 sourceB1539 sourceC1539 difference raw23326; decide +kernel
    rw [ha]
    exact (canonical23326 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1539 + sourceB1539) sourceC1539) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1539 + sourceB1539) sourceC1539) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1539 sourceB1539 sourceC1539 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1539 sourceB1539 sourceC1539
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1539, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1540 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1540 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1540 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm1540 : Integer.Sparse Master := [(Sum.inr 4179, 3), (Sum.inr 4190, 1), (Sum.inr 4193, 1), (Sum.inr 4348, 6), (Sum.inr 4359, 3), (Sum.inr 4362, 3), (Sum.inr 4496, 3), (Sum.inr 4500, 3), (Sum.inr 4501, 1), (Sum.inr 4508, 1), (Sum.inr 4845, 3), (Sum.inr 4897, 1), (Sum.inr 4899, 1)]

theorem sourceEq1540 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1540 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1540 + difference 0 1) (sourceB1540 + difference 1 0) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA1540 + difference 0 1) (sourceB1540 + difference 1 0) sourceC1540) = raw23333 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23333; decide +kernel
    rw [ha]
    exact (canonical23333 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1540 + difference 0 2) (sourceB1540 + difference 2 0) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA1540 + difference 0 2) (sourceB1540 + difference 2 0) sourceC1540) = raw23334 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23334; decide +kernel
    rw [ha]
    exact (canonical23334 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1540 + difference 0 3) (sourceB1540 + difference 3 0) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4845) := by
    have ha : (tripleCharges (sourceA1540 + difference 0 3) (sourceB1540 + difference 3 0) sourceC1540) = raw23335 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23335; decide +kernel
    rw [ha]
    exact (canonical23335 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1540 + difference 0 4) (sourceB1540 + difference 4 0) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA1540 + difference 0 4) (sourceB1540 + difference 4 0) sourceC1540) = raw3475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw3475; decide +kernel
    rw [ha]
    exact (canonical3475 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1540 + difference 0 5) (sourceB1540 + difference 5 0) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4897) := by
    have ha : (tripleCharges (sourceA1540 + difference 0 5) (sourceB1540 + difference 5 0) sourceC1540) = raw23336 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23336; decide +kernel
    rw [ha]
    exact (canonical23336 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1540 + difference 1 0) (sourceB1540 + difference 0 1) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4179) := by
    have ha : (tripleCharges (sourceA1540 + difference 1 0) (sourceB1540 + difference 0 1) sourceC1540) = raw23337 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23337; decide +kernel
    rw [ha]
    exact (canonical23337 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1540 + difference 1 2) (sourceB1540 + difference 2 1) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA1540 + difference 1 2) (sourceB1540 + difference 2 1) sourceC1540) = raw23338 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23338; decide +kernel
    rw [ha]
    exact (canonical23338 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1540 + difference 1 3) (sourceB1540 + difference 3 1) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA1540 + difference 1 3) (sourceB1540 + difference 3 1) sourceC1540) = raw23339 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23339; decide +kernel
    rw [ha]
    exact (canonical23339 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1540 + difference 1 4) (sourceB1540 + difference 4 1) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA1540 + difference 1 4) (sourceB1540 + difference 4 1) sourceC1540) = raw23340 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23340; decide +kernel
    rw [ha]
    exact (canonical23340 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1540 + difference 1 5) (sourceB1540 + difference 5 1) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1540 + difference 1 5) (sourceB1540 + difference 5 1) sourceC1540) = raw23341 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23341; decide +kernel
    rw [ha]
    exact (canonical23341 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1540 + difference 2 0) (sourceB1540 + difference 0 2) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4179) := by
    have ha : (tripleCharges (sourceA1540 + difference 2 0) (sourceB1540 + difference 0 2) sourceC1540) = raw23342 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23342; decide +kernel
    rw [ha]
    exact (canonical23342 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1540 + difference 2 1) (sourceB1540 + difference 1 2) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA1540 + difference 2 1) (sourceB1540 + difference 1 2) sourceC1540) = raw23343 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23343; decide +kernel
    rw [ha]
    exact (canonical23343 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1540 + difference 2 3) (sourceB1540 + difference 3 2) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA1540 + difference 2 3) (sourceB1540 + difference 3 2) sourceC1540) = raw23344 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23344; decide +kernel
    rw [ha]
    exact (canonical23344 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1540 + difference 2 4) (sourceB1540 + difference 4 2) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA1540 + difference 2 4) (sourceB1540 + difference 4 2) sourceC1540) = raw23345 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23345; decide +kernel
    rw [ha]
    exact (canonical23345 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1540 + difference 2 5) (sourceB1540 + difference 5 2) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1540 + difference 2 5) (sourceB1540 + difference 5 2) sourceC1540) = raw23346 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23346; decide +kernel
    rw [ha]
    exact (canonical23346 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1540 + difference 3 0) (sourceB1540 + difference 0 3) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4179) := by
    have ha : (tripleCharges (sourceA1540 + difference 3 0) (sourceB1540 + difference 0 3) sourceC1540) = raw23347 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23347; decide +kernel
    rw [ha]
    exact (canonical23347 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1540 + difference 3 1) (sourceB1540 + difference 1 3) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA1540 + difference 3 1) (sourceB1540 + difference 1 3) sourceC1540) = raw23348 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23348; decide +kernel
    rw [ha]
    exact (canonical23348 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1540 + difference 3 2) (sourceB1540 + difference 2 3) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4348) := by
    have ha : (tripleCharges (sourceA1540 + difference 3 2) (sourceB1540 + difference 2 3) sourceC1540) = raw23349 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23349; decide +kernel
    rw [ha]
    exact (canonical23349 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1540 + difference 3 4) (sourceB1540 + difference 4 3) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA1540 + difference 3 4) (sourceB1540 + difference 4 3) sourceC1540) = raw23350 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23350; decide +kernel
    rw [ha]
    exact (canonical23350 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1540 + difference 3 5) (sourceB1540 + difference 5 3) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4496) := by
    have ha : (tripleCharges (sourceA1540 + difference 3 5) (sourceB1540 + difference 5 3) sourceC1540) = raw23351 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23351; decide +kernel
    rw [ha]
    exact (canonical23351 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1540 + difference 4 0) (sourceB1540 + difference 0 4) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4190) := by
    have ha : (tripleCharges (sourceA1540 + difference 4 0) (sourceB1540 + difference 0 4) sourceC1540) = raw23352 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23352; decide +kernel
    rw [ha]
    exact (canonical23352 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1540 + difference 4 1) (sourceB1540 + difference 1 4) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA1540 + difference 4 1) (sourceB1540 + difference 1 4) sourceC1540) = raw23353 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23353; decide +kernel
    rw [ha]
    exact (canonical23353 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1540 + difference 4 2) (sourceB1540 + difference 2 4) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA1540 + difference 4 2) (sourceB1540 + difference 2 4) sourceC1540) = raw23354 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23354; decide +kernel
    rw [ha]
    exact (canonical23354 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1540 + difference 4 3) (sourceB1540 + difference 3 4) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4359) := by
    have ha : (tripleCharges (sourceA1540 + difference 4 3) (sourceB1540 + difference 3 4) sourceC1540) = raw23355 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23355; decide +kernel
    rw [ha]
    exact (canonical23355 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1540 + difference 4 5) (sourceB1540 + difference 5 4) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4501) := by
    have ha : (tripleCharges (sourceA1540 + difference 4 5) (sourceB1540 + difference 5 4) sourceC1540) = raw23356 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23356; decide +kernel
    rw [ha]
    exact (canonical23356 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1540 + difference 5 0) (sourceB1540 + difference 0 5) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4193) := by
    have ha : (tripleCharges (sourceA1540 + difference 5 0) (sourceB1540 + difference 0 5) sourceC1540) = raw23357 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23357; decide +kernel
    rw [ha]
    exact (canonical23357 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1540 + difference 5 1) (sourceB1540 + difference 1 5) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4362) := by
    have ha : (tripleCharges (sourceA1540 + difference 5 1) (sourceB1540 + difference 1 5) sourceC1540) = raw23358 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23358; decide +kernel
    rw [ha]
    exact (canonical23358 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1540 + difference 5 2) (sourceB1540 + difference 2 5) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4362) := by
    have ha : (tripleCharges (sourceA1540 + difference 5 2) (sourceB1540 + difference 2 5) sourceC1540) = raw23359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23359; decide +kernel
    rw [ha]
    exact (canonical23359 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1540 + difference 5 3) (sourceB1540 + difference 3 5) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4362) := by
    have ha : (tripleCharges (sourceA1540 + difference 5 3) (sourceB1540 + difference 3 5) sourceC1540) = raw23360 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw23360; decide +kernel
    rw [ha]
    exact (canonical23360 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1540 + difference 5 4) (sourceB1540 + difference 4 5) sourceC1540) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4508) := by
    have ha : (tripleCharges (sourceA1540 + difference 5 4) (sourceB1540 + difference 4 5) sourceC1540) = raw3471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1540 sourceB1540 sourceC1540 difference raw3471; decide +kernel
    rw [ha]
    exact (canonical3471 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1540 sourceB1540 sourceC1540
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1540, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1541 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1541 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1541 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm1541 : Integer.Sparse Master := [(Sum.inr 653, 3), (Sum.inr 654, 1), (Sum.inr 655, 1), (Sum.inr 1347, 6), (Sum.inr 1348, 3), (Sum.inr 1349, 3), (Sum.inr 1436, 3), (Sum.inr 1438, 1), (Sum.inr 1451, 3), (Sum.inr 1452, 1), (Sum.inr 2778, 1), (Sum.inr 3095, 3), (Sum.inr 3114, 1)]

theorem sourceEq1541 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1541 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1541 + difference 0 1) (sourceB1541 + difference 1 0) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3095) := by
    have ha : (tripleCharges (sourceA1541 + difference 0 1) (sourceB1541 + difference 1 0) sourceC1541) = raw23361 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23361; decide +kernel
    rw [ha]
    exact (canonical23361 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1541 + difference 0 2) (sourceB1541 + difference 2 0) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3095) := by
    have ha : (tripleCharges (sourceA1541 + difference 0 2) (sourceB1541 + difference 2 0) sourceC1541) = raw23362 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23362; decide +kernel
    rw [ha]
    exact (canonical23362 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1541 + difference 0 3) (sourceB1541 + difference 3 0) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3095) := by
    have ha : (tripleCharges (sourceA1541 + difference 0 3) (sourceB1541 + difference 3 0) sourceC1541) = raw23363 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23363; decide +kernel
    rw [ha]
    exact (canonical23363 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1541 + difference 0 4) (sourceB1541 + difference 4 0) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2778) := by
    have ha : (tripleCharges (sourceA1541 + difference 0 4) (sourceB1541 + difference 4 0) sourceC1541) = raw3505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw3505; decide +kernel
    rw [ha]
    exact (canonical3505 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1541 + difference 0 5) (sourceB1541 + difference 5 0) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3114) := by
    have ha : (tripleCharges (sourceA1541 + difference 0 5) (sourceB1541 + difference 5 0) sourceC1541) = raw23364 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23364; decide +kernel
    rw [ha]
    exact (canonical23364 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1541 + difference 1 0) (sourceB1541 + difference 0 1) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 653) := by
    have ha : (tripleCharges (sourceA1541 + difference 1 0) (sourceB1541 + difference 0 1) sourceC1541) = raw23365 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23365; decide +kernel
    rw [ha]
    exact (canonical23365 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1541 + difference 1 2) (sourceB1541 + difference 2 1) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1347) := by
    have ha : (tripleCharges (sourceA1541 + difference 1 2) (sourceB1541 + difference 2 1) sourceC1541) = raw23366 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23366; decide +kernel
    rw [ha]
    exact (canonical23366 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1541 + difference 1 3) (sourceB1541 + difference 3 1) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1347) := by
    have ha : (tripleCharges (sourceA1541 + difference 1 3) (sourceB1541 + difference 3 1) sourceC1541) = raw23367 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23367; decide +kernel
    rw [ha]
    exact (canonical23367 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1541 + difference 1 4) (sourceB1541 + difference 4 1) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA1541 + difference 1 4) (sourceB1541 + difference 4 1) sourceC1541) = raw23368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23368; decide +kernel
    rw [ha]
    exact (canonical23368 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1541 + difference 1 5) (sourceB1541 + difference 5 1) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1451) := by
    have ha : (tripleCharges (sourceA1541 + difference 1 5) (sourceB1541 + difference 5 1) sourceC1541) = raw23369 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23369; decide +kernel
    rw [ha]
    exact (canonical23369 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1541 + difference 2 0) (sourceB1541 + difference 0 2) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 653) := by
    have ha : (tripleCharges (sourceA1541 + difference 2 0) (sourceB1541 + difference 0 2) sourceC1541) = raw23370 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23370; decide +kernel
    rw [ha]
    exact (canonical23370 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1541 + difference 2 1) (sourceB1541 + difference 1 2) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1347) := by
    have ha : (tripleCharges (sourceA1541 + difference 2 1) (sourceB1541 + difference 1 2) sourceC1541) = raw23371 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23371; decide +kernel
    rw [ha]
    exact (canonical23371 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1541 + difference 2 3) (sourceB1541 + difference 3 2) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1347) := by
    have ha : (tripleCharges (sourceA1541 + difference 2 3) (sourceB1541 + difference 3 2) sourceC1541) = raw23372 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23372; decide +kernel
    rw [ha]
    exact (canonical23372 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1541 + difference 2 4) (sourceB1541 + difference 4 2) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA1541 + difference 2 4) (sourceB1541 + difference 4 2) sourceC1541) = raw23373 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23373; decide +kernel
    rw [ha]
    exact (canonical23373 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1541 + difference 2 5) (sourceB1541 + difference 5 2) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1451) := by
    have ha : (tripleCharges (sourceA1541 + difference 2 5) (sourceB1541 + difference 5 2) sourceC1541) = raw23374 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23374; decide +kernel
    rw [ha]
    exact (canonical23374 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1541 + difference 3 0) (sourceB1541 + difference 0 3) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 653) := by
    have ha : (tripleCharges (sourceA1541 + difference 3 0) (sourceB1541 + difference 0 3) sourceC1541) = raw23375 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23375; decide +kernel
    rw [ha]
    exact (canonical23375 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1541 + difference 3 1) (sourceB1541 + difference 1 3) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1347) := by
    have ha : (tripleCharges (sourceA1541 + difference 3 1) (sourceB1541 + difference 1 3) sourceC1541) = raw23376 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23376; decide +kernel
    rw [ha]
    exact (canonical23376 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1541 + difference 3 2) (sourceB1541 + difference 2 3) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1347) := by
    have ha : (tripleCharges (sourceA1541 + difference 3 2) (sourceB1541 + difference 2 3) sourceC1541) = raw23377 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23377; decide +kernel
    rw [ha]
    exact (canonical23377 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1541 + difference 3 4) (sourceB1541 + difference 4 3) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA1541 + difference 3 4) (sourceB1541 + difference 4 3) sourceC1541) = raw23378 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23378; decide +kernel
    rw [ha]
    exact (canonical23378 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1541 + difference 3 5) (sourceB1541 + difference 5 3) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1451) := by
    have ha : (tripleCharges (sourceA1541 + difference 3 5) (sourceB1541 + difference 5 3) sourceC1541) = raw23379 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23379; decide +kernel
    rw [ha]
    exact (canonical23379 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1541 + difference 4 0) (sourceB1541 + difference 0 4) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 655) := by
    have ha : (tripleCharges (sourceA1541 + difference 4 0) (sourceB1541 + difference 0 4) sourceC1541) = raw23380 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23380; decide +kernel
    rw [ha]
    exact (canonical23380 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1541 + difference 4 1) (sourceB1541 + difference 1 4) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1349) := by
    have ha : (tripleCharges (sourceA1541 + difference 4 1) (sourceB1541 + difference 1 4) sourceC1541) = raw23381 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23381; decide +kernel
    rw [ha]
    exact (canonical23381 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1541 + difference 4 2) (sourceB1541 + difference 2 4) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1349) := by
    have ha : (tripleCharges (sourceA1541 + difference 4 2) (sourceB1541 + difference 2 4) sourceC1541) = raw23382 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23382; decide +kernel
    rw [ha]
    exact (canonical23382 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1541 + difference 4 3) (sourceB1541 + difference 3 4) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1349) := by
    have ha : (tripleCharges (sourceA1541 + difference 4 3) (sourceB1541 + difference 3 4) sourceC1541) = raw23383 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23383; decide +kernel
    rw [ha]
    exact (canonical23383 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1541 + difference 4 5) (sourceB1541 + difference 5 4) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1452) := by
    have ha : (tripleCharges (sourceA1541 + difference 4 5) (sourceB1541 + difference 5 4) sourceC1541) = raw23384 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23384; decide +kernel
    rw [ha]
    exact (canonical23384 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1541 + difference 5 0) (sourceB1541 + difference 0 5) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 654) := by
    have ha : (tripleCharges (sourceA1541 + difference 5 0) (sourceB1541 + difference 0 5) sourceC1541) = raw23385 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23385; decide +kernel
    rw [ha]
    exact (canonical23385 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1541 + difference 5 1) (sourceB1541 + difference 1 5) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1348) := by
    have ha : (tripleCharges (sourceA1541 + difference 5 1) (sourceB1541 + difference 1 5) sourceC1541) = raw23386 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23386; decide +kernel
    rw [ha]
    exact (canonical23386 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1541 + difference 5 2) (sourceB1541 + difference 2 5) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1348) := by
    have ha : (tripleCharges (sourceA1541 + difference 5 2) (sourceB1541 + difference 2 5) sourceC1541) = raw23387 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23387; decide +kernel
    rw [ha]
    exact (canonical23387 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1541 + difference 5 3) (sourceB1541 + difference 3 5) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1348) := by
    have ha : (tripleCharges (sourceA1541 + difference 5 3) (sourceB1541 + difference 3 5) sourceC1541) = raw23388 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw23388; decide +kernel
    rw [ha]
    exact (canonical23388 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1541 + difference 5 4) (sourceB1541 + difference 4 5) sourceC1541) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1438) := by
    have ha : (tripleCharges (sourceA1541 + difference 5 4) (sourceB1541 + difference 4 5) sourceC1541) = raw3501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1541 sourceB1541 sourceC1541 difference raw3501; decide +kernel
    rw [ha]
    exact (canonical3501 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1541 sourceB1541 sourceC1541
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1541, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1542 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1542 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1542 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm1542 : Integer.Sparse Master := [(Sum.inr 1513, 3), (Sum.inr 1527, 1), (Sum.inr 1531, 1), (Sum.inr 1669, 6), (Sum.inr 1683, 3), (Sum.inr 1687, 3), (Sum.inr 1710, 3), (Sum.inr 1716, 3), (Sum.inr 1730, 1), (Sum.inr 1747, 1), (Sum.inr 2218, 3), (Sum.inr 2268, 1), (Sum.inr 2281, 1)]

theorem sourceEq1542 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1542 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1542 + difference 0 1) (sourceB1542 + difference 1 0) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1542 + difference 0 1) (sourceB1542 + difference 1 0) sourceC1542) = raw23389 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23389; decide +kernel
    rw [ha]
    exact (canonical23389 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1542 + difference 0 2) (sourceB1542 + difference 2 0) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1542 + difference 0 2) (sourceB1542 + difference 2 0) sourceC1542) = raw23390 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23390; decide +kernel
    rw [ha]
    exact (canonical23390 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1542 + difference 0 3) (sourceB1542 + difference 3 0) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2218) := by
    have ha : (tripleCharges (sourceA1542 + difference 0 3) (sourceB1542 + difference 3 0) sourceC1542) = raw23391 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23391; decide +kernel
    rw [ha]
    exact (canonical23391 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1542 + difference 0 4) (sourceB1542 + difference 4 0) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA1542 + difference 0 4) (sourceB1542 + difference 4 0) sourceC1542) = raw23392 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23392; decide +kernel
    rw [ha]
    exact (canonical23392 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1542 + difference 0 5) (sourceB1542 + difference 5 0) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2268) := by
    have ha : (tripleCharges (sourceA1542 + difference 0 5) (sourceB1542 + difference 5 0) sourceC1542) = raw23393 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23393; decide +kernel
    rw [ha]
    exact (canonical23393 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1542 + difference 1 0) (sourceB1542 + difference 0 1) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1513) := by
    have ha : (tripleCharges (sourceA1542 + difference 1 0) (sourceB1542 + difference 0 1) sourceC1542) = raw23394 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23394; decide +kernel
    rw [ha]
    exact (canonical23394 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1542 + difference 1 2) (sourceB1542 + difference 2 1) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1542 + difference 1 2) (sourceB1542 + difference 2 1) sourceC1542) = raw23395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23395; decide +kernel
    rw [ha]
    exact (canonical23395 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1542 + difference 1 3) (sourceB1542 + difference 3 1) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1542 + difference 1 3) (sourceB1542 + difference 3 1) sourceC1542) = raw23396 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23396; decide +kernel
    rw [ha]
    exact (canonical23396 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1542 + difference 1 4) (sourceB1542 + difference 4 1) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1542 + difference 1 4) (sourceB1542 + difference 4 1) sourceC1542) = raw23397 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23397; decide +kernel
    rw [ha]
    exact (canonical23397 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1542 + difference 1 5) (sourceB1542 + difference 5 1) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1542 + difference 1 5) (sourceB1542 + difference 5 1) sourceC1542) = raw23398 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23398; decide +kernel
    rw [ha]
    exact (canonical23398 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1542 + difference 2 0) (sourceB1542 + difference 0 2) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1513) := by
    have ha : (tripleCharges (sourceA1542 + difference 2 0) (sourceB1542 + difference 0 2) sourceC1542) = raw23399 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23399; decide +kernel
    rw [ha]
    exact (canonical23399 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1542 + difference 2 1) (sourceB1542 + difference 1 2) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1542 + difference 2 1) (sourceB1542 + difference 1 2) sourceC1542) = raw23400 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23400; decide +kernel
    rw [ha]
    exact (canonical23400 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1542 + difference 2 3) (sourceB1542 + difference 3 2) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1542 + difference 2 3) (sourceB1542 + difference 3 2) sourceC1542) = raw23401 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23401; decide +kernel
    rw [ha]
    exact (canonical23401 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1542 + difference 2 4) (sourceB1542 + difference 4 2) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1542 + difference 2 4) (sourceB1542 + difference 4 2) sourceC1542) = raw23402 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23402; decide +kernel
    rw [ha]
    exact (canonical23402 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1542 + difference 2 5) (sourceB1542 + difference 5 2) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1542 + difference 2 5) (sourceB1542 + difference 5 2) sourceC1542) = raw23403 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23403; decide +kernel
    rw [ha]
    exact (canonical23403 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1542 + difference 3 0) (sourceB1542 + difference 0 3) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1513) := by
    have ha : (tripleCharges (sourceA1542 + difference 3 0) (sourceB1542 + difference 0 3) sourceC1542) = raw23404 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23404; decide +kernel
    rw [ha]
    exact (canonical23404 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1542 + difference 3 1) (sourceB1542 + difference 1 3) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1542 + difference 3 1) (sourceB1542 + difference 1 3) sourceC1542) = raw23405 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23405; decide +kernel
    rw [ha]
    exact (canonical23405 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1542 + difference 3 2) (sourceB1542 + difference 2 3) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1669) := by
    have ha : (tripleCharges (sourceA1542 + difference 3 2) (sourceB1542 + difference 2 3) sourceC1542) = raw23406 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23406; decide +kernel
    rw [ha]
    exact (canonical23406 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1542 + difference 3 4) (sourceB1542 + difference 4 3) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA1542 + difference 3 4) (sourceB1542 + difference 4 3) sourceC1542) = raw23407 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23407; decide +kernel
    rw [ha]
    exact (canonical23407 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1542 + difference 3 5) (sourceB1542 + difference 5 3) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1542 + difference 3 5) (sourceB1542 + difference 5 3) sourceC1542) = raw23408 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23408; decide +kernel
    rw [ha]
    exact (canonical23408 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1542 + difference 4 0) (sourceB1542 + difference 0 4) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1527) := by
    have ha : (tripleCharges (sourceA1542 + difference 4 0) (sourceB1542 + difference 0 4) sourceC1542) = raw23409 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23409; decide +kernel
    rw [ha]
    exact (canonical23409 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1542 + difference 4 1) (sourceB1542 + difference 1 4) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA1542 + difference 4 1) (sourceB1542 + difference 1 4) sourceC1542) = raw23410 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23410; decide +kernel
    rw [ha]
    exact (canonical23410 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1542 + difference 4 2) (sourceB1542 + difference 2 4) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA1542 + difference 4 2) (sourceB1542 + difference 2 4) sourceC1542) = raw23411 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23411; decide +kernel
    rw [ha]
    exact (canonical23411 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1542 + difference 4 3) (sourceB1542 + difference 3 4) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA1542 + difference 4 3) (sourceB1542 + difference 3 4) sourceC1542) = raw23412 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23412; decide +kernel
    rw [ha]
    exact (canonical23412 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1542 + difference 4 5) (sourceB1542 + difference 5 4) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1730) := by
    have ha : (tripleCharges (sourceA1542 + difference 4 5) (sourceB1542 + difference 5 4) sourceC1542) = raw23413 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23413; decide +kernel
    rw [ha]
    exact (canonical23413 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1542 + difference 5 0) (sourceB1542 + difference 0 5) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1531) := by
    have ha : (tripleCharges (sourceA1542 + difference 5 0) (sourceB1542 + difference 0 5) sourceC1542) = raw23414 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23414; decide +kernel
    rw [ha]
    exact (canonical23414 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1542 + difference 5 1) (sourceB1542 + difference 1 5) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1687) := by
    have ha : (tripleCharges (sourceA1542 + difference 5 1) (sourceB1542 + difference 1 5) sourceC1542) = raw23415 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23415; decide +kernel
    rw [ha]
    exact (canonical23415 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1542 + difference 5 2) (sourceB1542 + difference 2 5) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1687) := by
    have ha : (tripleCharges (sourceA1542 + difference 5 2) (sourceB1542 + difference 2 5) sourceC1542) = raw23416 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23416; decide +kernel
    rw [ha]
    exact (canonical23416 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1542 + difference 5 3) (sourceB1542 + difference 3 5) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1687) := by
    have ha : (tripleCharges (sourceA1542 + difference 5 3) (sourceB1542 + difference 3 5) sourceC1542) = raw23417 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23417; decide +kernel
    rw [ha]
    exact (canonical23417 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1542 + difference 5 4) (sourceB1542 + difference 4 5) sourceC1542) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1747) := by
    have ha : (tripleCharges (sourceA1542 + difference 5 4) (sourceB1542 + difference 4 5) sourceC1542) = raw23418 := by
      apply Matrix.ext; unfold tripleCharges sourceA1542 sourceB1542 sourceC1542 difference raw23418; decide +kernel
    rw [ha]
    exact (canonical23418 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1542 sourceB1542 sourceC1542
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1542, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1543 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1543 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1543 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm1543 : Integer.Sparse Master := [(Sum.inr 607, 3), (Sum.inr 618, 1), (Sum.inr 621, 1), (Sum.inr 1094, 1), (Sum.inr 4085, -1)]

theorem sourceEq1543 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1543 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1543 + difference 0 0) (sourceB1543 + difference 0 0) sourceC1543) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1094) := by
    have ha : (tripleCharges (sourceA1543 + difference 0 0) (sourceB1543 + difference 0 0) sourceC1543) = raw20092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1543 sourceB1543 sourceC1543 difference raw20092; decide +kernel
    rw [ha]
    exact (canonical20092 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1543 + difference 1 0) (sourceB1543 + difference 0 1) sourceC1543) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 607) := by
    have ha : (tripleCharges (sourceA1543 + difference 1 0) (sourceB1543 + difference 0 1) sourceC1543) = raw23419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1543 sourceB1543 sourceC1543 difference raw23419; decide +kernel
    rw [ha]
    exact (canonical23419 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1543 + difference 2 0) (sourceB1543 + difference 0 2) sourceC1543) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 607) := by
    have ha : (tripleCharges (sourceA1543 + difference 2 0) (sourceB1543 + difference 0 2) sourceC1543) = raw23420 := by
      apply Matrix.ext; unfold tripleCharges sourceA1543 sourceB1543 sourceC1543 difference raw23420; decide +kernel
    rw [ha]
    exact (canonical23420 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1543 + difference 3 0) (sourceB1543 + difference 0 3) sourceC1543) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 607) := by
    have ha : (tripleCharges (sourceA1543 + difference 3 0) (sourceB1543 + difference 0 3) sourceC1543) = raw23421 := by
      apply Matrix.ext; unfold tripleCharges sourceA1543 sourceB1543 sourceC1543 difference raw23421; decide +kernel
    rw [ha]
    exact (canonical23421 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1543 + difference 4 0) (sourceB1543 + difference 0 4) sourceC1543) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 618) := by
    have ha : (tripleCharges (sourceA1543 + difference 4 0) (sourceB1543 + difference 0 4) sourceC1543) = raw23422 := by
      apply Matrix.ext; unfold tripleCharges sourceA1543 sourceB1543 sourceC1543 difference raw23422; decide +kernel
    rw [ha]
    exact (canonical23422 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1543 + difference 5 0) (sourceB1543 + difference 0 5) sourceC1543) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 621) := by
    have ha : (tripleCharges (sourceA1543 + difference 5 0) (sourceB1543 + difference 0 5) sourceC1543) = raw20088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1543 sourceB1543 sourceC1543 difference raw20088; decide +kernel
    rw [ha]
    exact (canonical20088 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1543 + sourceB1543) sourceC1543) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA1543 + sourceB1543) sourceC1543) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA1543 sourceB1543 sourceC1543 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1543 sourceB1543 sourceC1543
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1543, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1544 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1544 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC1544 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm1544 : Integer.Sparse Master := [(Sum.inr 607, 1), (Sum.inr 926, 2), (Sum.inr 1080, 1), (Sum.inr 1084, 1), (Sum.inr 1094, 1), (Sum.inr 4085, -1)]

theorem sourceEq1544 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1544 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1544 + difference 1 0) (sourceB1544 + difference 0 1) sourceC1544) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 607) := by
    have ha : (tripleCharges (sourceA1544 + difference 1 0) (sourceB1544 + difference 0 1) sourceC1544) = raw23419 := by
      apply Matrix.ext; unfold tripleCharges sourceA1544 sourceB1544 sourceC1544 difference raw23419; decide +kernel
    rw [ha]
    exact (canonical23419 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1544 + difference 1 1) (sourceB1544 + difference 1 1) sourceC1544) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1094) := by
    have ha : (tripleCharges (sourceA1544 + difference 1 1) (sourceB1544 + difference 1 1) sourceC1544) = raw20092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1544 sourceB1544 sourceC1544 difference raw20092; decide +kernel
    rw [ha]
    exact (canonical20092 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1544 + difference 1 2) (sourceB1544 + difference 2 1) sourceC1544) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 926) := by
    have ha : (tripleCharges (sourceA1544 + difference 1 2) (sourceB1544 + difference 2 1) sourceC1544) = raw23423 := by
      apply Matrix.ext; unfold tripleCharges sourceA1544 sourceB1544 sourceC1544 difference raw23423; decide +kernel
    rw [ha]
    exact (canonical23423 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1544 + difference 1 3) (sourceB1544 + difference 3 1) sourceC1544) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 926) := by
    have ha : (tripleCharges (sourceA1544 + difference 1 3) (sourceB1544 + difference 3 1) sourceC1544) = raw23424 := by
      apply Matrix.ext; unfold tripleCharges sourceA1544 sourceB1544 sourceC1544 difference raw23424; decide +kernel
    rw [ha]
    exact (canonical23424 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1544 + difference 1 4) (sourceB1544 + difference 4 1) sourceC1544) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1084) := by
    have ha : (tripleCharges (sourceA1544 + difference 1 4) (sourceB1544 + difference 4 1) sourceC1544) = raw23425 := by
      apply Matrix.ext; unfold tripleCharges sourceA1544 sourceB1544 sourceC1544 difference raw23425; decide +kernel
    rw [ha]
    exact (canonical23425 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1544 + difference 1 5) (sourceB1544 + difference 5 1) sourceC1544) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1080) := by
    have ha : (tripleCharges (sourceA1544 + difference 1 5) (sourceB1544 + difference 5 1) sourceC1544) = raw23426 := by
      apply Matrix.ext; unfold tripleCharges sourceA1544 sourceB1544 sourceC1544 difference raw23426; decide +kernel
    rw [ha]
    exact (canonical23426 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1544 + sourceB1544) sourceC1544) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA1544 + sourceB1544) sourceC1544) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA1544 sourceB1544 sourceC1544 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1544 sourceB1544 sourceC1544
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1544, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1545 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1545 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1545 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceForm1545 : Integer.Sparse Master := [(Sum.inr 4129, 3), (Sum.inr 4135, 1), (Sum.inr 4138, 1), (Sum.inr 4310, 6), (Sum.inr 4316, 3), (Sum.inr 4319, 3), (Sum.inr 4490, 3), (Sum.inr 4493, 1), (Sum.inr 4503, 3), (Sum.inr 4507, 1), (Sum.inr 5110, 3), (Sum.inr 5305, 1), (Sum.inr 5310, 1)]

theorem sourceEq1545 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1545 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1545 + difference 0 1) (sourceB1545 + difference 1 0) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA1545 + difference 0 1) (sourceB1545 + difference 1 0) sourceC1545) = raw7607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw7607; decide +kernel
    rw [ha]
    exact (canonical7607 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1545 + difference 0 2) (sourceB1545 + difference 2 0) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA1545 + difference 0 2) (sourceB1545 + difference 2 0) sourceC1545) = raw7608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw7608; decide +kernel
    rw [ha]
    exact (canonical7608 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1545 + difference 0 3) (sourceB1545 + difference 3 0) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA1545 + difference 0 3) (sourceB1545 + difference 3 0) sourceC1545) = raw7609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw7609; decide +kernel
    rw [ha]
    exact (canonical7609 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1545 + difference 0 4) (sourceB1545 + difference 4 0) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA1545 + difference 0 4) (sourceB1545 + difference 4 0) sourceC1545) = raw2871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw2871; decide +kernel
    rw [ha]
    exact (canonical2871 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1545 + difference 0 5) (sourceB1545 + difference 5 0) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5305) := by
    have ha : (tripleCharges (sourceA1545 + difference 0 5) (sourceB1545 + difference 5 0) sourceC1545) = raw3225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw3225; decide +kernel
    rw [ha]
    exact (canonical3225 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1545 + difference 1 0) (sourceB1545 + difference 0 1) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4129) := by
    have ha : (tripleCharges (sourceA1545 + difference 1 0) (sourceB1545 + difference 0 1) sourceC1545) = raw23427 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw23427; decide +kernel
    rw [ha]
    exact (canonical23427 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1545 + difference 1 2) (sourceB1545 + difference 2 1) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4310) := by
    have ha : (tripleCharges (sourceA1545 + difference 1 2) (sourceB1545 + difference 2 1) sourceC1545) = raw23428 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw23428; decide +kernel
    rw [ha]
    exact (canonical23428 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1545 + difference 1 3) (sourceB1545 + difference 3 1) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4310) := by
    have ha : (tripleCharges (sourceA1545 + difference 1 3) (sourceB1545 + difference 3 1) sourceC1545) = raw23429 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw23429; decide +kernel
    rw [ha]
    exact (canonical23429 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1545 + difference 1 4) (sourceB1545 + difference 4 1) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1545 + difference 1 4) (sourceB1545 + difference 4 1) sourceC1545) = raw7597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw7597; decide +kernel
    rw [ha]
    exact (canonical7597 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1545 + difference 1 5) (sourceB1545 + difference 5 1) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA1545 + difference 1 5) (sourceB1545 + difference 5 1) sourceC1545) = raw23430 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw23430; decide +kernel
    rw [ha]
    exact (canonical23430 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1545 + difference 2 0) (sourceB1545 + difference 0 2) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4129) := by
    have ha : (tripleCharges (sourceA1545 + difference 2 0) (sourceB1545 + difference 0 2) sourceC1545) = raw23431 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw23431; decide +kernel
    rw [ha]
    exact (canonical23431 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1545 + difference 2 1) (sourceB1545 + difference 1 2) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4310) := by
    have ha : (tripleCharges (sourceA1545 + difference 2 1) (sourceB1545 + difference 1 2) sourceC1545) = raw23432 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw23432; decide +kernel
    rw [ha]
    exact (canonical23432 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1545 + difference 2 3) (sourceB1545 + difference 3 2) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4310) := by
    have ha : (tripleCharges (sourceA1545 + difference 2 3) (sourceB1545 + difference 3 2) sourceC1545) = raw23433 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw23433; decide +kernel
    rw [ha]
    exact (canonical23433 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1545 + difference 2 4) (sourceB1545 + difference 4 2) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1545 + difference 2 4) (sourceB1545 + difference 4 2) sourceC1545) = raw7600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw7600; decide +kernel
    rw [ha]
    exact (canonical7600 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1545 + difference 2 5) (sourceB1545 + difference 5 2) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA1545 + difference 2 5) (sourceB1545 + difference 5 2) sourceC1545) = raw23434 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw23434; decide +kernel
    rw [ha]
    exact (canonical23434 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1545 + difference 3 0) (sourceB1545 + difference 0 3) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4129) := by
    have ha : (tripleCharges (sourceA1545 + difference 3 0) (sourceB1545 + difference 0 3) sourceC1545) = raw23435 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw23435; decide +kernel
    rw [ha]
    exact (canonical23435 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1545 + difference 3 1) (sourceB1545 + difference 1 3) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4310) := by
    have ha : (tripleCharges (sourceA1545 + difference 3 1) (sourceB1545 + difference 1 3) sourceC1545) = raw23436 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw23436; decide +kernel
    rw [ha]
    exact (canonical23436 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1545 + difference 3 2) (sourceB1545 + difference 2 3) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4310) := by
    have ha : (tripleCharges (sourceA1545 + difference 3 2) (sourceB1545 + difference 2 3) sourceC1545) = raw23437 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw23437; decide +kernel
    rw [ha]
    exact (canonical23437 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1545 + difference 3 4) (sourceB1545 + difference 4 3) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA1545 + difference 3 4) (sourceB1545 + difference 4 3) sourceC1545) = raw7603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw7603; decide +kernel
    rw [ha]
    exact (canonical7603 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1545 + difference 3 5) (sourceB1545 + difference 5 3) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4490) := by
    have ha : (tripleCharges (sourceA1545 + difference 3 5) (sourceB1545 + difference 5 3) sourceC1545) = raw23438 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw23438; decide +kernel
    rw [ha]
    exact (canonical23438 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1545 + difference 4 0) (sourceB1545 + difference 0 4) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4135) := by
    have ha : (tripleCharges (sourceA1545 + difference 4 0) (sourceB1545 + difference 0 4) sourceC1545) = raw23439 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw23439; decide +kernel
    rw [ha]
    exact (canonical23439 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1545 + difference 4 1) (sourceB1545 + difference 1 4) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4316) := by
    have ha : (tripleCharges (sourceA1545 + difference 4 1) (sourceB1545 + difference 1 4) sourceC1545) = raw23440 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw23440; decide +kernel
    rw [ha]
    exact (canonical23440 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1545 + difference 4 2) (sourceB1545 + difference 2 4) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4316) := by
    have ha : (tripleCharges (sourceA1545 + difference 4 2) (sourceB1545 + difference 2 4) sourceC1545) = raw23441 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw23441; decide +kernel
    rw [ha]
    exact (canonical23441 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1545 + difference 4 3) (sourceB1545 + difference 3 4) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4316) := by
    have ha : (tripleCharges (sourceA1545 + difference 4 3) (sourceB1545 + difference 3 4) sourceC1545) = raw23442 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw23442; decide +kernel
    rw [ha]
    exact (canonical23442 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1545 + difference 4 5) (sourceB1545 + difference 5 4) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4493) := by
    have ha : (tripleCharges (sourceA1545 + difference 4 5) (sourceB1545 + difference 5 4) sourceC1545) = raw23443 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw23443; decide +kernel
    rw [ha]
    exact (canonical23443 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1545 + difference 5 0) (sourceB1545 + difference 0 5) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4138) := by
    have ha : (tripleCharges (sourceA1545 + difference 5 0) (sourceB1545 + difference 0 5) sourceC1545) = raw21702 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw21702; decide +kernel
    rw [ha]
    exact (canonical21702 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1545 + difference 5 1) (sourceB1545 + difference 1 5) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4319) := by
    have ha : (tripleCharges (sourceA1545 + difference 5 1) (sourceB1545 + difference 1 5) sourceC1545) = raw21703 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw21703; decide +kernel
    rw [ha]
    exact (canonical21703 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1545 + difference 5 2) (sourceB1545 + difference 2 5) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4319) := by
    have ha : (tripleCharges (sourceA1545 + difference 5 2) (sourceB1545 + difference 2 5) sourceC1545) = raw21704 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw21704; decide +kernel
    rw [ha]
    exact (canonical21704 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1545 + difference 5 3) (sourceB1545 + difference 3 5) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4319) := by
    have ha : (tripleCharges (sourceA1545 + difference 5 3) (sourceB1545 + difference 3 5) sourceC1545) = raw21705 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw21705; decide +kernel
    rw [ha]
    exact (canonical21705 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1545 + difference 5 4) (sourceB1545 + difference 4 5) sourceC1545) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA1545 + difference 5 4) (sourceB1545 + difference 4 5) sourceC1545) = raw7610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1545 sourceB1545 sourceC1545 difference raw7610; decide +kernel
    rw [ha]
    exact (canonical7610 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1545 sourceB1545 sourceC1545
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1545, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1546 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1546 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1546 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceForm1546 : Integer.Sparse Master := [(Sum.inr 560, 3), (Sum.inr 565, 1), (Sum.inr 566, 1), (Sum.inr 888, 6), (Sum.inr 894, 3), (Sum.inr 897, 3), (Sum.inr 1074, 3), (Sum.inr 1077, 1), (Sum.inr 1087, 3), (Sum.inr 1091, 1), (Sum.inr 2522, 3), (Sum.inr 2783, 1), (Sum.inr 2788, 1)]

theorem sourceEq1546 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1546 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1546 + difference 0 1) (sourceB1546 + difference 1 0) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA1546 + difference 0 1) (sourceB1546 + difference 1 0) sourceC1546) = raw7635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw7635; decide +kernel
    rw [ha]
    exact (canonical7635 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1546 + difference 0 2) (sourceB1546 + difference 2 0) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA1546 + difference 0 2) (sourceB1546 + difference 2 0) sourceC1546) = raw7636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw7636; decide +kernel
    rw [ha]
    exact (canonical7636 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1546 + difference 0 3) (sourceB1546 + difference 3 0) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA1546 + difference 0 3) (sourceB1546 + difference 3 0) sourceC1546) = raw7637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw7637; decide +kernel
    rw [ha]
    exact (canonical7637 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1546 + difference 0 4) (sourceB1546 + difference 4 0) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2788) := by
    have ha : (tripleCharges (sourceA1546 + difference 0 4) (sourceB1546 + difference 4 0) sourceC1546) = raw21711 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw21711; decide +kernel
    rw [ha]
    exact (canonical21711 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1546 + difference 0 5) (sourceB1546 + difference 5 0) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA1546 + difference 0 5) (sourceB1546 + difference 5 0) sourceC1546) = raw7638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw7638; decide +kernel
    rw [ha]
    exact (canonical7638 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1546 + difference 1 0) (sourceB1546 + difference 0 1) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 560) := by
    have ha : (tripleCharges (sourceA1546 + difference 1 0) (sourceB1546 + difference 0 1) sourceC1546) = raw23444 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw23444; decide +kernel
    rw [ha]
    exact (canonical23444 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1546 + difference 1 2) (sourceB1546 + difference 2 1) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 888) := by
    have ha : (tripleCharges (sourceA1546 + difference 1 2) (sourceB1546 + difference 2 1) sourceC1546) = raw23445 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw23445; decide +kernel
    rw [ha]
    exact (canonical23445 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1546 + difference 1 3) (sourceB1546 + difference 3 1) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 888) := by
    have ha : (tripleCharges (sourceA1546 + difference 1 3) (sourceB1546 + difference 3 1) sourceC1546) = raw23446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw23446; decide +kernel
    rw [ha]
    exact (canonical23446 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1546 + difference 1 4) (sourceB1546 + difference 4 1) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1546 + difference 1 4) (sourceB1546 + difference 4 1) sourceC1546) = raw7619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw7619; decide +kernel
    rw [ha]
    exact (canonical7619 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1546 + difference 1 5) (sourceB1546 + difference 5 1) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1074) := by
    have ha : (tripleCharges (sourceA1546 + difference 1 5) (sourceB1546 + difference 5 1) sourceC1546) = raw23447 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw23447; decide +kernel
    rw [ha]
    exact (canonical23447 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1546 + difference 2 0) (sourceB1546 + difference 0 2) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 560) := by
    have ha : (tripleCharges (sourceA1546 + difference 2 0) (sourceB1546 + difference 0 2) sourceC1546) = raw23448 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw23448; decide +kernel
    rw [ha]
    exact (canonical23448 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1546 + difference 2 1) (sourceB1546 + difference 1 2) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 888) := by
    have ha : (tripleCharges (sourceA1546 + difference 2 1) (sourceB1546 + difference 1 2) sourceC1546) = raw23449 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw23449; decide +kernel
    rw [ha]
    exact (canonical23449 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1546 + difference 2 3) (sourceB1546 + difference 3 2) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 888) := by
    have ha : (tripleCharges (sourceA1546 + difference 2 3) (sourceB1546 + difference 3 2) sourceC1546) = raw23450 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw23450; decide +kernel
    rw [ha]
    exact (canonical23450 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1546 + difference 2 4) (sourceB1546 + difference 4 2) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1546 + difference 2 4) (sourceB1546 + difference 4 2) sourceC1546) = raw7624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw7624; decide +kernel
    rw [ha]
    exact (canonical7624 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1546 + difference 2 5) (sourceB1546 + difference 5 2) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1074) := by
    have ha : (tripleCharges (sourceA1546 + difference 2 5) (sourceB1546 + difference 5 2) sourceC1546) = raw23451 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw23451; decide +kernel
    rw [ha]
    exact (canonical23451 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1546 + difference 3 0) (sourceB1546 + difference 0 3) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 560) := by
    have ha : (tripleCharges (sourceA1546 + difference 3 0) (sourceB1546 + difference 0 3) sourceC1546) = raw23452 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw23452; decide +kernel
    rw [ha]
    exact (canonical23452 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1546 + difference 3 1) (sourceB1546 + difference 1 3) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 888) := by
    have ha : (tripleCharges (sourceA1546 + difference 3 1) (sourceB1546 + difference 1 3) sourceC1546) = raw23453 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw23453; decide +kernel
    rw [ha]
    exact (canonical23453 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1546 + difference 3 2) (sourceB1546 + difference 2 3) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 888) := by
    have ha : (tripleCharges (sourceA1546 + difference 3 2) (sourceB1546 + difference 2 3) sourceC1546) = raw23454 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw23454; decide +kernel
    rw [ha]
    exact (canonical23454 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1546 + difference 3 4) (sourceB1546 + difference 4 3) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1546 + difference 3 4) (sourceB1546 + difference 4 3) sourceC1546) = raw7629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw7629; decide +kernel
    rw [ha]
    exact (canonical7629 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1546 + difference 3 5) (sourceB1546 + difference 5 3) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1074) := by
    have ha : (tripleCharges (sourceA1546 + difference 3 5) (sourceB1546 + difference 5 3) sourceC1546) = raw23455 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw23455; decide +kernel
    rw [ha]
    exact (canonical23455 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1546 + difference 4 0) (sourceB1546 + difference 0 4) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 565) := by
    have ha : (tripleCharges (sourceA1546 + difference 4 0) (sourceB1546 + difference 0 4) sourceC1546) = raw23456 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw23456; decide +kernel
    rw [ha]
    exact (canonical23456 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1546 + difference 4 1) (sourceB1546 + difference 1 4) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 894) := by
    have ha : (tripleCharges (sourceA1546 + difference 4 1) (sourceB1546 + difference 1 4) sourceC1546) = raw23457 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw23457; decide +kernel
    rw [ha]
    exact (canonical23457 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1546 + difference 4 2) (sourceB1546 + difference 2 4) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 894) := by
    have ha : (tripleCharges (sourceA1546 + difference 4 2) (sourceB1546 + difference 2 4) sourceC1546) = raw23458 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw23458; decide +kernel
    rw [ha]
    exact (canonical23458 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1546 + difference 4 3) (sourceB1546 + difference 3 4) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 894) := by
    have ha : (tripleCharges (sourceA1546 + difference 4 3) (sourceB1546 + difference 3 4) sourceC1546) = raw23459 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw23459; decide +kernel
    rw [ha]
    exact (canonical23459 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1546 + difference 4 5) (sourceB1546 + difference 5 4) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1077) := by
    have ha : (tripleCharges (sourceA1546 + difference 4 5) (sourceB1546 + difference 5 4) sourceC1546) = raw23460 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw23460; decide +kernel
    rw [ha]
    exact (canonical23460 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1546 + difference 5 0) (sourceB1546 + difference 0 5) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 566) := by
    have ha : (tripleCharges (sourceA1546 + difference 5 0) (sourceB1546 + difference 0 5) sourceC1546) = raw21724 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw21724; decide +kernel
    rw [ha]
    exact (canonical21724 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1546 + difference 5 1) (sourceB1546 + difference 1 5) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 897) := by
    have ha : (tripleCharges (sourceA1546 + difference 5 1) (sourceB1546 + difference 1 5) sourceC1546) = raw21725 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw21725; decide +kernel
    rw [ha]
    exact (canonical21725 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1546 + difference 5 2) (sourceB1546 + difference 2 5) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 897) := by
    have ha : (tripleCharges (sourceA1546 + difference 5 2) (sourceB1546 + difference 2 5) sourceC1546) = raw21726 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw21726; decide +kernel
    rw [ha]
    exact (canonical21726 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1546 + difference 5 3) (sourceB1546 + difference 3 5) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 897) := by
    have ha : (tripleCharges (sourceA1546 + difference 5 3) (sourceB1546 + difference 3 5) sourceC1546) = raw21727 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw21727; decide +kernel
    rw [ha]
    exact (canonical21727 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1546 + difference 5 4) (sourceB1546 + difference 4 5) sourceC1546) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA1546 + difference 5 4) (sourceB1546 + difference 4 5) sourceC1546) = raw7639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1546 sourceB1546 sourceC1546 difference raw7639; decide +kernel
    rw [ha]
    exact (canonical7639 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1546 sourceB1546 sourceC1546
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1546, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1547 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB1547 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1547 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1547 : Integer.Sparse Master := [(Sum.inr 4272, 3), (Sum.inr 4280, 1), (Sum.inr 4284, 1), (Sum.inr 4403, 6), (Sum.inr 4430, 3), (Sum.inr 4431, 3), (Sum.inr 4465, 3), (Sum.inr 4466, 3), (Sum.inr 4509, 1), (Sum.inr 4511, 1), (Sum.inr 4611, 3), (Sum.inr 4626, 1), (Sum.inr 4627, 1)]

theorem sourceEq1547 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1547 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1547 + difference 0 1) (sourceB1547 + difference 1 0) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1547 + difference 0 1) (sourceB1547 + difference 1 0) sourceC1547) = raw23461 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23461; decide +kernel
    rw [ha]
    exact (canonical23461 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1547 + difference 0 2) (sourceB1547 + difference 2 0) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1547 + difference 0 2) (sourceB1547 + difference 2 0) sourceC1547) = raw23462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23462; decide +kernel
    rw [ha]
    exact (canonical23462 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1547 + difference 0 3) (sourceB1547 + difference 3 0) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA1547 + difference 0 3) (sourceB1547 + difference 3 0) sourceC1547) = raw22787 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw22787; decide +kernel
    rw [ha]
    exact (canonical22787 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1547 + difference 0 4) (sourceB1547 + difference 4 0) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4627) := by
    have ha : (tripleCharges (sourceA1547 + difference 0 4) (sourceB1547 + difference 4 0) sourceC1547) = raw22627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw22627; decide +kernel
    rw [ha]
    exact (canonical22627 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1547 + difference 0 5) (sourceB1547 + difference 5 0) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4626) := by
    have ha : (tripleCharges (sourceA1547 + difference 0 5) (sourceB1547 + difference 5 0) sourceC1547) = raw23463 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23463; decide +kernel
    rw [ha]
    exact (canonical23463 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1547 + difference 1 0) (sourceB1547 + difference 0 1) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4272) := by
    have ha : (tripleCharges (sourceA1547 + difference 1 0) (sourceB1547 + difference 0 1) sourceC1547) = raw23092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23092; decide +kernel
    rw [ha]
    exact (canonical23092 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1547 + difference 1 2) (sourceB1547 + difference 2 1) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4403) := by
    have ha : (tripleCharges (sourceA1547 + difference 1 2) (sourceB1547 + difference 2 1) sourceC1547) = raw23094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23094; decide +kernel
    rw [ha]
    exact (canonical23094 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1547 + difference 1 3) (sourceB1547 + difference 3 1) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4403) := by
    have ha : (tripleCharges (sourceA1547 + difference 1 3) (sourceB1547 + difference 3 1) sourceC1547) = raw23095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23095; decide +kernel
    rw [ha]
    exact (canonical23095 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1547 + difference 1 4) (sourceB1547 + difference 4 1) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1547 + difference 1 4) (sourceB1547 + difference 4 1) sourceC1547) = raw23270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23270; decide +kernel
    rw [ha]
    exact (canonical23270 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1547 + difference 1 5) (sourceB1547 + difference 5 1) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4465) := by
    have ha : (tripleCharges (sourceA1547 + difference 1 5) (sourceB1547 + difference 5 1) sourceC1547) = raw23096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23096; decide +kernel
    rw [ha]
    exact (canonical23096 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1547 + difference 2 0) (sourceB1547 + difference 0 2) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4272) := by
    have ha : (tripleCharges (sourceA1547 + difference 2 0) (sourceB1547 + difference 0 2) sourceC1547) = raw23464 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23464; decide +kernel
    rw [ha]
    exact (canonical23464 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1547 + difference 2 1) (sourceB1547 + difference 1 2) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4403) := by
    have ha : (tripleCharges (sourceA1547 + difference 2 1) (sourceB1547 + difference 1 2) sourceC1547) = raw23465 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23465; decide +kernel
    rw [ha]
    exact (canonical23465 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1547 + difference 2 3) (sourceB1547 + difference 3 2) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4403) := by
    have ha : (tripleCharges (sourceA1547 + difference 2 3) (sourceB1547 + difference 3 2) sourceC1547) = raw23466 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23466; decide +kernel
    rw [ha]
    exact (canonical23466 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1547 + difference 2 4) (sourceB1547 + difference 4 2) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1547 + difference 2 4) (sourceB1547 + difference 4 2) sourceC1547) = raw23083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23083; decide +kernel
    rw [ha]
    exact (canonical23083 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1547 + difference 2 5) (sourceB1547 + difference 5 2) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4465) := by
    have ha : (tripleCharges (sourceA1547 + difference 2 5) (sourceB1547 + difference 5 2) sourceC1547) = raw23467 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23467; decide +kernel
    rw [ha]
    exact (canonical23467 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1547 + difference 3 0) (sourceB1547 + difference 0 3) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4272) := by
    have ha : (tripleCharges (sourceA1547 + difference 3 0) (sourceB1547 + difference 0 3) sourceC1547) = raw23468 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23468; decide +kernel
    rw [ha]
    exact (canonical23468 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1547 + difference 3 1) (sourceB1547 + difference 1 3) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4403) := by
    have ha : (tripleCharges (sourceA1547 + difference 3 1) (sourceB1547 + difference 1 3) sourceC1547) = raw23469 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23469; decide +kernel
    rw [ha]
    exact (canonical23469 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1547 + difference 3 2) (sourceB1547 + difference 2 3) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4403) := by
    have ha : (tripleCharges (sourceA1547 + difference 3 2) (sourceB1547 + difference 2 3) sourceC1547) = raw23470 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23470; decide +kernel
    rw [ha]
    exact (canonical23470 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1547 + difference 3 4) (sourceB1547 + difference 4 3) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1547 + difference 3 4) (sourceB1547 + difference 4 3) sourceC1547) = raw23088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23088; decide +kernel
    rw [ha]
    exact (canonical23088 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1547 + difference 3 5) (sourceB1547 + difference 5 3) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4465) := by
    have ha : (tripleCharges (sourceA1547 + difference 3 5) (sourceB1547 + difference 5 3) sourceC1547) = raw23471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23471; decide +kernel
    rw [ha]
    exact (canonical23471 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1547 + difference 4 0) (sourceB1547 + difference 0 4) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4280) := by
    have ha : (tripleCharges (sourceA1547 + difference 4 0) (sourceB1547 + difference 0 4) sourceC1547) = raw23472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23472; decide +kernel
    rw [ha]
    exact (canonical23472 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1547 + difference 4 1) (sourceB1547 + difference 1 4) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4430) := by
    have ha : (tripleCharges (sourceA1547 + difference 4 1) (sourceB1547 + difference 1 4) sourceC1547) = raw23473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23473; decide +kernel
    rw [ha]
    exact (canonical23473 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1547 + difference 4 2) (sourceB1547 + difference 2 4) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4430) := by
    have ha : (tripleCharges (sourceA1547 + difference 4 2) (sourceB1547 + difference 2 4) sourceC1547) = raw23474 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23474; decide +kernel
    rw [ha]
    exact (canonical23474 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1547 + difference 4 3) (sourceB1547 + difference 3 4) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4430) := by
    have ha : (tripleCharges (sourceA1547 + difference 4 3) (sourceB1547 + difference 3 4) sourceC1547) = raw23475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23475; decide +kernel
    rw [ha]
    exact (canonical23475 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1547 + difference 4 5) (sourceB1547 + difference 5 4) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4509) := by
    have ha : (tripleCharges (sourceA1547 + difference 4 5) (sourceB1547 + difference 5 4) sourceC1547) = raw23476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23476; decide +kernel
    rw [ha]
    exact (canonical23476 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1547 + difference 5 0) (sourceB1547 + difference 0 5) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4284) := by
    have ha : (tripleCharges (sourceA1547 + difference 5 0) (sourceB1547 + difference 0 5) sourceC1547) = raw23477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23477; decide +kernel
    rw [ha]
    exact (canonical23477 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1547 + difference 5 1) (sourceB1547 + difference 1 5) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA1547 + difference 5 1) (sourceB1547 + difference 1 5) sourceC1547) = raw23478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23478; decide +kernel
    rw [ha]
    exact (canonical23478 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1547 + difference 5 2) (sourceB1547 + difference 2 5) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA1547 + difference 5 2) (sourceB1547 + difference 2 5) sourceC1547) = raw23479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw23479; decide +kernel
    rw [ha]
    exact (canonical23479 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1547 + difference 5 3) (sourceB1547 + difference 3 5) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA1547 + difference 5 3) (sourceB1547 + difference 3 5) sourceC1547) = raw22783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw22783; decide +kernel
    rw [ha]
    exact (canonical22783 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1547 + difference 5 4) (sourceB1547 + difference 4 5) sourceC1547) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1547 + difference 5 4) (sourceB1547 + difference 4 5) sourceC1547) = raw22623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1547 sourceB1547 sourceC1547 difference raw22623; decide +kernel
    rw [ha]
    exact (canonical22623 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1547 sourceB1547 sourceC1547
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1547, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1548 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB1548 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1548 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1548 : Integer.Sparse Master := [(Sum.inr 815, 3), (Sum.inr 862, 1), (Sum.inr 863, 1), (Sum.inr 984, 6), (Sum.inr 1011, 3), (Sum.inr 1012, 3), (Sum.inr 1048, 3), (Sum.inr 1049, 3), (Sum.inr 1093, 1), (Sum.inr 1095, 1), (Sum.inr 1245, 3), (Sum.inr 1310, 1), (Sum.inr 1311, 1)]

theorem sourceEq1548 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1548 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1548 + difference 0 1) (sourceB1548 + difference 1 0) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA1548 + difference 0 1) (sourceB1548 + difference 1 0) sourceC1548) = raw23480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23480; decide +kernel
    rw [ha]
    exact (canonical23480 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1548 + difference 0 2) (sourceB1548 + difference 2 0) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA1548 + difference 0 2) (sourceB1548 + difference 2 0) sourceC1548) = raw23481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23481; decide +kernel
    rw [ha]
    exact (canonical23481 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1548 + difference 0 3) (sourceB1548 + difference 3 0) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA1548 + difference 0 3) (sourceB1548 + difference 3 0) sourceC1548) = raw22808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw22808; decide +kernel
    rw [ha]
    exact (canonical22808 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1548 + difference 0 4) (sourceB1548 + difference 4 0) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1311) := by
    have ha : (tripleCharges (sourceA1548 + difference 0 4) (sourceB1548 + difference 4 0) sourceC1548) = raw22649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw22649; decide +kernel
    rw [ha]
    exact (canonical22649 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1548 + difference 0 5) (sourceB1548 + difference 5 0) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1310) := by
    have ha : (tripleCharges (sourceA1548 + difference 0 5) (sourceB1548 + difference 5 0) sourceC1548) = raw23482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23482; decide +kernel
    rw [ha]
    exact (canonical23482 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1548 + difference 1 0) (sourceB1548 + difference 0 1) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 815) := by
    have ha : (tripleCharges (sourceA1548 + difference 1 0) (sourceB1548 + difference 0 1) sourceC1548) = raw23116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23116; decide +kernel
    rw [ha]
    exact (canonical23116 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1548 + difference 1 2) (sourceB1548 + difference 2 1) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 984) := by
    have ha : (tripleCharges (sourceA1548 + difference 1 2) (sourceB1548 + difference 2 1) sourceC1548) = raw23118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23118; decide +kernel
    rw [ha]
    exact (canonical23118 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1548 + difference 1 3) (sourceB1548 + difference 3 1) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 984) := by
    have ha : (tripleCharges (sourceA1548 + difference 1 3) (sourceB1548 + difference 3 1) sourceC1548) = raw23119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23119; decide +kernel
    rw [ha]
    exact (canonical23119 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1548 + difference 1 4) (sourceB1548 + difference 4 1) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1548 + difference 1 4) (sourceB1548 + difference 4 1) sourceC1548) = raw23284 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23284; decide +kernel
    rw [ha]
    exact (canonical23284 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1548 + difference 1 5) (sourceB1548 + difference 5 1) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1048) := by
    have ha : (tripleCharges (sourceA1548 + difference 1 5) (sourceB1548 + difference 5 1) sourceC1548) = raw23120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23120; decide +kernel
    rw [ha]
    exact (canonical23120 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1548 + difference 2 0) (sourceB1548 + difference 0 2) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 815) := by
    have ha : (tripleCharges (sourceA1548 + difference 2 0) (sourceB1548 + difference 0 2) sourceC1548) = raw23483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23483; decide +kernel
    rw [ha]
    exact (canonical23483 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1548 + difference 2 1) (sourceB1548 + difference 1 2) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 984) := by
    have ha : (tripleCharges (sourceA1548 + difference 2 1) (sourceB1548 + difference 1 2) sourceC1548) = raw23484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23484; decide +kernel
    rw [ha]
    exact (canonical23484 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1548 + difference 2 3) (sourceB1548 + difference 3 2) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 984) := by
    have ha : (tripleCharges (sourceA1548 + difference 2 3) (sourceB1548 + difference 3 2) sourceC1548) = raw23485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23485; decide +kernel
    rw [ha]
    exact (canonical23485 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1548 + difference 2 4) (sourceB1548 + difference 4 2) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1548 + difference 2 4) (sourceB1548 + difference 4 2) sourceC1548) = raw23107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23107; decide +kernel
    rw [ha]
    exact (canonical23107 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1548 + difference 2 5) (sourceB1548 + difference 5 2) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1048) := by
    have ha : (tripleCharges (sourceA1548 + difference 2 5) (sourceB1548 + difference 5 2) sourceC1548) = raw23486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23486; decide +kernel
    rw [ha]
    exact (canonical23486 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1548 + difference 3 0) (sourceB1548 + difference 0 3) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 815) := by
    have ha : (tripleCharges (sourceA1548 + difference 3 0) (sourceB1548 + difference 0 3) sourceC1548) = raw23487 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23487; decide +kernel
    rw [ha]
    exact (canonical23487 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1548 + difference 3 1) (sourceB1548 + difference 1 3) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 984) := by
    have ha : (tripleCharges (sourceA1548 + difference 3 1) (sourceB1548 + difference 1 3) sourceC1548) = raw23488 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23488; decide +kernel
    rw [ha]
    exact (canonical23488 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1548 + difference 3 2) (sourceB1548 + difference 2 3) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 984) := by
    have ha : (tripleCharges (sourceA1548 + difference 3 2) (sourceB1548 + difference 2 3) sourceC1548) = raw23489 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23489; decide +kernel
    rw [ha]
    exact (canonical23489 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1548 + difference 3 4) (sourceB1548 + difference 4 3) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1548 + difference 3 4) (sourceB1548 + difference 4 3) sourceC1548) = raw23112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23112; decide +kernel
    rw [ha]
    exact (canonical23112 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1548 + difference 3 5) (sourceB1548 + difference 5 3) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1048) := by
    have ha : (tripleCharges (sourceA1548 + difference 3 5) (sourceB1548 + difference 5 3) sourceC1548) = raw23490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23490; decide +kernel
    rw [ha]
    exact (canonical23490 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1548 + difference 4 0) (sourceB1548 + difference 0 4) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 862) := by
    have ha : (tripleCharges (sourceA1548 + difference 4 0) (sourceB1548 + difference 0 4) sourceC1548) = raw23491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23491; decide +kernel
    rw [ha]
    exact (canonical23491 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1548 + difference 4 1) (sourceB1548 + difference 1 4) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1011) := by
    have ha : (tripleCharges (sourceA1548 + difference 4 1) (sourceB1548 + difference 1 4) sourceC1548) = raw23492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23492; decide +kernel
    rw [ha]
    exact (canonical23492 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1548 + difference 4 2) (sourceB1548 + difference 2 4) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1011) := by
    have ha : (tripleCharges (sourceA1548 + difference 4 2) (sourceB1548 + difference 2 4) sourceC1548) = raw23493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23493; decide +kernel
    rw [ha]
    exact (canonical23493 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1548 + difference 4 3) (sourceB1548 + difference 3 4) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1011) := by
    have ha : (tripleCharges (sourceA1548 + difference 4 3) (sourceB1548 + difference 3 4) sourceC1548) = raw23494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23494; decide +kernel
    rw [ha]
    exact (canonical23494 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1548 + difference 4 5) (sourceB1548 + difference 5 4) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1093) := by
    have ha : (tripleCharges (sourceA1548 + difference 4 5) (sourceB1548 + difference 5 4) sourceC1548) = raw23495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23495; decide +kernel
    rw [ha]
    exact (canonical23495 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1548 + difference 5 0) (sourceB1548 + difference 0 5) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 863) := by
    have ha : (tripleCharges (sourceA1548 + difference 5 0) (sourceB1548 + difference 0 5) sourceC1548) = raw23496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23496; decide +kernel
    rw [ha]
    exact (canonical23496 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1548 + difference 5 1) (sourceB1548 + difference 1 5) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1012) := by
    have ha : (tripleCharges (sourceA1548 + difference 5 1) (sourceB1548 + difference 1 5) sourceC1548) = raw23497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23497; decide +kernel
    rw [ha]
    exact (canonical23497 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1548 + difference 5 2) (sourceB1548 + difference 2 5) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1012) := by
    have ha : (tripleCharges (sourceA1548 + difference 5 2) (sourceB1548 + difference 2 5) sourceC1548) = raw23498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw23498; decide +kernel
    rw [ha]
    exact (canonical23498 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1548 + difference 5 3) (sourceB1548 + difference 3 5) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1012) := by
    have ha : (tripleCharges (sourceA1548 + difference 5 3) (sourceB1548 + difference 3 5) sourceC1548) = raw22804 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw22804; decide +kernel
    rw [ha]
    exact (canonical22804 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1548 + difference 5 4) (sourceB1548 + difference 4 5) sourceC1548) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1095) := by
    have ha : (tripleCharges (sourceA1548 + difference 5 4) (sourceB1548 + difference 4 5) sourceC1548) = raw22645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1548 sourceB1548 sourceC1548 difference raw22645; decide +kernel
    rw [ha]
    exact (canonical22645 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1548 sourceB1548 sourceC1548
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1548, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1549 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB1549 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC1549 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1549 : Integer.Sparse Master := [(Sum.inr 1273, 3), (Sum.inr 1282, 3), (Sum.inr 1285, 1), (Sum.inr 1309, 1), (Sum.inr 1310, 1), (Sum.inr 1311, 1), (Sum.inr 1400, 6), (Sum.inr 1418, 3), (Sum.inr 1419, 3), (Sum.inr 1430, 3), (Sum.inr 1455, 1), (Sum.inr 1471, 3), (Sum.inr 1487, 1)]

theorem sourceEq1549 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1549 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1549 + difference 0 1) (sourceB1549 + difference 1 0) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA1549 + difference 0 1) (sourceB1549 + difference 1 0) sourceC1549) = raw23499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23499; decide +kernel
    rw [ha]
    exact (canonical23499 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1549 + difference 0 2) (sourceB1549 + difference 2 0) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA1549 + difference 0 2) (sourceB1549 + difference 2 0) sourceC1549) = raw23500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23500; decide +kernel
    rw [ha]
    exact (canonical23500 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1549 + difference 0 3) (sourceB1549 + difference 3 0) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA1549 + difference 0 3) (sourceB1549 + difference 3 0) sourceC1549) = raw22837 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw22837; decide +kernel
    rw [ha]
    exact (canonical22837 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1549 + difference 0 4) (sourceB1549 + difference 4 0) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1311) := by
    have ha : (tripleCharges (sourceA1549 + difference 0 4) (sourceB1549 + difference 4 0) sourceC1549) = raw22832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw22832; decide +kernel
    rw [ha]
    exact (canonical22832 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1549 + difference 0 5) (sourceB1549 + difference 5 0) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1310) := by
    have ha : (tripleCharges (sourceA1549 + difference 0 5) (sourceB1549 + difference 5 0) sourceC1549) = raw23501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23501; decide +kernel
    rw [ha]
    exact (canonical23501 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1549 + difference 1 0) (sourceB1549 + difference 0 1) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1471) := by
    have ha : (tripleCharges (sourceA1549 + difference 1 0) (sourceB1549 + difference 0 1) sourceC1549) = raw23141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23141; decide +kernel
    rw [ha]
    exact (canonical23141 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1549 + difference 1 2) (sourceB1549 + difference 2 1) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1400) := by
    have ha : (tripleCharges (sourceA1549 + difference 1 2) (sourceB1549 + difference 2 1) sourceC1549) = raw23143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23143; decide +kernel
    rw [ha]
    exact (canonical23143 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1549 + difference 1 3) (sourceB1549 + difference 3 1) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1400) := by
    have ha : (tripleCharges (sourceA1549 + difference 1 3) (sourceB1549 + difference 3 1) sourceC1549) = raw23144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23144; decide +kernel
    rw [ha]
    exact (canonical23144 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1549 + difference 1 4) (sourceB1549 + difference 4 1) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA1549 + difference 1 4) (sourceB1549 + difference 4 1) sourceC1549) = raw23302 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23302; decide +kernel
    rw [ha]
    exact (canonical23302 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1549 + difference 1 5) (sourceB1549 + difference 5 1) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1418) := by
    have ha : (tripleCharges (sourceA1549 + difference 1 5) (sourceB1549 + difference 5 1) sourceC1549) = raw23145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23145; decide +kernel
    rw [ha]
    exact (canonical23145 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1549 + difference 2 0) (sourceB1549 + difference 0 2) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1471) := by
    have ha : (tripleCharges (sourceA1549 + difference 2 0) (sourceB1549 + difference 0 2) sourceC1549) = raw23502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23502; decide +kernel
    rw [ha]
    exact (canonical23502 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1549 + difference 2 1) (sourceB1549 + difference 1 2) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1400) := by
    have ha : (tripleCharges (sourceA1549 + difference 2 1) (sourceB1549 + difference 1 2) sourceC1549) = raw23503 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23503; decide +kernel
    rw [ha]
    exact (canonical23503 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1549 + difference 2 3) (sourceB1549 + difference 3 2) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1400) := by
    have ha : (tripleCharges (sourceA1549 + difference 2 3) (sourceB1549 + difference 3 2) sourceC1549) = raw23504 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23504; decide +kernel
    rw [ha]
    exact (canonical23504 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1549 + difference 2 4) (sourceB1549 + difference 4 2) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA1549 + difference 2 4) (sourceB1549 + difference 4 2) sourceC1549) = raw23132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23132; decide +kernel
    rw [ha]
    exact (canonical23132 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1549 + difference 2 5) (sourceB1549 + difference 5 2) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1418) := by
    have ha : (tripleCharges (sourceA1549 + difference 2 5) (sourceB1549 + difference 5 2) sourceC1549) = raw23505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23505; decide +kernel
    rw [ha]
    exact (canonical23505 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1549 + difference 3 0) (sourceB1549 + difference 0 3) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1471) := by
    have ha : (tripleCharges (sourceA1549 + difference 3 0) (sourceB1549 + difference 0 3) sourceC1549) = raw23506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23506; decide +kernel
    rw [ha]
    exact (canonical23506 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1549 + difference 3 1) (sourceB1549 + difference 1 3) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1400) := by
    have ha : (tripleCharges (sourceA1549 + difference 3 1) (sourceB1549 + difference 1 3) sourceC1549) = raw23507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23507; decide +kernel
    rw [ha]
    exact (canonical23507 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1549 + difference 3 2) (sourceB1549 + difference 2 3) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1400) := by
    have ha : (tripleCharges (sourceA1549 + difference 3 2) (sourceB1549 + difference 2 3) sourceC1549) = raw23508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23508; decide +kernel
    rw [ha]
    exact (canonical23508 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1549 + difference 3 4) (sourceB1549 + difference 4 3) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1419) := by
    have ha : (tripleCharges (sourceA1549 + difference 3 4) (sourceB1549 + difference 4 3) sourceC1549) = raw23137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23137; decide +kernel
    rw [ha]
    exact (canonical23137 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1549 + difference 3 5) (sourceB1549 + difference 5 3) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1418) := by
    have ha : (tripleCharges (sourceA1549 + difference 3 5) (sourceB1549 + difference 5 3) sourceC1549) = raw23509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23509; decide +kernel
    rw [ha]
    exact (canonical23509 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1549 + difference 4 0) (sourceB1549 + difference 0 4) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1285) := by
    have ha : (tripleCharges (sourceA1549 + difference 4 0) (sourceB1549 + difference 0 4) sourceC1549) = raw23510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23510; decide +kernel
    rw [ha]
    exact (canonical23510 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1549 + difference 4 1) (sourceB1549 + difference 1 4) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1282) := by
    have ha : (tripleCharges (sourceA1549 + difference 4 1) (sourceB1549 + difference 1 4) sourceC1549) = raw23511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23511; decide +kernel
    rw [ha]
    exact (canonical23511 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1549 + difference 4 2) (sourceB1549 + difference 2 4) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1282) := by
    have ha : (tripleCharges (sourceA1549 + difference 4 2) (sourceB1549 + difference 2 4) sourceC1549) = raw23512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23512; decide +kernel
    rw [ha]
    exact (canonical23512 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1549 + difference 4 3) (sourceB1549 + difference 3 4) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1282) := by
    have ha : (tripleCharges (sourceA1549 + difference 4 3) (sourceB1549 + difference 3 4) sourceC1549) = raw23513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23513; decide +kernel
    rw [ha]
    exact (canonical23513 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1549 + difference 4 5) (sourceB1549 + difference 5 4) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1309) := by
    have ha : (tripleCharges (sourceA1549 + difference 4 5) (sourceB1549 + difference 5 4) sourceC1549) = raw23514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23514; decide +kernel
    rw [ha]
    exact (canonical23514 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1549 + difference 5 0) (sourceB1549 + difference 0 5) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1487) := by
    have ha : (tripleCharges (sourceA1549 + difference 5 0) (sourceB1549 + difference 0 5) sourceC1549) = raw23515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23515; decide +kernel
    rw [ha]
    exact (canonical23515 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1549 + difference 5 1) (sourceB1549 + difference 1 5) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1430) := by
    have ha : (tripleCharges (sourceA1549 + difference 5 1) (sourceB1549 + difference 1 5) sourceC1549) = raw23516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23516; decide +kernel
    rw [ha]
    exact (canonical23516 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1549 + difference 5 2) (sourceB1549 + difference 2 5) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1430) := by
    have ha : (tripleCharges (sourceA1549 + difference 5 2) (sourceB1549 + difference 2 5) sourceC1549) = raw23517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw23517; decide +kernel
    rw [ha]
    exact (canonical23517 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1549 + difference 5 3) (sourceB1549 + difference 3 5) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1430) := by
    have ha : (tripleCharges (sourceA1549 + difference 5 3) (sourceB1549 + difference 3 5) sourceC1549) = raw22833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw22833; decide +kernel
    rw [ha]
    exact (canonical22833 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1549 + difference 5 4) (sourceB1549 + difference 4 5) sourceC1549) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1455) := by
    have ha : (tripleCharges (sourceA1549 + difference 5 4) (sourceB1549 + difference 4 5) sourceC1549) = raw22828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1549 sourceB1549 sourceC1549 difference raw22828; decide +kernel
    rw [ha]
    exact (canonical22828 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1549 sourceB1549 sourceC1549
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1549, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1550 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1550 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1550 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceForm1550 : Integer.Sparse Master := [(Sum.inr 4084, 1), (Sum.inr 4180, 3), (Sum.inr 4191, 1), (Sum.inr 4192, 1), (Sum.inr 4349, 6), (Sum.inr 4360, 3), (Sum.inr 4361, 3), (Sum.inr 4498, 3), (Sum.inr 4499, 3), (Sum.inr 4505, 1), (Sum.inr 4507, 1), (Sum.inr 4846, 3), (Sum.inr 4901, 1)]

theorem sourceEq1550 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1550 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1550 + difference 0 1) (sourceB1550 + difference 1 0) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA1550 + difference 0 1) (sourceB1550 + difference 1 0) sourceC1550) = raw11522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw11522; decide +kernel
    rw [ha]
    exact (canonical11522 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1550 + difference 0 2) (sourceB1550 + difference 2 0) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA1550 + difference 0 2) (sourceB1550 + difference 2 0) sourceC1550) = raw11523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw11523; decide +kernel
    rw [ha]
    exact (canonical11523 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1550 + difference 0 3) (sourceB1550 + difference 3 0) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA1550 + difference 0 3) (sourceB1550 + difference 3 0) sourceC1550) = raw11524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw11524; decide +kernel
    rw [ha]
    exact (canonical11524 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1550 + difference 0 4) (sourceB1550 + difference 4 0) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4901) := by
    have ha : (tripleCharges (sourceA1550 + difference 0 4) (sourceB1550 + difference 4 0) sourceC1550) = raw21634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw21634; decide +kernel
    rw [ha]
    exact (canonical21634 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1550 + difference 0 5) (sourceB1550 + difference 5 0) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1550 + difference 0 5) (sourceB1550 + difference 5 0) sourceC1550) = raw11525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw11525; decide +kernel
    rw [ha]
    exact (canonical11525 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1550 + difference 1 0) (sourceB1550 + difference 0 1) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4180) := by
    have ha : (tripleCharges (sourceA1550 + difference 1 0) (sourceB1550 + difference 0 1) sourceC1550) = raw23518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23518; decide +kernel
    rw [ha]
    exact (canonical23518 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1550 + difference 1 2) (sourceB1550 + difference 2 1) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1550 + difference 1 2) (sourceB1550 + difference 2 1) sourceC1550) = raw23519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23519; decide +kernel
    rw [ha]
    exact (canonical23519 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1550 + difference 1 3) (sourceB1550 + difference 3 1) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1550 + difference 1 3) (sourceB1550 + difference 3 1) sourceC1550) = raw23520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23520; decide +kernel
    rw [ha]
    exact (canonical23520 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1550 + difference 1 4) (sourceB1550 + difference 4 1) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1550 + difference 1 4) (sourceB1550 + difference 4 1) sourceC1550) = raw11506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw11506; decide +kernel
    rw [ha]
    exact (canonical11506 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1550 + difference 1 5) (sourceB1550 + difference 5 1) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1550 + difference 1 5) (sourceB1550 + difference 5 1) sourceC1550) = raw23521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23521; decide +kernel
    rw [ha]
    exact (canonical23521 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1550 + difference 2 0) (sourceB1550 + difference 0 2) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4180) := by
    have ha : (tripleCharges (sourceA1550 + difference 2 0) (sourceB1550 + difference 0 2) sourceC1550) = raw23522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23522; decide +kernel
    rw [ha]
    exact (canonical23522 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1550 + difference 2 1) (sourceB1550 + difference 1 2) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1550 + difference 2 1) (sourceB1550 + difference 1 2) sourceC1550) = raw23523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23523; decide +kernel
    rw [ha]
    exact (canonical23523 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1550 + difference 2 3) (sourceB1550 + difference 3 2) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1550 + difference 2 3) (sourceB1550 + difference 3 2) sourceC1550) = raw23524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23524; decide +kernel
    rw [ha]
    exact (canonical23524 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1550 + difference 2 4) (sourceB1550 + difference 4 2) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1550 + difference 2 4) (sourceB1550 + difference 4 2) sourceC1550) = raw11511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw11511; decide +kernel
    rw [ha]
    exact (canonical11511 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1550 + difference 2 5) (sourceB1550 + difference 5 2) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1550 + difference 2 5) (sourceB1550 + difference 5 2) sourceC1550) = raw23525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23525; decide +kernel
    rw [ha]
    exact (canonical23525 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1550 + difference 3 0) (sourceB1550 + difference 0 3) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4180) := by
    have ha : (tripleCharges (sourceA1550 + difference 3 0) (sourceB1550 + difference 0 3) sourceC1550) = raw23526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23526; decide +kernel
    rw [ha]
    exact (canonical23526 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1550 + difference 3 1) (sourceB1550 + difference 1 3) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1550 + difference 3 1) (sourceB1550 + difference 1 3) sourceC1550) = raw23527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23527; decide +kernel
    rw [ha]
    exact (canonical23527 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1550 + difference 3 2) (sourceB1550 + difference 2 3) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4349) := by
    have ha : (tripleCharges (sourceA1550 + difference 3 2) (sourceB1550 + difference 2 3) sourceC1550) = raw23528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23528; decide +kernel
    rw [ha]
    exact (canonical23528 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1550 + difference 3 4) (sourceB1550 + difference 4 3) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4499) := by
    have ha : (tripleCharges (sourceA1550 + difference 3 4) (sourceB1550 + difference 4 3) sourceC1550) = raw11516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw11516; decide +kernel
    rw [ha]
    exact (canonical11516 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1550 + difference 3 5) (sourceB1550 + difference 5 3) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4498) := by
    have ha : (tripleCharges (sourceA1550 + difference 3 5) (sourceB1550 + difference 5 3) sourceC1550) = raw23529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23529; decide +kernel
    rw [ha]
    exact (canonical23529 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1550 + difference 4 0) (sourceB1550 + difference 0 4) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4191) := by
    have ha : (tripleCharges (sourceA1550 + difference 4 0) (sourceB1550 + difference 0 4) sourceC1550) = raw23530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23530; decide +kernel
    rw [ha]
    exact (canonical23530 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1550 + difference 4 1) (sourceB1550 + difference 1 4) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1550 + difference 4 1) (sourceB1550 + difference 1 4) sourceC1550) = raw23531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23531; decide +kernel
    rw [ha]
    exact (canonical23531 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1550 + difference 4 2) (sourceB1550 + difference 2 4) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1550 + difference 4 2) (sourceB1550 + difference 2 4) sourceC1550) = raw23532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23532; decide +kernel
    rw [ha]
    exact (canonical23532 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1550 + difference 4 3) (sourceB1550 + difference 3 4) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4360) := by
    have ha : (tripleCharges (sourceA1550 + difference 4 3) (sourceB1550 + difference 3 4) sourceC1550) = raw23533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23533; decide +kernel
    rw [ha]
    exact (canonical23533 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1550 + difference 4 5) (sourceB1550 + difference 5 4) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4505) := by
    have ha : (tripleCharges (sourceA1550 + difference 4 5) (sourceB1550 + difference 5 4) sourceC1550) = raw23534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw23534; decide +kernel
    rw [ha]
    exact (canonical23534 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1550 + difference 5 0) (sourceB1550 + difference 0 5) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4192) := by
    have ha : (tripleCharges (sourceA1550 + difference 5 0) (sourceB1550 + difference 0 5) sourceC1550) = raw21647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw21647; decide +kernel
    rw [ha]
    exact (canonical21647 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1550 + difference 5 1) (sourceB1550 + difference 1 5) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4361) := by
    have ha : (tripleCharges (sourceA1550 + difference 5 1) (sourceB1550 + difference 1 5) sourceC1550) = raw21648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw21648; decide +kernel
    rw [ha]
    exact (canonical21648 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1550 + difference 5 2) (sourceB1550 + difference 2 5) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4361) := by
    have ha : (tripleCharges (sourceA1550 + difference 5 2) (sourceB1550 + difference 2 5) sourceC1550) = raw21649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw21649; decide +kernel
    rw [ha]
    exact (canonical21649 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1550 + difference 5 3) (sourceB1550 + difference 3 5) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4361) := by
    have ha : (tripleCharges (sourceA1550 + difference 5 3) (sourceB1550 + difference 3 5) sourceC1550) = raw21650 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw21650; decide +kernel
    rw [ha]
    exact (canonical21650 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1550 + difference 5 4) (sourceB1550 + difference 4 5) sourceC1550) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA1550 + difference 5 4) (sourceB1550 + difference 4 5) sourceC1550) = raw11526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1550 sourceB1550 sourceC1550 difference raw11526; decide +kernel
    rw [ha]
    exact (canonical11526 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1550 sourceB1550 sourceC1550
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1550, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1551 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1551 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1551 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceForm1551 : Integer.Sparse Master := [(Sum.inr 1519, 3), (Sum.inr 1538, 1), (Sum.inr 1539, 1), (Sum.inr 1675, 6), (Sum.inr 1693, 3), (Sum.inr 1694, 3), (Sum.inr 1727, 3), (Sum.inr 1728, 3), (Sum.inr 1754, 1), (Sum.inr 1756, 1), (Sum.inr 2229, 3), (Sum.inr 2293, 1), (Sum.inr 4084, 1)]

theorem sourceEq1551 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1551 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1551 + difference 0 1) (sourceB1551 + difference 1 0) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA1551 + difference 0 1) (sourceB1551 + difference 1 0) sourceC1551) = raw23535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23535; decide +kernel
    rw [ha]
    exact (canonical23535 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1551 + difference 0 2) (sourceB1551 + difference 2 0) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA1551 + difference 0 2) (sourceB1551 + difference 2 0) sourceC1551) = raw23536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23536; decide +kernel
    rw [ha]
    exact (canonical23536 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1551 + difference 0 3) (sourceB1551 + difference 3 0) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2229) := by
    have ha : (tripleCharges (sourceA1551 + difference 0 3) (sourceB1551 + difference 3 0) sourceC1551) = raw23537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23537; decide +kernel
    rw [ha]
    exact (canonical23537 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1551 + difference 0 4) (sourceB1551 + difference 4 0) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA1551 + difference 0 4) (sourceB1551 + difference 4 0) sourceC1551) = raw21660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw21660; decide +kernel
    rw [ha]
    exact (canonical21660 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1551 + difference 0 5) (sourceB1551 + difference 5 0) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (tripleCharges (sourceA1551 + difference 0 5) (sourceB1551 + difference 5 0) sourceC1551) = raw23538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23538; decide +kernel
    rw [ha]
    exact (canonical23538 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1551 + difference 1 0) (sourceB1551 + difference 0 1) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA1551 + difference 1 0) (sourceB1551 + difference 0 1) sourceC1551) = raw23539 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23539; decide +kernel
    rw [ha]
    exact (canonical23539 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1551 + difference 1 2) (sourceB1551 + difference 2 1) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA1551 + difference 1 2) (sourceB1551 + difference 2 1) sourceC1551) = raw23540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23540; decide +kernel
    rw [ha]
    exact (canonical23540 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1551 + difference 1 3) (sourceB1551 + difference 3 1) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA1551 + difference 1 3) (sourceB1551 + difference 3 1) sourceC1551) = raw23541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23541; decide +kernel
    rw [ha]
    exact (canonical23541 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1551 + difference 1 4) (sourceB1551 + difference 4 1) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1551 + difference 1 4) (sourceB1551 + difference 4 1) sourceC1551) = raw21665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw21665; decide +kernel
    rw [ha]
    exact (canonical21665 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1551 + difference 1 5) (sourceB1551 + difference 5 1) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1551 + difference 1 5) (sourceB1551 + difference 5 1) sourceC1551) = raw23542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23542; decide +kernel
    rw [ha]
    exact (canonical23542 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1551 + difference 2 0) (sourceB1551 + difference 0 2) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA1551 + difference 2 0) (sourceB1551 + difference 0 2) sourceC1551) = raw23543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23543; decide +kernel
    rw [ha]
    exact (canonical23543 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1551 + difference 2 1) (sourceB1551 + difference 1 2) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA1551 + difference 2 1) (sourceB1551 + difference 1 2) sourceC1551) = raw23544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23544; decide +kernel
    rw [ha]
    exact (canonical23544 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1551 + difference 2 3) (sourceB1551 + difference 3 2) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA1551 + difference 2 3) (sourceB1551 + difference 3 2) sourceC1551) = raw23545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23545; decide +kernel
    rw [ha]
    exact (canonical23545 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1551 + difference 2 4) (sourceB1551 + difference 4 2) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1551 + difference 2 4) (sourceB1551 + difference 4 2) sourceC1551) = raw21670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw21670; decide +kernel
    rw [ha]
    exact (canonical21670 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1551 + difference 2 5) (sourceB1551 + difference 5 2) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1551 + difference 2 5) (sourceB1551 + difference 5 2) sourceC1551) = raw23546 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23546; decide +kernel
    rw [ha]
    exact (canonical23546 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1551 + difference 3 0) (sourceB1551 + difference 0 3) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA1551 + difference 3 0) (sourceB1551 + difference 0 3) sourceC1551) = raw23547 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23547; decide +kernel
    rw [ha]
    exact (canonical23547 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1551 + difference 3 1) (sourceB1551 + difference 1 3) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA1551 + difference 3 1) (sourceB1551 + difference 1 3) sourceC1551) = raw23548 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23548; decide +kernel
    rw [ha]
    exact (canonical23548 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1551 + difference 3 2) (sourceB1551 + difference 2 3) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1675) := by
    have ha : (tripleCharges (sourceA1551 + difference 3 2) (sourceB1551 + difference 2 3) sourceC1551) = raw23549 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23549; decide +kernel
    rw [ha]
    exact (canonical23549 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1551 + difference 3 4) (sourceB1551 + difference 4 3) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1551 + difference 3 4) (sourceB1551 + difference 4 3) sourceC1551) = raw21675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw21675; decide +kernel
    rw [ha]
    exact (canonical21675 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1551 + difference 3 5) (sourceB1551 + difference 5 3) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1727) := by
    have ha : (tripleCharges (sourceA1551 + difference 3 5) (sourceB1551 + difference 5 3) sourceC1551) = raw23550 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23550; decide +kernel
    rw [ha]
    exact (canonical23550 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1551 + difference 4 0) (sourceB1551 + difference 0 4) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1538) := by
    have ha : (tripleCharges (sourceA1551 + difference 4 0) (sourceB1551 + difference 0 4) sourceC1551) = raw23551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23551; decide +kernel
    rw [ha]
    exact (canonical23551 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1551 + difference 4 1) (sourceB1551 + difference 1 4) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA1551 + difference 4 1) (sourceB1551 + difference 1 4) sourceC1551) = raw23552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23552; decide +kernel
    rw [ha]
    exact (canonical23552 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1551 + difference 4 2) (sourceB1551 + difference 2 4) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA1551 + difference 4 2) (sourceB1551 + difference 2 4) sourceC1551) = raw23553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23553; decide +kernel
    rw [ha]
    exact (canonical23553 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1551 + difference 4 3) (sourceB1551 + difference 3 4) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA1551 + difference 4 3) (sourceB1551 + difference 3 4) sourceC1551) = raw23554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23554; decide +kernel
    rw [ha]
    exact (canonical23554 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1551 + difference 4 5) (sourceB1551 + difference 5 4) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1754) := by
    have ha : (tripleCharges (sourceA1551 + difference 4 5) (sourceB1551 + difference 5 4) sourceC1551) = raw23555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23555; decide +kernel
    rw [ha]
    exact (canonical23555 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1551 + difference 5 0) (sourceB1551 + difference 0 5) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1539) := by
    have ha : (tripleCharges (sourceA1551 + difference 5 0) (sourceB1551 + difference 0 5) sourceC1551) = raw21676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw21676; decide +kernel
    rw [ha]
    exact (canonical21676 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1551 + difference 5 1) (sourceB1551 + difference 1 5) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA1551 + difference 5 1) (sourceB1551 + difference 1 5) sourceC1551) = raw21677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw21677; decide +kernel
    rw [ha]
    exact (canonical21677 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1551 + difference 5 2) (sourceB1551 + difference 2 5) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA1551 + difference 5 2) (sourceB1551 + difference 2 5) sourceC1551) = raw21678 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw21678; decide +kernel
    rw [ha]
    exact (canonical21678 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1551 + difference 5 3) (sourceB1551 + difference 3 5) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA1551 + difference 5 3) (sourceB1551 + difference 3 5) sourceC1551) = raw21679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw21679; decide +kernel
    rw [ha]
    exact (canonical21679 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1551 + difference 5 4) (sourceB1551 + difference 4 5) sourceC1551) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA1551 + difference 5 4) (sourceB1551 + difference 4 5) sourceC1551) = raw23556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1551 sourceB1551 sourceC1551 difference raw23556; decide +kernel
    rw [ha]
    exact (canonical23556 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1551 sourceB1551 sourceC1551
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1551, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1552 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1552 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceC1552 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceForm1552 : Integer.Sparse Master := [(Sum.inr 608, 3), (Sum.inr 619, 1), (Sum.inr 620, 1), (Sum.inr 1095, 1), (Sum.inr 4084, -1)]

theorem sourceEq1552 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1552 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1552 + difference 0 0) (sourceB1552 + difference 0 0) sourceC1552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1095) := by
    have ha : (tripleCharges (sourceA1552 + difference 0 0) (sourceB1552 + difference 0 0) sourceC1552) = raw23557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1552 sourceB1552 sourceC1552 difference raw23557; decide +kernel
    rw [ha]
    exact (canonical23557 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1552 + difference 1 0) (sourceB1552 + difference 0 1) sourceC1552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 608) := by
    have ha : (tripleCharges (sourceA1552 + difference 1 0) (sourceB1552 + difference 0 1) sourceC1552) = raw23558 := by
      apply Matrix.ext; unfold tripleCharges sourceA1552 sourceB1552 sourceC1552 difference raw23558; decide +kernel
    rw [ha]
    exact (canonical23558 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1552 + difference 2 0) (sourceB1552 + difference 0 2) sourceC1552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 608) := by
    have ha : (tripleCharges (sourceA1552 + difference 2 0) (sourceB1552 + difference 0 2) sourceC1552) = raw23559 := by
      apply Matrix.ext; unfold tripleCharges sourceA1552 sourceB1552 sourceC1552 difference raw23559; decide +kernel
    rw [ha]
    exact (canonical23559 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1552 + difference 3 0) (sourceB1552 + difference 0 3) sourceC1552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 608) := by
    have ha : (tripleCharges (sourceA1552 + difference 3 0) (sourceB1552 + difference 0 3) sourceC1552) = raw23560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1552 sourceB1552 sourceC1552 difference raw23560; decide +kernel
    rw [ha]
    exact (canonical23560 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1552 + difference 4 0) (sourceB1552 + difference 0 4) sourceC1552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 619) := by
    have ha : (tripleCharges (sourceA1552 + difference 4 0) (sourceB1552 + difference 0 4) sourceC1552) = raw23561 := by
      apply Matrix.ext; unfold tripleCharges sourceA1552 sourceB1552 sourceC1552 difference raw23561; decide +kernel
    rw [ha]
    exact (canonical23561 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1552 + difference 5 0) (sourceB1552 + difference 0 5) sourceC1552) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 620) := by
    have ha : (tripleCharges (sourceA1552 + difference 5 0) (sourceB1552 + difference 0 5) sourceC1552) = raw23562 := by
      apply Matrix.ext; unfold tripleCharges sourceA1552 sourceB1552 sourceC1552 difference raw23562; decide +kernel
    rw [ha]
    exact (canonical23562 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1552 + sourceB1552) sourceC1552) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1552 + sourceB1552) sourceC1552) = raw19413 := by
      apply Matrix.ext; unfold doubleCharges sourceA1552 sourceB1552 sourceC1552 raw19413; decide +kernel
    rw [ha]
    exact (canonical19413 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1552 sourceB1552 sourceC1552
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1552, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1553 : Charge := ![1, 0, 0, 0, 0, -1]
def sourceB1553 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC1553 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1553 : Integer.Sparse Master := [(Sum.inr 4071, 1), (Sum.inr 4273, 3), (Sum.inr 4284, 1), (Sum.inr 4404, 6), (Sum.inr 4431, 3), (Sum.inr 4432, 3), (Sum.inr 4466, 3), (Sum.inr 4467, 3), (Sum.inr 4510, 1), (Sum.inr 4511, 1), (Sum.inr 4612, 3), (Sum.inr 4627, 1), (Sum.inr 4628, 1)]

theorem sourceEq1553 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1553 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1553 + difference 0 1) (sourceB1553 + difference 1 0) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1553 + difference 0 1) (sourceB1553 + difference 1 0) sourceC1553) = raw22624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw22624; decide +kernel
    rw [ha]
    exact (canonical22624 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1553 + difference 0 2) (sourceB1553 + difference 2 0) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1553 + difference 0 2) (sourceB1553 + difference 2 0) sourceC1553) = raw22625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw22625; decide +kernel
    rw [ha]
    exact (canonical22625 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1553 + difference 0 3) (sourceB1553 + difference 3 0) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1553 + difference 0 3) (sourceB1553 + difference 3 0) sourceC1553) = raw22626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw22626; decide +kernel
    rw [ha]
    exact (canonical22626 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1553 + difference 0 4) (sourceB1553 + difference 4 0) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4628) := by
    have ha : (tripleCharges (sourceA1553 + difference 0 4) (sourceB1553 + difference 4 0) sourceC1553) = raw22530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw22530; decide +kernel
    rw [ha]
    exact (canonical22530 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1553 + difference 0 5) (sourceB1553 + difference 5 0) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4627) := by
    have ha : (tripleCharges (sourceA1553 + difference 0 5) (sourceB1553 + difference 5 0) sourceC1553) = raw22627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw22627; decide +kernel
    rw [ha]
    exact (canonical22627 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1553 + difference 1 0) (sourceB1553 + difference 0 1) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1553 + difference 1 0) (sourceB1553 + difference 0 1) sourceC1553) = raw23097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw23097; decide +kernel
    rw [ha]
    exact (canonical23097 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1553 + difference 1 2) (sourceB1553 + difference 2 1) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1553 + difference 1 2) (sourceB1553 + difference 2 1) sourceC1553) = raw23098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw23098; decide +kernel
    rw [ha]
    exact (canonical23098 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1553 + difference 1 3) (sourceB1553 + difference 3 1) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1553 + difference 1 3) (sourceB1553 + difference 3 1) sourceC1553) = raw22775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw22775; decide +kernel
    rw [ha]
    exact (canonical22775 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1553 + difference 1 4) (sourceB1553 + difference 4 1) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1553 + difference 1 4) (sourceB1553 + difference 4 1) sourceC1553) = raw22611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw22611; decide +kernel
    rw [ha]
    exact (canonical22611 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1553 + difference 1 5) (sourceB1553 + difference 5 1) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1553 + difference 1 5) (sourceB1553 + difference 5 1) sourceC1553) = raw23270 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw23270; decide +kernel
    rw [ha]
    exact (canonical23270 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1553 + difference 2 0) (sourceB1553 + difference 0 2) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1553 + difference 2 0) (sourceB1553 + difference 0 2) sourceC1553) = raw23563 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw23563; decide +kernel
    rw [ha]
    exact (canonical23563 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1553 + difference 2 1) (sourceB1553 + difference 1 2) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1553 + difference 2 1) (sourceB1553 + difference 1 2) sourceC1553) = raw23564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw23564; decide +kernel
    rw [ha]
    exact (canonical23564 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1553 + difference 2 3) (sourceB1553 + difference 3 2) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1553 + difference 2 3) (sourceB1553 + difference 3 2) sourceC1553) = raw22779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw22779; decide +kernel
    rw [ha]
    exact (canonical22779 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1553 + difference 2 4) (sourceB1553 + difference 4 2) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1553 + difference 2 4) (sourceB1553 + difference 4 2) sourceC1553) = raw22615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw22615; decide +kernel
    rw [ha]
    exact (canonical22615 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1553 + difference 2 5) (sourceB1553 + difference 5 2) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1553 + difference 2 5) (sourceB1553 + difference 5 2) sourceC1553) = raw23083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw23083; decide +kernel
    rw [ha]
    exact (canonical23083 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1553 + difference 3 0) (sourceB1553 + difference 0 3) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4273) := by
    have ha : (tripleCharges (sourceA1553 + difference 3 0) (sourceB1553 + difference 0 3) sourceC1553) = raw23565 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw23565; decide +kernel
    rw [ha]
    exact (canonical23565 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1553 + difference 3 1) (sourceB1553 + difference 1 3) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1553 + difference 3 1) (sourceB1553 + difference 1 3) sourceC1553) = raw23566 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw23566; decide +kernel
    rw [ha]
    exact (canonical23566 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1553 + difference 3 2) (sourceB1553 + difference 2 3) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1553 + difference 3 2) (sourceB1553 + difference 2 3) sourceC1553) = raw23567 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw23567; decide +kernel
    rw [ha]
    exact (canonical23567 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1553 + difference 3 4) (sourceB1553 + difference 4 3) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4467) := by
    have ha : (tripleCharges (sourceA1553 + difference 3 4) (sourceB1553 + difference 4 3) sourceC1553) = raw22619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw22619; decide +kernel
    rw [ha]
    exact (canonical22619 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1553 + difference 3 5) (sourceB1553 + difference 5 3) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA1553 + difference 3 5) (sourceB1553 + difference 5 3) sourceC1553) = raw23088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw23088; decide +kernel
    rw [ha]
    exact (canonical23088 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1553 + difference 4 0) (sourceB1553 + difference 0 4) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4284) := by
    have ha : (tripleCharges (sourceA1553 + difference 4 0) (sourceB1553 + difference 0 4) sourceC1553) = raw23477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw23477; decide +kernel
    rw [ha]
    exact (canonical23477 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1553 + difference 4 1) (sourceB1553 + difference 1 4) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA1553 + difference 4 1) (sourceB1553 + difference 1 4) sourceC1553) = raw23478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw23478; decide +kernel
    rw [ha]
    exact (canonical23478 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1553 + difference 4 2) (sourceB1553 + difference 2 4) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA1553 + difference 4 2) (sourceB1553 + difference 2 4) sourceC1553) = raw23479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw23479; decide +kernel
    rw [ha]
    exact (canonical23479 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1553 + difference 4 3) (sourceB1553 + difference 3 4) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA1553 + difference 4 3) (sourceB1553 + difference 3 4) sourceC1553) = raw22783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw22783; decide +kernel
    rw [ha]
    exact (canonical22783 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1553 + difference 4 5) (sourceB1553 + difference 5 4) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA1553 + difference 4 5) (sourceB1553 + difference 5 4) sourceC1553) = raw23093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw23093; decide +kernel
    rw [ha]
    exact (canonical23093 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1553 + difference 5 0) (sourceB1553 + difference 0 5) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (tripleCharges (sourceA1553 + difference 5 0) (sourceB1553 + difference 0 5) sourceC1553) = raw23568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw23568; decide +kernel
    rw [ha]
    exact (canonical23568 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1553 + difference 5 1) (sourceB1553 + difference 1 5) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4432) := by
    have ha : (tripleCharges (sourceA1553 + difference 5 1) (sourceB1553 + difference 1 5) sourceC1553) = raw23569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw23569; decide +kernel
    rw [ha]
    exact (canonical23569 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1553 + difference 5 2) (sourceB1553 + difference 2 5) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4432) := by
    have ha : (tripleCharges (sourceA1553 + difference 5 2) (sourceB1553 + difference 2 5) sourceC1553) = raw23570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw23570; decide +kernel
    rw [ha]
    exact (canonical23570 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1553 + difference 5 3) (sourceB1553 + difference 3 5) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4432) := by
    have ha : (tripleCharges (sourceA1553 + difference 5 3) (sourceB1553 + difference 3 5) sourceC1553) = raw22788 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw22788; decide +kernel
    rw [ha]
    exact (canonical22788 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1553 + difference 5 4) (sourceB1553 + difference 4 5) sourceC1553) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1553 + difference 5 4) (sourceB1553 + difference 4 5) sourceC1553) = raw22526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1553 sourceB1553 sourceC1553 difference raw22526; decide +kernel
    rw [ha]
    exact (canonical22526 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1553 sourceB1553 sourceC1553
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1553, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1554 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1554 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC1554 : Charge := ![3, 0, 0, 1, -3, -1]
def sourceForm1554 : Integer.Sparse Master := [(Sum.inr 1012, 1), (Sum.inr 1953, 1), (Sum.inr 2006, 2), (Sum.inr 2228, 1), (Sum.inr 2230, 1), (Sum.inr 4081, -1)]

theorem sourceEq1554 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1554 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1554 + difference 0 0) (sourceB1554 + difference 0 0) sourceC1554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1012) := by
    have ha : (tripleCharges (sourceA1554 + difference 0 0) (sourceB1554 + difference 0 0) sourceC1554) = raw21894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1554 sourceB1554 sourceC1554 difference raw21894; decide +kernel
    rw [ha]
    exact (canonical21894 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1554 + difference 0 1) (sourceB1554 + difference 1 0) sourceC1554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2006) := by
    have ha : (tripleCharges (sourceA1554 + difference 0 1) (sourceB1554 + difference 1 0) sourceC1554) = raw23571 := by
      apply Matrix.ext; unfold tripleCharges sourceA1554 sourceB1554 sourceC1554 difference raw23571; decide +kernel
    rw [ha]
    exact (canonical23571 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1554 + difference 0 2) (sourceB1554 + difference 2 0) sourceC1554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2006) := by
    have ha : (tripleCharges (sourceA1554 + difference 0 2) (sourceB1554 + difference 2 0) sourceC1554) = raw23572 := by
      apply Matrix.ext; unfold tripleCharges sourceA1554 sourceB1554 sourceC1554 difference raw23572; decide +kernel
    rw [ha]
    exact (canonical23572 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1554 + difference 0 3) (sourceB1554 + difference 3 0) sourceC1554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1953) := by
    have ha : (tripleCharges (sourceA1554 + difference 0 3) (sourceB1554 + difference 3 0) sourceC1554) = raw23573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1554 sourceB1554 sourceC1554 difference raw23573; decide +kernel
    rw [ha]
    exact (canonical23573 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1554 + difference 0 4) (sourceB1554 + difference 4 0) sourceC1554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1554 + difference 0 4) (sourceB1554 + difference 4 0) sourceC1554) = raw21889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1554 sourceB1554 sourceC1554 difference raw21889; decide +kernel
    rw [ha]
    exact (canonical21889 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1554 + difference 0 5) (sourceB1554 + difference 5 0) sourceC1554) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2228) := by
    have ha : (tripleCharges (sourceA1554 + difference 0 5) (sourceB1554 + difference 5 0) sourceC1554) = raw23574 := by
      apply Matrix.ext; unfold tripleCharges sourceA1554 sourceB1554 sourceC1554 difference raw23574; decide +kernel
    rw [ha]
    exact (canonical23574 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1554 + sourceB1554) sourceC1554) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1554 + sourceB1554) sourceC1554) = raw21890 := by
      apply Matrix.ext; unfold doubleCharges sourceA1554 sourceB1554 sourceC1554 raw21890; decide +kernel
    rw [ha]
    exact (canonical21890 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1554 sourceB1554 sourceC1554
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1554, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1555 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1555 : Charge := ![1, 0, 0, -1, 1, -1]
def sourceC1555 : Charge := ![3, 0, 0, 1, -3, -1]
def sourceForm1555 : Integer.Sparse Master := [(Sum.inr 882, 2), (Sum.inr 895, 1), (Sum.inr 897, 1), (Sum.inr 1012, 1), (Sum.inr 1953, 1), (Sum.inr 4081, -1)]

theorem sourceEq1555 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1555 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1555 + difference 0 3) (sourceB1555 + difference 3 0) sourceC1555) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1953) := by
    have ha : (tripleCharges (sourceA1555 + difference 0 3) (sourceB1555 + difference 3 0) sourceC1555) = raw23573 := by
      apply Matrix.ext; unfold tripleCharges sourceA1555 sourceB1555 sourceC1555 difference raw23573; decide +kernel
    rw [ha]
    exact (canonical23573 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1555 + difference 1 3) (sourceB1555 + difference 3 1) sourceC1555) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 882) := by
    have ha : (tripleCharges (sourceA1555 + difference 1 3) (sourceB1555 + difference 3 1) sourceC1555) = raw23575 := by
      apply Matrix.ext; unfold tripleCharges sourceA1555 sourceB1555 sourceC1555 difference raw23575; decide +kernel
    rw [ha]
    exact (canonical23575 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1555 + difference 2 3) (sourceB1555 + difference 3 2) sourceC1555) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 882) := by
    have ha : (tripleCharges (sourceA1555 + difference 2 3) (sourceB1555 + difference 3 2) sourceC1555) = raw23576 := by
      apply Matrix.ext; unfold tripleCharges sourceA1555 sourceB1555 sourceC1555 difference raw23576; decide +kernel
    rw [ha]
    exact (canonical23576 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1555 + difference 3 3) (sourceB1555 + difference 3 3) sourceC1555) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1012) := by
    have ha : (tripleCharges (sourceA1555 + difference 3 3) (sourceB1555 + difference 3 3) sourceC1555) = raw21894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1555 sourceB1555 sourceC1555 difference raw21894; decide +kernel
    rw [ha]
    exact (canonical21894 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1555 + difference 4 3) (sourceB1555 + difference 3 4) sourceC1555) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 895) := by
    have ha : (tripleCharges (sourceA1555 + difference 4 3) (sourceB1555 + difference 3 4) sourceC1555) = raw23577 := by
      apply Matrix.ext; unfold tripleCharges sourceA1555 sourceB1555 sourceC1555 difference raw23577; decide +kernel
    rw [ha]
    exact (canonical23577 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1555 + difference 5 3) (sourceB1555 + difference 3 5) sourceC1555) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 897) := by
    have ha : (tripleCharges (sourceA1555 + difference 5 3) (sourceB1555 + difference 3 5) sourceC1555) = raw23578 := by
      apply Matrix.ext; unfold tripleCharges sourceA1555 sourceB1555 sourceC1555 difference raw23578; decide +kernel
    rw [ha]
    exact (canonical23578 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1555 + sourceB1555) sourceC1555) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1555 + sourceB1555) sourceC1555) = raw21890 := by
      apply Matrix.ext; unfold doubleCharges sourceA1555 sourceB1555 sourceC1555 raw21890; decide +kernel
    rw [ha]
    exact (canonical21890 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1555 sourceB1555 sourceC1555
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1555, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1556 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1556 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1556 : Charge := ![3, 0, 0, 1, -2, -2]
def sourceForm1556 : Integer.Sparse Master := [(Sum.inr 4082, 1), (Sum.inr 4141, 2), (Sum.inr 4148, 2), (Sum.inr 4167, 1), (Sum.inr 4305, 2), (Sum.inr 4318, 2), (Sum.inr 4321, 2), (Sum.inr 4325, 4), (Sum.inr 4339, 2), (Sum.inr 4419, 4), (Sum.inr 4428, 2), (Sum.inr 4491, 2), (Sum.inr 4790, 2), (Sum.inr 4846, 2)]

theorem sourceEq1556 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1556 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1556 + difference 0 1) (sourceB1556 + difference 1 0) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4790) := by
    have ha : (tripleCharges (sourceA1556 + difference 0 1) (sourceB1556 + difference 1 0) sourceC1556) = raw23579 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23579; decide +kernel
    rw [ha]
    exact (canonical23579 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1556 + difference 0 2) (sourceB1556 + difference 2 0) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4790) := by
    have ha : (tripleCharges (sourceA1556 + difference 0 2) (sourceB1556 + difference 2 0) sourceC1556) = raw23580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23580; decide +kernel
    rw [ha]
    exact (canonical23580 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1556 + difference 0 3) (sourceB1556 + difference 3 0) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA1556 + difference 0 3) (sourceB1556 + difference 3 0) sourceC1556) = raw23581 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23581; decide +kernel
    rw [ha]
    exact (canonical23581 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1556 + difference 0 4) (sourceB1556 + difference 4 0) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA1556 + difference 0 4) (sourceB1556 + difference 4 0) sourceC1556) = raw23582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23582; decide +kernel
    rw [ha]
    exact (canonical23582 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1556 + difference 0 5) (sourceB1556 + difference 5 0) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4846) := by
    have ha : (tripleCharges (sourceA1556 + difference 0 5) (sourceB1556 + difference 5 0) sourceC1556) = raw23583 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23583; decide +kernel
    rw [ha]
    exact (canonical23583 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1556 + difference 1 0) (sourceB1556 + difference 0 1) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4141) := by
    have ha : (tripleCharges (sourceA1556 + difference 1 0) (sourceB1556 + difference 0 1) sourceC1556) = raw23584 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23584; decide +kernel
    rw [ha]
    exact (canonical23584 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1556 + difference 1 2) (sourceB1556 + difference 2 1) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4321) := by
    have ha : (tripleCharges (sourceA1556 + difference 1 2) (sourceB1556 + difference 2 1) sourceC1556) = raw23585 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23585; decide +kernel
    rw [ha]
    exact (canonical23585 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1556 + difference 1 3) (sourceB1556 + difference 3 1) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4305) := by
    have ha : (tripleCharges (sourceA1556 + difference 1 3) (sourceB1556 + difference 3 1) sourceC1556) = raw23586 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23586; decide +kernel
    rw [ha]
    exact (canonical23586 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1556 + difference 1 4) (sourceB1556 + difference 4 1) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1556 + difference 1 4) (sourceB1556 + difference 4 1) sourceC1556) = raw23587 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23587; decide +kernel
    rw [ha]
    exact (canonical23587 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1556 + difference 1 5) (sourceB1556 + difference 5 1) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1556 + difference 1 5) (sourceB1556 + difference 5 1) sourceC1556) = raw23588 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23588; decide +kernel
    rw [ha]
    exact (canonical23588 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1556 + difference 2 0) (sourceB1556 + difference 0 2) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4141) := by
    have ha : (tripleCharges (sourceA1556 + difference 2 0) (sourceB1556 + difference 0 2) sourceC1556) = raw23589 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23589; decide +kernel
    rw [ha]
    exact (canonical23589 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1556 + difference 2 1) (sourceB1556 + difference 1 2) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4321) := by
    have ha : (tripleCharges (sourceA1556 + difference 2 1) (sourceB1556 + difference 1 2) sourceC1556) = raw23590 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23590; decide +kernel
    rw [ha]
    exact (canonical23590 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1556 + difference 2 3) (sourceB1556 + difference 3 2) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4305) := by
    have ha : (tripleCharges (sourceA1556 + difference 2 3) (sourceB1556 + difference 3 2) sourceC1556) = raw23591 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23591; decide +kernel
    rw [ha]
    exact (canonical23591 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1556 + difference 2 4) (sourceB1556 + difference 4 2) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1556 + difference 2 4) (sourceB1556 + difference 4 2) sourceC1556) = raw23592 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23592; decide +kernel
    rw [ha]
    exact (canonical23592 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1556 + difference 2 5) (sourceB1556 + difference 5 2) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4419) := by
    have ha : (tripleCharges (sourceA1556 + difference 2 5) (sourceB1556 + difference 5 2) sourceC1556) = raw23593 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23593; decide +kernel
    rw [ha]
    exact (canonical23593 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1556 + difference 3 0) (sourceB1556 + difference 0 3) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4167) := by
    have ha : (tripleCharges (sourceA1556 + difference 3 0) (sourceB1556 + difference 0 3) sourceC1556) = raw23594 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23594; decide +kernel
    rw [ha]
    exact (canonical23594 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1556 + difference 3 1) (sourceB1556 + difference 1 3) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4339) := by
    have ha : (tripleCharges (sourceA1556 + difference 3 1) (sourceB1556 + difference 1 3) sourceC1556) = raw23595 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23595; decide +kernel
    rw [ha]
    exact (canonical23595 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1556 + difference 3 2) (sourceB1556 + difference 2 3) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4339) := by
    have ha : (tripleCharges (sourceA1556 + difference 3 2) (sourceB1556 + difference 2 3) sourceC1556) = raw23596 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23596; decide +kernel
    rw [ha]
    exact (canonical23596 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1556 + difference 3 4) (sourceB1556 + difference 4 3) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4491) := by
    have ha : (tripleCharges (sourceA1556 + difference 3 4) (sourceB1556 + difference 4 3) sourceC1556) = raw23597 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23597; decide +kernel
    rw [ha]
    exact (canonical23597 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1556 + difference 3 5) (sourceB1556 + difference 5 3) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4491) := by
    have ha : (tripleCharges (sourceA1556 + difference 3 5) (sourceB1556 + difference 5 3) sourceC1556) = raw23598 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23598; decide +kernel
    rw [ha]
    exact (canonical23598 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1556 + difference 4 0) (sourceB1556 + difference 0 4) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4148) := by
    have ha : (tripleCharges (sourceA1556 + difference 4 0) (sourceB1556 + difference 0 4) sourceC1556) = raw23599 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23599; decide +kernel
    rw [ha]
    exact (canonical23599 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1556 + difference 4 1) (sourceB1556 + difference 1 4) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4325) := by
    have ha : (tripleCharges (sourceA1556 + difference 4 1) (sourceB1556 + difference 1 4) sourceC1556) = raw23600 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23600; decide +kernel
    rw [ha]
    exact (canonical23600 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1556 + difference 4 2) (sourceB1556 + difference 2 4) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4325) := by
    have ha : (tripleCharges (sourceA1556 + difference 4 2) (sourceB1556 + difference 2 4) sourceC1556) = raw23601 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23601; decide +kernel
    rw [ha]
    exact (canonical23601 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1556 + difference 4 3) (sourceB1556 + difference 3 4) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4318) := by
    have ha : (tripleCharges (sourceA1556 + difference 4 3) (sourceB1556 + difference 3 4) sourceC1556) = raw23602 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23602; decide +kernel
    rw [ha]
    exact (canonical23602 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1556 + difference 4 5) (sourceB1556 + difference 5 4) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA1556 + difference 4 5) (sourceB1556 + difference 5 4) sourceC1556) = raw23603 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23603; decide +kernel
    rw [ha]
    exact (canonical23603 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1556 + difference 5 0) (sourceB1556 + difference 0 5) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4148) := by
    have ha : (tripleCharges (sourceA1556 + difference 5 0) (sourceB1556 + difference 0 5) sourceC1556) = raw23604 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23604; decide +kernel
    rw [ha]
    exact (canonical23604 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1556 + difference 5 1) (sourceB1556 + difference 1 5) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4325) := by
    have ha : (tripleCharges (sourceA1556 + difference 5 1) (sourceB1556 + difference 1 5) sourceC1556) = raw23605 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23605; decide +kernel
    rw [ha]
    exact (canonical23605 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1556 + difference 5 2) (sourceB1556 + difference 2 5) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4325) := by
    have ha : (tripleCharges (sourceA1556 + difference 5 2) (sourceB1556 + difference 2 5) sourceC1556) = raw23606 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23606; decide +kernel
    rw [ha]
    exact (canonical23606 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1556 + difference 5 3) (sourceB1556 + difference 3 5) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4318) := by
    have ha : (tripleCharges (sourceA1556 + difference 5 3) (sourceB1556 + difference 3 5) sourceC1556) = raw23607 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23607; decide +kernel
    rw [ha]
    exact (canonical23607 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1556 + difference 5 4) (sourceB1556 + difference 4 5) sourceC1556) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4428) := by
    have ha : (tripleCharges (sourceA1556 + difference 5 4) (sourceB1556 + difference 4 5) sourceC1556) = raw23608 := by
      apply Matrix.ext; unfold tripleCharges sourceA1556 sourceB1556 sourceC1556 difference raw23608; decide +kernel
    rw [ha]
    exact (canonical23608 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1556 sourceB1556 sourceC1556
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1556, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1557 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1557 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1557 : Charge := ![3, 0, 0, 1, -2, -2]
def sourceForm1557 : Integer.Sparse Master := [(Sum.inr 1490, 2), (Sum.inr 1496, 2), (Sum.inr 1500, 1), (Sum.inr 1560, 2), (Sum.inr 1579, 2), (Sum.inr 1587, 2), (Sum.inr 1591, 4), (Sum.inr 1605, 4), (Sum.inr 1630, 2), (Sum.inr 1634, 2), (Sum.inr 1653, 2), (Sum.inr 2007, 2), (Sum.inr 2066, 2), (Sum.inr 4082, 1)]

theorem sourceEq1557 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1557 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1557 + difference 0 1) (sourceB1557 + difference 1 0) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2007) := by
    have ha : (tripleCharges (sourceA1557 + difference 0 1) (sourceB1557 + difference 1 0) sourceC1557) = raw23609 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23609; decide +kernel
    rw [ha]
    exact (canonical23609 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1557 + difference 0 2) (sourceB1557 + difference 2 0) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2007) := by
    have ha : (tripleCharges (sourceA1557 + difference 0 2) (sourceB1557 + difference 2 0) sourceC1557) = raw23610 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23610; decide +kernel
    rw [ha]
    exact (canonical23610 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1557 + difference 0 3) (sourceB1557 + difference 3 0) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (tripleCharges (sourceA1557 + difference 0 3) (sourceB1557 + difference 3 0) sourceC1557) = raw23611 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23611; decide +kernel
    rw [ha]
    exact (canonical23611 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1557 + difference 0 4) (sourceB1557 + difference 4 0) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2066) := by
    have ha : (tripleCharges (sourceA1557 + difference 0 4) (sourceB1557 + difference 4 0) sourceC1557) = raw23612 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23612; decide +kernel
    rw [ha]
    exact (canonical23612 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1557 + difference 0 5) (sourceB1557 + difference 5 0) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2066) := by
    have ha : (tripleCharges (sourceA1557 + difference 0 5) (sourceB1557 + difference 5 0) sourceC1557) = raw23613 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23613; decide +kernel
    rw [ha]
    exact (canonical23613 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1557 + difference 1 0) (sourceB1557 + difference 0 1) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1490) := by
    have ha : (tripleCharges (sourceA1557 + difference 1 0) (sourceB1557 + difference 0 1) sourceC1557) = raw23614 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23614; decide +kernel
    rw [ha]
    exact (canonical23614 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1557 + difference 1 2) (sourceB1557 + difference 2 1) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1587) := by
    have ha : (tripleCharges (sourceA1557 + difference 1 2) (sourceB1557 + difference 2 1) sourceC1557) = raw23615 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23615; decide +kernel
    rw [ha]
    exact (canonical23615 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1557 + difference 1 3) (sourceB1557 + difference 3 1) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1560) := by
    have ha : (tripleCharges (sourceA1557 + difference 1 3) (sourceB1557 + difference 3 1) sourceC1557) = raw23616 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23616; decide +kernel
    rw [ha]
    exact (canonical23616 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1557 + difference 1 4) (sourceB1557 + difference 4 1) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1605) := by
    have ha : (tripleCharges (sourceA1557 + difference 1 4) (sourceB1557 + difference 4 1) sourceC1557) = raw23617 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23617; decide +kernel
    rw [ha]
    exact (canonical23617 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1557 + difference 1 5) (sourceB1557 + difference 5 1) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1605) := by
    have ha : (tripleCharges (sourceA1557 + difference 1 5) (sourceB1557 + difference 5 1) sourceC1557) = raw23618 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23618; decide +kernel
    rw [ha]
    exact (canonical23618 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1557 + difference 2 0) (sourceB1557 + difference 0 2) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1490) := by
    have ha : (tripleCharges (sourceA1557 + difference 2 0) (sourceB1557 + difference 0 2) sourceC1557) = raw23619 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23619; decide +kernel
    rw [ha]
    exact (canonical23619 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1557 + difference 2 1) (sourceB1557 + difference 1 2) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1587) := by
    have ha : (tripleCharges (sourceA1557 + difference 2 1) (sourceB1557 + difference 1 2) sourceC1557) = raw23620 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23620; decide +kernel
    rw [ha]
    exact (canonical23620 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1557 + difference 2 3) (sourceB1557 + difference 3 2) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1560) := by
    have ha : (tripleCharges (sourceA1557 + difference 2 3) (sourceB1557 + difference 3 2) sourceC1557) = raw23621 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23621; decide +kernel
    rw [ha]
    exact (canonical23621 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1557 + difference 2 4) (sourceB1557 + difference 4 2) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1605) := by
    have ha : (tripleCharges (sourceA1557 + difference 2 4) (sourceB1557 + difference 4 2) sourceC1557) = raw23622 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23622; decide +kernel
    rw [ha]
    exact (canonical23622 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1557 + difference 2 5) (sourceB1557 + difference 5 2) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1605) := by
    have ha : (tripleCharges (sourceA1557 + difference 2 5) (sourceB1557 + difference 5 2) sourceC1557) = raw23623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23623; decide +kernel
    rw [ha]
    exact (canonical23623 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1557 + difference 3 0) (sourceB1557 + difference 0 3) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1500) := by
    have ha : (tripleCharges (sourceA1557 + difference 3 0) (sourceB1557 + difference 0 3) sourceC1557) = raw23624 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23624; decide +kernel
    rw [ha]
    exact (canonical23624 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1557 + difference 3 1) (sourceB1557 + difference 1 3) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1634) := by
    have ha : (tripleCharges (sourceA1557 + difference 3 1) (sourceB1557 + difference 1 3) sourceC1557) = raw23625 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23625; decide +kernel
    rw [ha]
    exact (canonical23625 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1557 + difference 3 2) (sourceB1557 + difference 2 3) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1634) := by
    have ha : (tripleCharges (sourceA1557 + difference 3 2) (sourceB1557 + difference 2 3) sourceC1557) = raw23626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23626; decide +kernel
    rw [ha]
    exact (canonical23626 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1557 + difference 3 4) (sourceB1557 + difference 4 3) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1653) := by
    have ha : (tripleCharges (sourceA1557 + difference 3 4) (sourceB1557 + difference 4 3) sourceC1557) = raw23627 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23627; decide +kernel
    rw [ha]
    exact (canonical23627 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1557 + difference 3 5) (sourceB1557 + difference 5 3) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1653) := by
    have ha : (tripleCharges (sourceA1557 + difference 3 5) (sourceB1557 + difference 5 3) sourceC1557) = raw23628 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23628; decide +kernel
    rw [ha]
    exact (canonical23628 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1557 + difference 4 0) (sourceB1557 + difference 0 4) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1496) := by
    have ha : (tripleCharges (sourceA1557 + difference 4 0) (sourceB1557 + difference 0 4) sourceC1557) = raw23629 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23629; decide +kernel
    rw [ha]
    exact (canonical23629 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1557 + difference 4 1) (sourceB1557 + difference 1 4) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1591) := by
    have ha : (tripleCharges (sourceA1557 + difference 4 1) (sourceB1557 + difference 1 4) sourceC1557) = raw23630 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23630; decide +kernel
    rw [ha]
    exact (canonical23630 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1557 + difference 4 2) (sourceB1557 + difference 2 4) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1591) := by
    have ha : (tripleCharges (sourceA1557 + difference 4 2) (sourceB1557 + difference 2 4) sourceC1557) = raw23631 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23631; decide +kernel
    rw [ha]
    exact (canonical23631 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1557 + difference 4 3) (sourceB1557 + difference 3 4) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1579) := by
    have ha : (tripleCharges (sourceA1557 + difference 4 3) (sourceB1557 + difference 3 4) sourceC1557) = raw23632 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23632; decide +kernel
    rw [ha]
    exact (canonical23632 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1557 + difference 4 5) (sourceB1557 + difference 5 4) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1630) := by
    have ha : (tripleCharges (sourceA1557 + difference 4 5) (sourceB1557 + difference 5 4) sourceC1557) = raw23633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23633; decide +kernel
    rw [ha]
    exact (canonical23633 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1557 + difference 5 0) (sourceB1557 + difference 0 5) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1496) := by
    have ha : (tripleCharges (sourceA1557 + difference 5 0) (sourceB1557 + difference 0 5) sourceC1557) = raw23634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23634; decide +kernel
    rw [ha]
    exact (canonical23634 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1557 + difference 5 1) (sourceB1557 + difference 1 5) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1591) := by
    have ha : (tripleCharges (sourceA1557 + difference 5 1) (sourceB1557 + difference 1 5) sourceC1557) = raw23635 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23635; decide +kernel
    rw [ha]
    exact (canonical23635 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1557 + difference 5 2) (sourceB1557 + difference 2 5) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1591) := by
    have ha : (tripleCharges (sourceA1557 + difference 5 2) (sourceB1557 + difference 2 5) sourceC1557) = raw23636 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23636; decide +kernel
    rw [ha]
    exact (canonical23636 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1557 + difference 5 3) (sourceB1557 + difference 3 5) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1579) := by
    have ha : (tripleCharges (sourceA1557 + difference 5 3) (sourceB1557 + difference 3 5) sourceC1557) = raw23637 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23637; decide +kernel
    rw [ha]
    exact (canonical23637 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1557 + difference 5 4) (sourceB1557 + difference 4 5) sourceC1557) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1630) := by
    have ha : (tripleCharges (sourceA1557 + difference 5 4) (sourceB1557 + difference 4 5) sourceC1557) = raw23638 := by
      apply Matrix.ext; unfold tripleCharges sourceA1557 sourceB1557 sourceC1557 difference raw23638; decide +kernel
    rw [ha]
    exact (canonical23638 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1557 sourceB1557 sourceC1557
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1557, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1558 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1558 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1558 : Charge := ![3, 0, 0, 1, -2, -2]
def sourceForm1558 : Integer.Sparse Master := [(Sum.inr 569, 2), (Sum.inr 576, 2), (Sum.inr 595, 1), (Sum.inr 1013, 1), (Sum.inr 4082, -1)]

theorem sourceEq1558 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1558 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1558 + difference 0 0) (sourceB1558 + difference 0 0) sourceC1558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1013) := by
    have ha : (tripleCharges (sourceA1558 + difference 0 0) (sourceB1558 + difference 0 0) sourceC1558) = raw21909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1558 sourceB1558 sourceC1558 difference raw21909; decide +kernel
    rw [ha]
    exact (canonical21909 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1558 + difference 1 0) (sourceB1558 + difference 0 1) sourceC1558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 569) := by
    have ha : (tripleCharges (sourceA1558 + difference 1 0) (sourceB1558 + difference 0 1) sourceC1558) = raw23639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1558 sourceB1558 sourceC1558 difference raw23639; decide +kernel
    rw [ha]
    exact (canonical23639 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1558 + difference 2 0) (sourceB1558 + difference 0 2) sourceC1558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 569) := by
    have ha : (tripleCharges (sourceA1558 + difference 2 0) (sourceB1558 + difference 0 2) sourceC1558) = raw23640 := by
      apply Matrix.ext; unfold tripleCharges sourceA1558 sourceB1558 sourceC1558 difference raw23640; decide +kernel
    rw [ha]
    exact (canonical23640 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1558 + difference 3 0) (sourceB1558 + difference 0 3) sourceC1558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 595) := by
    have ha : (tripleCharges (sourceA1558 + difference 3 0) (sourceB1558 + difference 0 3) sourceC1558) = raw23641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1558 sourceB1558 sourceC1558 difference raw23641; decide +kernel
    rw [ha]
    exact (canonical23641 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1558 + difference 4 0) (sourceB1558 + difference 0 4) sourceC1558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 576) := by
    have ha : (tripleCharges (sourceA1558 + difference 4 0) (sourceB1558 + difference 0 4) sourceC1558) = raw23642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1558 sourceB1558 sourceC1558 difference raw23642; decide +kernel
    rw [ha]
    exact (canonical23642 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1558 + difference 5 0) (sourceB1558 + difference 0 5) sourceC1558) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 576) := by
    have ha : (tripleCharges (sourceA1558 + difference 5 0) (sourceB1558 + difference 0 5) sourceC1558) = raw21906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1558 sourceB1558 sourceC1558 difference raw21906; decide +kernel
    rw [ha]
    exact (canonical21906 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1558 + sourceB1558) sourceC1558) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1558 + sourceB1558) sourceC1558) = raw21901 := by
      apply Matrix.ext; unfold doubleCharges sourceA1558 sourceB1558 sourceC1558 raw21901; decide +kernel
    rw [ha]
    exact (canonical21901 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1558 sourceB1558 sourceC1558
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1558, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1559 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1559 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceC1559 : Charge := ![3, 0, 0, 1, -2, -2]
def sourceForm1559 : Integer.Sparse Master := [(Sum.inr 569, 1), (Sum.inr 883, 1), (Sum.inr 899, 1), (Sum.inr 1000, 2), (Sum.inr 1013, 1), (Sum.inr 4082, -1)]

theorem sourceEq1559 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1559 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1559 + difference 1 0) (sourceB1559 + difference 0 1) sourceC1559) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 569) := by
    have ha : (tripleCharges (sourceA1559 + difference 1 0) (sourceB1559 + difference 0 1) sourceC1559) = raw23639 := by
      apply Matrix.ext; unfold tripleCharges sourceA1559 sourceB1559 sourceC1559 difference raw23639; decide +kernel
    rw [ha]
    exact (canonical23639 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1559 + difference 1 1) (sourceB1559 + difference 1 1) sourceC1559) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1013) := by
    have ha : (tripleCharges (sourceA1559 + difference 1 1) (sourceB1559 + difference 1 1) sourceC1559) = raw21909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1559 sourceB1559 sourceC1559 difference raw21909; decide +kernel
    rw [ha]
    exact (canonical21909 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1559 + difference 1 2) (sourceB1559 + difference 2 1) sourceC1559) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 899) := by
    have ha : (tripleCharges (sourceA1559 + difference 1 2) (sourceB1559 + difference 2 1) sourceC1559) = raw23643 := by
      apply Matrix.ext; unfold tripleCharges sourceA1559 sourceB1559 sourceC1559 difference raw23643; decide +kernel
    rw [ha]
    exact (canonical23643 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1559 + difference 1 3) (sourceB1559 + difference 3 1) sourceC1559) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 883) := by
    have ha : (tripleCharges (sourceA1559 + difference 1 3) (sourceB1559 + difference 3 1) sourceC1559) = raw23644 := by
      apply Matrix.ext; unfold tripleCharges sourceA1559 sourceB1559 sourceC1559 difference raw23644; decide +kernel
    rw [ha]
    exact (canonical23644 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1559 + difference 1 4) (sourceB1559 + difference 4 1) sourceC1559) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1559 + difference 1 4) (sourceB1559 + difference 4 1) sourceC1559) = raw21910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1559 sourceB1559 sourceC1559 difference raw21910; decide +kernel
    rw [ha]
    exact (canonical21910 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1559 + difference 1 5) (sourceB1559 + difference 5 1) sourceC1559) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1000) := by
    have ha : (tripleCharges (sourceA1559 + difference 1 5) (sourceB1559 + difference 5 1) sourceC1559) = raw23645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1559 sourceB1559 sourceC1559 difference raw23645; decide +kernel
    rw [ha]
    exact (canonical23645 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1559 + sourceB1559) sourceC1559) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA1559 + sourceB1559) sourceC1559) = raw21901 := by
      apply Matrix.ext; unfold doubleCharges sourceA1559 sourceB1559 sourceC1559 raw21901; decide +kernel
    rw [ha]
    exact (canonical21901 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1559 sourceB1559 sourceC1559
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1559, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1560 : Charge := ![1, 0, 0, -1, 0, 0]
def sourceB1560 : Charge := ![3, 0, 0, 1, -2, -2]
def sourceC1560 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1560 : Integer.Sparse Master := [(Sum.inr 4071, 1), (Sum.inr 4214, 2), (Sum.inr 4228, 2), (Sum.inr 4378, 2), (Sum.inr 4383, 2), (Sum.inr 4385, 2), (Sum.inr 4389, 4), (Sum.inr 4404, 4), (Sum.inr 4431, 2), (Sum.inr 4432, 2), (Sum.inr 4511, 2), (Sum.inr 4575, 1), (Sum.inr 4586, 2), (Sum.inr 4612, 2)]

theorem sourceEq1560 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1560 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1560 + difference 0 1) (sourceB1560 + difference 1 0) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4586) := by
    have ha : (tripleCharges (sourceA1560 + difference 0 1) (sourceB1560 + difference 1 0) sourceC1560) = raw22789 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw22789; decide +kernel
    rw [ha]
    exact (canonical22789 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1560 + difference 0 2) (sourceB1560 + difference 2 0) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4586) := by
    have ha : (tripleCharges (sourceA1560 + difference 0 2) (sourceB1560 + difference 2 0) sourceC1560) = raw22790 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw22790; decide +kernel
    rw [ha]
    exact (canonical22790 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1560 + difference 0 3) (sourceB1560 + difference 3 0) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4575) := by
    have ha : (tripleCharges (sourceA1560 + difference 0 3) (sourceB1560 + difference 3 0) sourceC1560) = raw22791 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw22791; decide +kernel
    rw [ha]
    exact (canonical22791 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1560 + difference 0 4) (sourceB1560 + difference 4 0) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1560 + difference 0 4) (sourceB1560 + difference 4 0) sourceC1560) = raw22529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw22529; decide +kernel
    rw [ha]
    exact (canonical22529 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1560 + difference 0 5) (sourceB1560 + difference 5 0) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4612) := by
    have ha : (tripleCharges (sourceA1560 + difference 0 5) (sourceB1560 + difference 5 0) sourceC1560) = raw22626 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw22626; decide +kernel
    rw [ha]
    exact (canonical22626 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1560 + difference 1 0) (sourceB1560 + difference 0 1) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4214) := by
    have ha : (tripleCharges (sourceA1560 + difference 1 0) (sourceB1560 + difference 0 1) sourceC1560) = raw23646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23646; decide +kernel
    rw [ha]
    exact (canonical23646 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1560 + difference 1 2) (sourceB1560 + difference 2 1) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4385) := by
    have ha : (tripleCharges (sourceA1560 + difference 1 2) (sourceB1560 + difference 2 1) sourceC1560) = raw23647 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23647; decide +kernel
    rw [ha]
    exact (canonical23647 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1560 + difference 1 3) (sourceB1560 + difference 3 1) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4378) := by
    have ha : (tripleCharges (sourceA1560 + difference 1 3) (sourceB1560 + difference 3 1) sourceC1560) = raw23648 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23648; decide +kernel
    rw [ha]
    exact (canonical23648 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1560 + difference 1 4) (sourceB1560 + difference 4 1) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1560 + difference 1 4) (sourceB1560 + difference 4 1) sourceC1560) = raw23273 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23273; decide +kernel
    rw [ha]
    exact (canonical23273 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1560 + difference 1 5) (sourceB1560 + difference 5 1) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1560 + difference 1 5) (sourceB1560 + difference 5 1) sourceC1560) = raw22775 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw22775; decide +kernel
    rw [ha]
    exact (canonical22775 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1560 + difference 2 0) (sourceB1560 + difference 0 2) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4214) := by
    have ha : (tripleCharges (sourceA1560 + difference 2 0) (sourceB1560 + difference 0 2) sourceC1560) = raw23649 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23649; decide +kernel
    rw [ha]
    exact (canonical23649 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1560 + difference 2 1) (sourceB1560 + difference 1 2) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4385) := by
    have ha : (tripleCharges (sourceA1560 + difference 2 1) (sourceB1560 + difference 1 2) sourceC1560) = raw23650 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23650; decide +kernel
    rw [ha]
    exact (canonical23650 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1560 + difference 2 3) (sourceB1560 + difference 3 2) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4378) := by
    have ha : (tripleCharges (sourceA1560 + difference 2 3) (sourceB1560 + difference 3 2) sourceC1560) = raw23651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23651; decide +kernel
    rw [ha]
    exact (canonical23651 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1560 + difference 2 4) (sourceB1560 + difference 4 2) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1560 + difference 2 4) (sourceB1560 + difference 4 2) sourceC1560) = raw23652 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23652; decide +kernel
    rw [ha]
    exact (canonical23652 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1560 + difference 2 5) (sourceB1560 + difference 5 2) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4404) := by
    have ha : (tripleCharges (sourceA1560 + difference 2 5) (sourceB1560 + difference 5 2) sourceC1560) = raw22779 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw22779; decide +kernel
    rw [ha]
    exact (canonical22779 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1560 + difference 3 0) (sourceB1560 + difference 0 3) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (tripleCharges (sourceA1560 + difference 3 0) (sourceB1560 + difference 0 3) sourceC1560) = raw23568 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23568; decide +kernel
    rw [ha]
    exact (canonical23568 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1560 + difference 3 1) (sourceB1560 + difference 1 3) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4432) := by
    have ha : (tripleCharges (sourceA1560 + difference 3 1) (sourceB1560 + difference 1 3) sourceC1560) = raw23569 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23569; decide +kernel
    rw [ha]
    exact (canonical23569 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1560 + difference 3 2) (sourceB1560 + difference 2 3) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4432) := by
    have ha : (tripleCharges (sourceA1560 + difference 3 2) (sourceB1560 + difference 2 3) sourceC1560) = raw23570 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23570; decide +kernel
    rw [ha]
    exact (canonical23570 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1560 + difference 3 4) (sourceB1560 + difference 4 3) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1560 + difference 3 4) (sourceB1560 + difference 4 3) sourceC1560) = raw22526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw22526; decide +kernel
    rw [ha]
    exact (canonical22526 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1560 + difference 3 5) (sourceB1560 + difference 5 3) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4511) := by
    have ha : (tripleCharges (sourceA1560 + difference 3 5) (sourceB1560 + difference 5 3) sourceC1560) = raw22623 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw22623; decide +kernel
    rw [ha]
    exact (canonical22623 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1560 + difference 4 0) (sourceB1560 + difference 0 4) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4228) := by
    have ha : (tripleCharges (sourceA1560 + difference 4 0) (sourceB1560 + difference 0 4) sourceC1560) = raw23653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23653; decide +kernel
    rw [ha]
    exact (canonical23653 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1560 + difference 4 1) (sourceB1560 + difference 1 4) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4389) := by
    have ha : (tripleCharges (sourceA1560 + difference 4 1) (sourceB1560 + difference 1 4) sourceC1560) = raw23654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23654; decide +kernel
    rw [ha]
    exact (canonical23654 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1560 + difference 4 2) (sourceB1560 + difference 2 4) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4389) := by
    have ha : (tripleCharges (sourceA1560 + difference 4 2) (sourceB1560 + difference 2 4) sourceC1560) = raw23655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23655; decide +kernel
    rw [ha]
    exact (canonical23655 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1560 + difference 4 3) (sourceB1560 + difference 3 4) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4383) := by
    have ha : (tripleCharges (sourceA1560 + difference 4 3) (sourceB1560 + difference 3 4) sourceC1560) = raw23656 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23656; decide +kernel
    rw [ha]
    exact (canonical23656 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1560 + difference 4 5) (sourceB1560 + difference 5 4) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA1560 + difference 4 5) (sourceB1560 + difference 5 4) sourceC1560) = raw22783 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw22783; decide +kernel
    rw [ha]
    exact (canonical22783 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1560 + difference 5 0) (sourceB1560 + difference 0 5) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4228) := by
    have ha : (tripleCharges (sourceA1560 + difference 5 0) (sourceB1560 + difference 0 5) sourceC1560) = raw23657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23657; decide +kernel
    rw [ha]
    exact (canonical23657 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1560 + difference 5 1) (sourceB1560 + difference 1 5) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4389) := by
    have ha : (tripleCharges (sourceA1560 + difference 5 1) (sourceB1560 + difference 1 5) sourceC1560) = raw23658 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23658; decide +kernel
    rw [ha]
    exact (canonical23658 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1560 + difference 5 2) (sourceB1560 + difference 2 5) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4389) := by
    have ha : (tripleCharges (sourceA1560 + difference 5 2) (sourceB1560 + difference 2 5) sourceC1560) = raw23659 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23659; decide +kernel
    rw [ha]
    exact (canonical23659 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1560 + difference 5 3) (sourceB1560 + difference 3 5) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4383) := by
    have ha : (tripleCharges (sourceA1560 + difference 5 3) (sourceB1560 + difference 3 5) sourceC1560) = raw23660 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23660; decide +kernel
    rw [ha]
    exact (canonical23660 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1560 + difference 5 4) (sourceB1560 + difference 4 5) sourceC1560) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4431) := by
    have ha : (tripleCharges (sourceA1560 + difference 5 4) (sourceB1560 + difference 4 5) sourceC1560) = raw23661 := by
      apply Matrix.ext; unfold tripleCharges sourceA1560 sourceB1560 sourceC1560 difference raw23661; decide +kernel
    rw [ha]
    exact (canonical23661 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1560 sourceB1560 sourceC1560
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1560, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1561 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1561 : Charge := ![0, 2, 0, 0, 0, -2]
def sourceC1561 : Charge := ![4, -2, 0, 0, -2, 0]
def sourceForm1561 : Integer.Sparse Master := [(Sum.inr 562, 1), (Sum.inr 724, 2), (Sum.inr 830, 1), (Sum.inr 852, 1), (Sum.inr 858, 1), (Sum.inr 4071, -1)]

theorem sourceEq1561 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1561 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1561 + difference 1 0) (sourceB1561 + difference 0 1) sourceC1561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 562) := by
    have ha : (tripleCharges (sourceA1561 + difference 1 0) (sourceB1561 + difference 0 1) sourceC1561) = raw23662 := by
      apply Matrix.ext; unfold tripleCharges sourceA1561 sourceB1561 sourceC1561 difference raw23662; decide +kernel
    rw [ha]
    exact (canonical23662 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1561 + difference 1 1) (sourceB1561 + difference 1 1) sourceC1561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 830) := by
    have ha : (tripleCharges (sourceA1561 + difference 1 1) (sourceB1561 + difference 1 1) sourceC1561) = raw22020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1561 sourceB1561 sourceC1561 difference raw22020; decide +kernel
    rw [ha]
    exact (canonical22020 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1561 + difference 1 2) (sourceB1561 + difference 2 1) sourceC1561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 724) := by
    have ha : (tripleCharges (sourceA1561 + difference 1 2) (sourceB1561 + difference 2 1) sourceC1561) = raw23663 := by
      apply Matrix.ext; unfold tripleCharges sourceA1561 sourceB1561 sourceC1561 difference raw23663; decide +kernel
    rw [ha]
    exact (canonical23663 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1561 + difference 1 3) (sourceB1561 + difference 3 1) sourceC1561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 724) := by
    have ha : (tripleCharges (sourceA1561 + difference 1 3) (sourceB1561 + difference 3 1) sourceC1561) = raw23664 := by
      apply Matrix.ext; unfold tripleCharges sourceA1561 sourceB1561 sourceC1561 difference raw23664; decide +kernel
    rw [ha]
    exact (canonical23664 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1561 + difference 1 4) (sourceB1561 + difference 4 1) sourceC1561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 858) := by
    have ha : (tripleCharges (sourceA1561 + difference 1 4) (sourceB1561 + difference 4 1) sourceC1561) = raw22017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1561 sourceB1561 sourceC1561 difference raw22017; decide +kernel
    rw [ha]
    exact (canonical22017 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1561 + difference 1 5) (sourceB1561 + difference 5 1) sourceC1561) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 852) := by
    have ha : (tripleCharges (sourceA1561 + difference 1 5) (sourceB1561 + difference 5 1) sourceC1561) = raw23665 := by
      apply Matrix.ext; unfold tripleCharges sourceA1561 sourceB1561 sourceC1561 difference raw23665; decide +kernel
    rw [ha]
    exact (canonical23665 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1561 + sourceB1561) sourceC1561) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1561 + sourceB1561) sourceC1561) = raw22022 := by
      apply Matrix.ext; unfold doubleCharges sourceA1561 sourceB1561 sourceC1561 raw22022; decide +kernel
    rw [ha]
    exact (canonical22022 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1561 sourceB1561 sourceC1561
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1561, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1562 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1562 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC1562 : Charge := ![4, -2, 0, 0, -1, -1]
def sourceForm1562 : Integer.Sparse Master := [(Sum.inr 831, 1), (Sum.inr 1612, 2), (Sum.inr 1661, 1), (Sum.inr 1739, 2), (Sum.inr 4069, -1)]

theorem sourceEq1562 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1562 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1562 + difference 0 0) (sourceB1562 + difference 0 0) sourceC1562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 831) := by
    have ha : (tripleCharges (sourceA1562 + difference 0 0) (sourceB1562 + difference 0 0) sourceC1562) = raw22037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1562 sourceB1562 sourceC1562 difference raw22037; decide +kernel
    rw [ha]
    exact (canonical22037 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1562 + difference 0 1) (sourceB1562 + difference 1 0) sourceC1562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1661) := by
    have ha : (tripleCharges (sourceA1562 + difference 0 1) (sourceB1562 + difference 1 0) sourceC1562) = raw23666 := by
      apply Matrix.ext; unfold tripleCharges sourceA1562 sourceB1562 sourceC1562 difference raw23666; decide +kernel
    rw [ha]
    exact (canonical23666 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1562 + difference 0 2) (sourceB1562 + difference 2 0) sourceC1562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1612) := by
    have ha : (tripleCharges (sourceA1562 + difference 0 2) (sourceB1562 + difference 2 0) sourceC1562) = raw23667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1562 sourceB1562 sourceC1562 difference raw23667; decide +kernel
    rw [ha]
    exact (canonical23667 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1562 + difference 0 3) (sourceB1562 + difference 3 0) sourceC1562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1612) := by
    have ha : (tripleCharges (sourceA1562 + difference 0 3) (sourceB1562 + difference 3 0) sourceC1562) = raw23668 := by
      apply Matrix.ext; unfold tripleCharges sourceA1562 sourceB1562 sourceC1562 difference raw23668; decide +kernel
    rw [ha]
    exact (canonical23668 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1562 + difference 0 4) (sourceB1562 + difference 4 0) sourceC1562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1562 + difference 0 4) (sourceB1562 + difference 4 0) sourceC1562) = raw22028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1562 sourceB1562 sourceC1562 difference raw22028; decide +kernel
    rw [ha]
    exact (canonical22028 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1562 + difference 0 5) (sourceB1562 + difference 5 0) sourceC1562) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1562 + difference 0 5) (sourceB1562 + difference 5 0) sourceC1562) = raw23669 := by
      apply Matrix.ext; unfold tripleCharges sourceA1562 sourceB1562 sourceC1562 difference raw23669; decide +kernel
    rw [ha]
    exact (canonical23669 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1562 + sourceB1562) sourceC1562) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1562 + sourceB1562) sourceC1562) = raw22029 := by
      apply Matrix.ext; unfold doubleCharges sourceA1562 sourceB1562 sourceC1562 raw22029; decide +kernel
    rw [ha]
    exact (canonical22029 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1562 sourceB1562 sourceC1562
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1562, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1563 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1563 : Charge := ![0, 2, 0, 0, -1, -1]
def sourceC1563 : Charge := ![4, -2, 0, 0, -1, -1]
def sourceForm1563 : Integer.Sparse Master := [(Sum.inr 563, 1), (Sum.inr 725, 2), (Sum.inr 831, 1), (Sum.inr 856, 2), (Sum.inr 4069, -1)]

theorem sourceEq1563 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1563 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1563 + difference 1 0) (sourceB1563 + difference 0 1) sourceC1563) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 563) := by
    have ha : (tripleCharges (sourceA1563 + difference 1 0) (sourceB1563 + difference 0 1) sourceC1563) = raw23670 := by
      apply Matrix.ext; unfold tripleCharges sourceA1563 sourceB1563 sourceC1563 difference raw23670; decide +kernel
    rw [ha]
    exact (canonical23670 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1563 + difference 1 1) (sourceB1563 + difference 1 1) sourceC1563) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 831) := by
    have ha : (tripleCharges (sourceA1563 + difference 1 1) (sourceB1563 + difference 1 1) sourceC1563) = raw22037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1563 sourceB1563 sourceC1563 difference raw22037; decide +kernel
    rw [ha]
    exact (canonical22037 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1563 + difference 1 2) (sourceB1563 + difference 2 1) sourceC1563) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 725) := by
    have ha : (tripleCharges (sourceA1563 + difference 1 2) (sourceB1563 + difference 2 1) sourceC1563) = raw23671 := by
      apply Matrix.ext; unfold tripleCharges sourceA1563 sourceB1563 sourceC1563 difference raw23671; decide +kernel
    rw [ha]
    exact (canonical23671 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1563 + difference 1 3) (sourceB1563 + difference 3 1) sourceC1563) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 725) := by
    have ha : (tripleCharges (sourceA1563 + difference 1 3) (sourceB1563 + difference 3 1) sourceC1563) = raw23672 := by
      apply Matrix.ext; unfold tripleCharges sourceA1563 sourceB1563 sourceC1563 difference raw23672; decide +kernel
    rw [ha]
    exact (canonical23672 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1563 + difference 1 4) (sourceB1563 + difference 4 1) sourceC1563) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 856) := by
    have ha : (tripleCharges (sourceA1563 + difference 1 4) (sourceB1563 + difference 4 1) sourceC1563) = raw22034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1563 sourceB1563 sourceC1563 difference raw22034; decide +kernel
    rw [ha]
    exact (canonical22034 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1563 + difference 1 5) (sourceB1563 + difference 5 1) sourceC1563) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 856) := by
    have ha : (tripleCharges (sourceA1563 + difference 1 5) (sourceB1563 + difference 5 1) sourceC1563) = raw23673 := by
      apply Matrix.ext; unfold tripleCharges sourceA1563 sourceB1563 sourceC1563 difference raw23673; decide +kernel
    rw [ha]
    exact (canonical23673 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1563 + sourceB1563) sourceC1563) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1563 + sourceB1563) sourceC1563) = raw22029 := by
      apply Matrix.ext; unfold doubleCharges sourceA1563 sourceB1563 sourceC1563 raw22029; decide +kernel
    rw [ha]
    exact (canonical22029 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1563 sourceB1563 sourceC1563
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1563, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1564 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1564 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1564 : Charge := ![4, -1, -1, 0, -2, 0]
def sourceForm1564 : Integer.Sparse Master := [(Sum.inr 789, 1), (Sum.inr 1594, 1), (Sum.inr 1640, 2), (Sum.inr 1707, 1), (Sum.inr 1709, 1), (Sum.inr 4069, -1)]

theorem sourceEq1564 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1564 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1564 + difference 0 0) (sourceB1564 + difference 0 0) sourceC1564) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 789) := by
    have ha : (tripleCharges (sourceA1564 + difference 0 0) (sourceB1564 + difference 0 0) sourceC1564) = raw22076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1564 sourceB1564 sourceC1564 difference raw22076; decide +kernel
    rw [ha]
    exact (canonical22076 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1564 + difference 0 1) (sourceB1564 + difference 1 0) sourceC1564) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1640) := by
    have ha : (tripleCharges (sourceA1564 + difference 0 1) (sourceB1564 + difference 1 0) sourceC1564) = raw23674 := by
      apply Matrix.ext; unfold tripleCharges sourceA1564 sourceB1564 sourceC1564 difference raw23674; decide +kernel
    rw [ha]
    exact (canonical23674 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1564 + difference 0 2) (sourceB1564 + difference 2 0) sourceC1564) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1640) := by
    have ha : (tripleCharges (sourceA1564 + difference 0 2) (sourceB1564 + difference 2 0) sourceC1564) = raw23675 := by
      apply Matrix.ext; unfold tripleCharges sourceA1564 sourceB1564 sourceC1564 difference raw23675; decide +kernel
    rw [ha]
    exact (canonical23675 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1564 + difference 0 3) (sourceB1564 + difference 3 0) sourceC1564) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1594) := by
    have ha : (tripleCharges (sourceA1564 + difference 0 3) (sourceB1564 + difference 3 0) sourceC1564) = raw23676 := by
      apply Matrix.ext; unfold tripleCharges sourceA1564 sourceB1564 sourceC1564 difference raw23676; decide +kernel
    rw [ha]
    exact (canonical23676 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1564 + difference 0 4) (sourceB1564 + difference 4 0) sourceC1564) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA1564 + difference 0 4) (sourceB1564 + difference 4 0) sourceC1564) = raw22072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1564 sourceB1564 sourceC1564 difference raw22072; decide +kernel
    rw [ha]
    exact (canonical22072 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1564 + difference 0 5) (sourceB1564 + difference 5 0) sourceC1564) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1564 + difference 0 5) (sourceB1564 + difference 5 0) sourceC1564) = raw23677 := by
      apply Matrix.ext; unfold tripleCharges sourceA1564 sourceB1564 sourceC1564 difference raw23677; decide +kernel
    rw [ha]
    exact (canonical23677 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1564 + sourceB1564) sourceC1564) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1564 + sourceB1564) sourceC1564) = raw22078 := by
      apply Matrix.ext; unfold doubleCharges sourceA1564 sourceB1564 sourceC1564 raw22078; decide +kernel
    rw [ha]
    exact (canonical22078 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1564 sourceB1564 sourceC1564
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1564, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1565 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1565 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceC1565 : Charge := ![4, -1, -1, 0, -2, 0]
def sourceForm1565 : Integer.Sparse Master := [(Sum.inr 543, 1), (Sum.inr 703, 1), (Sum.inr 738, 1), (Sum.inr 789, 1), (Sum.inr 806, 1), (Sum.inr 811, 1), (Sum.inr 4069, -1)]

theorem sourceEq1565 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1565 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1565 + difference 1 0) (sourceB1565 + difference 0 1) sourceC1565) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 543) := by
    have ha : (tripleCharges (sourceA1565 + difference 1 0) (sourceB1565 + difference 0 1) sourceC1565) = raw23678 := by
      apply Matrix.ext; unfold tripleCharges sourceA1565 sourceB1565 sourceC1565 difference raw23678; decide +kernel
    rw [ha]
    exact (canonical23678 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1565 + difference 1 1) (sourceB1565 + difference 1 1) sourceC1565) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 789) := by
    have ha : (tripleCharges (sourceA1565 + difference 1 1) (sourceB1565 + difference 1 1) sourceC1565) = raw22076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1565 sourceB1565 sourceC1565 difference raw22076; decide +kernel
    rw [ha]
    exact (canonical22076 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1565 + difference 1 2) (sourceB1565 + difference 2 1) sourceC1565) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 738) := by
    have ha : (tripleCharges (sourceA1565 + difference 1 2) (sourceB1565 + difference 2 1) sourceC1565) = raw23679 := by
      apply Matrix.ext; unfold tripleCharges sourceA1565 sourceB1565 sourceC1565 difference raw23679; decide +kernel
    rw [ha]
    exact (canonical23679 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1565 + difference 1 3) (sourceB1565 + difference 3 1) sourceC1565) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 703) := by
    have ha : (tripleCharges (sourceA1565 + difference 1 3) (sourceB1565 + difference 3 1) sourceC1565) = raw23680 := by
      apply Matrix.ext; unfold tripleCharges sourceA1565 sourceB1565 sourceC1565 difference raw23680; decide +kernel
    rw [ha]
    exact (canonical23680 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1565 + difference 1 4) (sourceB1565 + difference 4 1) sourceC1565) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 811) := by
    have ha : (tripleCharges (sourceA1565 + difference 1 4) (sourceB1565 + difference 4 1) sourceC1565) = raw22073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1565 sourceB1565 sourceC1565 difference raw22073; decide +kernel
    rw [ha]
    exact (canonical22073 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1565 + difference 1 5) (sourceB1565 + difference 5 1) sourceC1565) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 806) := by
    have ha : (tripleCharges (sourceA1565 + difference 1 5) (sourceB1565 + difference 5 1) sourceC1565) = raw23681 := by
      apply Matrix.ext; unfold tripleCharges sourceA1565 sourceB1565 sourceC1565 difference raw23681; decide +kernel
    rw [ha]
    exact (canonical23681 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1565 + sourceB1565) sourceC1565) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1565 + sourceB1565) sourceC1565) = raw22078 := by
      apply Matrix.ext; unfold doubleCharges sourceA1565 sourceB1565 sourceC1565 raw22078; decide +kernel
    rw [ha]
    exact (canonical22078 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1565 sourceB1565 sourceC1565
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1565, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1566 : Charge := ![0, 1, 1, 0, 0, -2]
def sourceB1566 : Charge := ![4, -1, -1, 0, -2, 0]
def sourceC1566 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceForm1566 : Integer.Sparse Master := [(Sum.inr 552, 1), (Sum.inr 710, 1), (Sum.inr 823, 1), (Sum.inr 848, 1), (Sum.inr 852, 2), (Sum.inr 4071, -1)]

theorem sourceEq1566 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1566 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1566 + difference 5 0) (sourceB1566 + difference 0 5) sourceC1566) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 552) := by
    have ha : (tripleCharges (sourceA1566 + difference 5 0) (sourceB1566 + difference 0 5) sourceC1566) = raw23682 := by
      apply Matrix.ext; unfold tripleCharges sourceA1566 sourceB1566 sourceC1566 difference raw23682; decide +kernel
    rw [ha]
    exact (canonical23682 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1566 + difference 5 1) (sourceB1566 + difference 1 5) sourceC1566) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 852) := by
    have ha : (tripleCharges (sourceA1566 + difference 5 1) (sourceB1566 + difference 1 5) sourceC1566) = raw23683 := by
      apply Matrix.ext; unfold tripleCharges sourceA1566 sourceB1566 sourceC1566 difference raw23683; decide +kernel
    rw [ha]
    exact (canonical23683 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1566 + difference 5 2) (sourceB1566 + difference 2 5) sourceC1566) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 852) := by
    have ha : (tripleCharges (sourceA1566 + difference 5 2) (sourceB1566 + difference 2 5) sourceC1566) = raw23329 := by
      apply Matrix.ext; unfold tripleCharges sourceA1566 sourceB1566 sourceC1566 difference raw23329; decide +kernel
    rw [ha]
    exact (canonical23329 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1566 + difference 5 3) (sourceB1566 + difference 3 5) sourceC1566) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 710) := by
    have ha : (tripleCharges (sourceA1566 + difference 5 3) (sourceB1566 + difference 3 5) sourceC1566) = raw23328 := by
      apply Matrix.ext; unfold tripleCharges sourceA1566 sourceB1566 sourceC1566 difference raw23328; decide +kernel
    rw [ha]
    exact (canonical23328 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1566 + difference 5 4) (sourceB1566 + difference 4 5) sourceC1566) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 848) := by
    have ha : (tripleCharges (sourceA1566 + difference 5 4) (sourceB1566 + difference 4 5) sourceC1566) = raw23684 := by
      apply Matrix.ext; unfold tripleCharges sourceA1566 sourceB1566 sourceC1566 difference raw23684; decide +kernel
    rw [ha]
    exact (canonical23684 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1566 + difference 5 5) (sourceB1566 + difference 5 5) sourceC1566) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 823) := by
    have ha : (tripleCharges (sourceA1566 + difference 5 5) (sourceB1566 + difference 5 5) sourceC1566) = raw23685 := by
      apply Matrix.ext; unfold tripleCharges sourceA1566 sourceB1566 sourceC1566 difference raw23685; decide +kernel
    rw [ha]
    exact (canonical23685 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1566 + sourceB1566) sourceC1566) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4071) := by
    have ha : (doubleCharges (sourceA1566 + sourceB1566) sourceC1566) = raw22329 := by
      apply Matrix.ext; unfold doubleCharges sourceA1566 sourceB1566 sourceC1566 raw22329; decide +kernel
    rw [ha]
    exact (canonical22329 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1566 sourceB1566 sourceC1566
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1566, Integer.Sparse.eval]
  linarith only [hs]

def sourceA1567 : Charge := ![-4, 0, 0, 0, 2, 2]
def sourceB1567 : Charge := ![0, 1, 1, 0, -1, -1]
def sourceC1567 : Charge := ![4, -1, -1, 0, -1, -1]
def sourceForm1567 : Integer.Sparse Master := [(Sum.inr 790, 1), (Sum.inr 1595, 1), (Sum.inr 1641, 2), (Sum.inr 1708, 2), (Sum.inr 4068, -1)]

theorem sourceEq1567 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1567 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1567 + difference 0 0) (sourceB1567 + difference 0 0) sourceC1567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 790) := by
    have ha : (tripleCharges (sourceA1567 + difference 0 0) (sourceB1567 + difference 0 0) sourceC1567) = raw22093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1567 sourceB1567 sourceC1567 difference raw22093; decide +kernel
    rw [ha]
    exact (canonical22093 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1567 + difference 0 1) (sourceB1567 + difference 1 0) sourceC1567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1641) := by
    have ha : (tripleCharges (sourceA1567 + difference 0 1) (sourceB1567 + difference 1 0) sourceC1567) = raw23686 := by
      apply Matrix.ext; unfold tripleCharges sourceA1567 sourceB1567 sourceC1567 difference raw23686; decide +kernel
    rw [ha]
    exact (canonical23686 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1567 + difference 0 2) (sourceB1567 + difference 2 0) sourceC1567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1641) := by
    have ha : (tripleCharges (sourceA1567 + difference 0 2) (sourceB1567 + difference 2 0) sourceC1567) = raw23687 := by
      apply Matrix.ext; unfold tripleCharges sourceA1567 sourceB1567 sourceC1567 difference raw23687; decide +kernel
    rw [ha]
    exact (canonical23687 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1567 + difference 0 3) (sourceB1567 + difference 3 0) sourceC1567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1595) := by
    have ha : (tripleCharges (sourceA1567 + difference 0 3) (sourceB1567 + difference 3 0) sourceC1567) = raw23688 := by
      apply Matrix.ext; unfold tripleCharges sourceA1567 sourceB1567 sourceC1567 difference raw23688; decide +kernel
    rw [ha]
    exact (canonical23688 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1567 + difference 0 4) (sourceB1567 + difference 4 0) sourceC1567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1567 + difference 0 4) (sourceB1567 + difference 4 0) sourceC1567) = raw22084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1567 sourceB1567 sourceC1567 difference raw22084; decide +kernel
    rw [ha]
    exact (canonical22084 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1567 + difference 0 5) (sourceB1567 + difference 5 0) sourceC1567) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1708) := by
    have ha : (tripleCharges (sourceA1567 + difference 0 5) (sourceB1567 + difference 5 0) sourceC1567) = raw23689 := by
      apply Matrix.ext; unfold tripleCharges sourceA1567 sourceB1567 sourceC1567 difference raw23689; decide +kernel
    rw [ha]
    exact (canonical23689 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1567 + sourceB1567) sourceC1567) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4068) := by
    have ha : (doubleCharges (sourceA1567 + sourceB1567) sourceC1567) = raw22085 := by
      apply Matrix.ext; unfold doubleCharges sourceA1567 sourceB1567 sourceC1567 raw22085; decide +kernel
    rw [ha]
    exact (canonical22085 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1567 sourceB1567 sourceC1567
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1567, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
