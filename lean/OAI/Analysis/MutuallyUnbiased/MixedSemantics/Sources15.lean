import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical70

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA480 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB480 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC480 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceForm480 : Integer.Sparse Master := [(Sum.inr 1375, 1), (Sum.inr 2889, 1), (Sum.inr 2979, 2), (Sum.inr 3054, 1), (Sum.inr 3055, 1), (Sum.inr 4092, -1)]

theorem sourceEq480 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm480 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA480 + difference 4 0) (sourceB480 + difference 0 4) sourceC480) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1375) := by
    have ha : (tripleCharges (sourceA480 + difference 4 0) (sourceB480 + difference 0 4) sourceC480) = raw8535 := by
      apply Matrix.ext; unfold tripleCharges sourceA480 sourceB480 sourceC480 difference raw8535; decide +kernel
    rw [ha]
    exact (canonical8535 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA480 + difference 4 1) (sourceB480 + difference 1 4) sourceC480) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2979) := by
    have ha : (tripleCharges (sourceA480 + difference 4 1) (sourceB480 + difference 1 4) sourceC480) = raw8543 := by
      apply Matrix.ext; unfold tripleCharges sourceA480 sourceB480 sourceC480 difference raw8543; decide +kernel
    rw [ha]
    exact (canonical8543 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA480 + difference 4 2) (sourceB480 + difference 2 4) sourceC480) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2979) := by
    have ha : (tripleCharges (sourceA480 + difference 4 2) (sourceB480 + difference 2 4) sourceC480) = raw8548 := by
      apply Matrix.ext; unfold tripleCharges sourceA480 sourceB480 sourceC480 difference raw8548; decide +kernel
    rw [ha]
    exact (canonical8548 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA480 + difference 4 3) (sourceB480 + difference 3 4) sourceC480) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2889) := by
    have ha : (tripleCharges (sourceA480 + difference 4 3) (sourceB480 + difference 3 4) sourceC480) = raw8546 := by
      apply Matrix.ext; unfold tripleCharges sourceA480 sourceB480 sourceC480 difference raw8546; decide +kernel
    rw [ha]
    exact (canonical8546 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA480 + difference 4 4) (sourceB480 + difference 4 4) sourceC480) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA480 + difference 4 4) (sourceB480 + difference 4 4) sourceC480) = raw8525 := by
      apply Matrix.ext; unfold tripleCharges sourceA480 sourceB480 sourceC480 difference raw8525; decide +kernel
    rw [ha]
    exact (canonical8525 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA480 + difference 4 5) (sourceB480 + difference 5 4) sourceC480) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA480 + difference 4 5) (sourceB480 + difference 5 4) sourceC480) = raw8549 := by
      apply Matrix.ext; unfold tripleCharges sourceA480 sourceB480 sourceC480 difference raw8549; decide +kernel
    rw [ha]
    exact (canonical8549 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA480 + sourceB480) sourceC480) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA480 + sourceB480) sourceC480) = raw8531 := by
      apply Matrix.ext; unfold doubleCharges sourceA480 sourceB480 sourceC480 raw8531; decide +kernel
    rw [ha]
    exact (canonical8531 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA480 sourceB480 sourceC480
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm480, Integer.Sparse.eval]
  linarith only [hs]

def sourceA481 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB481 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC481 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceForm481 : Integer.Sparse Master := [(Sum.inr 2643, 1), (Sum.inr 3044, 2), (Sum.inr 3046, 1), (Sum.inr 3055, 1), (Sum.inr 3886, 1), (Sum.inr 4092, -1)]

theorem sourceEq481 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm481 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA481 + difference 0 4) (sourceB481 + difference 4 0) sourceC481) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3886) := by
    have ha : (tripleCharges (sourceA481 + difference 0 4) (sourceB481 + difference 4 0) sourceC481) = raw8529 := by
      apply Matrix.ext; unfold tripleCharges sourceA481 sourceB481 sourceC481 difference raw8529; decide +kernel
    rw [ha]
    exact (canonical8529 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA481 + difference 1 4) (sourceB481 + difference 4 1) sourceC481) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3044) := by
    have ha : (tripleCharges (sourceA481 + difference 1 4) (sourceB481 + difference 4 1) sourceC481) = raw8539 := by
      apply Matrix.ext; unfold tripleCharges sourceA481 sourceB481 sourceC481 difference raw8539; decide +kernel
    rw [ha]
    exact (canonical8539 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA481 + difference 2 4) (sourceB481 + difference 4 2) sourceC481) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3044) := by
    have ha : (tripleCharges (sourceA481 + difference 2 4) (sourceB481 + difference 4 2) sourceC481) = raw8550 := by
      apply Matrix.ext; unfold tripleCharges sourceA481 sourceB481 sourceC481 difference raw8550; decide +kernel
    rw [ha]
    exact (canonical8550 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA481 + difference 3 4) (sourceB481 + difference 4 3) sourceC481) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2643) := by
    have ha : (tripleCharges (sourceA481 + difference 3 4) (sourceB481 + difference 4 3) sourceC481) = raw8551 := by
      apply Matrix.ext; unfold tripleCharges sourceA481 sourceB481 sourceC481 difference raw8551; decide +kernel
    rw [ha]
    exact (canonical8551 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA481 + difference 4 4) (sourceB481 + difference 4 4) sourceC481) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA481 + difference 4 4) (sourceB481 + difference 4 4) sourceC481) = raw8525 := by
      apply Matrix.ext; unfold tripleCharges sourceA481 sourceB481 sourceC481 difference raw8525; decide +kernel
    rw [ha]
    exact (canonical8525 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA481 + difference 5 4) (sourceB481 + difference 4 5) sourceC481) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3046) := by
    have ha : (tripleCharges (sourceA481 + difference 5 4) (sourceB481 + difference 4 5) sourceC481) = raw8552 := by
      apply Matrix.ext; unfold tripleCharges sourceA481 sourceB481 sourceC481 difference raw8552; decide +kernel
    rw [ha]
    exact (canonical8552 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA481 + sourceB481) sourceC481) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA481 + sourceB481) sourceC481) = raw8531 := by
      apply Matrix.ext; unfold doubleCharges sourceA481 sourceB481 sourceC481 raw8531; decide +kernel
    rw [ha]
    exact (canonical8531 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA481 sourceB481 sourceC481
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm481, Integer.Sparse.eval]
  linarith only [hs]

def sourceA482 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB482 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC482 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm482 : Integer.Sparse Master := [(Sum.inr 4867, 2), (Sum.inr 4870, 2), (Sum.inr 4872, 1), (Sum.inr 4873, 1), (Sum.inr 4874, 1), (Sum.inr 4884, 1), (Sum.inr 4896, 1), (Sum.inr 5195, 2), (Sum.inr 5206, 1), (Sum.inr 5229, 2), (Sum.inr 5238, 1), (Sum.inr 5253, 2), (Sum.inr 5264, 2), (Sum.inr 5266, 2), (Sum.inr 5275, 1), (Sum.inr 5282, 2), (Sum.inr 5287, 2), (Sum.inr 5291, 1), (Sum.inr 5293, 1), (Sum.inr 5297, 1), (Sum.inr 5302, 1)]

theorem sourceEq482 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm482 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA482 + difference 0 1) (sourceB482 + difference 1 0) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA482 + difference 0 1) (sourceB482 + difference 1 0) sourceC482) = raw6703 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw6703; decide +kernel
    rw [ha]
    exact (canonical6703 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA482 + difference 0 2) (sourceB482 + difference 2 0) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA482 + difference 0 2) (sourceB482 + difference 2 0) sourceC482) = raw8553 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw8553; decide +kernel
    rw [ha]
    exact (canonical8553 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA482 + difference 0 3) (sourceB482 + difference 3 0) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA482 + difference 0 3) (sourceB482 + difference 3 0) sourceC482) = raw7920 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw7920; decide +kernel
    rw [ha]
    exact (canonical7920 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA482 + difference 0 4) (sourceB482 + difference 4 0) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5206) := by
    have ha : (tripleCharges (sourceA482 + difference 0 4) (sourceB482 + difference 4 0) sourceC482) = raw8554 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw8554; decide +kernel
    rw [ha]
    exact (canonical8554 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA482 + difference 0 5) (sourceB482 + difference 5 0) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA482 + difference 0 5) (sourceB482 + difference 5 0) sourceC482) = raw8555 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw8555; decide +kernel
    rw [ha]
    exact (canonical8555 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA482 + difference 1 0) (sourceB482 + difference 0 1) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA482 + difference 1 0) (sourceB482 + difference 0 1) sourceC482) = raw8556 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw8556; decide +kernel
    rw [ha]
    exact (canonical8556 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA482 + difference 1 2) (sourceB482 + difference 2 1) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5253) := by
    have ha : (tripleCharges (sourceA482 + difference 1 2) (sourceB482 + difference 2 1) sourceC482) = raw8557 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw8557; decide +kernel
    rw [ha]
    exact (canonical8557 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA482 + difference 1 3) (sourceB482 + difference 3 1) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA482 + difference 1 3) (sourceB482 + difference 3 1) sourceC482) = raw7924 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw7924; decide +kernel
    rw [ha]
    exact (canonical7924 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA482 + difference 1 4) (sourceB482 + difference 4 1) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5195) := by
    have ha : (tripleCharges (sourceA482 + difference 1 4) (sourceB482 + difference 4 1) sourceC482) = raw8558 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw8558; decide +kernel
    rw [ha]
    exact (canonical8558 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA482 + difference 1 5) (sourceB482 + difference 5 1) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA482 + difference 1 5) (sourceB482 + difference 5 1) sourceC482) = raw8559 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw8559; decide +kernel
    rw [ha]
    exact (canonical8559 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA482 + difference 2 0) (sourceB482 + difference 0 2) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4867) := by
    have ha : (tripleCharges (sourceA482 + difference 2 0) (sourceB482 + difference 0 2) sourceC482) = raw8560 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw8560; decide +kernel
    rw [ha]
    exact (canonical8560 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA482 + difference 2 1) (sourceB482 + difference 1 2) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5253) := by
    have ha : (tripleCharges (sourceA482 + difference 2 1) (sourceB482 + difference 1 2) sourceC482) = raw6713 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw6713; decide +kernel
    rw [ha]
    exact (canonical6713 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA482 + difference 2 3) (sourceB482 + difference 3 2) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA482 + difference 2 3) (sourceB482 + difference 3 2) sourceC482) = raw7226 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw7226; decide +kernel
    rw [ha]
    exact (canonical7226 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA482 + difference 2 4) (sourceB482 + difference 4 2) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5195) := by
    have ha : (tripleCharges (sourceA482 + difference 2 4) (sourceB482 + difference 4 2) sourceC482) = raw8561 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw8561; decide +kernel
    rw [ha]
    exact (canonical8561 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA482 + difference 2 5) (sourceB482 + difference 5 2) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA482 + difference 2 5) (sourceB482 + difference 5 2) sourceC482) = raw8562 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw8562; decide +kernel
    rw [ha]
    exact (canonical8562 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA482 + difference 3 0) (sourceB482 + difference 0 3) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4872) := by
    have ha : (tripleCharges (sourceA482 + difference 3 0) (sourceB482 + difference 0 3) sourceC482) = raw8563 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw8563; decide +kernel
    rw [ha]
    exact (canonical8563 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA482 + difference 3 1) (sourceB482 + difference 1 3) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4870) := by
    have ha : (tripleCharges (sourceA482 + difference 3 1) (sourceB482 + difference 1 3) sourceC482) = raw6718 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw6718; decide +kernel
    rw [ha]
    exact (canonical6718 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA482 + difference 3 2) (sourceB482 + difference 2 3) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4870) := by
    have ha : (tripleCharges (sourceA482 + difference 3 2) (sourceB482 + difference 2 3) sourceC482) = raw8564 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw8564; decide +kernel
    rw [ha]
    exact (canonical8564 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA482 + difference 3 4) (sourceB482 + difference 4 3) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4873) := by
    have ha : (tripleCharges (sourceA482 + difference 3 4) (sourceB482 + difference 4 3) sourceC482) = raw8565 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw8565; decide +kernel
    rw [ha]
    exact (canonical8565 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA482 + difference 3 5) (sourceB482 + difference 5 3) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4884) := by
    have ha : (tripleCharges (sourceA482 + difference 3 5) (sourceB482 + difference 5 3) sourceC482) = raw8566 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw8566; decide +kernel
    rw [ha]
    exact (canonical8566 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA482 + difference 4 0) (sourceB482 + difference 0 4) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA482 + difference 4 0) (sourceB482 + difference 0 4) sourceC482) = raw6705 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw6705; decide +kernel
    rw [ha]
    exact (canonical6705 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA482 + difference 4 1) (sourceB482 + difference 1 4) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA482 + difference 4 1) (sourceB482 + difference 1 4) sourceC482) = raw7063 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw7063; decide +kernel
    rw [ha]
    exact (canonical7063 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA482 + difference 4 2) (sourceB482 + difference 2 4) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA482 + difference 4 2) (sourceB482 + difference 2 4) sourceC482) = raw6706 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw6706; decide +kernel
    rw [ha]
    exact (canonical6706 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA482 + difference 4 3) (sourceB482 + difference 3 4) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA482 + difference 4 3) (sourceB482 + difference 3 4) sourceC482) = raw6707 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw6707; decide +kernel
    rw [ha]
    exact (canonical6707 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA482 + difference 4 5) (sourceB482 + difference 5 4) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA482 + difference 4 5) (sourceB482 + difference 5 4) sourceC482) = raw6709 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw6709; decide +kernel
    rw [ha]
    exact (canonical6709 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA482 + difference 5 0) (sourceB482 + difference 0 5) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4874) := by
    have ha : (tripleCharges (sourceA482 + difference 5 0) (sourceB482 + difference 0 5) sourceC482) = raw8567 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw8567; decide +kernel
    rw [ha]
    exact (canonical8567 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA482 + difference 5 1) (sourceB482 + difference 1 5) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA482 + difference 5 1) (sourceB482 + difference 1 5) sourceC482) = raw6727 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw6727; decide +kernel
    rw [ha]
    exact (canonical6727 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA482 + difference 5 2) (sourceB482 + difference 2 5) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA482 + difference 5 2) (sourceB482 + difference 2 5) sourceC482) = raw8568 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw8568; decide +kernel
    rw [ha]
    exact (canonical8568 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA482 + difference 5 3) (sourceB482 + difference 3 5) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA482 + difference 5 3) (sourceB482 + difference 3 5) sourceC482) = raw7930 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw7930; decide +kernel
    rw [ha]
    exact (canonical7930 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA482 + difference 5 4) (sourceB482 + difference 4 5) sourceC482) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5297) := by
    have ha : (tripleCharges (sourceA482 + difference 5 4) (sourceB482 + difference 4 5) sourceC482) = raw8569 := by
      apply Matrix.ext; unfold tripleCharges sourceA482 sourceB482 sourceC482 difference raw8569; decide +kernel
    rw [ha]
    exact (canonical8569 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA482 sourceB482 sourceC482
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm482, Integer.Sparse.eval]
  linarith only [hs]

def sourceA483 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB483 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC483 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm483 : Integer.Sparse Master := [(Sum.inr 2129, 2), (Sum.inr 2130, 1), (Sum.inr 2138, 1), (Sum.inr 2251, 2), (Sum.inr 2276, 1), (Sum.inr 2278, 1), (Sum.inr 2282, 1), (Sum.inr 2629, 2), (Sum.inr 2643, 1), (Sum.inr 2713, 2), (Sum.inr 2729, 2), (Sum.inr 2731, 2), (Sum.inr 2751, 2), (Sum.inr 2758, 2), (Sum.inr 2765, 1), (Sum.inr 2767, 1), (Sum.inr 2771, 1), (Sum.inr 2776, 1), (Sum.inr 3092, 2), (Sum.inr 3110, 1), (Sum.inr 3117, 1)]

theorem sourceEq483 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm483 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA483 + difference 0 1) (sourceB483 + difference 1 0) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA483 + difference 0 1) (sourceB483 + difference 1 0) sourceC483) = raw6731 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw6731; decide +kernel
    rw [ha]
    exact (canonical6731 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA483 + difference 0 2) (sourceB483 + difference 2 0) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA483 + difference 0 2) (sourceB483 + difference 2 0) sourceC483) = raw8570 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw8570; decide +kernel
    rw [ha]
    exact (canonical8570 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA483 + difference 0 3) (sourceB483 + difference 3 0) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA483 + difference 0 3) (sourceB483 + difference 3 0) sourceC483) = raw7933 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw7933; decide +kernel
    rw [ha]
    exact (canonical7933 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA483 + difference 0 4) (sourceB483 + difference 4 0) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2643) := by
    have ha : (tripleCharges (sourceA483 + difference 0 4) (sourceB483 + difference 4 0) sourceC483) = raw8571 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw8571; decide +kernel
    rw [ha]
    exact (canonical8571 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA483 + difference 0 5) (sourceB483 + difference 5 0) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3117) := by
    have ha : (tripleCharges (sourceA483 + difference 0 5) (sourceB483 + difference 5 0) sourceC483) = raw8572 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw8572; decide +kernel
    rw [ha]
    exact (canonical8572 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA483 + difference 1 0) (sourceB483 + difference 0 1) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA483 + difference 1 0) (sourceB483 + difference 0 1) sourceC483) = raw8573 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw8573; decide +kernel
    rw [ha]
    exact (canonical8573 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA483 + difference 1 2) (sourceB483 + difference 2 1) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2713) := by
    have ha : (tripleCharges (sourceA483 + difference 1 2) (sourceB483 + difference 2 1) sourceC483) = raw8574 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw8574; decide +kernel
    rw [ha]
    exact (canonical8574 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA483 + difference 1 3) (sourceB483 + difference 3 1) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA483 + difference 1 3) (sourceB483 + difference 3 1) sourceC483) = raw7937 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw7937; decide +kernel
    rw [ha]
    exact (canonical7937 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA483 + difference 1 4) (sourceB483 + difference 4 1) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2629) := by
    have ha : (tripleCharges (sourceA483 + difference 1 4) (sourceB483 + difference 4 1) sourceC483) = raw8575 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw8575; decide +kernel
    rw [ha]
    exact (canonical8575 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA483 + difference 1 5) (sourceB483 + difference 5 1) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2758) := by
    have ha : (tripleCharges (sourceA483 + difference 1 5) (sourceB483 + difference 5 1) sourceC483) = raw8576 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw8576; decide +kernel
    rw [ha]
    exact (canonical8576 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA483 + difference 2 0) (sourceB483 + difference 0 2) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2251) := by
    have ha : (tripleCharges (sourceA483 + difference 2 0) (sourceB483 + difference 0 2) sourceC483) = raw8577 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw8577; decide +kernel
    rw [ha]
    exact (canonical8577 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA483 + difference 2 1) (sourceB483 + difference 1 2) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2713) := by
    have ha : (tripleCharges (sourceA483 + difference 2 1) (sourceB483 + difference 1 2) sourceC483) = raw6741 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw6741; decide +kernel
    rw [ha]
    exact (canonical6741 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA483 + difference 2 3) (sourceB483 + difference 3 2) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA483 + difference 2 3) (sourceB483 + difference 3 2) sourceC483) = raw7244 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw7244; decide +kernel
    rw [ha]
    exact (canonical7244 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA483 + difference 2 4) (sourceB483 + difference 4 2) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2629) := by
    have ha : (tripleCharges (sourceA483 + difference 2 4) (sourceB483 + difference 4 2) sourceC483) = raw8578 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw8578; decide +kernel
    rw [ha]
    exact (canonical8578 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA483 + difference 2 5) (sourceB483 + difference 5 2) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2758) := by
    have ha : (tripleCharges (sourceA483 + difference 2 5) (sourceB483 + difference 5 2) sourceC483) = raw8579 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw8579; decide +kernel
    rw [ha]
    exact (canonical8579 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA483 + difference 3 0) (sourceB483 + difference 0 3) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2282) := by
    have ha : (tripleCharges (sourceA483 + difference 3 0) (sourceB483 + difference 0 3) sourceC483) = raw8580 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw8580; decide +kernel
    rw [ha]
    exact (canonical8580 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA483 + difference 3 1) (sourceB483 + difference 1 3) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2129) := by
    have ha : (tripleCharges (sourceA483 + difference 3 1) (sourceB483 + difference 1 3) sourceC483) = raw6746 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw6746; decide +kernel
    rw [ha]
    exact (canonical6746 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA483 + difference 3 2) (sourceB483 + difference 2 3) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2129) := by
    have ha : (tripleCharges (sourceA483 + difference 3 2) (sourceB483 + difference 2 3) sourceC483) = raw8581 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw8581; decide +kernel
    rw [ha]
    exact (canonical8581 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA483 + difference 3 4) (sourceB483 + difference 4 3) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2130) := by
    have ha : (tripleCharges (sourceA483 + difference 3 4) (sourceB483 + difference 4 3) sourceC483) = raw8582 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw8582; decide +kernel
    rw [ha]
    exact (canonical8582 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA483 + difference 3 5) (sourceB483 + difference 5 3) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2138) := by
    have ha : (tripleCharges (sourceA483 + difference 3 5) (sourceB483 + difference 5 3) sourceC483) = raw8583 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw8583; decide +kernel
    rw [ha]
    exact (canonical8583 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA483 + difference 4 0) (sourceB483 + difference 0 4) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA483 + difference 4 0) (sourceB483 + difference 0 4) sourceC483) = raw6733 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw6733; decide +kernel
    rw [ha]
    exact (canonical6733 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA483 + difference 4 1) (sourceB483 + difference 1 4) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA483 + difference 4 1) (sourceB483 + difference 1 4) sourceC483) = raw7077 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw7077; decide +kernel
    rw [ha]
    exact (canonical7077 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA483 + difference 4 2) (sourceB483 + difference 2 4) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA483 + difference 4 2) (sourceB483 + difference 2 4) sourceC483) = raw6734 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw6734; decide +kernel
    rw [ha]
    exact (canonical6734 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA483 + difference 4 3) (sourceB483 + difference 3 4) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA483 + difference 4 3) (sourceB483 + difference 3 4) sourceC483) = raw6735 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw6735; decide +kernel
    rw [ha]
    exact (canonical6735 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA483 + difference 4 5) (sourceB483 + difference 5 4) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA483 + difference 4 5) (sourceB483 + difference 5 4) sourceC483) = raw6737 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw6737; decide +kernel
    rw [ha]
    exact (canonical6737 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA483 + difference 5 0) (sourceB483 + difference 0 5) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2276) := by
    have ha : (tripleCharges (sourceA483 + difference 5 0) (sourceB483 + difference 0 5) sourceC483) = raw8584 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw8584; decide +kernel
    rw [ha]
    exact (canonical8584 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA483 + difference 5 1) (sourceB483 + difference 1 5) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA483 + difference 5 1) (sourceB483 + difference 1 5) sourceC483) = raw6755 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw6755; decide +kernel
    rw [ha]
    exact (canonical6755 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA483 + difference 5 2) (sourceB483 + difference 2 5) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA483 + difference 5 2) (sourceB483 + difference 2 5) sourceC483) = raw8585 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw8585; decide +kernel
    rw [ha]
    exact (canonical8585 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA483 + difference 5 3) (sourceB483 + difference 3 5) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA483 + difference 5 3) (sourceB483 + difference 3 5) sourceC483) = raw7943 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw7943; decide +kernel
    rw [ha]
    exact (canonical7943 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA483 + difference 5 4) (sourceB483 + difference 4 5) sourceC483) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2771) := by
    have ha : (tripleCharges (sourceA483 + difference 5 4) (sourceB483 + difference 4 5) sourceC483) = raw8586 := by
      apply Matrix.ext; unfold tripleCharges sourceA483 sourceB483 sourceC483 difference raw8586; decide +kernel
    rw [ha]
    exact (canonical8586 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA483 sourceB483 sourceC483
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm483, Integer.Sparse.eval]
  linarith only [hs]

def sourceA484 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB484 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC484 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm484 : Integer.Sparse Master := [(Sum.inr 2111, 2), (Sum.inr 2113, 1), (Sum.inr 2114, 1), (Sum.inr 2280, 1), (Sum.inr 2673, 2), (Sum.inr 2686, 1), (Sum.inr 2687, 1), (Sum.inr 2743, 1), (Sum.inr 3017, 2), (Sum.inr 3025, 2), (Sum.inr 3026, 2), (Sum.inr 3039, 2), (Sum.inr 3040, 2), (Sum.inr 3054, 1), (Sum.inr 3056, 1), (Sum.inr 3078, 2), (Sum.inr 3102, 1), (Sum.inr 3103, 1), (Sum.inr 3180, 2), (Sum.inr 3187, 1), (Sum.inr 3225, 1)]

theorem sourceEq484 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm484 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA484 + difference 0 1) (sourceB484 + difference 1 0) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA484 + difference 0 1) (sourceB484 + difference 1 0) sourceC484) = raw6759 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw6759; decide +kernel
    rw [ha]
    exact (canonical6759 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA484 + difference 0 2) (sourceB484 + difference 2 0) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA484 + difference 0 2) (sourceB484 + difference 2 0) sourceC484) = raw8587 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw8587; decide +kernel
    rw [ha]
    exact (canonical8587 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA484 + difference 0 3) (sourceB484 + difference 3 0) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA484 + difference 0 3) (sourceB484 + difference 3 0) sourceC484) = raw7946 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw7946; decide +kernel
    rw [ha]
    exact (canonical7946 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA484 + difference 0 4) (sourceB484 + difference 4 0) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2687) := by
    have ha : (tripleCharges (sourceA484 + difference 0 4) (sourceB484 + difference 4 0) sourceC484) = raw8588 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw8588; decide +kernel
    rw [ha]
    exact (canonical8588 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA484 + difference 0 5) (sourceB484 + difference 5 0) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA484 + difference 0 5) (sourceB484 + difference 5 0) sourceC484) = raw8589 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw8589; decide +kernel
    rw [ha]
    exact (canonical8589 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA484 + difference 1 0) (sourceB484 + difference 0 1) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA484 + difference 1 0) (sourceB484 + difference 0 1) sourceC484) = raw8590 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw8590; decide +kernel
    rw [ha]
    exact (canonical8590 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA484 + difference 1 2) (sourceB484 + difference 2 1) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3017) := by
    have ha : (tripleCharges (sourceA484 + difference 1 2) (sourceB484 + difference 2 1) sourceC484) = raw8591 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw8591; decide +kernel
    rw [ha]
    exact (canonical8591 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA484 + difference 1 3) (sourceB484 + difference 3 1) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA484 + difference 1 3) (sourceB484 + difference 3 1) sourceC484) = raw7950 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw7950; decide +kernel
    rw [ha]
    exact (canonical7950 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA484 + difference 1 4) (sourceB484 + difference 4 1) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3026) := by
    have ha : (tripleCharges (sourceA484 + difference 1 4) (sourceB484 + difference 4 1) sourceC484) = raw8592 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw8592; decide +kernel
    rw [ha]
    exact (canonical8592 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA484 + difference 1 5) (sourceB484 + difference 5 1) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA484 + difference 1 5) (sourceB484 + difference 5 1) sourceC484) = raw8593 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw8593; decide +kernel
    rw [ha]
    exact (canonical8593 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA484 + difference 2 0) (sourceB484 + difference 0 2) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA484 + difference 2 0) (sourceB484 + difference 0 2) sourceC484) = raw8594 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw8594; decide +kernel
    rw [ha]
    exact (canonical8594 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA484 + difference 2 1) (sourceB484 + difference 1 2) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3017) := by
    have ha : (tripleCharges (sourceA484 + difference 2 1) (sourceB484 + difference 1 2) sourceC484) = raw6769 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw6769; decide +kernel
    rw [ha]
    exact (canonical6769 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA484 + difference 2 3) (sourceB484 + difference 3 2) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA484 + difference 2 3) (sourceB484 + difference 3 2) sourceC484) = raw7262 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw7262; decide +kernel
    rw [ha]
    exact (canonical7262 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA484 + difference 2 4) (sourceB484 + difference 4 2) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3026) := by
    have ha : (tripleCharges (sourceA484 + difference 2 4) (sourceB484 + difference 4 2) sourceC484) = raw8595 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw8595; decide +kernel
    rw [ha]
    exact (canonical8595 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA484 + difference 2 5) (sourceB484 + difference 5 2) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA484 + difference 2 5) (sourceB484 + difference 5 2) sourceC484) = raw8596 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw8596; decide +kernel
    rw [ha]
    exact (canonical8596 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA484 + difference 3 0) (sourceB484 + difference 0 3) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2113) := by
    have ha : (tripleCharges (sourceA484 + difference 3 0) (sourceB484 + difference 0 3) sourceC484) = raw8597 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw8597; decide +kernel
    rw [ha]
    exact (canonical8597 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA484 + difference 3 1) (sourceB484 + difference 1 3) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2111) := by
    have ha : (tripleCharges (sourceA484 + difference 3 1) (sourceB484 + difference 1 3) sourceC484) = raw6774 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw6774; decide +kernel
    rw [ha]
    exact (canonical6774 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA484 + difference 3 2) (sourceB484 + difference 2 3) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2111) := by
    have ha : (tripleCharges (sourceA484 + difference 3 2) (sourceB484 + difference 2 3) sourceC484) = raw8598 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw8598; decide +kernel
    rw [ha]
    exact (canonical8598 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA484 + difference 3 4) (sourceB484 + difference 4 3) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2114) := by
    have ha : (tripleCharges (sourceA484 + difference 3 4) (sourceB484 + difference 4 3) sourceC484) = raw8599 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw8599; decide +kernel
    rw [ha]
    exact (canonical8599 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA484 + difference 3 5) (sourceB484 + difference 5 3) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2280) := by
    have ha : (tripleCharges (sourceA484 + difference 3 5) (sourceB484 + difference 5 3) sourceC484) = raw8600 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw8600; decide +kernel
    rw [ha]
    exact (canonical8600 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA484 + difference 4 0) (sourceB484 + difference 0 4) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA484 + difference 4 0) (sourceB484 + difference 0 4) sourceC484) = raw6761 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw6761; decide +kernel
    rw [ha]
    exact (canonical6761 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA484 + difference 4 1) (sourceB484 + difference 1 4) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA484 + difference 4 1) (sourceB484 + difference 1 4) sourceC484) = raw7091 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw7091; decide +kernel
    rw [ha]
    exact (canonical7091 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA484 + difference 4 2) (sourceB484 + difference 2 4) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA484 + difference 4 2) (sourceB484 + difference 2 4) sourceC484) = raw6762 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw6762; decide +kernel
    rw [ha]
    exact (canonical6762 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA484 + difference 4 3) (sourceB484 + difference 3 4) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA484 + difference 4 3) (sourceB484 + difference 3 4) sourceC484) = raw6763 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw6763; decide +kernel
    rw [ha]
    exact (canonical6763 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA484 + difference 4 5) (sourceB484 + difference 5 4) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA484 + difference 4 5) (sourceB484 + difference 5 4) sourceC484) = raw6765 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw6765; decide +kernel
    rw [ha]
    exact (canonical6765 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA484 + difference 5 0) (sourceB484 + difference 0 5) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3187) := by
    have ha : (tripleCharges (sourceA484 + difference 5 0) (sourceB484 + difference 0 5) sourceC484) = raw8601 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw8601; decide +kernel
    rw [ha]
    exact (canonical8601 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA484 + difference 5 1) (sourceB484 + difference 1 5) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3040) := by
    have ha : (tripleCharges (sourceA484 + difference 5 1) (sourceB484 + difference 1 5) sourceC484) = raw6783 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw6783; decide +kernel
    rw [ha]
    exact (canonical6783 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA484 + difference 5 2) (sourceB484 + difference 2 5) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3040) := by
    have ha : (tripleCharges (sourceA484 + difference 5 2) (sourceB484 + difference 2 5) sourceC484) = raw8602 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw8602; decide +kernel
    rw [ha]
    exact (canonical8602 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA484 + difference 5 3) (sourceB484 + difference 3 5) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA484 + difference 5 3) (sourceB484 + difference 3 5) sourceC484) = raw7956 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw7956; decide +kernel
    rw [ha]
    exact (canonical7956 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA484 + difference 5 4) (sourceB484 + difference 4 5) sourceC484) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3056) := by
    have ha : (tripleCharges (sourceA484 + difference 5 4) (sourceB484 + difference 4 5) sourceC484) = raw8603 := by
      apply Matrix.ext; unfold tripleCharges sourceA484 sourceB484 sourceC484 difference raw8603; decide +kernel
    rw [ha]
    exact (canonical8603 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA484 sourceB484 sourceC484
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm484, Integer.Sparse.eval]
  linarith only [hs]

def sourceA485 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB485 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC485 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm485 : Integer.Sparse Master := [(Sum.inr 2888, 1), (Sum.inr 3392, 2), (Sum.inr 3397, 1), (Sum.inr 3548, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

theorem sourceEq485 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm485 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA485 + difference 0 0) (sourceB485 + difference 0 0) sourceC485) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA485 + difference 0 0) (sourceB485 + difference 0 0) sourceC485) = raw6797 := by
      apply Matrix.ext; unfold tripleCharges sourceA485 sourceB485 sourceC485 difference raw6797; decide +kernel
    rw [ha]
    exact (canonical6797 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA485 + difference 0 1) (sourceB485 + difference 1 0) sourceC485) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3392) := by
    have ha : (tripleCharges (sourceA485 + difference 0 1) (sourceB485 + difference 1 0) sourceC485) = raw6788 := by
      apply Matrix.ext; unfold tripleCharges sourceA485 sourceB485 sourceC485 difference raw6788; decide +kernel
    rw [ha]
    exact (canonical6788 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA485 + difference 0 2) (sourceB485 + difference 2 0) sourceC485) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3392) := by
    have ha : (tripleCharges (sourceA485 + difference 0 2) (sourceB485 + difference 2 0) sourceC485) = raw8604 := by
      apply Matrix.ext; unfold tripleCharges sourceA485 sourceB485 sourceC485 difference raw8604; decide +kernel
    rw [ha]
    exact (canonical8604 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA485 + difference 0 3) (sourceB485 + difference 3 0) sourceC485) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA485 + difference 0 3) (sourceB485 + difference 3 0) sourceC485) = raw7959 := by
      apply Matrix.ext; unfold tripleCharges sourceA485 sourceB485 sourceC485 difference raw7959; decide +kernel
    rw [ha]
    exact (canonical7959 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA485 + difference 0 4) (sourceB485 + difference 4 0) sourceC485) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2888) := by
    have ha : (tripleCharges (sourceA485 + difference 0 4) (sourceB485 + difference 4 0) sourceC485) = raw8605 := by
      apply Matrix.ext; unfold tripleCharges sourceA485 sourceB485 sourceC485 difference raw8605; decide +kernel
    rw [ha]
    exact (canonical8605 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA485 + difference 0 5) (sourceB485 + difference 5 0) sourceC485) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3397) := by
    have ha : (tripleCharges (sourceA485 + difference 0 5) (sourceB485 + difference 5 0) sourceC485) = raw8606 := by
      apply Matrix.ext; unfold tripleCharges sourceA485 sourceB485 sourceC485 difference raw8606; decide +kernel
    rw [ha]
    exact (canonical8606 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA485 + sourceB485) sourceC485) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA485 + sourceB485) sourceC485) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA485 sourceB485 sourceC485 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA485 sourceB485 sourceC485
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm485, Integer.Sparse.eval]
  linarith only [hs]

def sourceA486 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB486 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC486 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm486 : Integer.Sparse Master := [(Sum.inr 2108, 2), (Sum.inr 2113, 1), (Sum.inr 2115, 1), (Sum.inr 2266, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

theorem sourceEq486 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm486 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA486 + difference 0 0) (sourceB486 + difference 0 0) sourceC486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA486 + difference 0 0) (sourceB486 + difference 0 0) sourceC486) = raw6797 := by
      apply Matrix.ext; unfold tripleCharges sourceA486 sourceB486 sourceC486 difference raw6797; decide +kernel
    rw [ha]
    exact (canonical6797 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA486 + difference 1 0) (sourceB486 + difference 0 1) sourceC486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA486 + difference 1 0) (sourceB486 + difference 0 1) sourceC486) = raw8607 := by
      apply Matrix.ext; unfold tripleCharges sourceA486 sourceB486 sourceC486 difference raw8607; decide +kernel
    rw [ha]
    exact (canonical8607 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA486 + difference 2 0) (sourceB486 + difference 0 2) sourceC486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA486 + difference 2 0) (sourceB486 + difference 0 2) sourceC486) = raw8608 := by
      apply Matrix.ext; unfold tripleCharges sourceA486 sourceB486 sourceC486 difference raw8608; decide +kernel
    rw [ha]
    exact (canonical8608 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA486 + difference 3 0) (sourceB486 + difference 0 3) sourceC486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2113) := by
    have ha : (tripleCharges (sourceA486 + difference 3 0) (sourceB486 + difference 0 3) sourceC486) = raw8609 := by
      apply Matrix.ext; unfold tripleCharges sourceA486 sourceB486 sourceC486 difference raw8609; decide +kernel
    rw [ha]
    exact (canonical8609 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA486 + difference 4 0) (sourceB486 + difference 0 4) sourceC486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA486 + difference 4 0) (sourceB486 + difference 0 4) sourceC486) = raw6790 := by
      apply Matrix.ext; unfold tripleCharges sourceA486 sourceB486 sourceC486 difference raw6790; decide +kernel
    rw [ha]
    exact (canonical6790 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA486 + difference 5 0) (sourceB486 + difference 0 5) sourceC486) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA486 + difference 5 0) (sourceB486 + difference 0 5) sourceC486) = raw8610 := by
      apply Matrix.ext; unfold tripleCharges sourceA486 sourceB486 sourceC486 difference raw8610; decide +kernel
    rw [ha]
    exact (canonical8610 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA486 + sourceB486) sourceC486) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA486 + sourceB486) sourceC486) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA486 sourceB486 sourceC486 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA486 sourceB486 sourceC486
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm486, Integer.Sparse.eval]
  linarith only [hs]

def sourceA487 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB487 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC487 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm487 : Integer.Sparse Master := [(Sum.inr 2108, 1), (Sum.inr 2883, 1), (Sum.inr 3504, 1), (Sum.inr 3577, 1), (Sum.inr 3580, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

theorem sourceEq487 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm487 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA487 + difference 1 0) (sourceB487 + difference 0 1) sourceC487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA487 + difference 1 0) (sourceB487 + difference 0 1) sourceC487) = raw8607 := by
      apply Matrix.ext; unfold tripleCharges sourceA487 sourceB487 sourceC487 difference raw8607; decide +kernel
    rw [ha]
    exact (canonical8607 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA487 + difference 1 1) (sourceB487 + difference 1 1) sourceC487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA487 + difference 1 1) (sourceB487 + difference 1 1) sourceC487) = raw6797 := by
      apply Matrix.ext; unfold tripleCharges sourceA487 sourceB487 sourceC487 difference raw6797; decide +kernel
    rw [ha]
    exact (canonical6797 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA487 + difference 1 2) (sourceB487 + difference 2 1) sourceC487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3504) := by
    have ha : (tripleCharges (sourceA487 + difference 1 2) (sourceB487 + difference 2 1) sourceC487) = raw8611 := by
      apply Matrix.ext; unfold tripleCharges sourceA487 sourceB487 sourceC487 difference raw8611; decide +kernel
    rw [ha]
    exact (canonical8611 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA487 + difference 1 3) (sourceB487 + difference 3 1) sourceC487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA487 + difference 1 3) (sourceB487 + difference 3 1) sourceC487) = raw7965 := by
      apply Matrix.ext; unfold tripleCharges sourceA487 sourceB487 sourceC487 difference raw7965; decide +kernel
    rw [ha]
    exact (canonical7965 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA487 + difference 1 4) (sourceB487 + difference 4 1) sourceC487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2883) := by
    have ha : (tripleCharges (sourceA487 + difference 1 4) (sourceB487 + difference 4 1) sourceC487) = raw8612 := by
      apply Matrix.ext; unfold tripleCharges sourceA487 sourceB487 sourceC487 difference raw8612; decide +kernel
    rw [ha]
    exact (canonical8612 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA487 + difference 1 5) (sourceB487 + difference 5 1) sourceC487) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3577) := by
    have ha : (tripleCharges (sourceA487 + difference 1 5) (sourceB487 + difference 5 1) sourceC487) = raw8613 := by
      apply Matrix.ext; unfold tripleCharges sourceA487 sourceB487 sourceC487 difference raw8613; decide +kernel
    rw [ha]
    exact (canonical8613 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA487 + sourceB487) sourceC487) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA487 + sourceB487) sourceC487) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA487 sourceB487 sourceC487 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA487 sourceB487 sourceC487
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm487, Integer.Sparse.eval]
  linarith only [hs]

def sourceA488 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB488 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC488 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm488 : Integer.Sparse Master := [(Sum.inr 2113, 1), (Sum.inr 2887, 1), (Sum.inr 3157, 2), (Sum.inr 3161, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

theorem sourceEq488 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm488 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA488 + difference 3 0) (sourceB488 + difference 0 3) sourceC488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2113) := by
    have ha : (tripleCharges (sourceA488 + difference 3 0) (sourceB488 + difference 0 3) sourceC488) = raw8609 := by
      apply Matrix.ext; unfold tripleCharges sourceA488 sourceB488 sourceC488 difference raw8609; decide +kernel
    rw [ha]
    exact (canonical8609 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA488 + difference 3 1) (sourceB488 + difference 1 3) sourceC488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3157) := by
    have ha : (tripleCharges (sourceA488 + difference 3 1) (sourceB488 + difference 1 3) sourceC488) = raw6809 := by
      apply Matrix.ext; unfold tripleCharges sourceA488 sourceB488 sourceC488 difference raw6809; decide +kernel
    rw [ha]
    exact (canonical6809 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA488 + difference 3 2) (sourceB488 + difference 2 3) sourceC488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3157) := by
    have ha : (tripleCharges (sourceA488 + difference 3 2) (sourceB488 + difference 2 3) sourceC488) = raw8614 := by
      apply Matrix.ext; unfold tripleCharges sourceA488 sourceB488 sourceC488 difference raw8614; decide +kernel
    rw [ha]
    exact (canonical8614 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA488 + difference 3 3) (sourceB488 + difference 3 3) sourceC488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA488 + difference 3 3) (sourceB488 + difference 3 3) sourceC488) = raw6797 := by
      apply Matrix.ext; unfold tripleCharges sourceA488 sourceB488 sourceC488 difference raw6797; decide +kernel
    rw [ha]
    exact (canonical6797 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA488 + difference 3 4) (sourceB488 + difference 4 3) sourceC488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2887) := by
    have ha : (tripleCharges (sourceA488 + difference 3 4) (sourceB488 + difference 4 3) sourceC488) = raw8615 := by
      apply Matrix.ext; unfold tripleCharges sourceA488 sourceB488 sourceC488 difference raw8615; decide +kernel
    rw [ha]
    exact (canonical8615 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA488 + difference 3 5) (sourceB488 + difference 5 3) sourceC488) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3161) := by
    have ha : (tripleCharges (sourceA488 + difference 3 5) (sourceB488 + difference 5 3) sourceC488) = raw8616 := by
      apply Matrix.ext; unfold tripleCharges sourceA488 sourceB488 sourceC488 difference raw8616; decide +kernel
    rw [ha]
    exact (canonical8616 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA488 + sourceB488) sourceC488) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA488 + sourceB488) sourceC488) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA488 sourceB488 sourceC488 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA488 sourceB488 sourceC488
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm488, Integer.Sparse.eval]
  linarith only [hs]

def sourceA489 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB489 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC489 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm489 : Integer.Sparse Master := [(Sum.inr 2883, 2), (Sum.inr 2887, 1), (Sum.inr 2888, 1), (Sum.inr 3056, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

theorem sourceEq489 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm489 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA489 + difference 0 4) (sourceB489 + difference 4 0) sourceC489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2888) := by
    have ha : (tripleCharges (sourceA489 + difference 0 4) (sourceB489 + difference 4 0) sourceC489) = raw8605 := by
      apply Matrix.ext; unfold tripleCharges sourceA489 sourceB489 sourceC489 difference raw8605; decide +kernel
    rw [ha]
    exact (canonical8605 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA489 + difference 1 4) (sourceB489 + difference 4 1) sourceC489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2883) := by
    have ha : (tripleCharges (sourceA489 + difference 1 4) (sourceB489 + difference 4 1) sourceC489) = raw8612 := by
      apply Matrix.ext; unfold tripleCharges sourceA489 sourceB489 sourceC489 difference raw8612; decide +kernel
    rw [ha]
    exact (canonical8612 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA489 + difference 2 4) (sourceB489 + difference 4 2) sourceC489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2883) := by
    have ha : (tripleCharges (sourceA489 + difference 2 4) (sourceB489 + difference 4 2) sourceC489) = raw8617 := by
      apply Matrix.ext; unfold tripleCharges sourceA489 sourceB489 sourceC489 difference raw8617; decide +kernel
    rw [ha]
    exact (canonical8617 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA489 + difference 3 4) (sourceB489 + difference 4 3) sourceC489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2887) := by
    have ha : (tripleCharges (sourceA489 + difference 3 4) (sourceB489 + difference 4 3) sourceC489) = raw8615 := by
      apply Matrix.ext; unfold tripleCharges sourceA489 sourceB489 sourceC489 difference raw8615; decide +kernel
    rw [ha]
    exact (canonical8615 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA489 + difference 4 4) (sourceB489 + difference 4 4) sourceC489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA489 + difference 4 4) (sourceB489 + difference 4 4) sourceC489) = raw6797 := by
      apply Matrix.ext; unfold tripleCharges sourceA489 sourceB489 sourceC489 difference raw6797; decide +kernel
    rw [ha]
    exact (canonical6797 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA489 + difference 5 4) (sourceB489 + difference 4 5) sourceC489) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3056) := by
    have ha : (tripleCharges (sourceA489 + difference 5 4) (sourceB489 + difference 4 5) sourceC489) = raw8618 := by
      apply Matrix.ext; unfold tripleCharges sourceA489 sourceB489 sourceC489 difference raw8618; decide +kernel
    rw [ha]
    exact (canonical8618 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA489 + sourceB489) sourceC489) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA489 + sourceB489) sourceC489) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA489 sourceB489 sourceC489 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA489 sourceB489 sourceC489
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm489, Integer.Sparse.eval]
  linarith only [hs]

def sourceA490 : Charge := ![1, 0, 0, 2, -2, -1]
def sourceB490 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC490 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm490 : Integer.Sparse Master := [(Sum.inr 2115, 1), (Sum.inr 3056, 1), (Sum.inr 3506, 2), (Sum.inr 3582, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

theorem sourceEq490 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm490 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA490 + difference 5 0) (sourceB490 + difference 0 5) sourceC490) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2115) := by
    have ha : (tripleCharges (sourceA490 + difference 5 0) (sourceB490 + difference 0 5) sourceC490) = raw8610 := by
      apply Matrix.ext; unfold tripleCharges sourceA490 sourceB490 sourceC490 difference raw8610; decide +kernel
    rw [ha]
    exact (canonical8610 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA490 + difference 5 1) (sourceB490 + difference 1 5) sourceC490) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3506) := by
    have ha : (tripleCharges (sourceA490 + difference 5 1) (sourceB490 + difference 1 5) sourceC490) = raw6812 := by
      apply Matrix.ext; unfold tripleCharges sourceA490 sourceB490 sourceC490 difference raw6812; decide +kernel
    rw [ha]
    exact (canonical6812 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA490 + difference 5 2) (sourceB490 + difference 2 5) sourceC490) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3506) := by
    have ha : (tripleCharges (sourceA490 + difference 5 2) (sourceB490 + difference 2 5) sourceC490) = raw8619 := by
      apply Matrix.ext; unfold tripleCharges sourceA490 sourceB490 sourceC490 difference raw8619; decide +kernel
    rw [ha]
    exact (canonical8619 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA490 + difference 5 3) (sourceB490 + difference 3 5) sourceC490) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA490 + difference 5 3) (sourceB490 + difference 3 5) sourceC490) = raw7966 := by
      apply Matrix.ext; unfold tripleCharges sourceA490 sourceB490 sourceC490 difference raw7966; decide +kernel
    rw [ha]
    exact (canonical7966 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA490 + difference 5 4) (sourceB490 + difference 4 5) sourceC490) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3056) := by
    have ha : (tripleCharges (sourceA490 + difference 5 4) (sourceB490 + difference 4 5) sourceC490) = raw8618 := by
      apply Matrix.ext; unfold tripleCharges sourceA490 sourceB490 sourceC490 difference raw8618; decide +kernel
    rw [ha]
    exact (canonical8618 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA490 + difference 5 5) (sourceB490 + difference 5 5) sourceC490) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA490 + difference 5 5) (sourceB490 + difference 5 5) sourceC490) = raw6797 := by
      apply Matrix.ext; unfold tripleCharges sourceA490 sourceB490 sourceC490 difference raw6797; decide +kernel
    rw [ha]
    exact (canonical6797 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA490 + sourceB490) sourceC490) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA490 + sourceB490) sourceC490) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA490 sourceB490 sourceC490 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA490 sourceB490 sourceC490
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm490, Integer.Sparse.eval]
  linarith only [hs]

def sourceA491 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB491 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceC491 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceForm491 : Integer.Sparse Master := [(Sum.inr 4570, 2), (Sum.inr 4572, 1), (Sum.inr 4575, 1), (Sum.inr 4619, 1), (Sum.inr 4747, 2), (Sum.inr 4754, 1), (Sum.inr 4899, 1), (Sum.inr 5155, 2), (Sum.inr 5156, 2), (Sum.inr 5170, 2), (Sum.inr 5213, 2), (Sum.inr 5214, 1), (Sum.inr 5301, 2), (Sum.inr 5302, 4), (Sum.inr 5306, 1), (Sum.inr 5310, 1), (Sum.inr 5412, 2), (Sum.inr 5453, 1), (Sum.inr 5456, 1)]

theorem sourceEq491 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm491 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA491 + difference 0 1) (sourceB491 + difference 1 0) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA491 + difference 0 1) (sourceB491 + difference 1 0) sourceC491) = raw8620 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8620; decide +kernel
    rw [ha]
    exact (canonical8620 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA491 + difference 0 2) (sourceB491 + difference 2 0) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA491 + difference 0 2) (sourceB491 + difference 2 0) sourceC491) = raw8621 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8621; decide +kernel
    rw [ha]
    exact (canonical8621 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA491 + difference 0 3) (sourceB491 + difference 3 0) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA491 + difference 0 3) (sourceB491 + difference 3 0) sourceC491) = raw8622 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8622; decide +kernel
    rw [ha]
    exact (canonical8622 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA491 + difference 0 4) (sourceB491 + difference 4 0) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5456) := by
    have ha : (tripleCharges (sourceA491 + difference 0 4) (sourceB491 + difference 4 0) sourceC491) = raw8623 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8623; decide +kernel
    rw [ha]
    exact (canonical8623 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA491 + difference 0 5) (sourceB491 + difference 5 0) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA491 + difference 0 5) (sourceB491 + difference 5 0) sourceC491) = raw8624 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8624; decide +kernel
    rw [ha]
    exact (canonical8624 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA491 + difference 1 0) (sourceB491 + difference 0 1) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4570) := by
    have ha : (tripleCharges (sourceA491 + difference 1 0) (sourceB491 + difference 0 1) sourceC491) = raw8625 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8625; decide +kernel
    rw [ha]
    exact (canonical8625 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA491 + difference 1 2) (sourceB491 + difference 2 1) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA491 + difference 1 2) (sourceB491 + difference 2 1) sourceC491) = raw8626 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8626; decide +kernel
    rw [ha]
    exact (canonical8626 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA491 + difference 1 3) (sourceB491 + difference 3 1) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5213) := by
    have ha : (tripleCharges (sourceA491 + difference 1 3) (sourceB491 + difference 3 1) sourceC491) = raw8627 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8627; decide +kernel
    rw [ha]
    exact (canonical8627 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA491 + difference 1 4) (sourceB491 + difference 4 1) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA491 + difference 1 4) (sourceB491 + difference 4 1) sourceC491) = raw8628 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8628; decide +kernel
    rw [ha]
    exact (canonical8628 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA491 + difference 1 5) (sourceB491 + difference 5 1) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA491 + difference 1 5) (sourceB491 + difference 5 1) sourceC491) = raw8629 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8629; decide +kernel
    rw [ha]
    exact (canonical8629 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA491 + difference 2 0) (sourceB491 + difference 0 2) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4570) := by
    have ha : (tripleCharges (sourceA491 + difference 2 0) (sourceB491 + difference 0 2) sourceC491) = raw8630 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8630; decide +kernel
    rw [ha]
    exact (canonical8630 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA491 + difference 2 1) (sourceB491 + difference 1 2) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA491 + difference 2 1) (sourceB491 + difference 1 2) sourceC491) = raw8631 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8631; decide +kernel
    rw [ha]
    exact (canonical8631 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA491 + difference 2 3) (sourceB491 + difference 3 2) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5213) := by
    have ha : (tripleCharges (sourceA491 + difference 2 3) (sourceB491 + difference 3 2) sourceC491) = raw8632 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8632; decide +kernel
    rw [ha]
    exact (canonical8632 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA491 + difference 2 4) (sourceB491 + difference 4 2) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA491 + difference 2 4) (sourceB491 + difference 4 2) sourceC491) = raw8633 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8633; decide +kernel
    rw [ha]
    exact (canonical8633 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA491 + difference 2 5) (sourceB491 + difference 5 2) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA491 + difference 2 5) (sourceB491 + difference 5 2) sourceC491) = raw8634 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8634; decide +kernel
    rw [ha]
    exact (canonical8634 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA491 + difference 3 0) (sourceB491 + difference 0 3) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA491 + difference 3 0) (sourceB491 + difference 0 3) sourceC491) = raw8635 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8635; decide +kernel
    rw [ha]
    exact (canonical8635 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA491 + difference 3 1) (sourceB491 + difference 1 3) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA491 + difference 3 1) (sourceB491 + difference 1 3) sourceC491) = raw8636 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8636; decide +kernel
    rw [ha]
    exact (canonical8636 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA491 + difference 3 2) (sourceB491 + difference 2 3) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA491 + difference 3 2) (sourceB491 + difference 2 3) sourceC491) = raw8637 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8637; decide +kernel
    rw [ha]
    exact (canonical8637 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA491 + difference 3 4) (sourceB491 + difference 4 3) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA491 + difference 3 4) (sourceB491 + difference 4 3) sourceC491) = raw8638 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8638; decide +kernel
    rw [ha]
    exact (canonical8638 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA491 + difference 3 5) (sourceB491 + difference 5 3) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA491 + difference 3 5) (sourceB491 + difference 5 3) sourceC491) = raw8639 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8639; decide +kernel
    rw [ha]
    exact (canonical8639 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA491 + difference 4 0) (sourceB491 + difference 0 4) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4575) := by
    have ha : (tripleCharges (sourceA491 + difference 4 0) (sourceB491 + difference 0 4) sourceC491) = raw8640 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8640; decide +kernel
    rw [ha]
    exact (canonical8640 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA491 + difference 4 1) (sourceB491 + difference 1 4) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5156) := by
    have ha : (tripleCharges (sourceA491 + difference 4 1) (sourceB491 + difference 1 4) sourceC491) = raw8641 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8641; decide +kernel
    rw [ha]
    exact (canonical8641 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA491 + difference 4 2) (sourceB491 + difference 2 4) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5156) := by
    have ha : (tripleCharges (sourceA491 + difference 4 2) (sourceB491 + difference 2 4) sourceC491) = raw8642 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8642; decide +kernel
    rw [ha]
    exact (canonical8642 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA491 + difference 4 3) (sourceB491 + difference 3 4) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5214) := by
    have ha : (tripleCharges (sourceA491 + difference 4 3) (sourceB491 + difference 3 4) sourceC491) = raw8643 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8643; decide +kernel
    rw [ha]
    exact (canonical8643 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA491 + difference 4 5) (sourceB491 + difference 5 4) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA491 + difference 4 5) (sourceB491 + difference 5 4) sourceC491) = raw8644 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8644; decide +kernel
    rw [ha]
    exact (canonical8644 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA491 + difference 5 0) (sourceB491 + difference 0 5) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4572) := by
    have ha : (tripleCharges (sourceA491 + difference 5 0) (sourceB491 + difference 0 5) sourceC491) = raw8645 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8645; decide +kernel
    rw [ha]
    exact (canonical8645 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA491 + difference 5 1) (sourceB491 + difference 1 5) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA491 + difference 5 1) (sourceB491 + difference 1 5) sourceC491) = raw8646 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8646; decide +kernel
    rw [ha]
    exact (canonical8646 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA491 + difference 5 2) (sourceB491 + difference 2 5) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA491 + difference 5 2) (sourceB491 + difference 2 5) sourceC491) = raw8647 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8647; decide +kernel
    rw [ha]
    exact (canonical8647 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA491 + difference 5 3) (sourceB491 + difference 3 5) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4754) := by
    have ha : (tripleCharges (sourceA491 + difference 5 3) (sourceB491 + difference 3 5) sourceC491) = raw8648 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8648; decide +kernel
    rw [ha]
    exact (canonical8648 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA491 + difference 5 4) (sourceB491 + difference 4 5) sourceC491) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA491 + difference 5 4) (sourceB491 + difference 4 5) sourceC491) = raw8649 := by
      apply Matrix.ext; unfold tripleCharges sourceA491 sourceB491 sourceC491 difference raw8649; decide +kernel
    rw [ha]
    exact (canonical8649 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA491 sourceB491 sourceC491
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm491, Integer.Sparse.eval]
  linarith only [hs]

def sourceA492 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB492 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceC492 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceForm492 : Integer.Sparse Master := [(Sum.inr 1188, 2), (Sum.inr 1190, 1), (Sum.inr 1193, 1), (Sum.inr 1294, 1), (Sum.inr 1926, 2), (Sum.inr 1951, 1), (Sum.inr 2281, 1), (Sum.inr 2840, 2), (Sum.inr 2843, 1), (Sum.inr 2908, 2), (Sum.inr 2911, 2), (Sum.inr 2954, 2), (Sum.inr 3053, 2), (Sum.inr 3054, 3), (Sum.inr 3120, 1), (Sum.inr 3121, 1), (Sum.inr 3626, 1), (Sum.inr 3814, 2), (Sum.inr 3912, 1), (Sum.inr 3916, 1)]

theorem sourceEq492 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm492 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA492 + difference 0 1) (sourceB492 + difference 1 0) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA492 + difference 0 1) (sourceB492 + difference 1 0) sourceC492) = raw8650 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8650; decide +kernel
    rw [ha]
    exact (canonical8650 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA492 + difference 0 2) (sourceB492 + difference 2 0) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA492 + difference 0 2) (sourceB492 + difference 2 0) sourceC492) = raw8651 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8651; decide +kernel
    rw [ha]
    exact (canonical8651 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA492 + difference 0 3) (sourceB492 + difference 3 0) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA492 + difference 0 3) (sourceB492 + difference 3 0) sourceC492) = raw8652 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8652; decide +kernel
    rw [ha]
    exact (canonical8652 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA492 + difference 0 4) (sourceB492 + difference 4 0) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3916) := by
    have ha : (tripleCharges (sourceA492 + difference 0 4) (sourceB492 + difference 4 0) sourceC492) = raw8653 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8653; decide +kernel
    rw [ha]
    exact (canonical8653 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA492 + difference 0 5) (sourceB492 + difference 5 0) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3912) := by
    have ha : (tripleCharges (sourceA492 + difference 0 5) (sourceB492 + difference 5 0) sourceC492) = raw8654 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8654; decide +kernel
    rw [ha]
    exact (canonical8654 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA492 + difference 1 0) (sourceB492 + difference 0 1) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1188) := by
    have ha : (tripleCharges (sourceA492 + difference 1 0) (sourceB492 + difference 0 1) sourceC492) = raw8655 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8655; decide +kernel
    rw [ha]
    exact (canonical8655 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA492 + difference 1 2) (sourceB492 + difference 2 1) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2908) := by
    have ha : (tripleCharges (sourceA492 + difference 1 2) (sourceB492 + difference 2 1) sourceC492) = raw8656 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8656; decide +kernel
    rw [ha]
    exact (canonical8656 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA492 + difference 1 3) (sourceB492 + difference 3 1) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2840) := by
    have ha : (tripleCharges (sourceA492 + difference 1 3) (sourceB492 + difference 3 1) sourceC492) = raw8657 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8657; decide +kernel
    rw [ha]
    exact (canonical8657 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA492 + difference 1 4) (sourceB492 + difference 4 1) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA492 + difference 1 4) (sourceB492 + difference 4 1) sourceC492) = raw8658 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8658; decide +kernel
    rw [ha]
    exact (canonical8658 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA492 + difference 1 5) (sourceB492 + difference 5 1) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA492 + difference 1 5) (sourceB492 + difference 5 1) sourceC492) = raw8659 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8659; decide +kernel
    rw [ha]
    exact (canonical8659 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA492 + difference 2 0) (sourceB492 + difference 0 2) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1188) := by
    have ha : (tripleCharges (sourceA492 + difference 2 0) (sourceB492 + difference 0 2) sourceC492) = raw8660 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8660; decide +kernel
    rw [ha]
    exact (canonical8660 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA492 + difference 2 1) (sourceB492 + difference 1 2) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2908) := by
    have ha : (tripleCharges (sourceA492 + difference 2 1) (sourceB492 + difference 1 2) sourceC492) = raw8661 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8661; decide +kernel
    rw [ha]
    exact (canonical8661 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA492 + difference 2 3) (sourceB492 + difference 3 2) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2840) := by
    have ha : (tripleCharges (sourceA492 + difference 2 3) (sourceB492 + difference 3 2) sourceC492) = raw8662 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8662; decide +kernel
    rw [ha]
    exact (canonical8662 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA492 + difference 2 4) (sourceB492 + difference 4 2) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA492 + difference 2 4) (sourceB492 + difference 4 2) sourceC492) = raw8663 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8663; decide +kernel
    rw [ha]
    exact (canonical8663 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA492 + difference 2 5) (sourceB492 + difference 5 2) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA492 + difference 2 5) (sourceB492 + difference 5 2) sourceC492) = raw8664 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8664; decide +kernel
    rw [ha]
    exact (canonical8664 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA492 + difference 3 0) (sourceB492 + difference 0 3) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA492 + difference 3 0) (sourceB492 + difference 0 3) sourceC492) = raw8665 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8665; decide +kernel
    rw [ha]
    exact (canonical8665 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA492 + difference 3 1) (sourceB492 + difference 1 3) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA492 + difference 3 1) (sourceB492 + difference 1 3) sourceC492) = raw8666 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8666; decide +kernel
    rw [ha]
    exact (canonical8666 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA492 + difference 3 2) (sourceB492 + difference 2 3) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA492 + difference 3 2) (sourceB492 + difference 2 3) sourceC492) = raw8667 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8667; decide +kernel
    rw [ha]
    exact (canonical8667 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA492 + difference 3 4) (sourceB492 + difference 4 3) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3121) := by
    have ha : (tripleCharges (sourceA492 + difference 3 4) (sourceB492 + difference 4 3) sourceC492) = raw8668 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8668; decide +kernel
    rw [ha]
    exact (canonical8668 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA492 + difference 3 5) (sourceB492 + difference 5 3) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA492 + difference 3 5) (sourceB492 + difference 5 3) sourceC492) = raw8669 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8669; decide +kernel
    rw [ha]
    exact (canonical8669 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA492 + difference 4 0) (sourceB492 + difference 0 4) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1193) := by
    have ha : (tripleCharges (sourceA492 + difference 4 0) (sourceB492 + difference 0 4) sourceC492) = raw8670 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8670; decide +kernel
    rw [ha]
    exact (canonical8670 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA492 + difference 4 1) (sourceB492 + difference 1 4) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2911) := by
    have ha : (tripleCharges (sourceA492 + difference 4 1) (sourceB492 + difference 1 4) sourceC492) = raw8671 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8671; decide +kernel
    rw [ha]
    exact (canonical8671 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA492 + difference 4 2) (sourceB492 + difference 2 4) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2911) := by
    have ha : (tripleCharges (sourceA492 + difference 4 2) (sourceB492 + difference 2 4) sourceC492) = raw8672 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8672; decide +kernel
    rw [ha]
    exact (canonical8672 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA492 + difference 4 3) (sourceB492 + difference 3 4) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2843) := by
    have ha : (tripleCharges (sourceA492 + difference 4 3) (sourceB492 + difference 3 4) sourceC492) = raw8673 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8673; decide +kernel
    rw [ha]
    exact (canonical8673 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA492 + difference 4 5) (sourceB492 + difference 5 4) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA492 + difference 4 5) (sourceB492 + difference 5 4) sourceC492) = raw8674 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8674; decide +kernel
    rw [ha]
    exact (canonical8674 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA492 + difference 5 0) (sourceB492 + difference 0 5) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1190) := by
    have ha : (tripleCharges (sourceA492 + difference 5 0) (sourceB492 + difference 0 5) sourceC492) = raw8675 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8675; decide +kernel
    rw [ha]
    exact (canonical8675 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA492 + difference 5 1) (sourceB492 + difference 1 5) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA492 + difference 5 1) (sourceB492 + difference 1 5) sourceC492) = raw8676 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8676; decide +kernel
    rw [ha]
    exact (canonical8676 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA492 + difference 5 2) (sourceB492 + difference 2 5) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA492 + difference 5 2) (sourceB492 + difference 2 5) sourceC492) = raw8677 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8677; decide +kernel
    rw [ha]
    exact (canonical8677 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA492 + difference 5 3) (sourceB492 + difference 3 5) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1951) := by
    have ha : (tripleCharges (sourceA492 + difference 5 3) (sourceB492 + difference 3 5) sourceC492) = raw8678 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8678; decide +kernel
    rw [ha]
    exact (canonical8678 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA492 + difference 5 4) (sourceB492 + difference 4 5) sourceC492) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA492 + difference 5 4) (sourceB492 + difference 4 5) sourceC492) = raw8679 := by
      apply Matrix.ext; unfold tripleCharges sourceA492 sourceB492 sourceC492 difference raw8679; decide +kernel
    rw [ha]
    exact (canonical8679 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA492 sourceB492 sourceC492
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm492, Integer.Sparse.eval]
  linarith only [hs]

def sourceA493 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB493 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC493 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceForm493 : Integer.Sparse Master := [(Sum.inr 4475, 2), (Sum.inr 4476, 1), (Sum.inr 4480, 1), (Sum.inr 4500, 1), (Sum.inr 5086, 2), (Sum.inr 5087, 2), (Sum.inr 5090, 2), (Sum.inr 5103, 2), (Sum.inr 5109, 1), (Sum.inr 5204, 2), (Sum.inr 5207, 1), (Sum.inr 5267, 2), (Sum.inr 5268, 1), (Sum.inr 5276, 1), (Sum.inr 5295, 1), (Sum.inr 5299, 2), (Sum.inr 5300, 1), (Sum.inr 5411, 2), (Sum.inr 5413, 1), (Sum.inr 5443, 1), (Sum.inr 5451, 1)]

theorem sourceEq493 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm493 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA493 + difference 0 1) (sourceB493 + difference 1 0) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA493 + difference 0 1) (sourceB493 + difference 1 0) sourceC493) = raw8680 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8680; decide +kernel
    rw [ha]
    exact (canonical8680 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA493 + difference 0 2) (sourceB493 + difference 2 0) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA493 + difference 0 2) (sourceB493 + difference 2 0) sourceC493) = raw8681 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8681; decide +kernel
    rw [ha]
    exact (canonical8681 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA493 + difference 0 3) (sourceB493 + difference 3 0) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5413) := by
    have ha : (tripleCharges (sourceA493 + difference 0 3) (sourceB493 + difference 3 0) sourceC493) = raw8682 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8682; decide +kernel
    rw [ha]
    exact (canonical8682 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA493 + difference 0 4) (sourceB493 + difference 4 0) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA493 + difference 0 4) (sourceB493 + difference 4 0) sourceC493) = raw8683 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8683; decide +kernel
    rw [ha]
    exact (canonical8683 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA493 + difference 0 5) (sourceB493 + difference 5 0) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA493 + difference 0 5) (sourceB493 + difference 5 0) sourceC493) = raw8684 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8684; decide +kernel
    rw [ha]
    exact (canonical8684 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA493 + difference 1 0) (sourceB493 + difference 0 1) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA493 + difference 1 0) (sourceB493 + difference 0 1) sourceC493) = raw8685 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8685; decide +kernel
    rw [ha]
    exact (canonical8685 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA493 + difference 1 2) (sourceB493 + difference 2 1) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA493 + difference 1 2) (sourceB493 + difference 2 1) sourceC493) = raw8686 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8686; decide +kernel
    rw [ha]
    exact (canonical8686 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA493 + difference 1 3) (sourceB493 + difference 3 1) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA493 + difference 1 3) (sourceB493 + difference 3 1) sourceC493) = raw8687 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8687; decide +kernel
    rw [ha]
    exact (canonical8687 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA493 + difference 1 4) (sourceB493 + difference 4 1) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA493 + difference 1 4) (sourceB493 + difference 4 1) sourceC493) = raw8688 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8688; decide +kernel
    rw [ha]
    exact (canonical8688 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA493 + difference 1 5) (sourceB493 + difference 5 1) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA493 + difference 1 5) (sourceB493 + difference 5 1) sourceC493) = raw8689 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8689; decide +kernel
    rw [ha]
    exact (canonical8689 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA493 + difference 2 0) (sourceB493 + difference 0 2) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA493 + difference 2 0) (sourceB493 + difference 0 2) sourceC493) = raw8690 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8690; decide +kernel
    rw [ha]
    exact (canonical8690 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA493 + difference 2 1) (sourceB493 + difference 1 2) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA493 + difference 2 1) (sourceB493 + difference 1 2) sourceC493) = raw8691 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8691; decide +kernel
    rw [ha]
    exact (canonical8691 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA493 + difference 2 3) (sourceB493 + difference 3 2) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA493 + difference 2 3) (sourceB493 + difference 3 2) sourceC493) = raw8692 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8692; decide +kernel
    rw [ha]
    exact (canonical8692 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA493 + difference 2 4) (sourceB493 + difference 4 2) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA493 + difference 2 4) (sourceB493 + difference 4 2) sourceC493) = raw8693 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8693; decide +kernel
    rw [ha]
    exact (canonical8693 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA493 + difference 2 5) (sourceB493 + difference 5 2) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA493 + difference 2 5) (sourceB493 + difference 5 2) sourceC493) = raw8694 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8694; decide +kernel
    rw [ha]
    exact (canonical8694 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA493 + difference 3 0) (sourceB493 + difference 0 3) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA493 + difference 3 0) (sourceB493 + difference 0 3) sourceC493) = raw8695 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8695; decide +kernel
    rw [ha]
    exact (canonical8695 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA493 + difference 3 1) (sourceB493 + difference 1 3) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA493 + difference 3 1) (sourceB493 + difference 1 3) sourceC493) = raw8696 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8696; decide +kernel
    rw [ha]
    exact (canonical8696 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA493 + difference 3 2) (sourceB493 + difference 2 3) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA493 + difference 3 2) (sourceB493 + difference 2 3) sourceC493) = raw8697 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8697; decide +kernel
    rw [ha]
    exact (canonical8697 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA493 + difference 3 4) (sourceB493 + difference 4 3) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA493 + difference 3 4) (sourceB493 + difference 4 3) sourceC493) = raw8698 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8698; decide +kernel
    rw [ha]
    exact (canonical8698 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA493 + difference 3 5) (sourceB493 + difference 5 3) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA493 + difference 3 5) (sourceB493 + difference 5 3) sourceC493) = raw8699 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8699; decide +kernel
    rw [ha]
    exact (canonical8699 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA493 + difference 4 0) (sourceB493 + difference 0 4) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4480) := by
    have ha : (tripleCharges (sourceA493 + difference 4 0) (sourceB493 + difference 0 4) sourceC493) = raw8700 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8700; decide +kernel
    rw [ha]
    exact (canonical8700 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA493 + difference 4 1) (sourceB493 + difference 1 4) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA493 + difference 4 1) (sourceB493 + difference 1 4) sourceC493) = raw8701 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8701; decide +kernel
    rw [ha]
    exact (canonical8701 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA493 + difference 4 2) (sourceB493 + difference 2 4) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA493 + difference 4 2) (sourceB493 + difference 2 4) sourceC493) = raw8702 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8702; decide +kernel
    rw [ha]
    exact (canonical8702 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA493 + difference 4 3) (sourceB493 + difference 3 4) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5207) := by
    have ha : (tripleCharges (sourceA493 + difference 4 3) (sourceB493 + difference 3 4) sourceC493) = raw8703 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8703; decide +kernel
    rw [ha]
    exact (canonical8703 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA493 + difference 4 5) (sourceB493 + difference 5 4) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA493 + difference 4 5) (sourceB493 + difference 5 4) sourceC493) = raw8704 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8704; decide +kernel
    rw [ha]
    exact (canonical8704 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA493 + difference 5 0) (sourceB493 + difference 0 5) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4476) := by
    have ha : (tripleCharges (sourceA493 + difference 5 0) (sourceB493 + difference 0 5) sourceC493) = raw8705 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8705; decide +kernel
    rw [ha]
    exact (canonical8705 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA493 + difference 5 1) (sourceB493 + difference 1 5) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5087) := by
    have ha : (tripleCharges (sourceA493 + difference 5 1) (sourceB493 + difference 1 5) sourceC493) = raw8706 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8706; decide +kernel
    rw [ha]
    exact (canonical8706 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA493 + difference 5 2) (sourceB493 + difference 2 5) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5087) := by
    have ha : (tripleCharges (sourceA493 + difference 5 2) (sourceB493 + difference 2 5) sourceC493) = raw8707 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8707; decide +kernel
    rw [ha]
    exact (canonical8707 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA493 + difference 5 3) (sourceB493 + difference 3 5) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA493 + difference 5 3) (sourceB493 + difference 3 5) sourceC493) = raw8708 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8708; decide +kernel
    rw [ha]
    exact (canonical8708 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA493 + difference 5 4) (sourceB493 + difference 4 5) sourceC493) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA493 + difference 5 4) (sourceB493 + difference 4 5) sourceC493) = raw8709 := by
      apply Matrix.ext; unfold tripleCharges sourceA493 sourceB493 sourceC493 difference raw8709; decide +kernel
    rw [ha]
    exact (canonical8709 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA493 sourceB493 sourceC493
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm493, Integer.Sparse.eval]
  linarith only [hs]

def sourceA494 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB494 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC494 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceForm494 : Integer.Sparse Master := [(Sum.inr 1058, 2), (Sum.inr 1059, 1), (Sum.inr 1063, 1), (Sum.inr 1084, 1), (Sum.inr 2494, 2), (Sum.inr 2495, 2), (Sum.inr 2499, 2), (Sum.inr 2513, 2), (Sum.inr 2638, 2), (Sum.inr 2640, 1), (Sum.inr 2644, 1), (Sum.inr 2732, 2), (Sum.inr 2734, 1), (Sum.inr 2744, 1), (Sum.inr 2773, 2), (Sum.inr 2774, 1), (Sum.inr 2781, 1), (Sum.inr 3883, 2), (Sum.inr 3888, 1), (Sum.inr 3889, 1), (Sum.inr 4006, 1)]

theorem sourceEq494 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm494 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA494 + difference 0 1) (sourceB494 + difference 1 0) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA494 + difference 0 1) (sourceB494 + difference 1 0) sourceC494) = raw8710 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8710; decide +kernel
    rw [ha]
    exact (canonical8710 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA494 + difference 0 2) (sourceB494 + difference 2 0) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA494 + difference 0 2) (sourceB494 + difference 2 0) sourceC494) = raw8711 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8711; decide +kernel
    rw [ha]
    exact (canonical8711 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA494 + difference 0 3) (sourceB494 + difference 3 0) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4006) := by
    have ha : (tripleCharges (sourceA494 + difference 0 3) (sourceB494 + difference 3 0) sourceC494) = raw8712 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8712; decide +kernel
    rw [ha]
    exact (canonical8712 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA494 + difference 0 4) (sourceB494 + difference 4 0) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA494 + difference 0 4) (sourceB494 + difference 4 0) sourceC494) = raw8713 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8713; decide +kernel
    rw [ha]
    exact (canonical8713 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA494 + difference 0 5) (sourceB494 + difference 5 0) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3888) := by
    have ha : (tripleCharges (sourceA494 + difference 0 5) (sourceB494 + difference 5 0) sourceC494) = raw8714 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8714; decide +kernel
    rw [ha]
    exact (canonical8714 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA494 + difference 1 0) (sourceB494 + difference 0 1) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1058) := by
    have ha : (tripleCharges (sourceA494 + difference 1 0) (sourceB494 + difference 0 1) sourceC494) = raw8715 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8715; decide +kernel
    rw [ha]
    exact (canonical8715 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA494 + difference 1 2) (sourceB494 + difference 2 1) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA494 + difference 1 2) (sourceB494 + difference 2 1) sourceC494) = raw8716 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8716; decide +kernel
    rw [ha]
    exact (canonical8716 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA494 + difference 1 3) (sourceB494 + difference 3 1) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2638) := by
    have ha : (tripleCharges (sourceA494 + difference 1 3) (sourceB494 + difference 3 1) sourceC494) = raw8717 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8717; decide +kernel
    rw [ha]
    exact (canonical8717 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA494 + difference 1 4) (sourceB494 + difference 4 1) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA494 + difference 1 4) (sourceB494 + difference 4 1) sourceC494) = raw8718 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8718; decide +kernel
    rw [ha]
    exact (canonical8718 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA494 + difference 1 5) (sourceB494 + difference 5 1) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA494 + difference 1 5) (sourceB494 + difference 5 1) sourceC494) = raw8719 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8719; decide +kernel
    rw [ha]
    exact (canonical8719 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA494 + difference 2 0) (sourceB494 + difference 0 2) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1058) := by
    have ha : (tripleCharges (sourceA494 + difference 2 0) (sourceB494 + difference 0 2) sourceC494) = raw8720 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8720; decide +kernel
    rw [ha]
    exact (canonical8720 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA494 + difference 2 1) (sourceB494 + difference 1 2) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA494 + difference 2 1) (sourceB494 + difference 1 2) sourceC494) = raw8721 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8721; decide +kernel
    rw [ha]
    exact (canonical8721 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA494 + difference 2 3) (sourceB494 + difference 3 2) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2638) := by
    have ha : (tripleCharges (sourceA494 + difference 2 3) (sourceB494 + difference 3 2) sourceC494) = raw8722 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8722; decide +kernel
    rw [ha]
    exact (canonical8722 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA494 + difference 2 4) (sourceB494 + difference 4 2) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA494 + difference 2 4) (sourceB494 + difference 4 2) sourceC494) = raw8723 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8723; decide +kernel
    rw [ha]
    exact (canonical8723 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA494 + difference 2 5) (sourceB494 + difference 5 2) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA494 + difference 2 5) (sourceB494 + difference 5 2) sourceC494) = raw8724 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8724; decide +kernel
    rw [ha]
    exact (canonical8724 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA494 + difference 3 0) (sourceB494 + difference 0 3) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1084) := by
    have ha : (tripleCharges (sourceA494 + difference 3 0) (sourceB494 + difference 0 3) sourceC494) = raw8725 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8725; decide +kernel
    rw [ha]
    exact (canonical8725 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA494 + difference 3 1) (sourceB494 + difference 1 3) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA494 + difference 3 1) (sourceB494 + difference 1 3) sourceC494) = raw8726 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8726; decide +kernel
    rw [ha]
    exact (canonical8726 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA494 + difference 3 2) (sourceB494 + difference 2 3) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA494 + difference 3 2) (sourceB494 + difference 2 3) sourceC494) = raw8727 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8727; decide +kernel
    rw [ha]
    exact (canonical8727 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA494 + difference 3 4) (sourceB494 + difference 4 3) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA494 + difference 3 4) (sourceB494 + difference 4 3) sourceC494) = raw8728 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8728; decide +kernel
    rw [ha]
    exact (canonical8728 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA494 + difference 3 5) (sourceB494 + difference 5 3) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA494 + difference 3 5) (sourceB494 + difference 5 3) sourceC494) = raw8729 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8729; decide +kernel
    rw [ha]
    exact (canonical8729 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA494 + difference 4 0) (sourceB494 + difference 0 4) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1063) := by
    have ha : (tripleCharges (sourceA494 + difference 4 0) (sourceB494 + difference 0 4) sourceC494) = raw8730 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8730; decide +kernel
    rw [ha]
    exact (canonical8730 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA494 + difference 4 1) (sourceB494 + difference 1 4) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2499) := by
    have ha : (tripleCharges (sourceA494 + difference 4 1) (sourceB494 + difference 1 4) sourceC494) = raw8731 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8731; decide +kernel
    rw [ha]
    exact (canonical8731 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA494 + difference 4 2) (sourceB494 + difference 2 4) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2499) := by
    have ha : (tripleCharges (sourceA494 + difference 4 2) (sourceB494 + difference 2 4) sourceC494) = raw8732 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8732; decide +kernel
    rw [ha]
    exact (canonical8732 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA494 + difference 4 3) (sourceB494 + difference 3 4) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2644) := by
    have ha : (tripleCharges (sourceA494 + difference 4 3) (sourceB494 + difference 3 4) sourceC494) = raw8733 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8733; decide +kernel
    rw [ha]
    exact (canonical8733 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA494 + difference 4 5) (sourceB494 + difference 5 4) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA494 + difference 4 5) (sourceB494 + difference 5 4) sourceC494) = raw8734 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8734; decide +kernel
    rw [ha]
    exact (canonical8734 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA494 + difference 5 0) (sourceB494 + difference 0 5) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1059) := by
    have ha : (tripleCharges (sourceA494 + difference 5 0) (sourceB494 + difference 0 5) sourceC494) = raw8735 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8735; decide +kernel
    rw [ha]
    exact (canonical8735 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA494 + difference 5 1) (sourceB494 + difference 1 5) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2495) := by
    have ha : (tripleCharges (sourceA494 + difference 5 1) (sourceB494 + difference 1 5) sourceC494) = raw8736 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8736; decide +kernel
    rw [ha]
    exact (canonical8736 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA494 + difference 5 2) (sourceB494 + difference 2 5) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2495) := by
    have ha : (tripleCharges (sourceA494 + difference 5 2) (sourceB494 + difference 2 5) sourceC494) = raw8737 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8737; decide +kernel
    rw [ha]
    exact (canonical8737 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA494 + difference 5 3) (sourceB494 + difference 3 5) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2640) := by
    have ha : (tripleCharges (sourceA494 + difference 5 3) (sourceB494 + difference 3 5) sourceC494) = raw8738 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8738; decide +kernel
    rw [ha]
    exact (canonical8738 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA494 + difference 5 4) (sourceB494 + difference 4 5) sourceC494) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA494 + difference 5 4) (sourceB494 + difference 4 5) sourceC494) = raw8739 := by
      apply Matrix.ext; unfold tripleCharges sourceA494 sourceB494 sourceC494 difference raw8739; decide +kernel
    rw [ha]
    exact (canonical8739 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA494 sourceB494 sourceC494
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm494, Integer.Sparse.eval]
  linarith only [hs]

def sourceA495 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB495 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC495 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceForm495 : Integer.Sparse Master := [(Sum.inr 1715, 2), (Sum.inr 1716, 1), (Sum.inr 1729, 1), (Sum.inr 1740, 1), (Sum.inr 3024, 2), (Sum.inr 3052, 1), (Sum.inr 3098, 1), (Sum.inr 3464, 2), (Sum.inr 3472, 2), (Sum.inr 3480, 2), (Sum.inr 3486, 1), (Sum.inr 3541, 2), (Sum.inr 3549, 1), (Sum.inr 3573, 2), (Sum.inr 3584, 1), (Sum.inr 3624, 2), (Sum.inr 3631, 1), (Sum.inr 3809, 2), (Sum.inr 3817, 1), (Sum.inr 3862, 1), (Sum.inr 3987, 1)]

theorem sourceEq495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm495 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA495 + difference 0 1) (sourceB495 + difference 1 0) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA495 + difference 0 1) (sourceB495 + difference 1 0) sourceC495) = raw8740 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8740; decide +kernel
    rw [ha]
    exact (canonical8740 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA495 + difference 0 2) (sourceB495 + difference 2 0) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA495 + difference 0 2) (sourceB495 + difference 2 0) sourceC495) = raw8741 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8741; decide +kernel
    rw [ha]
    exact (canonical8741 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA495 + difference 0 3) (sourceB495 + difference 3 0) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA495 + difference 0 3) (sourceB495 + difference 3 0) sourceC495) = raw8742 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8742; decide +kernel
    rw [ha]
    exact (canonical8742 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA495 + difference 0 4) (sourceB495 + difference 4 0) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA495 + difference 0 4) (sourceB495 + difference 4 0) sourceC495) = raw8743 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8743; decide +kernel
    rw [ha]
    exact (canonical8743 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA495 + difference 0 5) (sourceB495 + difference 5 0) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA495 + difference 0 5) (sourceB495 + difference 5 0) sourceC495) = raw8744 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8744; decide +kernel
    rw [ha]
    exact (canonical8744 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA495 + difference 1 0) (sourceB495 + difference 0 1) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA495 + difference 1 0) (sourceB495 + difference 0 1) sourceC495) = raw8745 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8745; decide +kernel
    rw [ha]
    exact (canonical8745 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA495 + difference 1 2) (sourceB495 + difference 2 1) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA495 + difference 1 2) (sourceB495 + difference 2 1) sourceC495) = raw8746 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8746; decide +kernel
    rw [ha]
    exact (canonical8746 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA495 + difference 1 3) (sourceB495 + difference 3 1) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3624) := by
    have ha : (tripleCharges (sourceA495 + difference 1 3) (sourceB495 + difference 3 1) sourceC495) = raw8747 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8747; decide +kernel
    rw [ha]
    exact (canonical8747 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA495 + difference 1 4) (sourceB495 + difference 4 1) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA495 + difference 1 4) (sourceB495 + difference 4 1) sourceC495) = raw8748 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8748; decide +kernel
    rw [ha]
    exact (canonical8748 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA495 + difference 1 5) (sourceB495 + difference 5 1) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA495 + difference 1 5) (sourceB495 + difference 5 1) sourceC495) = raw8749 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8749; decide +kernel
    rw [ha]
    exact (canonical8749 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA495 + difference 2 0) (sourceB495 + difference 0 2) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA495 + difference 2 0) (sourceB495 + difference 0 2) sourceC495) = raw8750 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8750; decide +kernel
    rw [ha]
    exact (canonical8750 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA495 + difference 2 1) (sourceB495 + difference 1 2) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA495 + difference 2 1) (sourceB495 + difference 1 2) sourceC495) = raw8751 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8751; decide +kernel
    rw [ha]
    exact (canonical8751 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA495 + difference 2 3) (sourceB495 + difference 3 2) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3624) := by
    have ha : (tripleCharges (sourceA495 + difference 2 3) (sourceB495 + difference 3 2) sourceC495) = raw8752 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8752; decide +kernel
    rw [ha]
    exact (canonical8752 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA495 + difference 2 4) (sourceB495 + difference 4 2) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA495 + difference 2 4) (sourceB495 + difference 4 2) sourceC495) = raw8753 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8753; decide +kernel
    rw [ha]
    exact (canonical8753 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA495 + difference 2 5) (sourceB495 + difference 5 2) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA495 + difference 2 5) (sourceB495 + difference 5 2) sourceC495) = raw8754 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8754; decide +kernel
    rw [ha]
    exact (canonical8754 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA495 + difference 3 0) (sourceB495 + difference 0 3) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA495 + difference 3 0) (sourceB495 + difference 0 3) sourceC495) = raw8755 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8755; decide +kernel
    rw [ha]
    exact (canonical8755 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA495 + difference 3 1) (sourceB495 + difference 1 3) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA495 + difference 3 1) (sourceB495 + difference 1 3) sourceC495) = raw8756 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8756; decide +kernel
    rw [ha]
    exact (canonical8756 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA495 + difference 3 2) (sourceB495 + difference 2 3) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA495 + difference 3 2) (sourceB495 + difference 2 3) sourceC495) = raw8757 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8757; decide +kernel
    rw [ha]
    exact (canonical8757 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA495 + difference 3 4) (sourceB495 + difference 4 3) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA495 + difference 3 4) (sourceB495 + difference 4 3) sourceC495) = raw8758 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8758; decide +kernel
    rw [ha]
    exact (canonical8758 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA495 + difference 3 5) (sourceB495 + difference 5 3) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA495 + difference 3 5) (sourceB495 + difference 5 3) sourceC495) = raw8759 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8759; decide +kernel
    rw [ha]
    exact (canonical8759 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA495 + difference 4 0) (sourceB495 + difference 0 4) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1740) := by
    have ha : (tripleCharges (sourceA495 + difference 4 0) (sourceB495 + difference 0 4) sourceC495) = raw8760 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8760; decide +kernel
    rw [ha]
    exact (canonical8760 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA495 + difference 4 1) (sourceB495 + difference 1 4) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA495 + difference 4 1) (sourceB495 + difference 1 4) sourceC495) = raw8761 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8761; decide +kernel
    rw [ha]
    exact (canonical8761 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA495 + difference 4 2) (sourceB495 + difference 2 4) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA495 + difference 4 2) (sourceB495 + difference 2 4) sourceC495) = raw8762 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8762; decide +kernel
    rw [ha]
    exact (canonical8762 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA495 + difference 4 3) (sourceB495 + difference 3 4) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3631) := by
    have ha : (tripleCharges (sourceA495 + difference 4 3) (sourceB495 + difference 3 4) sourceC495) = raw8763 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8763; decide +kernel
    rw [ha]
    exact (canonical8763 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA495 + difference 4 5) (sourceB495 + difference 5 4) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA495 + difference 4 5) (sourceB495 + difference 5 4) sourceC495) = raw8764 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8764; decide +kernel
    rw [ha]
    exact (canonical8764 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA495 + difference 5 0) (sourceB495 + difference 0 5) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA495 + difference 5 0) (sourceB495 + difference 0 5) sourceC495) = raw8765 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8765; decide +kernel
    rw [ha]
    exact (canonical8765 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA495 + difference 5 1) (sourceB495 + difference 1 5) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA495 + difference 5 1) (sourceB495 + difference 1 5) sourceC495) = raw8766 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8766; decide +kernel
    rw [ha]
    exact (canonical8766 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA495 + difference 5 2) (sourceB495 + difference 2 5) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA495 + difference 5 2) (sourceB495 + difference 2 5) sourceC495) = raw8767 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8767; decide +kernel
    rw [ha]
    exact (canonical8767 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA495 + difference 5 3) (sourceB495 + difference 3 5) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3486) := by
    have ha : (tripleCharges (sourceA495 + difference 5 3) (sourceB495 + difference 3 5) sourceC495) = raw8768 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8768; decide +kernel
    rw [ha]
    exact (canonical8768 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA495 + difference 5 4) (sourceB495 + difference 4 5) sourceC495) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA495 + difference 5 4) (sourceB495 + difference 4 5) sourceC495) = raw8769 := by
      apply Matrix.ext; unfold tripleCharges sourceA495 sourceB495 sourceC495 difference raw8769; decide +kernel
    rw [ha]
    exact (canonical8769 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA495 sourceB495 sourceC495
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm495, Integer.Sparse.eval]
  linarith only [hs]

def sourceA496 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB496 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC496 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceForm496 : Integer.Sparse Master := [(Sum.inr 3054, 1), (Sum.inr 3813, 2), (Sum.inr 3817, 1), (Sum.inr 3907, 1), (Sum.inr 3913, 1), (Sum.inr 4092, -1)]

theorem sourceEq496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm496 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA496 + difference 0 0) (sourceB496 + difference 0 0) sourceC496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA496 + difference 0 0) (sourceB496 + difference 0 0) sourceC496) = raw8770 := by
      apply Matrix.ext; unfold tripleCharges sourceA496 sourceB496 sourceC496 difference raw8770; decide +kernel
    rw [ha]
    exact (canonical8770 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA496 + difference 0 1) (sourceB496 + difference 1 0) sourceC496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA496 + difference 0 1) (sourceB496 + difference 1 0) sourceC496) = raw8771 := by
      apply Matrix.ext; unfold tripleCharges sourceA496 sourceB496 sourceC496 difference raw8771; decide +kernel
    rw [ha]
    exact (canonical8771 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA496 + difference 0 2) (sourceB496 + difference 2 0) sourceC496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA496 + difference 0 2) (sourceB496 + difference 2 0) sourceC496) = raw8772 := by
      apply Matrix.ext; unfold tripleCharges sourceA496 sourceB496 sourceC496 difference raw8772; decide +kernel
    rw [ha]
    exact (canonical8772 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA496 + difference 0 3) (sourceB496 + difference 3 0) sourceC496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3817) := by
    have ha : (tripleCharges (sourceA496 + difference 0 3) (sourceB496 + difference 3 0) sourceC496) = raw8773 := by
      apply Matrix.ext; unfold tripleCharges sourceA496 sourceB496 sourceC496 difference raw8773; decide +kernel
    rw [ha]
    exact (canonical8773 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA496 + difference 0 4) (sourceB496 + difference 4 0) sourceC496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA496 + difference 0 4) (sourceB496 + difference 4 0) sourceC496) = raw8774 := by
      apply Matrix.ext; unfold tripleCharges sourceA496 sourceB496 sourceC496 difference raw8774; decide +kernel
    rw [ha]
    exact (canonical8774 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA496 + difference 0 5) (sourceB496 + difference 5 0) sourceC496) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3913) := by
    have ha : (tripleCharges (sourceA496 + difference 0 5) (sourceB496 + difference 5 0) sourceC496) = raw8775 := by
      apply Matrix.ext; unfold tripleCharges sourceA496 sourceB496 sourceC496 difference raw8775; decide +kernel
    rw [ha]
    exact (canonical8775 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA496 + sourceB496) sourceC496) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA496 + sourceB496) sourceC496) = raw8776 := by
      apply Matrix.ext; unfold doubleCharges sourceA496 sourceB496 sourceC496 raw8776; decide +kernel
    rw [ha]
    exact (canonical8776 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA496 sourceB496 sourceC496
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm496, Integer.Sparse.eval]
  linarith only [hs]

def sourceA497 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB497 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC497 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceForm497 : Integer.Sparse Master := [(Sum.inr 1367, 2), (Sum.inr 1372, 1), (Sum.inr 1375, 1), (Sum.inr 1436, 1), (Sum.inr 3054, 1), (Sum.inr 4092, -1)]

theorem sourceEq497 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm497 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA497 + difference 0 0) (sourceB497 + difference 0 0) sourceC497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA497 + difference 0 0) (sourceB497 + difference 0 0) sourceC497) = raw8770 := by
      apply Matrix.ext; unfold tripleCharges sourceA497 sourceB497 sourceC497 difference raw8770; decide +kernel
    rw [ha]
    exact (canonical8770 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA497 + difference 1 0) (sourceB497 + difference 0 1) sourceC497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1367) := by
    have ha : (tripleCharges (sourceA497 + difference 1 0) (sourceB497 + difference 0 1) sourceC497) = raw8777 := by
      apply Matrix.ext; unfold tripleCharges sourceA497 sourceB497 sourceC497 difference raw8777; decide +kernel
    rw [ha]
    exact (canonical8777 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA497 + difference 2 0) (sourceB497 + difference 0 2) sourceC497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1367) := by
    have ha : (tripleCharges (sourceA497 + difference 2 0) (sourceB497 + difference 0 2) sourceC497) = raw8778 := by
      apply Matrix.ext; unfold tripleCharges sourceA497 sourceB497 sourceC497 difference raw8778; decide +kernel
    rw [ha]
    exact (canonical8778 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA497 + difference 3 0) (sourceB497 + difference 0 3) sourceC497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA497 + difference 3 0) (sourceB497 + difference 0 3) sourceC497) = raw8779 := by
      apply Matrix.ext; unfold tripleCharges sourceA497 sourceB497 sourceC497 difference raw8779; decide +kernel
    rw [ha]
    exact (canonical8779 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA497 + difference 4 0) (sourceB497 + difference 0 4) sourceC497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1375) := by
    have ha : (tripleCharges (sourceA497 + difference 4 0) (sourceB497 + difference 0 4) sourceC497) = raw8780 := by
      apply Matrix.ext; unfold tripleCharges sourceA497 sourceB497 sourceC497 difference raw8780; decide +kernel
    rw [ha]
    exact (canonical8780 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA497 + difference 5 0) (sourceB497 + difference 0 5) sourceC497) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1372) := by
    have ha : (tripleCharges (sourceA497 + difference 5 0) (sourceB497 + difference 0 5) sourceC497) = raw8781 := by
      apply Matrix.ext; unfold tripleCharges sourceA497 sourceB497 sourceC497 difference raw8781; decide +kernel
    rw [ha]
    exact (canonical8781 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA497 + sourceB497) sourceC497) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA497 + sourceB497) sourceC497) = raw8776 := by
      apply Matrix.ext; unfold doubleCharges sourceA497 sourceB497 sourceC497 raw8776; decide +kernel
    rw [ha]
    exact (canonical8776 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA497 sourceB497 sourceC497
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm497, Integer.Sparse.eval]
  linarith only [hs]

def sourceA498 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB498 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC498 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceForm498 : Integer.Sparse Master := [(Sum.inr 2495, 1), (Sum.inr 2759, 1), (Sum.inr 2974, 1), (Sum.inr 2979, 1), (Sum.inr 3054, 1), (Sum.inr 3813, 1), (Sum.inr 4092, -1)]

theorem sourceEq498 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm498 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA498 + difference 0 1) (sourceB498 + difference 1 0) sourceC498) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA498 + difference 0 1) (sourceB498 + difference 1 0) sourceC498) = raw8771 := by
      apply Matrix.ext; unfold tripleCharges sourceA498 sourceB498 sourceC498 difference raw8771; decide +kernel
    rw [ha]
    exact (canonical8771 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA498 + difference 1 1) (sourceB498 + difference 1 1) sourceC498) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA498 + difference 1 1) (sourceB498 + difference 1 1) sourceC498) = raw8770 := by
      apply Matrix.ext; unfold tripleCharges sourceA498 sourceB498 sourceC498 difference raw8770; decide +kernel
    rw [ha]
    exact (canonical8770 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA498 + difference 2 1) (sourceB498 + difference 1 2) sourceC498) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA498 + difference 2 1) (sourceB498 + difference 1 2) sourceC498) = raw8782 := by
      apply Matrix.ext; unfold tripleCharges sourceA498 sourceB498 sourceC498 difference raw8782; decide +kernel
    rw [ha]
    exact (canonical8782 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA498 + difference 3 1) (sourceB498 + difference 1 3) sourceC498) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2759) := by
    have ha : (tripleCharges (sourceA498 + difference 3 1) (sourceB498 + difference 1 3) sourceC498) = raw8783 := by
      apply Matrix.ext; unfold tripleCharges sourceA498 sourceB498 sourceC498 difference raw8783; decide +kernel
    rw [ha]
    exact (canonical8783 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA498 + difference 4 1) (sourceB498 + difference 1 4) sourceC498) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2979) := by
    have ha : (tripleCharges (sourceA498 + difference 4 1) (sourceB498 + difference 1 4) sourceC498) = raw8784 := by
      apply Matrix.ext; unfold tripleCharges sourceA498 sourceB498 sourceC498 difference raw8784; decide +kernel
    rw [ha]
    exact (canonical8784 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA498 + difference 5 1) (sourceB498 + difference 1 5) sourceC498) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2495) := by
    have ha : (tripleCharges (sourceA498 + difference 5 1) (sourceB498 + difference 1 5) sourceC498) = raw8785 := by
      apply Matrix.ext; unfold tripleCharges sourceA498 sourceB498 sourceC498 difference raw8785; decide +kernel
    rw [ha]
    exact (canonical8785 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA498 + sourceB498) sourceC498) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA498 + sourceB498) sourceC498) = raw8776 := by
      apply Matrix.ext; unfold doubleCharges sourceA498 sourceB498 sourceC498 raw8776; decide +kernel
    rw [ha]
    exact (canonical8776 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA498 sourceB498 sourceC498
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm498, Integer.Sparse.eval]
  linarith only [hs]

def sourceA499 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB499 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC499 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm499 : Integer.Sparse Master := [(Sum.inr 4880, 2), (Sum.inr 4881, 1), (Sum.inr 4884, 1), (Sum.inr 4891, 2), (Sum.inr 4892, 1), (Sum.inr 4896, 1), (Sum.inr 4898, 1), (Sum.inr 5103, 2), (Sum.inr 5110, 1), (Sum.inr 5228, 2), (Sum.inr 5238, 1), (Sum.inr 5254, 2), (Sum.inr 5266, 2), (Sum.inr 5267, 2), (Sum.inr 5274, 1), (Sum.inr 5276, 1), (Sum.inr 5284, 2), (Sum.inr 5287, 2), (Sum.inr 5293, 1), (Sum.inr 5294, 1), (Sum.inr 5300, 1)]

theorem sourceEq499 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm499 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA499 + difference 0 1) (sourceB499 + difference 1 0) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA499 + difference 0 1) (sourceB499 + difference 1 0) sourceC499) = raw6704 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw6704; decide +kernel
    rw [ha]
    exact (canonical6704 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA499 + difference 0 2) (sourceB499 + difference 2 0) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA499 + difference 0 2) (sourceB499 + difference 2 0) sourceC499) = raw8786 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw8786; decide +kernel
    rw [ha]
    exact (canonical8786 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA499 + difference 0 3) (sourceB499 + difference 3 0) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5274) := by
    have ha : (tripleCharges (sourceA499 + difference 0 3) (sourceB499 + difference 3 0) sourceC499) = raw7921 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw7921; decide +kernel
    rw [ha]
    exact (canonical7921 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA499 + difference 0 4) (sourceB499 + difference 4 0) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5238) := by
    have ha : (tripleCharges (sourceA499 + difference 0 4) (sourceB499 + difference 4 0) sourceC499) = raw8555 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw8555; decide +kernel
    rw [ha]
    exact (canonical8555 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA499 + difference 0 5) (sourceB499 + difference 5 0) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA499 + difference 0 5) (sourceB499 + difference 5 0) sourceC499) = raw8787 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw8787; decide +kernel
    rw [ha]
    exact (canonical8787 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA499 + difference 1 0) (sourceB499 + difference 0 1) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA499 + difference 1 0) (sourceB499 + difference 0 1) sourceC499) = raw5675 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw5675; decide +kernel
    rw [ha]
    exact (canonical5675 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA499 + difference 1 2) (sourceB499 + difference 2 1) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA499 + difference 1 2) (sourceB499 + difference 2 1) sourceC499) = raw8788 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw8788; decide +kernel
    rw [ha]
    exact (canonical8788 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA499 + difference 1 3) (sourceB499 + difference 3 1) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA499 + difference 1 3) (sourceB499 + difference 3 1) sourceC499) = raw5659 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw5659; decide +kernel
    rw [ha]
    exact (canonical5659 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA499 + difference 1 4) (sourceB499 + difference 4 1) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA499 + difference 1 4) (sourceB499 + difference 4 1) sourceC499) = raw8559 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw8559; decide +kernel
    rw [ha]
    exact (canonical8559 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA499 + difference 1 5) (sourceB499 + difference 5 1) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA499 + difference 1 5) (sourceB499 + difference 5 1) sourceC499) = raw8789 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw8789; decide +kernel
    rw [ha]
    exact (canonical8789 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA499 + difference 2 0) (sourceB499 + difference 0 2) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA499 + difference 2 0) (sourceB499 + difference 0 2) sourceC499) = raw5674 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw5674; decide +kernel
    rw [ha]
    exact (canonical5674 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA499 + difference 2 1) (sourceB499 + difference 1 2) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA499 + difference 2 1) (sourceB499 + difference 1 2) sourceC499) = raw6714 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw6714; decide +kernel
    rw [ha]
    exact (canonical6714 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA499 + difference 2 3) (sourceB499 + difference 3 2) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA499 + difference 2 3) (sourceB499 + difference 3 2) sourceC499) = raw5658 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw5658; decide +kernel
    rw [ha]
    exact (canonical5658 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA499 + difference 2 4) (sourceB499 + difference 4 2) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA499 + difference 2 4) (sourceB499 + difference 4 2) sourceC499) = raw8562 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw8562; decide +kernel
    rw [ha]
    exact (canonical8562 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA499 + difference 2 5) (sourceB499 + difference 5 2) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA499 + difference 2 5) (sourceB499 + difference 5 2) sourceC499) = raw8790 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw8790; decide +kernel
    rw [ha]
    exact (canonical8790 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA499 + difference 3 0) (sourceB499 + difference 0 3) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA499 + difference 3 0) (sourceB499 + difference 0 3) sourceC499) = raw8791 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw8791; decide +kernel
    rw [ha]
    exact (canonical8791 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA499 + difference 3 1) (sourceB499 + difference 1 3) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA499 + difference 3 1) (sourceB499 + difference 1 3) sourceC499) = raw6719 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw6719; decide +kernel
    rw [ha]
    exact (canonical6719 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA499 + difference 3 2) (sourceB499 + difference 2 3) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA499 + difference 3 2) (sourceB499 + difference 2 3) sourceC499) = raw8792 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw8792; decide +kernel
    rw [ha]
    exact (canonical8792 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA499 + difference 3 4) (sourceB499 + difference 4 3) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4884) := by
    have ha : (tripleCharges (sourceA499 + difference 3 4) (sourceB499 + difference 4 3) sourceC499) = raw8566 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw8566; decide +kernel
    rw [ha]
    exact (canonical8566 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA499 + difference 3 5) (sourceB499 + difference 5 3) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4881) := by
    have ha : (tripleCharges (sourceA499 + difference 3 5) (sourceB499 + difference 5 3) sourceC499) = raw8793 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw8793; decide +kernel
    rw [ha]
    exact (canonical8793 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA499 + difference 4 0) (sourceB499 + difference 0 4) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA499 + difference 4 0) (sourceB499 + difference 0 4) sourceC499) = raw7053 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw7053; decide +kernel
    rw [ha]
    exact (canonical7053 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA499 + difference 4 1) (sourceB499 + difference 1 4) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA499 + difference 4 1) (sourceB499 + difference 1 4) sourceC499) = raw6384 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw6384; decide +kernel
    rw [ha]
    exact (canonical6384 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA499 + difference 4 2) (sourceB499 + difference 2 4) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA499 + difference 4 2) (sourceB499 + difference 2 4) sourceC499) = raw7054 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw7054; decide +kernel
    rw [ha]
    exact (canonical7054 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA499 + difference 4 3) (sourceB499 + difference 3 4) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA499 + difference 4 3) (sourceB499 + difference 3 4) sourceC499) = raw6375 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw6375; decide +kernel
    rw [ha]
    exact (canonical6375 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA499 + difference 4 5) (sourceB499 + difference 5 4) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA499 + difference 4 5) (sourceB499 + difference 5 4) sourceC499) = raw7055 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw7055; decide +kernel
    rw [ha]
    exact (canonical7055 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA499 + difference 5 0) (sourceB499 + difference 0 5) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA499 + difference 5 0) (sourceB499 + difference 0 5) sourceC499) = raw6705 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw6705; decide +kernel
    rw [ha]
    exact (canonical6705 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA499 + difference 5 1) (sourceB499 + difference 1 5) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA499 + difference 5 1) (sourceB499 + difference 1 5) sourceC499) = raw7063 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw7063; decide +kernel
    rw [ha]
    exact (canonical7063 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA499 + difference 5 2) (sourceB499 + difference 2 5) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA499 + difference 5 2) (sourceB499 + difference 2 5) sourceC499) = raw6706 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw6706; decide +kernel
    rw [ha]
    exact (canonical6706 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA499 + difference 5 3) (sourceB499 + difference 3 5) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA499 + difference 5 3) (sourceB499 + difference 3 5) sourceC499) = raw6707 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw6707; decide +kernel
    rw [ha]
    exact (canonical6707 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA499 + difference 5 4) (sourceB499 + difference 4 5) sourceC499) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA499 + difference 5 4) (sourceB499 + difference 4 5) sourceC499) = raw6708 := by
      apply Matrix.ext; unfold tripleCharges sourceA499 sourceB499 sourceC499 difference raw6708; decide +kernel
    rw [ha]
    exact (canonical6708 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA499 sourceB499 sourceC499
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm499, Integer.Sparse.eval]
  linarith only [hs]

def sourceA500 : Charge := ![1, 0, 0, 2, -1, -2]
def sourceB500 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC500 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm500 : Integer.Sparse Master := [(Sum.inr 2254, 2), (Sum.inr 2255, 1), (Sum.inr 2267, 1), (Sum.inr 2280, 1), (Sum.inr 2672, 2), (Sum.inr 2685, 1), (Sum.inr 2686, 1), (Sum.inr 2742, 1), (Sum.inr 3016, 2), (Sum.inr 3024, 2), (Sum.inr 3025, 2), (Sum.inr 3038, 2), (Sum.inr 3039, 2), (Sum.inr 3052, 1), (Sum.inr 3055, 1), (Sum.inr 3077, 2), (Sum.inr 3101, 1), (Sum.inr 3102, 1), (Sum.inr 3222, 2), (Sum.inr 3224, 1), (Sum.inr 3225, 1)]

theorem sourceEq500 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm500 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA500 + difference 0 1) (sourceB500 + difference 1 0) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA500 + difference 0 1) (sourceB500 + difference 1 0) sourceC500) = raw6760 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw6760; decide +kernel
    rw [ha]
    exact (canonical6760 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA500 + difference 0 2) (sourceB500 + difference 2 0) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA500 + difference 0 2) (sourceB500 + difference 2 0) sourceC500) = raw8794 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw8794; decide +kernel
    rw [ha]
    exact (canonical8794 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA500 + difference 0 3) (sourceB500 + difference 3 0) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2742) := by
    have ha : (tripleCharges (sourceA500 + difference 0 3) (sourceB500 + difference 3 0) sourceC500) = raw7947 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw7947; decide +kernel
    rw [ha]
    exact (canonical7947 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA500 + difference 0 4) (sourceB500 + difference 4 0) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2686) := by
    have ha : (tripleCharges (sourceA500 + difference 0 4) (sourceB500 + difference 4 0) sourceC500) = raw8589 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw8589; decide +kernel
    rw [ha]
    exact (canonical8589 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA500 + difference 0 5) (sourceB500 + difference 5 0) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA500 + difference 0 5) (sourceB500 + difference 5 0) sourceC500) = raw8795 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw8795; decide +kernel
    rw [ha]
    exact (canonical8795 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA500 + difference 1 0) (sourceB500 + difference 0 1) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA500 + difference 1 0) (sourceB500 + difference 0 1) sourceC500) = raw5735 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw5735; decide +kernel
    rw [ha]
    exact (canonical5735 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA500 + difference 1 2) (sourceB500 + difference 2 1) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA500 + difference 1 2) (sourceB500 + difference 2 1) sourceC500) = raw8796 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw8796; decide +kernel
    rw [ha]
    exact (canonical8796 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA500 + difference 1 3) (sourceB500 + difference 3 1) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA500 + difference 1 3) (sourceB500 + difference 3 1) sourceC500) = raw5719 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw5719; decide +kernel
    rw [ha]
    exact (canonical5719 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA500 + difference 1 4) (sourceB500 + difference 4 1) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA500 + difference 1 4) (sourceB500 + difference 4 1) sourceC500) = raw8593 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw8593; decide +kernel
    rw [ha]
    exact (canonical8593 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA500 + difference 1 5) (sourceB500 + difference 5 1) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA500 + difference 1 5) (sourceB500 + difference 5 1) sourceC500) = raw8797 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw8797; decide +kernel
    rw [ha]
    exact (canonical8797 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA500 + difference 2 0) (sourceB500 + difference 0 2) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA500 + difference 2 0) (sourceB500 + difference 0 2) sourceC500) = raw5734 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw5734; decide +kernel
    rw [ha]
    exact (canonical5734 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA500 + difference 2 1) (sourceB500 + difference 1 2) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA500 + difference 2 1) (sourceB500 + difference 1 2) sourceC500) = raw6770 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw6770; decide +kernel
    rw [ha]
    exact (canonical6770 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA500 + difference 2 3) (sourceB500 + difference 3 2) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA500 + difference 2 3) (sourceB500 + difference 3 2) sourceC500) = raw5718 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw5718; decide +kernel
    rw [ha]
    exact (canonical5718 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA500 + difference 2 4) (sourceB500 + difference 4 2) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA500 + difference 2 4) (sourceB500 + difference 4 2) sourceC500) = raw8596 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw8596; decide +kernel
    rw [ha]
    exact (canonical8596 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA500 + difference 2 5) (sourceB500 + difference 5 2) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA500 + difference 2 5) (sourceB500 + difference 5 2) sourceC500) = raw8798 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw8798; decide +kernel
    rw [ha]
    exact (canonical8798 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA500 + difference 3 0) (sourceB500 + difference 0 3) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA500 + difference 3 0) (sourceB500 + difference 0 3) sourceC500) = raw8799 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw8799; decide +kernel
    rw [ha]
    exact (canonical8799 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA500 + difference 3 1) (sourceB500 + difference 1 3) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA500 + difference 3 1) (sourceB500 + difference 1 3) sourceC500) = raw6775 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw6775; decide +kernel
    rw [ha]
    exact (canonical6775 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA500 + difference 3 2) (sourceB500 + difference 2 3) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA500 + difference 3 2) (sourceB500 + difference 2 3) sourceC500) = raw8800 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw8800; decide +kernel
    rw [ha]
    exact (canonical8800 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA500 + difference 3 4) (sourceB500 + difference 4 3) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2280) := by
    have ha : (tripleCharges (sourceA500 + difference 3 4) (sourceB500 + difference 4 3) sourceC500) = raw8600 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw8600; decide +kernel
    rw [ha]
    exact (canonical8600 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA500 + difference 3 5) (sourceB500 + difference 5 3) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA500 + difference 3 5) (sourceB500 + difference 5 3) sourceC500) = raw8801 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw8801; decide +kernel
    rw [ha]
    exact (canonical8801 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA500 + difference 4 0) (sourceB500 + difference 0 4) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3224) := by
    have ha : (tripleCharges (sourceA500 + difference 4 0) (sourceB500 + difference 0 4) sourceC500) = raw7081 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw7081; decide +kernel
    rw [ha]
    exact (canonical7081 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA500 + difference 4 1) (sourceB500 + difference 1 4) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA500 + difference 4 1) (sourceB500 + difference 1 4) sourceC500) = raw6428 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw6428; decide +kernel
    rw [ha]
    exact (canonical6428 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA500 + difference 4 2) (sourceB500 + difference 2 4) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA500 + difference 4 2) (sourceB500 + difference 2 4) sourceC500) = raw7082 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw7082; decide +kernel
    rw [ha]
    exact (canonical7082 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA500 + difference 4 3) (sourceB500 + difference 3 4) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA500 + difference 4 3) (sourceB500 + difference 3 4) sourceC500) = raw6419 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw6419; decide +kernel
    rw [ha]
    exact (canonical6419 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA500 + difference 4 5) (sourceB500 + difference 5 4) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA500 + difference 4 5) (sourceB500 + difference 5 4) sourceC500) = raw7083 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw7083; decide +kernel
    rw [ha]
    exact (canonical7083 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA500 + difference 5 0) (sourceB500 + difference 0 5) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA500 + difference 5 0) (sourceB500 + difference 0 5) sourceC500) = raw6761 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw6761; decide +kernel
    rw [ha]
    exact (canonical6761 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA500 + difference 5 1) (sourceB500 + difference 1 5) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA500 + difference 5 1) (sourceB500 + difference 1 5) sourceC500) = raw7091 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw7091; decide +kernel
    rw [ha]
    exact (canonical7091 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA500 + difference 5 2) (sourceB500 + difference 2 5) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA500 + difference 5 2) (sourceB500 + difference 2 5) sourceC500) = raw6762 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw6762; decide +kernel
    rw [ha]
    exact (canonical6762 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA500 + difference 5 3) (sourceB500 + difference 3 5) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA500 + difference 5 3) (sourceB500 + difference 3 5) sourceC500) = raw6763 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw6763; decide +kernel
    rw [ha]
    exact (canonical6763 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA500 + difference 5 4) (sourceB500 + difference 4 5) sourceC500) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA500 + difference 5 4) (sourceB500 + difference 4 5) sourceC500) = raw6764 := by
      apply Matrix.ext; unfold tripleCharges sourceA500 sourceB500 sourceC500 difference raw6764; decide +kernel
    rw [ha]
    exact (canonical6764 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA500 sourceB500 sourceC500
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm500, Integer.Sparse.eval]
  linarith only [hs]

def sourceA501 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB501 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC501 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceForm501 : Integer.Sparse Master := [(Sum.inr 4582, 1), (Sum.inr 4584, 1), (Sum.inr 4585, 1), (Sum.inr 4603, 2), (Sum.inr 4992, 1), (Sum.inr 5001, 2), (Sum.inr 5011, 1), (Sum.inr 5016, 2), (Sum.inr 5145, 2), (Sum.inr 5190, 2), (Sum.inr 5199, 2), (Sum.inr 5250, 1), (Sum.inr 5252, 1), (Sum.inr 5259, 2), (Sum.inr 5270, 1), (Sum.inr 5281, 1), (Sum.inr 5290, 2), (Sum.inr 5429, 1), (Sum.inr 5439, 1), (Sum.inr 5446, 2), (Sum.inr 5450, 1)]

theorem sourceEq501 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm501 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA501 + difference 0 1) (sourceB501 + difference 1 0) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA501 + difference 0 1) (sourceB501 + difference 1 0) sourceC501) = raw8802 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8802; decide +kernel
    rw [ha]
    exact (canonical8802 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA501 + difference 0 2) (sourceB501 + difference 2 0) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA501 + difference 0 2) (sourceB501 + difference 2 0) sourceC501) = raw8803 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8803; decide +kernel
    rw [ha]
    exact (canonical8803 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA501 + difference 0 3) (sourceB501 + difference 3 0) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA501 + difference 0 3) (sourceB501 + difference 3 0) sourceC501) = raw8804 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8804; decide +kernel
    rw [ha]
    exact (canonical8804 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA501 + difference 0 4) (sourceB501 + difference 4 0) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA501 + difference 0 4) (sourceB501 + difference 4 0) sourceC501) = raw8805 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8805; decide +kernel
    rw [ha]
    exact (canonical8805 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA501 + difference 0 5) (sourceB501 + difference 5 0) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA501 + difference 0 5) (sourceB501 + difference 5 0) sourceC501) = raw8806 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8806; decide +kernel
    rw [ha]
    exact (canonical8806 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA501 + difference 1 0) (sourceB501 + difference 0 1) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4582) := by
    have ha : (tripleCharges (sourceA501 + difference 1 0) (sourceB501 + difference 0 1) sourceC501) = raw8807 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8807; decide +kernel
    rw [ha]
    exact (canonical8807 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA501 + difference 1 2) (sourceB501 + difference 2 1) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5190) := by
    have ha : (tripleCharges (sourceA501 + difference 1 2) (sourceB501 + difference 2 1) sourceC501) = raw8808 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8808; decide +kernel
    rw [ha]
    exact (canonical8808 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA501 + difference 1 3) (sourceB501 + difference 3 1) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5190) := by
    have ha : (tripleCharges (sourceA501 + difference 1 3) (sourceB501 + difference 3 1) sourceC501) = raw8809 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8809; decide +kernel
    rw [ha]
    exact (canonical8809 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA501 + difference 1 4) (sourceB501 + difference 4 1) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA501 + difference 1 4) (sourceB501 + difference 4 1) sourceC501) = raw8810 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8810; decide +kernel
    rw [ha]
    exact (canonical8810 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA501 + difference 1 5) (sourceB501 + difference 5 1) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA501 + difference 1 5) (sourceB501 + difference 5 1) sourceC501) = raw8811 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8811; decide +kernel
    rw [ha]
    exact (canonical8811 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA501 + difference 2 0) (sourceB501 + difference 0 2) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA501 + difference 2 0) (sourceB501 + difference 0 2) sourceC501) = raw8812 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8812; decide +kernel
    rw [ha]
    exact (canonical8812 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA501 + difference 2 1) (sourceB501 + difference 1 2) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA501 + difference 2 1) (sourceB501 + difference 1 2) sourceC501) = raw8813 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8813; decide +kernel
    rw [ha]
    exact (canonical8813 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA501 + difference 2 3) (sourceB501 + difference 3 2) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA501 + difference 2 3) (sourceB501 + difference 3 2) sourceC501) = raw8814 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8814; decide +kernel
    rw [ha]
    exact (canonical8814 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA501 + difference 2 4) (sourceB501 + difference 4 2) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA501 + difference 2 4) (sourceB501 + difference 4 2) sourceC501) = raw8815 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8815; decide +kernel
    rw [ha]
    exact (canonical8815 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA501 + difference 2 5) (sourceB501 + difference 5 2) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA501 + difference 2 5) (sourceB501 + difference 5 2) sourceC501) = raw8816 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8816; decide +kernel
    rw [ha]
    exact (canonical8816 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA501 + difference 3 0) (sourceB501 + difference 0 3) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA501 + difference 3 0) (sourceB501 + difference 0 3) sourceC501) = raw8817 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8817; decide +kernel
    rw [ha]
    exact (canonical8817 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA501 + difference 3 1) (sourceB501 + difference 1 3) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA501 + difference 3 1) (sourceB501 + difference 1 3) sourceC501) = raw8818 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8818; decide +kernel
    rw [ha]
    exact (canonical8818 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA501 + difference 3 2) (sourceB501 + difference 2 3) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5199) := by
    have ha : (tripleCharges (sourceA501 + difference 3 2) (sourceB501 + difference 2 3) sourceC501) = raw8819 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8819; decide +kernel
    rw [ha]
    exact (canonical8819 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA501 + difference 3 4) (sourceB501 + difference 4 3) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA501 + difference 3 4) (sourceB501 + difference 4 3) sourceC501) = raw8820 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8820; decide +kernel
    rw [ha]
    exact (canonical8820 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA501 + difference 3 5) (sourceB501 + difference 5 3) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA501 + difference 3 5) (sourceB501 + difference 5 3) sourceC501) = raw8821 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8821; decide +kernel
    rw [ha]
    exact (canonical8821 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA501 + difference 4 0) (sourceB501 + difference 0 4) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4585) := by
    have ha : (tripleCharges (sourceA501 + difference 4 0) (sourceB501 + difference 0 4) sourceC501) = raw8822 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8822; decide +kernel
    rw [ha]
    exact (canonical8822 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA501 + difference 4 1) (sourceB501 + difference 1 4) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5011) := by
    have ha : (tripleCharges (sourceA501 + difference 4 1) (sourceB501 + difference 1 4) sourceC501) = raw8823 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8823; decide +kernel
    rw [ha]
    exact (canonical8823 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA501 + difference 4 2) (sourceB501 + difference 2 4) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5016) := by
    have ha : (tripleCharges (sourceA501 + difference 4 2) (sourceB501 + difference 2 4) sourceC501) = raw8824 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8824; decide +kernel
    rw [ha]
    exact (canonical8824 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA501 + difference 4 3) (sourceB501 + difference 3 4) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5016) := by
    have ha : (tripleCharges (sourceA501 + difference 4 3) (sourceB501 + difference 3 4) sourceC501) = raw8825 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8825; decide +kernel
    rw [ha]
    exact (canonical8825 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA501 + difference 4 5) (sourceB501 + difference 5 4) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA501 + difference 4 5) (sourceB501 + difference 5 4) sourceC501) = raw8826 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8826; decide +kernel
    rw [ha]
    exact (canonical8826 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA501 + difference 5 0) (sourceB501 + difference 0 5) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4584) := by
    have ha : (tripleCharges (sourceA501 + difference 5 0) (sourceB501 + difference 0 5) sourceC501) = raw8827 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8827; decide +kernel
    rw [ha]
    exact (canonical8827 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA501 + difference 5 1) (sourceB501 + difference 1 5) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4992) := by
    have ha : (tripleCharges (sourceA501 + difference 5 1) (sourceB501 + difference 1 5) sourceC501) = raw8828 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8828; decide +kernel
    rw [ha]
    exact (canonical8828 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA501 + difference 5 2) (sourceB501 + difference 2 5) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5001) := by
    have ha : (tripleCharges (sourceA501 + difference 5 2) (sourceB501 + difference 2 5) sourceC501) = raw8829 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8829; decide +kernel
    rw [ha]
    exact (canonical8829 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA501 + difference 5 3) (sourceB501 + difference 3 5) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5001) := by
    have ha : (tripleCharges (sourceA501 + difference 5 3) (sourceB501 + difference 3 5) sourceC501) = raw8830 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8830; decide +kernel
    rw [ha]
    exact (canonical8830 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA501 + difference 5 4) (sourceB501 + difference 4 5) sourceC501) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA501 + difference 5 4) (sourceB501 + difference 4 5) sourceC501) = raw8831 := by
      apply Matrix.ext; unfold tripleCharges sourceA501 sourceB501 sourceC501 difference raw8831; decide +kernel
    rw [ha]
    exact (canonical8831 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA501 sourceB501 sourceC501
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm501, Integer.Sparse.eval]
  linarith only [hs]

def sourceA502 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB502 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC502 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceForm502 : Integer.Sparse Master := [(Sum.inr 1201, 1), (Sum.inr 1203, 1), (Sum.inr 1204, 1), (Sum.inr 1237, 2), (Sum.inr 2378, 1), (Sum.inr 2386, 2), (Sum.inr 2712, 1), (Sum.inr 2854, 2), (Sum.inr 2855, 2), (Sum.inr 2882, 2), (Sum.inr 2912, 1), (Sum.inr 2925, 2), (Sum.inr 3065, 1), (Sum.inr 3074, 1), (Sum.inr 3075, 1), (Sum.inr 3088, 2), (Sum.inr 3099, 2), (Sum.inr 3954, 1), (Sum.inr 3959, 2), (Sum.inr 4012, 1), (Sum.inr 4029, 1)]

theorem sourceEq502 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm502 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA502 + difference 0 1) (sourceB502 + difference 1 0) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA502 + difference 0 1) (sourceB502 + difference 1 0) sourceC502) = raw8832 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8832; decide +kernel
    rw [ha]
    exact (canonical8832 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA502 + difference 0 2) (sourceB502 + difference 2 0) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA502 + difference 0 2) (sourceB502 + difference 2 0) sourceC502) = raw8833 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8833; decide +kernel
    rw [ha]
    exact (canonical8833 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA502 + difference 0 3) (sourceB502 + difference 3 0) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA502 + difference 0 3) (sourceB502 + difference 3 0) sourceC502) = raw8834 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8834; decide +kernel
    rw [ha]
    exact (canonical8834 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA502 + difference 0 4) (sourceB502 + difference 4 0) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA502 + difference 0 4) (sourceB502 + difference 4 0) sourceC502) = raw8835 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8835; decide +kernel
    rw [ha]
    exact (canonical8835 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA502 + difference 0 5) (sourceB502 + difference 5 0) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA502 + difference 0 5) (sourceB502 + difference 5 0) sourceC502) = raw8836 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8836; decide +kernel
    rw [ha]
    exact (canonical8836 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA502 + difference 1 0) (sourceB502 + difference 0 1) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1201) := by
    have ha : (tripleCharges (sourceA502 + difference 1 0) (sourceB502 + difference 0 1) sourceC502) = raw8837 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8837; decide +kernel
    rw [ha]
    exact (canonical8837 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA502 + difference 1 2) (sourceB502 + difference 2 1) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2854) := by
    have ha : (tripleCharges (sourceA502 + difference 1 2) (sourceB502 + difference 2 1) sourceC502) = raw8838 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8838; decide +kernel
    rw [ha]
    exact (canonical8838 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA502 + difference 1 3) (sourceB502 + difference 3 1) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2854) := by
    have ha : (tripleCharges (sourceA502 + difference 1 3) (sourceB502 + difference 3 1) sourceC502) = raw8839 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8839; decide +kernel
    rw [ha]
    exact (canonical8839 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA502 + difference 1 4) (sourceB502 + difference 4 1) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA502 + difference 1 4) (sourceB502 + difference 4 1) sourceC502) = raw8840 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8840; decide +kernel
    rw [ha]
    exact (canonical8840 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA502 + difference 1 5) (sourceB502 + difference 5 1) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA502 + difference 1 5) (sourceB502 + difference 5 1) sourceC502) = raw8841 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8841; decide +kernel
    rw [ha]
    exact (canonical8841 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA502 + difference 2 0) (sourceB502 + difference 0 2) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA502 + difference 2 0) (sourceB502 + difference 0 2) sourceC502) = raw8842 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8842; decide +kernel
    rw [ha]
    exact (canonical8842 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA502 + difference 2 1) (sourceB502 + difference 1 2) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA502 + difference 2 1) (sourceB502 + difference 1 2) sourceC502) = raw8843 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8843; decide +kernel
    rw [ha]
    exact (canonical8843 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA502 + difference 2 3) (sourceB502 + difference 3 2) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA502 + difference 2 3) (sourceB502 + difference 3 2) sourceC502) = raw8844 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8844; decide +kernel
    rw [ha]
    exact (canonical8844 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA502 + difference 2 4) (sourceB502 + difference 4 2) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA502 + difference 2 4) (sourceB502 + difference 4 2) sourceC502) = raw8845 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8845; decide +kernel
    rw [ha]
    exact (canonical8845 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA502 + difference 2 5) (sourceB502 + difference 5 2) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA502 + difference 2 5) (sourceB502 + difference 5 2) sourceC502) = raw8846 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8846; decide +kernel
    rw [ha]
    exact (canonical8846 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA502 + difference 3 0) (sourceB502 + difference 0 3) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA502 + difference 3 0) (sourceB502 + difference 0 3) sourceC502) = raw8847 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8847; decide +kernel
    rw [ha]
    exact (canonical8847 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA502 + difference 3 1) (sourceB502 + difference 1 3) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA502 + difference 3 1) (sourceB502 + difference 1 3) sourceC502) = raw8848 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8848; decide +kernel
    rw [ha]
    exact (canonical8848 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA502 + difference 3 2) (sourceB502 + difference 2 3) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA502 + difference 3 2) (sourceB502 + difference 2 3) sourceC502) = raw8849 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8849; decide +kernel
    rw [ha]
    exact (canonical8849 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA502 + difference 3 4) (sourceB502 + difference 4 3) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA502 + difference 3 4) (sourceB502 + difference 4 3) sourceC502) = raw8850 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8850; decide +kernel
    rw [ha]
    exact (canonical8850 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA502 + difference 3 5) (sourceB502 + difference 5 3) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA502 + difference 3 5) (sourceB502 + difference 5 3) sourceC502) = raw8851 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8851; decide +kernel
    rw [ha]
    exact (canonical8851 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA502 + difference 4 0) (sourceB502 + difference 0 4) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1204) := by
    have ha : (tripleCharges (sourceA502 + difference 4 0) (sourceB502 + difference 0 4) sourceC502) = raw8852 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8852; decide +kernel
    rw [ha]
    exact (canonical8852 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA502 + difference 4 1) (sourceB502 + difference 1 4) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2912) := by
    have ha : (tripleCharges (sourceA502 + difference 4 1) (sourceB502 + difference 1 4) sourceC502) = raw8853 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8853; decide +kernel
    rw [ha]
    exact (canonical8853 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA502 + difference 4 2) (sourceB502 + difference 2 4) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2855) := by
    have ha : (tripleCharges (sourceA502 + difference 4 2) (sourceB502 + difference 2 4) sourceC502) = raw8854 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8854; decide +kernel
    rw [ha]
    exact (canonical8854 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA502 + difference 4 3) (sourceB502 + difference 3 4) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2855) := by
    have ha : (tripleCharges (sourceA502 + difference 4 3) (sourceB502 + difference 3 4) sourceC502) = raw8855 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8855; decide +kernel
    rw [ha]
    exact (canonical8855 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA502 + difference 4 5) (sourceB502 + difference 5 4) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA502 + difference 4 5) (sourceB502 + difference 5 4) sourceC502) = raw8856 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8856; decide +kernel
    rw [ha]
    exact (canonical8856 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA502 + difference 5 0) (sourceB502 + difference 0 5) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1203) := by
    have ha : (tripleCharges (sourceA502 + difference 5 0) (sourceB502 + difference 0 5) sourceC502) = raw8857 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8857; decide +kernel
    rw [ha]
    exact (canonical8857 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA502 + difference 5 1) (sourceB502 + difference 1 5) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2378) := by
    have ha : (tripleCharges (sourceA502 + difference 5 1) (sourceB502 + difference 1 5) sourceC502) = raw8858 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8858; decide +kernel
    rw [ha]
    exact (canonical8858 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA502 + difference 5 2) (sourceB502 + difference 2 5) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2386) := by
    have ha : (tripleCharges (sourceA502 + difference 5 2) (sourceB502 + difference 2 5) sourceC502) = raw8859 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8859; decide +kernel
    rw [ha]
    exact (canonical8859 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA502 + difference 5 3) (sourceB502 + difference 3 5) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2386) := by
    have ha : (tripleCharges (sourceA502 + difference 5 3) (sourceB502 + difference 3 5) sourceC502) = raw8860 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8860; decide +kernel
    rw [ha]
    exact (canonical8860 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA502 + difference 5 4) (sourceB502 + difference 4 5) sourceC502) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA502 + difference 5 4) (sourceB502 + difference 4 5) sourceC502) = raw8861 := by
      apply Matrix.ext; unfold tripleCharges sourceA502 sourceB502 sourceC502 difference raw8861; decide +kernel
    rw [ha]
    exact (canonical8861 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA502 sourceB502 sourceC502
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm502, Integer.Sparse.eval]
  linarith only [hs]

def sourceA503 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB503 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC503 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceForm503 : Integer.Sparse Master := [(Sum.inr 2396, 1), (Sum.inr 2397, 1), (Sum.inr 2401, 2), (Sum.inr 2738, 1), (Sum.inr 3282, 1), (Sum.inr 3283, 1), (Sum.inr 3294, 2), (Sum.inr 3350, 1), (Sum.inr 3355, 2), (Sum.inr 3531, 1), (Sum.inr 3543, 1), (Sum.inr 3544, 2), (Sum.inr 3562, 2), (Sum.inr 3568, 2), (Sum.inr 3571, 1), (Sum.inr 3578, 2), (Sum.inr 3581, 2), (Sum.inr 3858, 1), (Sum.inr 3874, 1), (Sum.inr 3884, 2), (Sum.inr 3887, 1)]

theorem sourceEq503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm503 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA503 + difference 0 1) (sourceB503 + difference 1 0) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA503 + difference 0 1) (sourceB503 + difference 1 0) sourceC503) = raw8862 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8862; decide +kernel
    rw [ha]
    exact (canonical8862 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA503 + difference 0 2) (sourceB503 + difference 2 0) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA503 + difference 0 2) (sourceB503 + difference 2 0) sourceC503) = raw8863 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8863; decide +kernel
    rw [ha]
    exact (canonical8863 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA503 + difference 0 3) (sourceB503 + difference 3 0) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA503 + difference 0 3) (sourceB503 + difference 3 0) sourceC503) = raw8864 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8864; decide +kernel
    rw [ha]
    exact (canonical8864 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA503 + difference 0 4) (sourceB503 + difference 4 0) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3858) := by
    have ha : (tripleCharges (sourceA503 + difference 0 4) (sourceB503 + difference 4 0) sourceC503) = raw8865 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8865; decide +kernel
    rw [ha]
    exact (canonical8865 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA503 + difference 0 5) (sourceB503 + difference 5 0) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3887) := by
    have ha : (tripleCharges (sourceA503 + difference 0 5) (sourceB503 + difference 5 0) sourceC503) = raw8866 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8866; decide +kernel
    rw [ha]
    exact (canonical8866 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA503 + difference 1 0) (sourceB503 + difference 0 1) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3282) := by
    have ha : (tripleCharges (sourceA503 + difference 1 0) (sourceB503 + difference 0 1) sourceC503) = raw8867 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8867; decide +kernel
    rw [ha]
    exact (canonical8867 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA503 + difference 1 2) (sourceB503 + difference 2 1) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3568) := by
    have ha : (tripleCharges (sourceA503 + difference 1 2) (sourceB503 + difference 2 1) sourceC503) = raw8868 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8868; decide +kernel
    rw [ha]
    exact (canonical8868 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA503 + difference 1 3) (sourceB503 + difference 3 1) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3568) := by
    have ha : (tripleCharges (sourceA503 + difference 1 3) (sourceB503 + difference 3 1) sourceC503) = raw8869 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8869; decide +kernel
    rw [ha]
    exact (canonical8869 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA503 + difference 1 4) (sourceB503 + difference 4 1) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA503 + difference 1 4) (sourceB503 + difference 4 1) sourceC503) = raw8870 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8870; decide +kernel
    rw [ha]
    exact (canonical8870 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA503 + difference 1 5) (sourceB503 + difference 5 1) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA503 + difference 1 5) (sourceB503 + difference 5 1) sourceC503) = raw8871 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8871; decide +kernel
    rw [ha]
    exact (canonical8871 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA503 + difference 2 0) (sourceB503 + difference 0 2) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA503 + difference 2 0) (sourceB503 + difference 0 2) sourceC503) = raw8872 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8872; decide +kernel
    rw [ha]
    exact (canonical8872 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA503 + difference 2 1) (sourceB503 + difference 1 2) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA503 + difference 2 1) (sourceB503 + difference 1 2) sourceC503) = raw8873 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8873; decide +kernel
    rw [ha]
    exact (canonical8873 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA503 + difference 2 3) (sourceB503 + difference 3 2) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA503 + difference 2 3) (sourceB503 + difference 3 2) sourceC503) = raw8874 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8874; decide +kernel
    rw [ha]
    exact (canonical8874 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA503 + difference 2 4) (sourceB503 + difference 4 2) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA503 + difference 2 4) (sourceB503 + difference 4 2) sourceC503) = raw8875 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8875; decide +kernel
    rw [ha]
    exact (canonical8875 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA503 + difference 2 5) (sourceB503 + difference 5 2) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA503 + difference 2 5) (sourceB503 + difference 5 2) sourceC503) = raw8876 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8876; decide +kernel
    rw [ha]
    exact (canonical8876 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA503 + difference 3 0) (sourceB503 + difference 0 3) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA503 + difference 3 0) (sourceB503 + difference 0 3) sourceC503) = raw8877 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8877; decide +kernel
    rw [ha]
    exact (canonical8877 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA503 + difference 3 1) (sourceB503 + difference 1 3) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA503 + difference 3 1) (sourceB503 + difference 1 3) sourceC503) = raw8878 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8878; decide +kernel
    rw [ha]
    exact (canonical8878 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA503 + difference 3 2) (sourceB503 + difference 2 3) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3578) := by
    have ha : (tripleCharges (sourceA503 + difference 3 2) (sourceB503 + difference 2 3) sourceC503) = raw8879 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8879; decide +kernel
    rw [ha]
    exact (canonical8879 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA503 + difference 3 4) (sourceB503 + difference 4 3) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA503 + difference 3 4) (sourceB503 + difference 4 3) sourceC503) = raw8880 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8880; decide +kernel
    rw [ha]
    exact (canonical8880 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA503 + difference 3 5) (sourceB503 + difference 5 3) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA503 + difference 3 5) (sourceB503 + difference 5 3) sourceC503) = raw8881 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8881; decide +kernel
    rw [ha]
    exact (canonical8881 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA503 + difference 4 0) (sourceB503 + difference 0 4) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2397) := by
    have ha : (tripleCharges (sourceA503 + difference 4 0) (sourceB503 + difference 0 4) sourceC503) = raw8882 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8882; decide +kernel
    rw [ha]
    exact (canonical8882 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA503 + difference 4 1) (sourceB503 + difference 1 4) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2396) := by
    have ha : (tripleCharges (sourceA503 + difference 4 1) (sourceB503 + difference 1 4) sourceC503) = raw8883 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8883; decide +kernel
    rw [ha]
    exact (canonical8883 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA503 + difference 4 2) (sourceB503 + difference 2 4) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2401) := by
    have ha : (tripleCharges (sourceA503 + difference 4 2) (sourceB503 + difference 2 4) sourceC503) = raw8884 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8884; decide +kernel
    rw [ha]
    exact (canonical8884 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA503 + difference 4 3) (sourceB503 + difference 3 4) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2401) := by
    have ha : (tripleCharges (sourceA503 + difference 4 3) (sourceB503 + difference 3 4) sourceC503) = raw8885 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8885; decide +kernel
    rw [ha]
    exact (canonical8885 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA503 + difference 4 5) (sourceB503 + difference 5 4) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA503 + difference 4 5) (sourceB503 + difference 5 4) sourceC503) = raw8886 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8886; decide +kernel
    rw [ha]
    exact (canonical8886 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA503 + difference 5 0) (sourceB503 + difference 0 5) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3283) := by
    have ha : (tripleCharges (sourceA503 + difference 5 0) (sourceB503 + difference 0 5) sourceC503) = raw8887 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8887; decide +kernel
    rw [ha]
    exact (canonical8887 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA503 + difference 5 1) (sourceB503 + difference 1 5) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3350) := by
    have ha : (tripleCharges (sourceA503 + difference 5 1) (sourceB503 + difference 1 5) sourceC503) = raw8888 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8888; decide +kernel
    rw [ha]
    exact (canonical8888 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA503 + difference 5 2) (sourceB503 + difference 2 5) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3355) := by
    have ha : (tripleCharges (sourceA503 + difference 5 2) (sourceB503 + difference 2 5) sourceC503) = raw8889 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8889; decide +kernel
    rw [ha]
    exact (canonical8889 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA503 + difference 5 3) (sourceB503 + difference 3 5) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3355) := by
    have ha : (tripleCharges (sourceA503 + difference 5 3) (sourceB503 + difference 3 5) sourceC503) = raw8890 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8890; decide +kernel
    rw [ha]
    exact (canonical8890 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA503 + difference 5 4) (sourceB503 + difference 4 5) sourceC503) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA503 + difference 5 4) (sourceB503 + difference 4 5) sourceC503) = raw8891 := by
      apply Matrix.ext; unfold tripleCharges sourceA503 sourceB503 sourceC503 difference raw8891; decide +kernel
    rw [ha]
    exact (canonical8891 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA503 sourceB503 sourceC503
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm503, Integer.Sparse.eval]
  linarith only [hs]

def sourceA504 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB504 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC504 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceForm504 : Integer.Sparse Master := [(Sum.inr 2751, 1), (Sum.inr 3846, 1), (Sum.inr 3881, 2), (Sum.inr 3902, 1), (Sum.inr 3910, 1), (Sum.inr 4091, -1)]

theorem sourceEq504 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm504 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA504 + difference 0 0) (sourceB504 + difference 0 0) sourceC504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA504 + difference 0 0) (sourceB504 + difference 0 0) sourceC504) = raw8892 := by
      apply Matrix.ext; unfold tripleCharges sourceA504 sourceB504 sourceC504 difference raw8892; decide +kernel
    rw [ha]
    exact (canonical8892 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA504 + difference 0 1) (sourceB504 + difference 1 0) sourceC504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA504 + difference 0 1) (sourceB504 + difference 1 0) sourceC504) = raw8893 := by
      apply Matrix.ext; unfold tripleCharges sourceA504 sourceB504 sourceC504 difference raw8893; decide +kernel
    rw [ha]
    exact (canonical8893 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA504 + difference 0 2) (sourceB504 + difference 2 0) sourceC504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA504 + difference 0 2) (sourceB504 + difference 2 0) sourceC504) = raw8894 := by
      apply Matrix.ext; unfold tripleCharges sourceA504 sourceB504 sourceC504 difference raw8894; decide +kernel
    rw [ha]
    exact (canonical8894 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA504 + difference 0 3) (sourceB504 + difference 3 0) sourceC504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA504 + difference 0 3) (sourceB504 + difference 3 0) sourceC504) = raw8895 := by
      apply Matrix.ext; unfold tripleCharges sourceA504 sourceB504 sourceC504 difference raw8895; decide +kernel
    rw [ha]
    exact (canonical8895 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA504 + difference 0 4) (sourceB504 + difference 4 0) sourceC504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA504 + difference 0 4) (sourceB504 + difference 4 0) sourceC504) = raw8896 := by
      apply Matrix.ext; unfold tripleCharges sourceA504 sourceB504 sourceC504 difference raw8896; decide +kernel
    rw [ha]
    exact (canonical8896 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA504 + difference 0 5) (sourceB504 + difference 5 0) sourceC504) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA504 + difference 0 5) (sourceB504 + difference 5 0) sourceC504) = raw8897 := by
      apply Matrix.ext; unfold tripleCharges sourceA504 sourceB504 sourceC504 difference raw8897; decide +kernel
    rw [ha]
    exact (canonical8897 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA504 + sourceB504) sourceC504) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA504 + sourceB504) sourceC504) = raw8898 := by
      apply Matrix.ext; unfold doubleCharges sourceA504 sourceB504 sourceC504 raw8898; decide +kernel
    rw [ha]
    exact (canonical8898 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA504 sourceB504 sourceC504
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm504, Integer.Sparse.eval]
  linarith only [hs]

def sourceA505 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB505 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC505 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceForm505 : Integer.Sparse Master := [(Sum.inr 1247, 1), (Sum.inr 1249, 1), (Sum.inr 1253, 1), (Sum.inr 1262, 2), (Sum.inr 2751, 1), (Sum.inr 4091, -1)]

theorem sourceEq505 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm505 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA505 + difference 0 0) (sourceB505 + difference 0 0) sourceC505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA505 + difference 0 0) (sourceB505 + difference 0 0) sourceC505) = raw8892 := by
      apply Matrix.ext; unfold tripleCharges sourceA505 sourceB505 sourceC505 difference raw8892; decide +kernel
    rw [ha]
    exact (canonical8892 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA505 + difference 1 0) (sourceB505 + difference 0 1) sourceC505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1247) := by
    have ha : (tripleCharges (sourceA505 + difference 1 0) (sourceB505 + difference 0 1) sourceC505) = raw8899 := by
      apply Matrix.ext; unfold tripleCharges sourceA505 sourceB505 sourceC505 difference raw8899; decide +kernel
    rw [ha]
    exact (canonical8899 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA505 + difference 2 0) (sourceB505 + difference 0 2) sourceC505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA505 + difference 2 0) (sourceB505 + difference 0 2) sourceC505) = raw8900 := by
      apply Matrix.ext; unfold tripleCharges sourceA505 sourceB505 sourceC505 difference raw8900; decide +kernel
    rw [ha]
    exact (canonical8900 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA505 + difference 3 0) (sourceB505 + difference 0 3) sourceC505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA505 + difference 3 0) (sourceB505 + difference 0 3) sourceC505) = raw8901 := by
      apply Matrix.ext; unfold tripleCharges sourceA505 sourceB505 sourceC505 difference raw8901; decide +kernel
    rw [ha]
    exact (canonical8901 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA505 + difference 4 0) (sourceB505 + difference 0 4) sourceC505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1253) := by
    have ha : (tripleCharges (sourceA505 + difference 4 0) (sourceB505 + difference 0 4) sourceC505) = raw8902 := by
      apply Matrix.ext; unfold tripleCharges sourceA505 sourceB505 sourceC505 difference raw8902; decide +kernel
    rw [ha]
    exact (canonical8902 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA505 + difference 5 0) (sourceB505 + difference 0 5) sourceC505) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1249) := by
    have ha : (tripleCharges (sourceA505 + difference 5 0) (sourceB505 + difference 0 5) sourceC505) = raw8903 := by
      apply Matrix.ext; unfold tripleCharges sourceA505 sourceB505 sourceC505 difference raw8903; decide +kernel
    rw [ha]
    exact (canonical8903 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA505 + sourceB505) sourceC505) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA505 + sourceB505) sourceC505) = raw8898 := by
      apply Matrix.ext; unfold doubleCharges sourceA505 sourceB505 sourceC505 raw8898; decide +kernel
    rw [ha]
    exact (canonical8898 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA505 sourceB505 sourceC505
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm505, Integer.Sparse.eval]
  linarith only [hs]

def sourceA506 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB506 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC506 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceForm506 : Integer.Sparse Master := [(Sum.inr 2562, 1), (Sum.inr 2564, 1), (Sum.inr 2567, 2), (Sum.inr 2751, 1), (Sum.inr 3846, 1), (Sum.inr 4091, -1)]

theorem sourceEq506 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm506 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA506 + difference 0 1) (sourceB506 + difference 1 0) sourceC506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA506 + difference 0 1) (sourceB506 + difference 1 0) sourceC506) = raw8893 := by
      apply Matrix.ext; unfold tripleCharges sourceA506 sourceB506 sourceC506 difference raw8893; decide +kernel
    rw [ha]
    exact (canonical8893 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA506 + difference 1 1) (sourceB506 + difference 1 1) sourceC506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA506 + difference 1 1) (sourceB506 + difference 1 1) sourceC506) = raw8892 := by
      apply Matrix.ext; unfold tripleCharges sourceA506 sourceB506 sourceC506 difference raw8892; decide +kernel
    rw [ha]
    exact (canonical8892 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA506 + difference 2 1) (sourceB506 + difference 1 2) sourceC506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA506 + difference 2 1) (sourceB506 + difference 1 2) sourceC506) = raw8904 := by
      apply Matrix.ext; unfold tripleCharges sourceA506 sourceB506 sourceC506 difference raw8904; decide +kernel
    rw [ha]
    exact (canonical8904 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA506 + difference 3 1) (sourceB506 + difference 1 3) sourceC506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA506 + difference 3 1) (sourceB506 + difference 1 3) sourceC506) = raw8905 := by
      apply Matrix.ext; unfold tripleCharges sourceA506 sourceB506 sourceC506 difference raw8905; decide +kernel
    rw [ha]
    exact (canonical8905 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA506 + difference 4 1) (sourceB506 + difference 1 4) sourceC506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2564) := by
    have ha : (tripleCharges (sourceA506 + difference 4 1) (sourceB506 + difference 1 4) sourceC506) = raw8906 := by
      apply Matrix.ext; unfold tripleCharges sourceA506 sourceB506 sourceC506 difference raw8906; decide +kernel
    rw [ha]
    exact (canonical8906 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA506 + difference 5 1) (sourceB506 + difference 1 5) sourceC506) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2562) := by
    have ha : (tripleCharges (sourceA506 + difference 5 1) (sourceB506 + difference 1 5) sourceC506) = raw8907 := by
      apply Matrix.ext; unfold tripleCharges sourceA506 sourceB506 sourceC506 difference raw8907; decide +kernel
    rw [ha]
    exact (canonical8907 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA506 + sourceB506) sourceC506) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA506 + sourceB506) sourceC506) = raw8898 := by
      apply Matrix.ext; unfold doubleCharges sourceA506 sourceB506 sourceC506 raw8898; decide +kernel
    rw [ha]
    exact (canonical8898 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA506 sourceB506 sourceC506
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm506, Integer.Sparse.eval]
  linarith only [hs]

def sourceA507 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB507 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC507 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceForm507 : Integer.Sparse Master := [(Sum.inr 1262, 1), (Sum.inr 2567, 1), (Sum.inr 2633, 1), (Sum.inr 2723, 1), (Sum.inr 2751, 1), (Sum.inr 2764, 1), (Sum.inr 4091, -1)]

theorem sourceEq507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm507 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA507 + difference 2 0) (sourceB507 + difference 0 2) sourceC507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA507 + difference 2 0) (sourceB507 + difference 0 2) sourceC507) = raw8900 := by
      apply Matrix.ext; unfold tripleCharges sourceA507 sourceB507 sourceC507 difference raw8900; decide +kernel
    rw [ha]
    exact (canonical8900 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA507 + difference 2 1) (sourceB507 + difference 1 2) sourceC507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA507 + difference 2 1) (sourceB507 + difference 1 2) sourceC507) = raw8904 := by
      apply Matrix.ext; unfold tripleCharges sourceA507 sourceB507 sourceC507 difference raw8904; decide +kernel
    rw [ha]
    exact (canonical8904 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA507 + difference 2 2) (sourceB507 + difference 2 2) sourceC507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA507 + difference 2 2) (sourceB507 + difference 2 2) sourceC507) = raw8892 := by
      apply Matrix.ext; unfold tripleCharges sourceA507 sourceB507 sourceC507 difference raw8892; decide +kernel
    rw [ha]
    exact (canonical8892 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA507 + difference 2 3) (sourceB507 + difference 3 2) sourceC507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2633) := by
    have ha : (tripleCharges (sourceA507 + difference 2 3) (sourceB507 + difference 3 2) sourceC507) = raw8908 := by
      apply Matrix.ext; unfold tripleCharges sourceA507 sourceB507 sourceC507 difference raw8908; decide +kernel
    rw [ha]
    exact (canonical8908 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA507 + difference 2 4) (sourceB507 + difference 4 2) sourceC507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA507 + difference 2 4) (sourceB507 + difference 4 2) sourceC507) = raw8909 := by
      apply Matrix.ext; unfold tripleCharges sourceA507 sourceB507 sourceC507 difference raw8909; decide +kernel
    rw [ha]
    exact (canonical8909 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA507 + difference 2 5) (sourceB507 + difference 5 2) sourceC507) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA507 + difference 2 5) (sourceB507 + difference 5 2) sourceC507) = raw8910 := by
      apply Matrix.ext; unfold tripleCharges sourceA507 sourceB507 sourceC507 difference raw8910; decide +kernel
    rw [ha]
    exact (canonical8910 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA507 + sourceB507) sourceC507) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA507 + sourceB507) sourceC507) = raw8898 := by
      apply Matrix.ext; unfold doubleCharges sourceA507 sourceB507 sourceC507 raw8898; decide +kernel
    rw [ha]
    exact (canonical8898 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA507 sourceB507 sourceC507
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm507, Integer.Sparse.eval]
  linarith only [hs]

def sourceA508 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB508 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC508 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceForm508 : Integer.Sparse Master := [(Sum.inr 2622, 1), (Sum.inr 2624, 1), (Sum.inr 2627, 1), (Sum.inr 2633, 1), (Sum.inr 2751, 1), (Sum.inr 3881, 1), (Sum.inr 4091, -1)]

theorem sourceEq508 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm508 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA508 + difference 0 2) (sourceB508 + difference 2 0) sourceC508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA508 + difference 0 2) (sourceB508 + difference 2 0) sourceC508) = raw8894 := by
      apply Matrix.ext; unfold tripleCharges sourceA508 sourceB508 sourceC508 difference raw8894; decide +kernel
    rw [ha]
    exact (canonical8894 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA508 + difference 1 2) (sourceB508 + difference 2 1) sourceC508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2622) := by
    have ha : (tripleCharges (sourceA508 + difference 1 2) (sourceB508 + difference 2 1) sourceC508) = raw8911 := by
      apply Matrix.ext; unfold tripleCharges sourceA508 sourceB508 sourceC508 difference raw8911; decide +kernel
    rw [ha]
    exact (canonical8911 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA508 + difference 2 2) (sourceB508 + difference 2 2) sourceC508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA508 + difference 2 2) (sourceB508 + difference 2 2) sourceC508) = raw8892 := by
      apply Matrix.ext; unfold tripleCharges sourceA508 sourceB508 sourceC508 difference raw8892; decide +kernel
    rw [ha]
    exact (canonical8892 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA508 + difference 3 2) (sourceB508 + difference 2 3) sourceC508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2633) := by
    have ha : (tripleCharges (sourceA508 + difference 3 2) (sourceB508 + difference 2 3) sourceC508) = raw8912 := by
      apply Matrix.ext; unfold tripleCharges sourceA508 sourceB508 sourceC508 difference raw8912; decide +kernel
    rw [ha]
    exact (canonical8912 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA508 + difference 4 2) (sourceB508 + difference 2 4) sourceC508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2627) := by
    have ha : (tripleCharges (sourceA508 + difference 4 2) (sourceB508 + difference 2 4) sourceC508) = raw8913 := by
      apply Matrix.ext; unfold tripleCharges sourceA508 sourceB508 sourceC508 difference raw8913; decide +kernel
    rw [ha]
    exact (canonical8913 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA508 + difference 5 2) (sourceB508 + difference 2 5) sourceC508) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2624) := by
    have ha : (tripleCharges (sourceA508 + difference 5 2) (sourceB508 + difference 2 5) sourceC508) = raw8914 := by
      apply Matrix.ext; unfold tripleCharges sourceA508 sourceB508 sourceC508 difference raw8914; decide +kernel
    rw [ha]
    exact (canonical8914 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA508 + sourceB508) sourceC508) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA508 + sourceB508) sourceC508) = raw8898 := by
      apply Matrix.ext; unfold doubleCharges sourceA508 sourceB508 sourceC508 raw8898; decide +kernel
    rw [ha]
    exact (canonical8898 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA508 sourceB508 sourceC508
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm508, Integer.Sparse.eval]
  linarith only [hs]

def sourceA509 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB509 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceC509 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceForm509 : Integer.Sparse Master := [(Sum.inr 1253, 1), (Sum.inr 2564, 1), (Sum.inr 2627, 2), (Sum.inr 2751, 1), (Sum.inr 2754, 1), (Sum.inr 4091, -1)]

theorem sourceEq509 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm509 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA509 + difference 4 0) (sourceB509 + difference 0 4) sourceC509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1253) := by
    have ha : (tripleCharges (sourceA509 + difference 4 0) (sourceB509 + difference 0 4) sourceC509) = raw8902 := by
      apply Matrix.ext; unfold tripleCharges sourceA509 sourceB509 sourceC509 difference raw8902; decide +kernel
    rw [ha]
    exact (canonical8902 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA509 + difference 4 1) (sourceB509 + difference 1 4) sourceC509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2564) := by
    have ha : (tripleCharges (sourceA509 + difference 4 1) (sourceB509 + difference 1 4) sourceC509) = raw8906 := by
      apply Matrix.ext; unfold tripleCharges sourceA509 sourceB509 sourceC509 difference raw8906; decide +kernel
    rw [ha]
    exact (canonical8906 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA509 + difference 4 2) (sourceB509 + difference 2 4) sourceC509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2627) := by
    have ha : (tripleCharges (sourceA509 + difference 4 2) (sourceB509 + difference 2 4) sourceC509) = raw8913 := by
      apply Matrix.ext; unfold tripleCharges sourceA509 sourceB509 sourceC509 difference raw8913; decide +kernel
    rw [ha]
    exact (canonical8913 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA509 + difference 4 3) (sourceB509 + difference 3 4) sourceC509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2627) := by
    have ha : (tripleCharges (sourceA509 + difference 4 3) (sourceB509 + difference 3 4) sourceC509) = raw8915 := by
      apply Matrix.ext; unfold tripleCharges sourceA509 sourceB509 sourceC509 difference raw8915; decide +kernel
    rw [ha]
    exact (canonical8915 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA509 + difference 4 4) (sourceB509 + difference 4 4) sourceC509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA509 + difference 4 4) (sourceB509 + difference 4 4) sourceC509) = raw8892 := by
      apply Matrix.ext; unfold tripleCharges sourceA509 sourceB509 sourceC509 difference raw8892; decide +kernel
    rw [ha]
    exact (canonical8892 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA509 + difference 4 5) (sourceB509 + difference 5 4) sourceC509) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA509 + difference 4 5) (sourceB509 + difference 5 4) sourceC509) = raw8916 := by
      apply Matrix.ext; unfold tripleCharges sourceA509 sourceB509 sourceC509 difference raw8916; decide +kernel
    rw [ha]
    exact (canonical8916 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA509 + sourceB509) sourceC509) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA509 + sourceB509) sourceC509) = raw8898 := by
      apply Matrix.ext; unfold doubleCharges sourceA509 sourceB509 sourceC509 raw8898; decide +kernel
    rw [ha]
    exact (canonical8898 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA509 sourceB509 sourceC509
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm509, Integer.Sparse.eval]
  linarith only [hs]

def sourceA510 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB510 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC510 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceForm510 : Integer.Sparse Master := [(Sum.inr 4436, 1), (Sum.inr 4437, 1), (Sum.inr 4444, 1), (Sum.inr 4453, 2), (Sum.inr 5064, 1), (Sum.inr 5067, 1), (Sum.inr 5071, 2), (Sum.inr 5145, 2), (Sum.inr 5147, 2), (Sum.inr 5152, 2), (Sum.inr 5164, 2), (Sum.inr 5220, 1), (Sum.inr 5222, 1), (Sum.inr 5229, 2), (Sum.inr 5281, 1), (Sum.inr 5284, 1), (Sum.inr 5289, 2), (Sum.inr 5448, 1), (Sum.inr 5471, 1), (Sum.inr 5473, 2), (Sum.inr 5485, 1)]

theorem sourceEq510 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm510 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA510 + difference 0 1) (sourceB510 + difference 1 0) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA510 + difference 0 1) (sourceB510 + difference 1 0) sourceC510) = raw8917 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8917; decide +kernel
    rw [ha]
    exact (canonical8917 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA510 + difference 0 2) (sourceB510 + difference 2 0) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA510 + difference 0 2) (sourceB510 + difference 2 0) sourceC510) = raw8918 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8918; decide +kernel
    rw [ha]
    exact (canonical8918 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA510 + difference 0 3) (sourceB510 + difference 3 0) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA510 + difference 0 3) (sourceB510 + difference 3 0) sourceC510) = raw8919 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8919; decide +kernel
    rw [ha]
    exact (canonical8919 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA510 + difference 0 4) (sourceB510 + difference 4 0) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA510 + difference 0 4) (sourceB510 + difference 4 0) sourceC510) = raw8920 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8920; decide +kernel
    rw [ha]
    exact (canonical8920 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA510 + difference 0 5) (sourceB510 + difference 5 0) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA510 + difference 0 5) (sourceB510 + difference 5 0) sourceC510) = raw8921 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8921; decide +kernel
    rw [ha]
    exact (canonical8921 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA510 + difference 1 0) (sourceB510 + difference 0 1) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4436) := by
    have ha : (tripleCharges (sourceA510 + difference 1 0) (sourceB510 + difference 0 1) sourceC510) = raw8922 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8922; decide +kernel
    rw [ha]
    exact (canonical8922 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA510 + difference 1 2) (sourceB510 + difference 2 1) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA510 + difference 1 2) (sourceB510 + difference 2 1) sourceC510) = raw8923 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8923; decide +kernel
    rw [ha]
    exact (canonical8923 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA510 + difference 1 3) (sourceB510 + difference 3 1) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA510 + difference 1 3) (sourceB510 + difference 3 1) sourceC510) = raw8924 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8924; decide +kernel
    rw [ha]
    exact (canonical8924 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA510 + difference 1 4) (sourceB510 + difference 4 1) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5220) := by
    have ha : (tripleCharges (sourceA510 + difference 1 4) (sourceB510 + difference 4 1) sourceC510) = raw8925 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8925; decide +kernel
    rw [ha]
    exact (canonical8925 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA510 + difference 1 5) (sourceB510 + difference 5 1) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA510 + difference 1 5) (sourceB510 + difference 5 1) sourceC510) = raw8926 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8926; decide +kernel
    rw [ha]
    exact (canonical8926 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA510 + difference 2 0) (sourceB510 + difference 0 2) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4453) := by
    have ha : (tripleCharges (sourceA510 + difference 2 0) (sourceB510 + difference 0 2) sourceC510) = raw8927 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8927; decide +kernel
    rw [ha]
    exact (canonical8927 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA510 + difference 2 1) (sourceB510 + difference 1 2) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5071) := by
    have ha : (tripleCharges (sourceA510 + difference 2 1) (sourceB510 + difference 1 2) sourceC510) = raw8928 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8928; decide +kernel
    rw [ha]
    exact (canonical8928 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA510 + difference 2 3) (sourceB510 + difference 3 2) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA510 + difference 2 3) (sourceB510 + difference 3 2) sourceC510) = raw8929 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8929; decide +kernel
    rw [ha]
    exact (canonical8929 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA510 + difference 2 4) (sourceB510 + difference 4 2) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA510 + difference 2 4) (sourceB510 + difference 4 2) sourceC510) = raw8930 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8930; decide +kernel
    rw [ha]
    exact (canonical8930 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA510 + difference 2 5) (sourceB510 + difference 5 2) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA510 + difference 2 5) (sourceB510 + difference 5 2) sourceC510) = raw8931 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8931; decide +kernel
    rw [ha]
    exact (canonical8931 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA510 + difference 3 0) (sourceB510 + difference 0 3) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4453) := by
    have ha : (tripleCharges (sourceA510 + difference 3 0) (sourceB510 + difference 0 3) sourceC510) = raw8932 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8932; decide +kernel
    rw [ha]
    exact (canonical8932 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA510 + difference 3 1) (sourceB510 + difference 1 3) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5071) := by
    have ha : (tripleCharges (sourceA510 + difference 3 1) (sourceB510 + difference 1 3) sourceC510) = raw8933 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8933; decide +kernel
    rw [ha]
    exact (canonical8933 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA510 + difference 3 2) (sourceB510 + difference 2 3) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA510 + difference 3 2) (sourceB510 + difference 2 3) sourceC510) = raw8934 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8934; decide +kernel
    rw [ha]
    exact (canonical8934 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA510 + difference 3 4) (sourceB510 + difference 4 3) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA510 + difference 3 4) (sourceB510 + difference 4 3) sourceC510) = raw8935 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8935; decide +kernel
    rw [ha]
    exact (canonical8935 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA510 + difference 3 5) (sourceB510 + difference 5 3) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA510 + difference 3 5) (sourceB510 + difference 5 3) sourceC510) = raw8936 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8936; decide +kernel
    rw [ha]
    exact (canonical8936 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA510 + difference 4 0) (sourceB510 + difference 0 4) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4444) := by
    have ha : (tripleCharges (sourceA510 + difference 4 0) (sourceB510 + difference 0 4) sourceC510) = raw8937 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8937; decide +kernel
    rw [ha]
    exact (canonical8937 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA510 + difference 4 1) (sourceB510 + difference 1 4) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5067) := by
    have ha : (tripleCharges (sourceA510 + difference 4 1) (sourceB510 + difference 1 4) sourceC510) = raw8938 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8938; decide +kernel
    rw [ha]
    exact (canonical8938 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA510 + difference 4 2) (sourceB510 + difference 2 4) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA510 + difference 4 2) (sourceB510 + difference 2 4) sourceC510) = raw8939 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8939; decide +kernel
    rw [ha]
    exact (canonical8939 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA510 + difference 4 3) (sourceB510 + difference 3 4) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5152) := by
    have ha : (tripleCharges (sourceA510 + difference 4 3) (sourceB510 + difference 3 4) sourceC510) = raw8940 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8940; decide +kernel
    rw [ha]
    exact (canonical8940 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA510 + difference 4 5) (sourceB510 + difference 5 4) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA510 + difference 4 5) (sourceB510 + difference 5 4) sourceC510) = raw8941 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8941; decide +kernel
    rw [ha]
    exact (canonical8941 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA510 + difference 5 0) (sourceB510 + difference 0 5) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4437) := by
    have ha : (tripleCharges (sourceA510 + difference 5 0) (sourceB510 + difference 0 5) sourceC510) = raw8942 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8942; decide +kernel
    rw [ha]
    exact (canonical8942 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA510 + difference 5 1) (sourceB510 + difference 1 5) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5064) := by
    have ha : (tripleCharges (sourceA510 + difference 5 1) (sourceB510 + difference 1 5) sourceC510) = raw8943 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8943; decide +kernel
    rw [ha]
    exact (canonical8943 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA510 + difference 5 2) (sourceB510 + difference 2 5) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA510 + difference 5 2) (sourceB510 + difference 2 5) sourceC510) = raw8944 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8944; decide +kernel
    rw [ha]
    exact (canonical8944 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA510 + difference 5 3) (sourceB510 + difference 3 5) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA510 + difference 5 3) (sourceB510 + difference 3 5) sourceC510) = raw8945 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8945; decide +kernel
    rw [ha]
    exact (canonical8945 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA510 + difference 5 4) (sourceB510 + difference 4 5) sourceC510) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5222) := by
    have ha : (tripleCharges (sourceA510 + difference 5 4) (sourceB510 + difference 4 5) sourceC510) = raw8946 := by
      apply Matrix.ext; unfold tripleCharges sourceA510 sourceB510 sourceC510 difference raw8946; decide +kernel
    rw [ha]
    exact (canonical8946 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA510 sourceB510 sourceC510
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm510, Integer.Sparse.eval]
  linarith only [hs]

def sourceA511 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB511 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC511 : Charge := ![1, 0, 1, 1, -2, -1]
def sourceForm511 : Integer.Sparse Master := [(Sum.inr 1018, 1), (Sum.inr 1019, 1), (Sum.inr 1026, 1), (Sum.inr 1036, 2), (Sum.inr 2469, 1), (Sum.inr 2473, 1), (Sum.inr 2478, 2), (Sum.inr 2567, 2), (Sum.inr 2569, 2), (Sum.inr 2576, 2), (Sum.inr 2591, 2), (Sum.inr 2662, 1), (Sum.inr 2664, 1), (Sum.inr 2673, 2), (Sum.inr 2750, 1), (Sum.inr 2753, 1), (Sum.inr 2763, 2), (Sum.inr 3885, 1), (Sum.inr 3976, 1), (Sum.inr 3995, 2), (Sum.inr 3998, 1)]

theorem sourceEq511 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm511 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA511 + difference 0 1) (sourceB511 + difference 1 0) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3976) := by
    have ha : (tripleCharges (sourceA511 + difference 0 1) (sourceB511 + difference 1 0) sourceC511) = raw8947 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8947; decide +kernel
    rw [ha]
    exact (canonical8947 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA511 + difference 0 2) (sourceB511 + difference 2 0) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA511 + difference 0 2) (sourceB511 + difference 2 0) sourceC511) = raw8948 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8948; decide +kernel
    rw [ha]
    exact (canonical8948 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA511 + difference 0 3) (sourceB511 + difference 3 0) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA511 + difference 0 3) (sourceB511 + difference 3 0) sourceC511) = raw8949 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8949; decide +kernel
    rw [ha]
    exact (canonical8949 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA511 + difference 0 4) (sourceB511 + difference 4 0) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA511 + difference 0 4) (sourceB511 + difference 4 0) sourceC511) = raw8950 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8950; decide +kernel
    rw [ha]
    exact (canonical8950 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA511 + difference 0 5) (sourceB511 + difference 5 0) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA511 + difference 0 5) (sourceB511 + difference 5 0) sourceC511) = raw8951 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8951; decide +kernel
    rw [ha]
    exact (canonical8951 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA511 + difference 1 0) (sourceB511 + difference 0 1) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1018) := by
    have ha : (tripleCharges (sourceA511 + difference 1 0) (sourceB511 + difference 0 1) sourceC511) = raw8952 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8952; decide +kernel
    rw [ha]
    exact (canonical8952 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA511 + difference 1 2) (sourceB511 + difference 2 1) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA511 + difference 1 2) (sourceB511 + difference 2 1) sourceC511) = raw8953 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8953; decide +kernel
    rw [ha]
    exact (canonical8953 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA511 + difference 1 3) (sourceB511 + difference 3 1) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA511 + difference 1 3) (sourceB511 + difference 3 1) sourceC511) = raw8954 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8954; decide +kernel
    rw [ha]
    exact (canonical8954 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA511 + difference 1 4) (sourceB511 + difference 4 1) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2662) := by
    have ha : (tripleCharges (sourceA511 + difference 1 4) (sourceB511 + difference 4 1) sourceC511) = raw8955 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8955; decide +kernel
    rw [ha]
    exact (canonical8955 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA511 + difference 1 5) (sourceB511 + difference 5 1) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA511 + difference 1 5) (sourceB511 + difference 5 1) sourceC511) = raw8956 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8956; decide +kernel
    rw [ha]
    exact (canonical8956 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA511 + difference 2 0) (sourceB511 + difference 0 2) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1036) := by
    have ha : (tripleCharges (sourceA511 + difference 2 0) (sourceB511 + difference 0 2) sourceC511) = raw8957 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8957; decide +kernel
    rw [ha]
    exact (canonical8957 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA511 + difference 2 1) (sourceB511 + difference 1 2) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2478) := by
    have ha : (tripleCharges (sourceA511 + difference 2 1) (sourceB511 + difference 1 2) sourceC511) = raw8958 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8958; decide +kernel
    rw [ha]
    exact (canonical8958 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA511 + difference 2 3) (sourceB511 + difference 3 2) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2591) := by
    have ha : (tripleCharges (sourceA511 + difference 2 3) (sourceB511 + difference 3 2) sourceC511) = raw8959 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8959; decide +kernel
    rw [ha]
    exact (canonical8959 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA511 + difference 2 4) (sourceB511 + difference 4 2) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA511 + difference 2 4) (sourceB511 + difference 4 2) sourceC511) = raw8960 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8960; decide +kernel
    rw [ha]
    exact (canonical8960 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA511 + difference 2 5) (sourceB511 + difference 5 2) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA511 + difference 2 5) (sourceB511 + difference 5 2) sourceC511) = raw8961 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8961; decide +kernel
    rw [ha]
    exact (canonical8961 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA511 + difference 3 0) (sourceB511 + difference 0 3) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1036) := by
    have ha : (tripleCharges (sourceA511 + difference 3 0) (sourceB511 + difference 0 3) sourceC511) = raw8962 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8962; decide +kernel
    rw [ha]
    exact (canonical8962 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA511 + difference 3 1) (sourceB511 + difference 1 3) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2478) := by
    have ha : (tripleCharges (sourceA511 + difference 3 1) (sourceB511 + difference 1 3) sourceC511) = raw8963 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8963; decide +kernel
    rw [ha]
    exact (canonical8963 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA511 + difference 3 2) (sourceB511 + difference 2 3) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2591) := by
    have ha : (tripleCharges (sourceA511 + difference 3 2) (sourceB511 + difference 2 3) sourceC511) = raw8964 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8964; decide +kernel
    rw [ha]
    exact (canonical8964 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA511 + difference 3 4) (sourceB511 + difference 4 3) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA511 + difference 3 4) (sourceB511 + difference 4 3) sourceC511) = raw8965 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8965; decide +kernel
    rw [ha]
    exact (canonical8965 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA511 + difference 3 5) (sourceB511 + difference 5 3) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA511 + difference 3 5) (sourceB511 + difference 5 3) sourceC511) = raw8966 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8966; decide +kernel
    rw [ha]
    exact (canonical8966 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA511 + difference 4 0) (sourceB511 + difference 0 4) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1026) := by
    have ha : (tripleCharges (sourceA511 + difference 4 0) (sourceB511 + difference 0 4) sourceC511) = raw8967 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8967; decide +kernel
    rw [ha]
    exact (canonical8967 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA511 + difference 4 1) (sourceB511 + difference 1 4) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2473) := by
    have ha : (tripleCharges (sourceA511 + difference 4 1) (sourceB511 + difference 1 4) sourceC511) = raw8968 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8968; decide +kernel
    rw [ha]
    exact (canonical8968 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA511 + difference 4 2) (sourceB511 + difference 2 4) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2576) := by
    have ha : (tripleCharges (sourceA511 + difference 4 2) (sourceB511 + difference 2 4) sourceC511) = raw8969 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8969; decide +kernel
    rw [ha]
    exact (canonical8969 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA511 + difference 4 3) (sourceB511 + difference 3 4) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2576) := by
    have ha : (tripleCharges (sourceA511 + difference 4 3) (sourceB511 + difference 3 4) sourceC511) = raw8970 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8970; decide +kernel
    rw [ha]
    exact (canonical8970 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA511 + difference 4 5) (sourceB511 + difference 5 4) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA511 + difference 4 5) (sourceB511 + difference 5 4) sourceC511) = raw8971 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8971; decide +kernel
    rw [ha]
    exact (canonical8971 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA511 + difference 5 0) (sourceB511 + difference 0 5) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1019) := by
    have ha : (tripleCharges (sourceA511 + difference 5 0) (sourceB511 + difference 0 5) sourceC511) = raw8972 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8972; decide +kernel
    rw [ha]
    exact (canonical8972 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA511 + difference 5 1) (sourceB511 + difference 1 5) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2469) := by
    have ha : (tripleCharges (sourceA511 + difference 5 1) (sourceB511 + difference 1 5) sourceC511) = raw8973 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8973; decide +kernel
    rw [ha]
    exact (canonical8973 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA511 + difference 5 2) (sourceB511 + difference 2 5) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2569) := by
    have ha : (tripleCharges (sourceA511 + difference 5 2) (sourceB511 + difference 2 5) sourceC511) = raw8974 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8974; decide +kernel
    rw [ha]
    exact (canonical8974 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA511 + difference 5 3) (sourceB511 + difference 3 5) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2569) := by
    have ha : (tripleCharges (sourceA511 + difference 5 3) (sourceB511 + difference 3 5) sourceC511) = raw8975 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8975; decide +kernel
    rw [ha]
    exact (canonical8975 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA511 + difference 5 4) (sourceB511 + difference 4 5) sourceC511) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA511 + difference 5 4) (sourceB511 + difference 4 5) sourceC511) = raw8976 := by
      apply Matrix.ext; unfold tripleCharges sourceA511 sourceB511 sourceC511 difference raw8976; decide +kernel
    rw [ha]
    exact (canonical8976 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA511 sourceB511 sourceC511
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm511, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
