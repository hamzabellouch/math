import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical60

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA384 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB384 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC384 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceForm384 : Integer.Sparse Master := [(Sum.inr 1248, 1), (Sum.inr 2623, 2), (Sum.inr 2710, 1), (Sum.inr 2745, 1), (Sum.inr 2750, 1), (Sum.inr 4091, -1)]

theorem sourceEq384 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm384 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA384 + difference 1 0) (sourceB384 + difference 0 1) sourceC384) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1248) := by
    have ha : (tripleCharges (sourceA384 + difference 1 0) (sourceB384 + difference 0 1) sourceC384) = raw7388 := by
      apply Matrix.ext; unfold tripleCharges sourceA384 sourceB384 sourceC384 difference raw7388; decide +kernel
    rw [ha]
    exact (canonical7388 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA384 + difference 1 1) (sourceB384 + difference 1 1) sourceC384) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA384 + difference 1 1) (sourceB384 + difference 1 1) sourceC384) = raw7381 := by
      apply Matrix.ext; unfold tripleCharges sourceA384 sourceB384 sourceC384 difference raw7381; decide +kernel
    rw [ha]
    exact (canonical7381 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA384 + difference 1 2) (sourceB384 + difference 2 1) sourceC384) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2623) := by
    have ha : (tripleCharges (sourceA384 + difference 1 2) (sourceB384 + difference 2 1) sourceC384) = raw7393 := by
      apply Matrix.ext; unfold tripleCharges sourceA384 sourceB384 sourceC384 difference raw7393; decide +kernel
    rw [ha]
    exact (canonical7393 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA384 + difference 1 3) (sourceB384 + difference 3 1) sourceC384) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2623) := by
    have ha : (tripleCharges (sourceA384 + difference 1 3) (sourceB384 + difference 3 1) sourceC384) = raw7394 := by
      apply Matrix.ext; unfold tripleCharges sourceA384 sourceB384 sourceC384 difference raw7394; decide +kernel
    rw [ha]
    exact (canonical7394 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA384 + difference 1 4) (sourceB384 + difference 4 1) sourceC384) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2745) := by
    have ha : (tripleCharges (sourceA384 + difference 1 4) (sourceB384 + difference 4 1) sourceC384) = raw7395 := by
      apply Matrix.ext; unfold tripleCharges sourceA384 sourceB384 sourceC384 difference raw7395; decide +kernel
    rw [ha]
    exact (canonical7395 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA384 + difference 1 5) (sourceB384 + difference 5 1) sourceC384) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA384 + difference 1 5) (sourceB384 + difference 5 1) sourceC384) = raw7396 := by
      apply Matrix.ext; unfold tripleCharges sourceA384 sourceB384 sourceC384 difference raw7396; decide +kernel
    rw [ha]
    exact (canonical7396 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA384 + sourceB384) sourceC384) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA384 + sourceB384) sourceC384) = raw7387 := by
      apply Matrix.ext; unfold doubleCharges sourceA384 sourceB384 sourceC384 raw7387; decide +kernel
    rw [ha]
    exact (canonical7387 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA384 sourceB384 sourceC384
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm384, Integer.Sparse.eval]
  linarith only [hs]

def sourceA385 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB385 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC385 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceForm385 : Integer.Sparse Master := [(Sum.inr 2471, 1), (Sum.inr 2473, 1), (Sum.inr 2483, 2), (Sum.inr 2710, 1), (Sum.inr 3801, 1), (Sum.inr 4091, -1)]

theorem sourceEq385 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm385 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA385 + difference 0 1) (sourceB385 + difference 1 0) sourceC385) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA385 + difference 0 1) (sourceB385 + difference 1 0) sourceC385) = raw7382 := by
      apply Matrix.ext; unfold tripleCharges sourceA385 sourceB385 sourceC385 difference raw7382; decide +kernel
    rw [ha]
    exact (canonical7382 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA385 + difference 1 1) (sourceB385 + difference 1 1) sourceC385) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA385 + difference 1 1) (sourceB385 + difference 1 1) sourceC385) = raw7381 := by
      apply Matrix.ext; unfold tripleCharges sourceA385 sourceB385 sourceC385 difference raw7381; decide +kernel
    rw [ha]
    exact (canonical7381 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA385 + difference 2 1) (sourceB385 + difference 1 2) sourceC385) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA385 + difference 2 1) (sourceB385 + difference 1 2) sourceC385) = raw7397 := by
      apply Matrix.ext; unfold tripleCharges sourceA385 sourceB385 sourceC385 difference raw7397; decide +kernel
    rw [ha]
    exact (canonical7397 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA385 + difference 3 1) (sourceB385 + difference 1 3) sourceC385) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA385 + difference 3 1) (sourceB385 + difference 1 3) sourceC385) = raw7398 := by
      apply Matrix.ext; unfold tripleCharges sourceA385 sourceB385 sourceC385 difference raw7398; decide +kernel
    rw [ha]
    exact (canonical7398 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA385 + difference 4 1) (sourceB385 + difference 1 4) sourceC385) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2473) := by
    have ha : (tripleCharges (sourceA385 + difference 4 1) (sourceB385 + difference 1 4) sourceC385) = raw7399 := by
      apply Matrix.ext; unfold tripleCharges sourceA385 sourceB385 sourceC385 difference raw7399; decide +kernel
    rw [ha]
    exact (canonical7399 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA385 + difference 5 1) (sourceB385 + difference 1 5) sourceC385) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA385 + difference 5 1) (sourceB385 + difference 1 5) sourceC385) = raw7400 := by
      apply Matrix.ext; unfold tripleCharges sourceA385 sourceB385 sourceC385 difference raw7400; decide +kernel
    rw [ha]
    exact (canonical7400 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA385 + sourceB385) sourceC385) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA385 + sourceB385) sourceC385) = raw7387 := by
      apply Matrix.ext; unfold doubleCharges sourceA385 sourceB385 sourceC385 raw7387; decide +kernel
    rw [ha]
    exact (canonical7387 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA385 sourceB385 sourceC385
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm385, Integer.Sparse.eval]
  linarith only [hs]

def sourceA386 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB386 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC386 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceForm386 : Integer.Sparse Master := [(Sum.inr 1216, 1), (Sum.inr 2483, 1), (Sum.inr 2617, 1), (Sum.inr 2710, 2), (Sum.inr 2721, 1), (Sum.inr 4091, -1)]

theorem sourceEq386 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm386 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA386 + difference 2 0) (sourceB386 + difference 0 2) sourceC386) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA386 + difference 2 0) (sourceB386 + difference 0 2) sourceC386) = raw7389 := by
      apply Matrix.ext; unfold tripleCharges sourceA386 sourceB386 sourceC386 difference raw7389; decide +kernel
    rw [ha]
    exact (canonical7389 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA386 + difference 2 1) (sourceB386 + difference 1 2) sourceC386) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA386 + difference 2 1) (sourceB386 + difference 1 2) sourceC386) = raw7397 := by
      apply Matrix.ext; unfold tripleCharges sourceA386 sourceB386 sourceC386 difference raw7397; decide +kernel
    rw [ha]
    exact (canonical7397 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA386 + difference 2 2) (sourceB386 + difference 2 2) sourceC386) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA386 + difference 2 2) (sourceB386 + difference 2 2) sourceC386) = raw7381 := by
      apply Matrix.ext; unfold tripleCharges sourceA386 sourceB386 sourceC386 difference raw7381; decide +kernel
    rw [ha]
    exact (canonical7381 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA386 + difference 2 3) (sourceB386 + difference 3 2) sourceC386) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2617) := by
    have ha : (tripleCharges (sourceA386 + difference 2 3) (sourceB386 + difference 3 2) sourceC386) = raw7401 := by
      apply Matrix.ext; unfold tripleCharges sourceA386 sourceB386 sourceC386 difference raw7401; decide +kernel
    rw [ha]
    exact (canonical7401 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA386 + difference 2 4) (sourceB386 + difference 4 2) sourceC386) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA386 + difference 2 4) (sourceB386 + difference 4 2) sourceC386) = raw7402 := by
      apply Matrix.ext; unfold tripleCharges sourceA386 sourceB386 sourceC386 difference raw7402; decide +kernel
    rw [ha]
    exact (canonical7402 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA386 + difference 2 5) (sourceB386 + difference 5 2) sourceC386) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA386 + difference 2 5) (sourceB386 + difference 5 2) sourceC386) = raw7403 := by
      apply Matrix.ext; unfold tripleCharges sourceA386 sourceB386 sourceC386 difference raw7403; decide +kernel
    rw [ha]
    exact (canonical7403 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA386 + sourceB386) sourceC386) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA386 + sourceB386) sourceC386) = raw7387 := by
      apply Matrix.ext; unfold doubleCharges sourceA386 sourceB386 sourceC386 raw7387; decide +kernel
    rw [ha]
    exact (canonical7387 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA386 sourceB386 sourceC386
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm386, Integer.Sparse.eval]
  linarith only [hs]

def sourceA387 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB387 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC387 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceForm387 : Integer.Sparse Master := [(Sum.inr 2611, 1), (Sum.inr 2612, 1), (Sum.inr 2617, 1), (Sum.inr 2623, 1), (Sum.inr 2710, 1), (Sum.inr 3872, 1), (Sum.inr 4091, -1)]

theorem sourceEq387 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm387 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA387 + difference 0 2) (sourceB387 + difference 2 0) sourceC387) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA387 + difference 0 2) (sourceB387 + difference 2 0) sourceC387) = raw7383 := by
      apply Matrix.ext; unfold tripleCharges sourceA387 sourceB387 sourceC387 difference raw7383; decide +kernel
    rw [ha]
    exact (canonical7383 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA387 + difference 1 2) (sourceB387 + difference 2 1) sourceC387) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2623) := by
    have ha : (tripleCharges (sourceA387 + difference 1 2) (sourceB387 + difference 2 1) sourceC387) = raw7393 := by
      apply Matrix.ext; unfold tripleCharges sourceA387 sourceB387 sourceC387 difference raw7393; decide +kernel
    rw [ha]
    exact (canonical7393 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA387 + difference 2 2) (sourceB387 + difference 2 2) sourceC387) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA387 + difference 2 2) (sourceB387 + difference 2 2) sourceC387) = raw7381 := by
      apply Matrix.ext; unfold tripleCharges sourceA387 sourceB387 sourceC387 difference raw7381; decide +kernel
    rw [ha]
    exact (canonical7381 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA387 + difference 3 2) (sourceB387 + difference 2 3) sourceC387) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2617) := by
    have ha : (tripleCharges (sourceA387 + difference 3 2) (sourceB387 + difference 2 3) sourceC387) = raw7404 := by
      apply Matrix.ext; unfold tripleCharges sourceA387 sourceB387 sourceC387 difference raw7404; decide +kernel
    rw [ha]
    exact (canonical7404 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA387 + difference 4 2) (sourceB387 + difference 2 4) sourceC387) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2612) := by
    have ha : (tripleCharges (sourceA387 + difference 4 2) (sourceB387 + difference 2 4) sourceC387) = raw7405 := by
      apply Matrix.ext; unfold tripleCharges sourceA387 sourceB387 sourceC387 difference raw7405; decide +kernel
    rw [ha]
    exact (canonical7405 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA387 + difference 5 2) (sourceB387 + difference 2 5) sourceC387) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2611) := by
    have ha : (tripleCharges (sourceA387 + difference 5 2) (sourceB387 + difference 2 5) sourceC387) = raw7406 := by
      apply Matrix.ext; unfold tripleCharges sourceA387 sourceB387 sourceC387 difference raw7406; decide +kernel
    rw [ha]
    exact (canonical7406 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA387 + sourceB387) sourceC387) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA387 + sourceB387) sourceC387) = raw7387 := by
      apply Matrix.ext; unfold doubleCharges sourceA387 sourceB387 sourceC387 raw7387; decide +kernel
    rw [ha]
    exact (canonical7387 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA387 sourceB387 sourceC387
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm387, Integer.Sparse.eval]
  linarith only [hs]

def sourceA388 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB388 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceC388 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceForm388 : Integer.Sparse Master := [(Sum.inr 2707, 1), (Sum.inr 2710, 3), (Sum.inr 2745, 1), (Sum.inr 3899, 1), (Sum.inr 4091, -1)]

theorem sourceEq388 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm388 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA388 + difference 0 4) (sourceB388 + difference 4 0) sourceC388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3899) := by
    have ha : (tripleCharges (sourceA388 + difference 0 4) (sourceB388 + difference 4 0) sourceC388) = raw7385 := by
      apply Matrix.ext; unfold tripleCharges sourceA388 sourceB388 sourceC388 difference raw7385; decide +kernel
    rw [ha]
    exact (canonical7385 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA388 + difference 1 4) (sourceB388 + difference 4 1) sourceC388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2745) := by
    have ha : (tripleCharges (sourceA388 + difference 1 4) (sourceB388 + difference 4 1) sourceC388) = raw7395 := by
      apply Matrix.ext; unfold tripleCharges sourceA388 sourceB388 sourceC388 difference raw7395; decide +kernel
    rw [ha]
    exact (canonical7395 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA388 + difference 2 4) (sourceB388 + difference 4 2) sourceC388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA388 + difference 2 4) (sourceB388 + difference 4 2) sourceC388) = raw7402 := by
      apply Matrix.ext; unfold tripleCharges sourceA388 sourceB388 sourceC388 difference raw7402; decide +kernel
    rw [ha]
    exact (canonical7402 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA388 + difference 3 4) (sourceB388 + difference 4 3) sourceC388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA388 + difference 3 4) (sourceB388 + difference 4 3) sourceC388) = raw7407 := by
      apply Matrix.ext; unfold tripleCharges sourceA388 sourceB388 sourceC388 difference raw7407; decide +kernel
    rw [ha]
    exact (canonical7407 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA388 + difference 4 4) (sourceB388 + difference 4 4) sourceC388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA388 + difference 4 4) (sourceB388 + difference 4 4) sourceC388) = raw7381 := by
      apply Matrix.ext; unfold tripleCharges sourceA388 sourceB388 sourceC388 difference raw7381; decide +kernel
    rw [ha]
    exact (canonical7381 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA388 + difference 5 4) (sourceB388 + difference 4 5) sourceC388) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2707) := by
    have ha : (tripleCharges (sourceA388 + difference 5 4) (sourceB388 + difference 4 5) sourceC388) = raw7408 := by
      apply Matrix.ext; unfold tripleCharges sourceA388 sourceB388 sourceC388 difference raw7408; decide +kernel
    rw [ha]
    exact (canonical7408 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA388 + sourceB388) sourceC388) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA388 + sourceB388) sourceC388) = raw7387 := by
      apply Matrix.ext; unfold doubleCharges sourceA388 sourceB388 sourceC388 raw7387; decide +kernel
    rw [ha]
    exact (canonical7387 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA388 sourceB388 sourceC388
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm388, Integer.Sparse.eval]
  linarith only [hs]

def sourceA389 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB389 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC389 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceForm389 : Integer.Sparse Master := [(Sum.inr 4391, 1), (Sum.inr 4392, 1), (Sum.inr 4400, 2), (Sum.inr 4439, 1), (Sum.inr 4992, 1), (Sum.inr 4993, 1), (Sum.inr 4999, 2), (Sum.inr 5128, 2), (Sum.inr 5129, 2), (Sum.inr 5138, 2), (Sum.inr 5149, 2), (Sum.inr 5249, 1), (Sum.inr 5252, 1), (Sum.inr 5255, 2), (Sum.inr 5260, 2), (Sum.inr 5281, 1), (Sum.inr 5284, 1), (Sum.inr 5424, 2), (Sum.inr 5429, 1), (Sum.inr 5439, 1), (Sum.inr 5481, 1)]

theorem sourceEq389 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm389 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA389 + difference 0 1) (sourceB389 + difference 1 0) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA389 + difference 0 1) (sourceB389 + difference 1 0) sourceC389) = raw7409 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7409; decide +kernel
    rw [ha]
    exact (canonical7409 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA389 + difference 0 2) (sourceB389 + difference 2 0) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA389 + difference 0 2) (sourceB389 + difference 2 0) sourceC389) = raw7410 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7410; decide +kernel
    rw [ha]
    exact (canonical7410 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA389 + difference 0 3) (sourceB389 + difference 3 0) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA389 + difference 0 3) (sourceB389 + difference 3 0) sourceC389) = raw7411 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7411; decide +kernel
    rw [ha]
    exact (canonical7411 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA389 + difference 0 4) (sourceB389 + difference 4 0) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA389 + difference 0 4) (sourceB389 + difference 4 0) sourceC389) = raw7412 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7412; decide +kernel
    rw [ha]
    exact (canonical7412 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA389 + difference 0 5) (sourceB389 + difference 5 0) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA389 + difference 0 5) (sourceB389 + difference 5 0) sourceC389) = raw7413 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7413; decide +kernel
    rw [ha]
    exact (canonical7413 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA389 + difference 1 0) (sourceB389 + difference 0 1) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA389 + difference 1 0) (sourceB389 + difference 0 1) sourceC389) = raw7414 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7414; decide +kernel
    rw [ha]
    exact (canonical7414 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA389 + difference 1 2) (sourceB389 + difference 2 1) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA389 + difference 1 2) (sourceB389 + difference 2 1) sourceC389) = raw7415 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7415; decide +kernel
    rw [ha]
    exact (canonical7415 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA389 + difference 1 3) (sourceB389 + difference 3 1) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA389 + difference 1 3) (sourceB389 + difference 3 1) sourceC389) = raw7416 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7416; decide +kernel
    rw [ha]
    exact (canonical7416 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA389 + difference 1 4) (sourceB389 + difference 4 1) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA389 + difference 1 4) (sourceB389 + difference 4 1) sourceC389) = raw7417 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7417; decide +kernel
    rw [ha]
    exact (canonical7417 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA389 + difference 1 5) (sourceB389 + difference 5 1) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA389 + difference 1 5) (sourceB389 + difference 5 1) sourceC389) = raw7418 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7418; decide +kernel
    rw [ha]
    exact (canonical7418 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA389 + difference 2 0) (sourceB389 + difference 0 2) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4400) := by
    have ha : (tripleCharges (sourceA389 + difference 2 0) (sourceB389 + difference 0 2) sourceC389) = raw7419 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7419; decide +kernel
    rw [ha]
    exact (canonical7419 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA389 + difference 2 1) (sourceB389 + difference 1 2) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4999) := by
    have ha : (tripleCharges (sourceA389 + difference 2 1) (sourceB389 + difference 1 2) sourceC389) = raw7420 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7420; decide +kernel
    rw [ha]
    exact (canonical7420 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA389 + difference 2 3) (sourceB389 + difference 3 2) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA389 + difference 2 3) (sourceB389 + difference 3 2) sourceC389) = raw7421 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7421; decide +kernel
    rw [ha]
    exact (canonical7421 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA389 + difference 2 4) (sourceB389 + difference 4 2) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA389 + difference 2 4) (sourceB389 + difference 4 2) sourceC389) = raw7422 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7422; decide +kernel
    rw [ha]
    exact (canonical7422 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA389 + difference 2 5) (sourceB389 + difference 5 2) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA389 + difference 2 5) (sourceB389 + difference 5 2) sourceC389) = raw7423 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7423; decide +kernel
    rw [ha]
    exact (canonical7423 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA389 + difference 3 0) (sourceB389 + difference 0 3) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4400) := by
    have ha : (tripleCharges (sourceA389 + difference 3 0) (sourceB389 + difference 0 3) sourceC389) = raw7424 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7424; decide +kernel
    rw [ha]
    exact (canonical7424 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA389 + difference 3 1) (sourceB389 + difference 1 3) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4999) := by
    have ha : (tripleCharges (sourceA389 + difference 3 1) (sourceB389 + difference 1 3) sourceC389) = raw7425 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7425; decide +kernel
    rw [ha]
    exact (canonical7425 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA389 + difference 3 2) (sourceB389 + difference 2 3) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA389 + difference 3 2) (sourceB389 + difference 2 3) sourceC389) = raw7426 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7426; decide +kernel
    rw [ha]
    exact (canonical7426 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA389 + difference 3 4) (sourceB389 + difference 4 3) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA389 + difference 3 4) (sourceB389 + difference 4 3) sourceC389) = raw7427 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7427; decide +kernel
    rw [ha]
    exact (canonical7427 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA389 + difference 3 5) (sourceB389 + difference 5 3) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA389 + difference 3 5) (sourceB389 + difference 5 3) sourceC389) = raw7428 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7428; decide +kernel
    rw [ha]
    exact (canonical7428 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA389 + difference 4 0) (sourceB389 + difference 0 4) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4392) := by
    have ha : (tripleCharges (sourceA389 + difference 4 0) (sourceB389 + difference 0 4) sourceC389) = raw7429 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7429; decide +kernel
    rw [ha]
    exact (canonical7429 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA389 + difference 4 1) (sourceB389 + difference 1 4) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4993) := by
    have ha : (tripleCharges (sourceA389 + difference 4 1) (sourceB389 + difference 1 4) sourceC389) = raw7430 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7430; decide +kernel
    rw [ha]
    exact (canonical7430 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA389 + difference 4 2) (sourceB389 + difference 2 4) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA389 + difference 4 2) (sourceB389 + difference 2 4) sourceC389) = raw7431 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7431; decide +kernel
    rw [ha]
    exact (canonical7431 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA389 + difference 4 3) (sourceB389 + difference 3 4) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA389 + difference 4 3) (sourceB389 + difference 3 4) sourceC389) = raw7432 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7432; decide +kernel
    rw [ha]
    exact (canonical7432 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA389 + difference 4 5) (sourceB389 + difference 5 4) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5249) := by
    have ha : (tripleCharges (sourceA389 + difference 4 5) (sourceB389 + difference 5 4) sourceC389) = raw7433 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7433; decide +kernel
    rw [ha]
    exact (canonical7433 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA389 + difference 5 0) (sourceB389 + difference 0 5) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4391) := by
    have ha : (tripleCharges (sourceA389 + difference 5 0) (sourceB389 + difference 0 5) sourceC389) = raw7434 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7434; decide +kernel
    rw [ha]
    exact (canonical7434 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA389 + difference 5 1) (sourceB389 + difference 1 5) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4992) := by
    have ha : (tripleCharges (sourceA389 + difference 5 1) (sourceB389 + difference 1 5) sourceC389) = raw7435 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7435; decide +kernel
    rw [ha]
    exact (canonical7435 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA389 + difference 5 2) (sourceB389 + difference 2 5) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA389 + difference 5 2) (sourceB389 + difference 2 5) sourceC389) = raw7436 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7436; decide +kernel
    rw [ha]
    exact (canonical7436 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA389 + difference 5 3) (sourceB389 + difference 3 5) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA389 + difference 5 3) (sourceB389 + difference 3 5) sourceC389) = raw7437 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7437; decide +kernel
    rw [ha]
    exact (canonical7437 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA389 + difference 5 4) (sourceB389 + difference 4 5) sourceC389) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5252) := by
    have ha : (tripleCharges (sourceA389 + difference 5 4) (sourceB389 + difference 4 5) sourceC389) = raw7438 := by
      apply Matrix.ext; unfold tripleCharges sourceA389 sourceB389 sourceC389 difference raw7438; decide +kernel
    rw [ha]
    exact (canonical7438 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA389 sourceB389 sourceC389
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm389, Integer.Sparse.eval]
  linarith only [hs]

def sourceA390 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB390 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC390 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceForm390 : Integer.Sparse Master := [(Sum.inr 972, 1), (Sum.inr 973, 1), (Sum.inr 981, 2), (Sum.inr 1021, 1), (Sum.inr 2378, 1), (Sum.inr 2379, 1), (Sum.inr 2384, 2), (Sum.inr 2543, 2), (Sum.inr 2545, 2), (Sum.inr 2557, 2), (Sum.inr 2570, 2), (Sum.inr 2708, 1), (Sum.inr 2712, 1), (Sum.inr 2718, 2), (Sum.inr 2724, 2), (Sum.inr 2750, 1), (Sum.inr 2753, 1), (Sum.inr 3954, 1), (Sum.inr 3979, 1), (Sum.inr 3990, 2), (Sum.inr 4012, 1)]

theorem sourceEq390 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm390 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA390 + difference 0 1) (sourceB390 + difference 1 0) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA390 + difference 0 1) (sourceB390 + difference 1 0) sourceC390) = raw7439 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7439; decide +kernel
    rw [ha]
    exact (canonical7439 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA390 + difference 0 2) (sourceB390 + difference 2 0) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA390 + difference 0 2) (sourceB390 + difference 2 0) sourceC390) = raw7440 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7440; decide +kernel
    rw [ha]
    exact (canonical7440 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA390 + difference 0 3) (sourceB390 + difference 3 0) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA390 + difference 0 3) (sourceB390 + difference 3 0) sourceC390) = raw7441 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7441; decide +kernel
    rw [ha]
    exact (canonical7441 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA390 + difference 0 4) (sourceB390 + difference 4 0) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA390 + difference 0 4) (sourceB390 + difference 4 0) sourceC390) = raw7442 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7442; decide +kernel
    rw [ha]
    exact (canonical7442 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA390 + difference 0 5) (sourceB390 + difference 5 0) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3979) := by
    have ha : (tripleCharges (sourceA390 + difference 0 5) (sourceB390 + difference 5 0) sourceC390) = raw7443 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7443; decide +kernel
    rw [ha]
    exact (canonical7443 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA390 + difference 1 0) (sourceB390 + difference 0 1) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA390 + difference 1 0) (sourceB390 + difference 0 1) sourceC390) = raw7444 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7444; decide +kernel
    rw [ha]
    exact (canonical7444 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA390 + difference 1 2) (sourceB390 + difference 2 1) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2570) := by
    have ha : (tripleCharges (sourceA390 + difference 1 2) (sourceB390 + difference 2 1) sourceC390) = raw7445 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7445; decide +kernel
    rw [ha]
    exact (canonical7445 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA390 + difference 1 3) (sourceB390 + difference 3 1) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2570) := by
    have ha : (tripleCharges (sourceA390 + difference 1 3) (sourceB390 + difference 3 1) sourceC390) = raw7446 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7446; decide +kernel
    rw [ha]
    exact (canonical7446 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA390 + difference 1 4) (sourceB390 + difference 4 1) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA390 + difference 1 4) (sourceB390 + difference 4 1) sourceC390) = raw7447 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7447; decide +kernel
    rw [ha]
    exact (canonical7447 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA390 + difference 1 5) (sourceB390 + difference 5 1) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA390 + difference 1 5) (sourceB390 + difference 5 1) sourceC390) = raw7448 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7448; decide +kernel
    rw [ha]
    exact (canonical7448 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA390 + difference 2 0) (sourceB390 + difference 0 2) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 981) := by
    have ha : (tripleCharges (sourceA390 + difference 2 0) (sourceB390 + difference 0 2) sourceC390) = raw7449 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7449; decide +kernel
    rw [ha]
    exact (canonical7449 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA390 + difference 2 1) (sourceB390 + difference 1 2) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2384) := by
    have ha : (tripleCharges (sourceA390 + difference 2 1) (sourceB390 + difference 1 2) sourceC390) = raw7450 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7450; decide +kernel
    rw [ha]
    exact (canonical7450 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA390 + difference 2 3) (sourceB390 + difference 3 2) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2557) := by
    have ha : (tripleCharges (sourceA390 + difference 2 3) (sourceB390 + difference 3 2) sourceC390) = raw7451 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7451; decide +kernel
    rw [ha]
    exact (canonical7451 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA390 + difference 2 4) (sourceB390 + difference 4 2) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA390 + difference 2 4) (sourceB390 + difference 4 2) sourceC390) = raw7452 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7452; decide +kernel
    rw [ha]
    exact (canonical7452 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA390 + difference 2 5) (sourceB390 + difference 5 2) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA390 + difference 2 5) (sourceB390 + difference 5 2) sourceC390) = raw7453 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7453; decide +kernel
    rw [ha]
    exact (canonical7453 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA390 + difference 3 0) (sourceB390 + difference 0 3) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 981) := by
    have ha : (tripleCharges (sourceA390 + difference 3 0) (sourceB390 + difference 0 3) sourceC390) = raw7454 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7454; decide +kernel
    rw [ha]
    exact (canonical7454 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA390 + difference 3 1) (sourceB390 + difference 1 3) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2384) := by
    have ha : (tripleCharges (sourceA390 + difference 3 1) (sourceB390 + difference 1 3) sourceC390) = raw7455 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7455; decide +kernel
    rw [ha]
    exact (canonical7455 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA390 + difference 3 2) (sourceB390 + difference 2 3) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2557) := by
    have ha : (tripleCharges (sourceA390 + difference 3 2) (sourceB390 + difference 2 3) sourceC390) = raw7456 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7456; decide +kernel
    rw [ha]
    exact (canonical7456 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA390 + difference 3 4) (sourceB390 + difference 4 3) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA390 + difference 3 4) (sourceB390 + difference 4 3) sourceC390) = raw7457 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7457; decide +kernel
    rw [ha]
    exact (canonical7457 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA390 + difference 3 5) (sourceB390 + difference 5 3) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA390 + difference 3 5) (sourceB390 + difference 5 3) sourceC390) = raw7458 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7458; decide +kernel
    rw [ha]
    exact (canonical7458 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA390 + difference 4 0) (sourceB390 + difference 0 4) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 973) := by
    have ha : (tripleCharges (sourceA390 + difference 4 0) (sourceB390 + difference 0 4) sourceC390) = raw7459 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7459; decide +kernel
    rw [ha]
    exact (canonical7459 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA390 + difference 4 1) (sourceB390 + difference 1 4) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2379) := by
    have ha : (tripleCharges (sourceA390 + difference 4 1) (sourceB390 + difference 1 4) sourceC390) = raw7460 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7460; decide +kernel
    rw [ha]
    exact (canonical7460 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA390 + difference 4 2) (sourceB390 + difference 2 4) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2545) := by
    have ha : (tripleCharges (sourceA390 + difference 4 2) (sourceB390 + difference 2 4) sourceC390) = raw7461 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7461; decide +kernel
    rw [ha]
    exact (canonical7461 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA390 + difference 4 3) (sourceB390 + difference 3 4) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2545) := by
    have ha : (tripleCharges (sourceA390 + difference 4 3) (sourceB390 + difference 3 4) sourceC390) = raw7462 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7462; decide +kernel
    rw [ha]
    exact (canonical7462 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA390 + difference 4 5) (sourceB390 + difference 5 4) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA390 + difference 4 5) (sourceB390 + difference 5 4) sourceC390) = raw7463 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7463; decide +kernel
    rw [ha]
    exact (canonical7463 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA390 + difference 5 0) (sourceB390 + difference 0 5) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 972) := by
    have ha : (tripleCharges (sourceA390 + difference 5 0) (sourceB390 + difference 0 5) sourceC390) = raw7464 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7464; decide +kernel
    rw [ha]
    exact (canonical7464 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA390 + difference 5 1) (sourceB390 + difference 1 5) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2378) := by
    have ha : (tripleCharges (sourceA390 + difference 5 1) (sourceB390 + difference 1 5) sourceC390) = raw7465 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7465; decide +kernel
    rw [ha]
    exact (canonical7465 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA390 + difference 5 2) (sourceB390 + difference 2 5) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA390 + difference 5 2) (sourceB390 + difference 2 5) sourceC390) = raw7466 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7466; decide +kernel
    rw [ha]
    exact (canonical7466 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA390 + difference 5 3) (sourceB390 + difference 3 5) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA390 + difference 5 3) (sourceB390 + difference 3 5) sourceC390) = raw7467 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7467; decide +kernel
    rw [ha]
    exact (canonical7467 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA390 + difference 5 4) (sourceB390 + difference 4 5) sourceC390) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA390 + difference 5 4) (sourceB390 + difference 4 5) sourceC390) = raw7468 := by
      apply Matrix.ext; unfold tripleCharges sourceA390 sourceB390 sourceC390 difference raw7468; decide +kernel
    rw [ha]
    exact (canonical7468 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA390 sourceB390 sourceC390
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm390, Integer.Sparse.eval]
  linarith only [hs]

def sourceA391 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB391 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC391 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceForm391 : Integer.Sparse Master := [(Sum.inr 1606, 1), (Sum.inr 1607, 2), (Sum.inr 1613, 1), (Sum.inr 1713, 1), (Sum.inr 3345, 1), (Sum.inr 3346, 2), (Sum.inr 3350, 1), (Sum.inr 3502, 1), (Sum.inr 3503, 2), (Sum.inr 3516, 2), (Sum.inr 3517, 2), (Sum.inr 3519, 2), (Sum.inr 3540, 2), (Sum.inr 3543, 1), (Sum.inr 3571, 1), (Sum.inr 3605, 2), (Sum.inr 3625, 1), (Sum.inr 3843, 2), (Sum.inr 3858, 1), (Sum.inr 3874, 1), (Sum.inr 3991, 1)]

theorem sourceEq391 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm391 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA391 + difference 0 1) (sourceB391 + difference 1 0) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA391 + difference 0 1) (sourceB391 + difference 1 0) sourceC391) = raw7469 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7469; decide +kernel
    rw [ha]
    exact (canonical7469 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA391 + difference 0 2) (sourceB391 + difference 2 0) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA391 + difference 0 2) (sourceB391 + difference 2 0) sourceC391) = raw7470 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7470; decide +kernel
    rw [ha]
    exact (canonical7470 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA391 + difference 0 3) (sourceB391 + difference 3 0) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA391 + difference 0 3) (sourceB391 + difference 3 0) sourceC391) = raw7471 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7471; decide +kernel
    rw [ha]
    exact (canonical7471 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA391 + difference 0 4) (sourceB391 + difference 4 0) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3858) := by
    have ha : (tripleCharges (sourceA391 + difference 0 4) (sourceB391 + difference 4 0) sourceC391) = raw7472 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7472; decide +kernel
    rw [ha]
    exact (canonical7472 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA391 + difference 0 5) (sourceB391 + difference 5 0) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3991) := by
    have ha : (tripleCharges (sourceA391 + difference 0 5) (sourceB391 + difference 5 0) sourceC391) = raw7473 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7473; decide +kernel
    rw [ha]
    exact (canonical7473 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA391 + difference 1 0) (sourceB391 + difference 0 1) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA391 + difference 1 0) (sourceB391 + difference 0 1) sourceC391) = raw7474 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7474; decide +kernel
    rw [ha]
    exact (canonical7474 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA391 + difference 1 2) (sourceB391 + difference 2 1) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA391 + difference 1 2) (sourceB391 + difference 2 1) sourceC391) = raw7475 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7475; decide +kernel
    rw [ha]
    exact (canonical7475 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA391 + difference 1 3) (sourceB391 + difference 3 1) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3605) := by
    have ha : (tripleCharges (sourceA391 + difference 1 3) (sourceB391 + difference 3 1) sourceC391) = raw7476 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7476; decide +kernel
    rw [ha]
    exact (canonical7476 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA391 + difference 1 4) (sourceB391 + difference 4 1) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA391 + difference 1 4) (sourceB391 + difference 4 1) sourceC391) = raw7477 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7477; decide +kernel
    rw [ha]
    exact (canonical7477 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA391 + difference 1 5) (sourceB391 + difference 5 1) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA391 + difference 1 5) (sourceB391 + difference 5 1) sourceC391) = raw7478 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7478; decide +kernel
    rw [ha]
    exact (canonical7478 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA391 + difference 2 0) (sourceB391 + difference 0 2) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1607) := by
    have ha : (tripleCharges (sourceA391 + difference 2 0) (sourceB391 + difference 0 2) sourceC391) = raw7479 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7479; decide +kernel
    rw [ha]
    exact (canonical7479 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA391 + difference 2 1) (sourceB391 + difference 1 2) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3346) := by
    have ha : (tripleCharges (sourceA391 + difference 2 1) (sourceB391 + difference 1 2) sourceC391) = raw7480 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7480; decide +kernel
    rw [ha]
    exact (canonical7480 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA391 + difference 2 3) (sourceB391 + difference 3 2) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA391 + difference 2 3) (sourceB391 + difference 3 2) sourceC391) = raw7481 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7481; decide +kernel
    rw [ha]
    exact (canonical7481 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA391 + difference 2 4) (sourceB391 + difference 4 2) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA391 + difference 2 4) (sourceB391 + difference 4 2) sourceC391) = raw7482 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7482; decide +kernel
    rw [ha]
    exact (canonical7482 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA391 + difference 2 5) (sourceB391 + difference 5 2) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA391 + difference 2 5) (sourceB391 + difference 5 2) sourceC391) = raw7483 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7483; decide +kernel
    rw [ha]
    exact (canonical7483 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA391 + difference 3 0) (sourceB391 + difference 0 3) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1607) := by
    have ha : (tripleCharges (sourceA391 + difference 3 0) (sourceB391 + difference 0 3) sourceC391) = raw7484 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7484; decide +kernel
    rw [ha]
    exact (canonical7484 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA391 + difference 3 1) (sourceB391 + difference 1 3) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3346) := by
    have ha : (tripleCharges (sourceA391 + difference 3 1) (sourceB391 + difference 1 3) sourceC391) = raw7485 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7485; decide +kernel
    rw [ha]
    exact (canonical7485 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA391 + difference 3 2) (sourceB391 + difference 2 3) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA391 + difference 3 2) (sourceB391 + difference 2 3) sourceC391) = raw7486 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7486; decide +kernel
    rw [ha]
    exact (canonical7486 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA391 + difference 3 4) (sourceB391 + difference 4 3) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA391 + difference 3 4) (sourceB391 + difference 4 3) sourceC391) = raw7487 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7487; decide +kernel
    rw [ha]
    exact (canonical7487 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA391 + difference 3 5) (sourceB391 + difference 5 3) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA391 + difference 3 5) (sourceB391 + difference 5 3) sourceC391) = raw7488 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7488; decide +kernel
    rw [ha]
    exact (canonical7488 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA391 + difference 4 0) (sourceB391 + difference 0 4) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1606) := by
    have ha : (tripleCharges (sourceA391 + difference 4 0) (sourceB391 + difference 0 4) sourceC391) = raw7489 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7489; decide +kernel
    rw [ha]
    exact (canonical7489 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA391 + difference 4 1) (sourceB391 + difference 1 4) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3345) := by
    have ha : (tripleCharges (sourceA391 + difference 4 1) (sourceB391 + difference 1 4) sourceC391) = raw7490 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7490; decide +kernel
    rw [ha]
    exact (canonical7490 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA391 + difference 4 2) (sourceB391 + difference 2 4) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA391 + difference 4 2) (sourceB391 + difference 2 4) sourceC391) = raw7491 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7491; decide +kernel
    rw [ha]
    exact (canonical7491 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA391 + difference 4 3) (sourceB391 + difference 3 4) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA391 + difference 4 3) (sourceB391 + difference 3 4) sourceC391) = raw7492 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7492; decide +kernel
    rw [ha]
    exact (canonical7492 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA391 + difference 4 5) (sourceB391 + difference 5 4) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3502) := by
    have ha : (tripleCharges (sourceA391 + difference 4 5) (sourceB391 + difference 5 4) sourceC391) = raw7493 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7493; decide +kernel
    rw [ha]
    exact (canonical7493 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA391 + difference 5 0) (sourceB391 + difference 0 5) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1613) := by
    have ha : (tripleCharges (sourceA391 + difference 5 0) (sourceB391 + difference 0 5) sourceC391) = raw7494 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7494; decide +kernel
    rw [ha]
    exact (canonical7494 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA391 + difference 5 1) (sourceB391 + difference 1 5) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3350) := by
    have ha : (tripleCharges (sourceA391 + difference 5 1) (sourceB391 + difference 1 5) sourceC391) = raw7495 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7495; decide +kernel
    rw [ha]
    exact (canonical7495 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA391 + difference 5 2) (sourceB391 + difference 2 5) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA391 + difference 5 2) (sourceB391 + difference 2 5) sourceC391) = raw7496 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7496; decide +kernel
    rw [ha]
    exact (canonical7496 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA391 + difference 5 3) (sourceB391 + difference 3 5) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA391 + difference 5 3) (sourceB391 + difference 3 5) sourceC391) = raw7497 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7497; decide +kernel
    rw [ha]
    exact (canonical7497 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA391 + difference 5 4) (sourceB391 + difference 4 5) sourceC391) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA391 + difference 5 4) (sourceB391 + difference 4 5) sourceC391) = raw7498 := by
      apply Matrix.ext; unfold tripleCharges sourceA391 sourceB391 sourceC391 difference raw7498; decide +kernel
    rw [ha]
    exact (canonical7498 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA391 sourceB391 sourceC391
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm391, Integer.Sparse.eval]
  linarith only [hs]

def sourceA392 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB392 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC392 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceForm392 : Integer.Sparse Master := [(Sum.inr 3064, 1), (Sum.inr 3838, 2), (Sum.inr 3846, 1), (Sum.inr 3902, 1), (Sum.inr 4008, 1), (Sum.inr 4091, -1)]

theorem sourceEq392 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm392 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA392 + difference 0 0) (sourceB392 + difference 0 0) sourceC392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA392 + difference 0 0) (sourceB392 + difference 0 0) sourceC392) = raw7499 := by
      apply Matrix.ext; unfold tripleCharges sourceA392 sourceB392 sourceC392 difference raw7499; decide +kernel
    rw [ha]
    exact (canonical7499 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA392 + difference 0 1) (sourceB392 + difference 1 0) sourceC392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA392 + difference 0 1) (sourceB392 + difference 1 0) sourceC392) = raw7500 := by
      apply Matrix.ext; unfold tripleCharges sourceA392 sourceB392 sourceC392 difference raw7500; decide +kernel
    rw [ha]
    exact (canonical7500 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA392 + difference 0 2) (sourceB392 + difference 2 0) sourceC392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA392 + difference 0 2) (sourceB392 + difference 2 0) sourceC392) = raw7501 := by
      apply Matrix.ext; unfold tripleCharges sourceA392 sourceB392 sourceC392 difference raw7501; decide +kernel
    rw [ha]
    exact (canonical7501 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA392 + difference 0 3) (sourceB392 + difference 3 0) sourceC392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA392 + difference 0 3) (sourceB392 + difference 3 0) sourceC392) = raw7502 := by
      apply Matrix.ext; unfold tripleCharges sourceA392 sourceB392 sourceC392 difference raw7502; decide +kernel
    rw [ha]
    exact (canonical7502 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA392 + difference 0 4) (sourceB392 + difference 4 0) sourceC392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA392 + difference 0 4) (sourceB392 + difference 4 0) sourceC392) = raw7503 := by
      apply Matrix.ext; unfold tripleCharges sourceA392 sourceB392 sourceC392 difference raw7503; decide +kernel
    rw [ha]
    exact (canonical7503 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA392 + difference 0 5) (sourceB392 + difference 5 0) sourceC392) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4008) := by
    have ha : (tripleCharges (sourceA392 + difference 0 5) (sourceB392 + difference 5 0) sourceC392) = raw7504 := by
      apply Matrix.ext; unfold tripleCharges sourceA392 sourceB392 sourceC392 difference raw7504; decide +kernel
    rw [ha]
    exact (canonical7504 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA392 + sourceB392) sourceC392) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA392 + sourceB392) sourceC392) = raw7505 := by
      apply Matrix.ext; unfold doubleCharges sourceA392 sourceB392 sourceC392 raw7505; decide +kernel
    rw [ha]
    exact (canonical7505 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA392 sourceB392 sourceC392
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm392, Integer.Sparse.eval]
  linarith only [hs]

def sourceA393 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB393 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC393 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceForm393 : Integer.Sparse Master := [(Sum.inr 1378, 1), (Sum.inr 1380, 1), (Sum.inr 1383, 1), (Sum.inr 1392, 2), (Sum.inr 3064, 1), (Sum.inr 4091, -1)]

theorem sourceEq393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm393 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA393 + difference 0 0) (sourceB393 + difference 0 0) sourceC393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA393 + difference 0 0) (sourceB393 + difference 0 0) sourceC393) = raw7499 := by
      apply Matrix.ext; unfold tripleCharges sourceA393 sourceB393 sourceC393 difference raw7499; decide +kernel
    rw [ha]
    exact (canonical7499 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA393 + difference 1 0) (sourceB393 + difference 0 1) sourceC393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1383) := by
    have ha : (tripleCharges (sourceA393 + difference 1 0) (sourceB393 + difference 0 1) sourceC393) = raw7506 := by
      apply Matrix.ext; unfold tripleCharges sourceA393 sourceB393 sourceC393 difference raw7506; decide +kernel
    rw [ha]
    exact (canonical7506 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA393 + difference 2 0) (sourceB393 + difference 0 2) sourceC393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1392) := by
    have ha : (tripleCharges (sourceA393 + difference 2 0) (sourceB393 + difference 0 2) sourceC393) = raw7507 := by
      apply Matrix.ext; unfold tripleCharges sourceA393 sourceB393 sourceC393 difference raw7507; decide +kernel
    rw [ha]
    exact (canonical7507 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA393 + difference 3 0) (sourceB393 + difference 0 3) sourceC393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1392) := by
    have ha : (tripleCharges (sourceA393 + difference 3 0) (sourceB393 + difference 0 3) sourceC393) = raw7508 := by
      apply Matrix.ext; unfold tripleCharges sourceA393 sourceB393 sourceC393 difference raw7508; decide +kernel
    rw [ha]
    exact (canonical7508 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA393 + difference 4 0) (sourceB393 + difference 0 4) sourceC393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1380) := by
    have ha : (tripleCharges (sourceA393 + difference 4 0) (sourceB393 + difference 0 4) sourceC393) = raw7509 := by
      apply Matrix.ext; unfold tripleCharges sourceA393 sourceB393 sourceC393 difference raw7509; decide +kernel
    rw [ha]
    exact (canonical7509 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA393 + difference 5 0) (sourceB393 + difference 0 5) sourceC393) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1378) := by
    have ha : (tripleCharges (sourceA393 + difference 5 0) (sourceB393 + difference 0 5) sourceC393) = raw7510 := by
      apply Matrix.ext; unfold tripleCharges sourceA393 sourceB393 sourceC393 difference raw7510; decide +kernel
    rw [ha]
    exact (canonical7510 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA393 + sourceB393) sourceC393) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA393 + sourceB393) sourceC393) = raw7505 := by
      apply Matrix.ext; unfold doubleCharges sourceA393 sourceB393 sourceC393 raw7505; decide +kernel
    rw [ha]
    exact (canonical7505 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA393 sourceB393 sourceC393
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm393, Integer.Sparse.eval]
  linarith only [hs]

def sourceA394 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB394 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC394 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceForm394 : Integer.Sparse Master := [(Sum.inr 1383, 1), (Sum.inr 2924, 2), (Sum.inr 3064, 1), (Sum.inr 3074, 1), (Sum.inr 3077, 1), (Sum.inr 4091, -1)]

theorem sourceEq394 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm394 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA394 + difference 1 0) (sourceB394 + difference 0 1) sourceC394) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1383) := by
    have ha : (tripleCharges (sourceA394 + difference 1 0) (sourceB394 + difference 0 1) sourceC394) = raw7506 := by
      apply Matrix.ext; unfold tripleCharges sourceA394 sourceB394 sourceC394 difference raw7506; decide +kernel
    rw [ha]
    exact (canonical7506 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA394 + difference 1 1) (sourceB394 + difference 1 1) sourceC394) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA394 + difference 1 1) (sourceB394 + difference 1 1) sourceC394) = raw7499 := by
      apply Matrix.ext; unfold tripleCharges sourceA394 sourceB394 sourceC394 difference raw7499; decide +kernel
    rw [ha]
    exact (canonical7499 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA394 + difference 1 2) (sourceB394 + difference 2 1) sourceC394) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA394 + difference 1 2) (sourceB394 + difference 2 1) sourceC394) = raw7511 := by
      apply Matrix.ext; unfold tripleCharges sourceA394 sourceB394 sourceC394 difference raw7511; decide +kernel
    rw [ha]
    exact (canonical7511 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA394 + difference 1 3) (sourceB394 + difference 3 1) sourceC394) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA394 + difference 1 3) (sourceB394 + difference 3 1) sourceC394) = raw7512 := by
      apply Matrix.ext; unfold tripleCharges sourceA394 sourceB394 sourceC394 difference raw7512; decide +kernel
    rw [ha]
    exact (canonical7512 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA394 + difference 1 4) (sourceB394 + difference 4 1) sourceC394) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA394 + difference 1 4) (sourceB394 + difference 4 1) sourceC394) = raw7513 := by
      apply Matrix.ext; unfold tripleCharges sourceA394 sourceB394 sourceC394 difference raw7513; decide +kernel
    rw [ha]
    exact (canonical7513 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA394 + difference 1 5) (sourceB394 + difference 5 1) sourceC394) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA394 + difference 1 5) (sourceB394 + difference 5 1) sourceC394) = raw7514 := by
      apply Matrix.ext; unfold tripleCharges sourceA394 sourceB394 sourceC394 difference raw7514; decide +kernel
    rw [ha]
    exact (canonical7514 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA394 + sourceB394) sourceC394) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA394 + sourceB394) sourceC394) = raw7505 := by
      apply Matrix.ext; unfold doubleCharges sourceA394 sourceB394 sourceC394 raw7505; decide +kernel
    rw [ha]
    exact (canonical7505 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA394 sourceB394 sourceC394
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm394, Integer.Sparse.eval]
  linarith only [hs]

def sourceA395 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB395 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC395 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceForm395 : Integer.Sparse Master := [(Sum.inr 2562, 1), (Sum.inr 3012, 1), (Sum.inr 3013, 2), (Sum.inr 3064, 1), (Sum.inr 3846, 1), (Sum.inr 4091, -1)]

theorem sourceEq395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm395 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA395 + difference 0 1) (sourceB395 + difference 1 0) sourceC395) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA395 + difference 0 1) (sourceB395 + difference 1 0) sourceC395) = raw7500 := by
      apply Matrix.ext; unfold tripleCharges sourceA395 sourceB395 sourceC395 difference raw7500; decide +kernel
    rw [ha]
    exact (canonical7500 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA395 + difference 1 1) (sourceB395 + difference 1 1) sourceC395) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA395 + difference 1 1) (sourceB395 + difference 1 1) sourceC395) = raw7499 := by
      apply Matrix.ext; unfold tripleCharges sourceA395 sourceB395 sourceC395 difference raw7499; decide +kernel
    rw [ha]
    exact (canonical7499 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA395 + difference 2 1) (sourceB395 + difference 1 2) sourceC395) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3013) := by
    have ha : (tripleCharges (sourceA395 + difference 2 1) (sourceB395 + difference 1 2) sourceC395) = raw7515 := by
      apply Matrix.ext; unfold tripleCharges sourceA395 sourceB395 sourceC395 difference raw7515; decide +kernel
    rw [ha]
    exact (canonical7515 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA395 + difference 3 1) (sourceB395 + difference 1 3) sourceC395) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3013) := by
    have ha : (tripleCharges (sourceA395 + difference 3 1) (sourceB395 + difference 1 3) sourceC395) = raw7516 := by
      apply Matrix.ext; unfold tripleCharges sourceA395 sourceB395 sourceC395 difference raw7516; decide +kernel
    rw [ha]
    exact (canonical7516 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA395 + difference 4 1) (sourceB395 + difference 1 4) sourceC395) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3012) := by
    have ha : (tripleCharges (sourceA395 + difference 4 1) (sourceB395 + difference 1 4) sourceC395) = raw7517 := by
      apply Matrix.ext; unfold tripleCharges sourceA395 sourceB395 sourceC395 difference raw7517; decide +kernel
    rw [ha]
    exact (canonical7517 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA395 + difference 5 1) (sourceB395 + difference 1 5) sourceC395) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2562) := by
    have ha : (tripleCharges (sourceA395 + difference 5 1) (sourceB395 + difference 1 5) sourceC395) = raw7518 := by
      apply Matrix.ext; unfold tripleCharges sourceA395 sourceB395 sourceC395 difference raw7518; decide +kernel
    rw [ha]
    exact (canonical7518 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA395 + sourceB395) sourceC395) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA395 + sourceB395) sourceC395) = raw7505 := by
      apply Matrix.ext; unfold doubleCharges sourceA395 sourceB395 sourceC395 raw7505; decide +kernel
    rw [ha]
    exact (canonical7505 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA395 sourceB395 sourceC395
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm395, Integer.Sparse.eval]
  linarith only [hs]

def sourceA396 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB396 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC396 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceForm396 : Integer.Sparse Master := [(Sum.inr 2543, 1), (Sum.inr 2916, 1), (Sum.inr 2924, 1), (Sum.inr 2933, 1), (Sum.inr 3064, 1), (Sum.inr 3838, 1), (Sum.inr 4091, -1)]

theorem sourceEq396 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm396 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA396 + difference 0 2) (sourceB396 + difference 2 0) sourceC396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA396 + difference 0 2) (sourceB396 + difference 2 0) sourceC396) = raw7501 := by
      apply Matrix.ext; unfold tripleCharges sourceA396 sourceB396 sourceC396 difference raw7501; decide +kernel
    rw [ha]
    exact (canonical7501 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA396 + difference 1 2) (sourceB396 + difference 2 1) sourceC396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA396 + difference 1 2) (sourceB396 + difference 2 1) sourceC396) = raw7511 := by
      apply Matrix.ext; unfold tripleCharges sourceA396 sourceB396 sourceC396 difference raw7511; decide +kernel
    rw [ha]
    exact (canonical7511 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA396 + difference 2 2) (sourceB396 + difference 2 2) sourceC396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA396 + difference 2 2) (sourceB396 + difference 2 2) sourceC396) = raw7499 := by
      apply Matrix.ext; unfold tripleCharges sourceA396 sourceB396 sourceC396 difference raw7499; decide +kernel
    rw [ha]
    exact (canonical7499 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA396 + difference 3 2) (sourceB396 + difference 2 3) sourceC396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2933) := by
    have ha : (tripleCharges (sourceA396 + difference 3 2) (sourceB396 + difference 2 3) sourceC396) = raw7519 := by
      apply Matrix.ext; unfold tripleCharges sourceA396 sourceB396 sourceC396 difference raw7519; decide +kernel
    rw [ha]
    exact (canonical7519 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA396 + difference 4 2) (sourceB396 + difference 2 4) sourceC396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA396 + difference 4 2) (sourceB396 + difference 2 4) sourceC396) = raw7520 := by
      apply Matrix.ext; unfold tripleCharges sourceA396 sourceB396 sourceC396 difference raw7520; decide +kernel
    rw [ha]
    exact (canonical7520 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA396 + difference 5 2) (sourceB396 + difference 2 5) sourceC396) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA396 + difference 5 2) (sourceB396 + difference 2 5) sourceC396) = raw7521 := by
      apply Matrix.ext; unfold tripleCharges sourceA396 sourceB396 sourceC396 difference raw7521; decide +kernel
    rw [ha]
    exact (canonical7521 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA396 + sourceB396) sourceC396) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA396 + sourceB396) sourceC396) = raw7505 := by
      apply Matrix.ext; unfold doubleCharges sourceA396 sourceB396 sourceC396 raw7505; decide +kernel
    rw [ha]
    exact (canonical7505 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA396 sourceB396 sourceC396
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm396, Integer.Sparse.eval]
  linarith only [hs]

def sourceA397 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB397 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC397 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceForm397 : Integer.Sparse Master := [(Sum.inr 1380, 1), (Sum.inr 2916, 2), (Sum.inr 3012, 1), (Sum.inr 3064, 1), (Sum.inr 3066, 1), (Sum.inr 4091, -1)]

theorem sourceEq397 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm397 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA397 + difference 4 0) (sourceB397 + difference 0 4) sourceC397) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1380) := by
    have ha : (tripleCharges (sourceA397 + difference 4 0) (sourceB397 + difference 0 4) sourceC397) = raw7509 := by
      apply Matrix.ext; unfold tripleCharges sourceA397 sourceB397 sourceC397 difference raw7509; decide +kernel
    rw [ha]
    exact (canonical7509 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA397 + difference 4 1) (sourceB397 + difference 1 4) sourceC397) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3012) := by
    have ha : (tripleCharges (sourceA397 + difference 4 1) (sourceB397 + difference 1 4) sourceC397) = raw7517 := by
      apply Matrix.ext; unfold tripleCharges sourceA397 sourceB397 sourceC397 difference raw7517; decide +kernel
    rw [ha]
    exact (canonical7517 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA397 + difference 4 2) (sourceB397 + difference 2 4) sourceC397) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA397 + difference 4 2) (sourceB397 + difference 2 4) sourceC397) = raw7520 := by
      apply Matrix.ext; unfold tripleCharges sourceA397 sourceB397 sourceC397 difference raw7520; decide +kernel
    rw [ha]
    exact (canonical7520 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA397 + difference 4 3) (sourceB397 + difference 3 4) sourceC397) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA397 + difference 4 3) (sourceB397 + difference 3 4) sourceC397) = raw7522 := by
      apply Matrix.ext; unfold tripleCharges sourceA397 sourceB397 sourceC397 difference raw7522; decide +kernel
    rw [ha]
    exact (canonical7522 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA397 + difference 4 4) (sourceB397 + difference 4 4) sourceC397) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA397 + difference 4 4) (sourceB397 + difference 4 4) sourceC397) = raw7499 := by
      apply Matrix.ext; unfold tripleCharges sourceA397 sourceB397 sourceC397 difference raw7499; decide +kernel
    rw [ha]
    exact (canonical7499 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA397 + difference 4 5) (sourceB397 + difference 5 4) sourceC397) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3066) := by
    have ha : (tripleCharges (sourceA397 + difference 4 5) (sourceB397 + difference 5 4) sourceC397) = raw7523 := by
      apply Matrix.ext; unfold tripleCharges sourceA397 sourceB397 sourceC397 difference raw7523; decide +kernel
    rw [ha]
    exact (canonical7523 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA397 + sourceB397) sourceC397) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA397 + sourceB397) sourceC397) = raw7505 := by
      apply Matrix.ext; unfold doubleCharges sourceA397 sourceB397 sourceC397 raw7505; decide +kernel
    rw [ha]
    exact (canonical7505 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA397 sourceB397 sourceC397
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm397, Integer.Sparse.eval]
  linarith only [hs]

def sourceA398 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceB398 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC398 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm398 : Integer.Sparse Master := [(Sum.inr 4815, 1), (Sum.inr 4816, 2), (Sum.inr 4831, 1), (Sum.inr 4889, 1), (Sum.inr 5133, 1), (Sum.inr 5136, 2), (Sum.inr 5159, 1), (Sum.inr 5220, 1), (Sum.inr 5221, 1), (Sum.inr 5224, 2), (Sum.inr 5241, 1), (Sum.inr 5243, 1), (Sum.inr 5250, 1), (Sum.inr 5254, 2), (Sum.inr 5258, 2), (Sum.inr 5259, 2), (Sum.inr 5260, 2), (Sum.inr 5267, 2), (Sum.inr 5270, 1), (Sum.inr 5284, 1), (Sum.inr 5294, 2)]

theorem sourceEq398 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm398 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA398 + difference 0 1) (sourceB398 + difference 1 0) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5243) := by
    have ha : (tripleCharges (sourceA398 + difference 0 1) (sourceB398 + difference 1 0) sourceC398) = raw7524 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw7524; decide +kernel
    rw [ha]
    exact (canonical7524 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA398 + difference 0 2) (sourceB398 + difference 2 0) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA398 + difference 0 2) (sourceB398 + difference 2 0) sourceC398) = raw6371 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw6371; decide +kernel
    rw [ha]
    exact (canonical6371 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA398 + difference 0 3) (sourceB398 + difference 3 0) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA398 + difference 0 3) (sourceB398 + difference 3 0) sourceC398) = raw7525 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw7525; decide +kernel
    rw [ha]
    exact (canonical7525 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA398 + difference 0 4) (sourceB398 + difference 4 0) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5241) := by
    have ha : (tripleCharges (sourceA398 + difference 0 4) (sourceB398 + difference 4 0) sourceC398) = raw7224 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw7224; decide +kernel
    rw [ha]
    exact (canonical7224 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA398 + difference 0 5) (sourceB398 + difference 5 0) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5133) := by
    have ha : (tripleCharges (sourceA398 + difference 0 5) (sourceB398 + difference 5 0) sourceC398) = raw7526 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw7526; decide +kernel
    rw [ha]
    exact (canonical7526 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA398 + difference 1 0) (sourceB398 + difference 0 1) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA398 + difference 1 0) (sourceB398 + difference 0 1) sourceC398) = raw5679 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw5679; decide +kernel
    rw [ha]
    exact (canonical5679 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA398 + difference 1 2) (sourceB398 + difference 2 1) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA398 + difference 1 2) (sourceB398 + difference 2 1) sourceC398) = raw6375 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw6375; decide +kernel
    rw [ha]
    exact (canonical6375 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA398 + difference 1 3) (sourceB398 + difference 3 1) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA398 + difference 1 3) (sourceB398 + difference 3 1) sourceC398) = raw7527 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw7527; decide +kernel
    rw [ha]
    exact (canonical7527 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA398 + difference 1 4) (sourceB398 + difference 4 1) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA398 + difference 1 4) (sourceB398 + difference 4 1) sourceC398) = raw5658 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw5658; decide +kernel
    rw [ha]
    exact (canonical5658 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA398 + difference 1 5) (sourceB398 + difference 5 1) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA398 + difference 1 5) (sourceB398 + difference 5 1) sourceC398) = raw7528 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw7528; decide +kernel
    rw [ha]
    exact (canonical7528 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA398 + difference 2 0) (sourceB398 + difference 0 2) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA398 + difference 2 0) (sourceB398 + difference 0 2) sourceC398) = raw7529 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw7529; decide +kernel
    rw [ha]
    exact (canonical7529 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA398 + difference 2 1) (sourceB398 + difference 1 2) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5224) := by
    have ha : (tripleCharges (sourceA398 + difference 2 1) (sourceB398 + difference 1 2) sourceC398) = raw7530 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw7530; decide +kernel
    rw [ha]
    exact (canonical7530 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA398 + difference 2 3) (sourceB398 + difference 3 2) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA398 + difference 2 3) (sourceB398 + difference 3 2) sourceC398) = raw7531 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw7531; decide +kernel
    rw [ha]
    exact (canonical7531 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA398 + difference 2 4) (sourceB398 + difference 4 2) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA398 + difference 2 4) (sourceB398 + difference 4 2) sourceC398) = raw7231 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw7231; decide +kernel
    rw [ha]
    exact (canonical7231 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA398 + difference 2 5) (sourceB398 + difference 5 2) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5136) := by
    have ha : (tripleCharges (sourceA398 + difference 2 5) (sourceB398 + difference 5 2) sourceC398) = raw7532 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw7532; decide +kernel
    rw [ha]
    exact (canonical7532 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA398 + difference 3 0) (sourceB398 + difference 0 3) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA398 + difference 3 0) (sourceB398 + difference 0 3) sourceC398) = raw7056 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw7056; decide +kernel
    rw [ha]
    exact (canonical7056 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA398 + difference 3 1) (sourceB398 + difference 1 3) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5224) := by
    have ha : (tripleCharges (sourceA398 + difference 3 1) (sourceB398 + difference 1 3) sourceC398) = raw7057 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw7057; decide +kernel
    rw [ha]
    exact (canonical7057 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA398 + difference 3 2) (sourceB398 + difference 2 3) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA398 + difference 3 2) (sourceB398 + difference 2 3) sourceC398) = raw6384 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw6384; decide +kernel
    rw [ha]
    exact (canonical6384 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA398 + difference 3 4) (sourceB398 + difference 4 3) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA398 + difference 3 4) (sourceB398 + difference 4 3) sourceC398) = raw6714 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw6714; decide +kernel
    rw [ha]
    exact (canonical6714 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA398 + difference 3 5) (sourceB398 + difference 5 3) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5136) := by
    have ha : (tripleCharges (sourceA398 + difference 3 5) (sourceB398 + difference 5 3) sourceC398) = raw7058 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw7058; decide +kernel
    rw [ha]
    exact (canonical7058 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA398 + difference 4 0) (sourceB398 + difference 0 4) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA398 + difference 4 0) (sourceB398 + difference 0 4) sourceC398) = raw6377 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw6377; decide +kernel
    rw [ha]
    exact (canonical6377 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA398 + difference 4 1) (sourceB398 + difference 1 4) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5221) := by
    have ha : (tripleCharges (sourceA398 + difference 4 1) (sourceB398 + difference 1 4) sourceC398) = raw6378 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw6378; decide +kernel
    rw [ha]
    exact (canonical6378 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA398 + difference 4 2) (sourceB398 + difference 2 4) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA398 + difference 4 2) (sourceB398 + difference 2 4) sourceC398) = raw6028 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw6028; decide +kernel
    rw [ha]
    exact (canonical6028 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA398 + difference 4 3) (sourceB398 + difference 3 4) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA398 + difference 4 3) (sourceB398 + difference 3 4) sourceC398) = raw6023 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw6023; decide +kernel
    rw [ha]
    exact (canonical6023 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA398 + difference 4 5) (sourceB398 + difference 5 4) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5159) := by
    have ha : (tripleCharges (sourceA398 + difference 4 5) (sourceB398 + difference 5 4) sourceC398) = raw6380 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw6380; decide +kernel
    rw [ha]
    exact (canonical6380 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA398 + difference 5 0) (sourceB398 + difference 0 5) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4831) := by
    have ha : (tripleCharges (sourceA398 + difference 5 0) (sourceB398 + difference 0 5) sourceC398) = raw7232 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw7232; decide +kernel
    rw [ha]
    exact (canonical7232 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA398 + difference 5 1) (sourceB398 + difference 1 5) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5220) := by
    have ha : (tripleCharges (sourceA398 + difference 5 1) (sourceB398 + difference 1 5) sourceC398) = raw7233 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw7233; decide +kernel
    rw [ha]
    exact (canonical7233 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA398 + difference 5 2) (sourceB398 + difference 2 5) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA398 + difference 5 2) (sourceB398 + difference 2 5) sourceC398) = raw6390 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw6390; decide +kernel
    rw [ha]
    exact (canonical6390 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA398 + difference 5 3) (sourceB398 + difference 3 5) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA398 + difference 5 3) (sourceB398 + difference 3 5) sourceC398) = raw7234 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw7234; decide +kernel
    rw [ha]
    exact (canonical7234 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA398 + difference 5 4) (sourceB398 + difference 4 5) sourceC398) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA398 + difference 5 4) (sourceB398 + difference 4 5) sourceC398) = raw6712 := by
      apply Matrix.ext; unfold tripleCharges sourceA398 sourceB398 sourceC398 difference raw6712; decide +kernel
    rw [ha]
    exact (canonical6712 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA398 sourceB398 sourceC398
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm398, Integer.Sparse.eval]
  linarith only [hs]

def sourceA399 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceB399 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC399 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm399 : Integer.Sparse Master := [(Sum.inr 2191, 1), (Sum.inr 2192, 1), (Sum.inr 2196, 2), (Sum.inr 2245, 1), (Sum.inr 2662, 1), (Sum.inr 2663, 1), (Sum.inr 2666, 2), (Sum.inr 2709, 1), (Sum.inr 2711, 1), (Sum.inr 2714, 2), (Sum.inr 2715, 2), (Sum.inr 2723, 2), (Sum.inr 2724, 2), (Sum.inr 2732, 2), (Sum.inr 2753, 1), (Sum.inr 2754, 1), (Sum.inr 2768, 2), (Sum.inr 2940, 1), (Sum.inr 3030, 1), (Sum.inr 3081, 1), (Sum.inr 3089, 2)]

theorem sourceEq399 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm399 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA399 + difference 0 1) (sourceB399 + difference 1 0) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3030) := by
    have ha : (tripleCharges (sourceA399 + difference 0 1) (sourceB399 + difference 1 0) sourceC399) = raw7533 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw7533; decide +kernel
    rw [ha]
    exact (canonical7533 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA399 + difference 0 2) (sourceB399 + difference 2 0) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA399 + difference 0 2) (sourceB399 + difference 2 0) sourceC399) = raw6393 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw6393; decide +kernel
    rw [ha]
    exact (canonical6393 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA399 + difference 0 3) (sourceB399 + difference 3 0) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA399 + difference 0 3) (sourceB399 + difference 3 0) sourceC399) = raw7534 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw7534; decide +kernel
    rw [ha]
    exact (canonical7534 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA399 + difference 0 4) (sourceB399 + difference 4 0) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3081) := by
    have ha : (tripleCharges (sourceA399 + difference 0 4) (sourceB399 + difference 4 0) sourceC399) = raw7242 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw7242; decide +kernel
    rw [ha]
    exact (canonical7242 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA399 + difference 0 5) (sourceB399 + difference 5 0) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2940) := by
    have ha : (tripleCharges (sourceA399 + difference 0 5) (sourceB399 + difference 5 0) sourceC399) = raw7535 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw7535; decide +kernel
    rw [ha]
    exact (canonical7535 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA399 + difference 1 0) (sourceB399 + difference 0 1) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA399 + difference 1 0) (sourceB399 + difference 0 1) sourceC399) = raw5709 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw5709; decide +kernel
    rw [ha]
    exact (canonical5709 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA399 + difference 1 2) (sourceB399 + difference 2 1) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA399 + difference 1 2) (sourceB399 + difference 2 1) sourceC399) = raw6397 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw6397; decide +kernel
    rw [ha]
    exact (canonical6397 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA399 + difference 1 3) (sourceB399 + difference 3 1) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA399 + difference 1 3) (sourceB399 + difference 3 1) sourceC399) = raw7536 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw7536; decide +kernel
    rw [ha]
    exact (canonical7536 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA399 + difference 1 4) (sourceB399 + difference 4 1) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA399 + difference 1 4) (sourceB399 + difference 4 1) sourceC399) = raw5688 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw5688; decide +kernel
    rw [ha]
    exact (canonical5688 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA399 + difference 1 5) (sourceB399 + difference 5 1) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA399 + difference 1 5) (sourceB399 + difference 5 1) sourceC399) = raw7537 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw7537; decide +kernel
    rw [ha]
    exact (canonical7537 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA399 + difference 2 0) (sourceB399 + difference 0 2) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA399 + difference 2 0) (sourceB399 + difference 0 2) sourceC399) = raw7538 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw7538; decide +kernel
    rw [ha]
    exact (canonical7538 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA399 + difference 2 1) (sourceB399 + difference 1 2) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2666) := by
    have ha : (tripleCharges (sourceA399 + difference 2 1) (sourceB399 + difference 1 2) sourceC399) = raw7539 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw7539; decide +kernel
    rw [ha]
    exact (canonical7539 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA399 + difference 2 3) (sourceB399 + difference 3 2) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA399 + difference 2 3) (sourceB399 + difference 3 2) sourceC399) = raw7540 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw7540; decide +kernel
    rw [ha]
    exact (canonical7540 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA399 + difference 2 4) (sourceB399 + difference 4 2) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA399 + difference 2 4) (sourceB399 + difference 4 2) sourceC399) = raw7249 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw7249; decide +kernel
    rw [ha]
    exact (canonical7249 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA399 + difference 2 5) (sourceB399 + difference 5 2) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2715) := by
    have ha : (tripleCharges (sourceA399 + difference 2 5) (sourceB399 + difference 5 2) sourceC399) = raw7541 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw7541; decide +kernel
    rw [ha]
    exact (canonical7541 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA399 + difference 3 0) (sourceB399 + difference 0 3) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA399 + difference 3 0) (sourceB399 + difference 0 3) sourceC399) = raw7070 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw7070; decide +kernel
    rw [ha]
    exact (canonical7070 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA399 + difference 3 1) (sourceB399 + difference 1 3) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2666) := by
    have ha : (tripleCharges (sourceA399 + difference 3 1) (sourceB399 + difference 1 3) sourceC399) = raw7071 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw7071; decide +kernel
    rw [ha]
    exact (canonical7071 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA399 + difference 3 2) (sourceB399 + difference 2 3) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA399 + difference 3 2) (sourceB399 + difference 2 3) sourceC399) = raw6406 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw6406; decide +kernel
    rw [ha]
    exact (canonical6406 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA399 + difference 3 4) (sourceB399 + difference 4 3) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA399 + difference 3 4) (sourceB399 + difference 4 3) sourceC399) = raw6742 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw6742; decide +kernel
    rw [ha]
    exact (canonical6742 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA399 + difference 3 5) (sourceB399 + difference 5 3) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2715) := by
    have ha : (tripleCharges (sourceA399 + difference 3 5) (sourceB399 + difference 5 3) sourceC399) = raw7072 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw7072; decide +kernel
    rw [ha]
    exact (canonical7072 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA399 + difference 4 0) (sourceB399 + difference 0 4) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA399 + difference 4 0) (sourceB399 + difference 0 4) sourceC399) = raw6399 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw6399; decide +kernel
    rw [ha]
    exact (canonical6399 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA399 + difference 4 1) (sourceB399 + difference 1 4) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2663) := by
    have ha : (tripleCharges (sourceA399 + difference 4 1) (sourceB399 + difference 1 4) sourceC399) = raw6400 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw6400; decide +kernel
    rw [ha]
    exact (canonical6400 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA399 + difference 4 2) (sourceB399 + difference 2 4) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA399 + difference 4 2) (sourceB399 + difference 2 4) sourceC399) = raw6058 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw6058; decide +kernel
    rw [ha]
    exact (canonical6058 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA399 + difference 4 3) (sourceB399 + difference 3 4) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA399 + difference 4 3) (sourceB399 + difference 3 4) sourceC399) = raw6053 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw6053; decide +kernel
    rw [ha]
    exact (canonical6053 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA399 + difference 4 5) (sourceB399 + difference 5 4) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2711) := by
    have ha : (tripleCharges (sourceA399 + difference 4 5) (sourceB399 + difference 5 4) sourceC399) = raw6402 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw6402; decide +kernel
    rw [ha]
    exact (canonical6402 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA399 + difference 5 0) (sourceB399 + difference 0 5) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA399 + difference 5 0) (sourceB399 + difference 0 5) sourceC399) = raw7250 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw7250; decide +kernel
    rw [ha]
    exact (canonical7250 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA399 + difference 5 1) (sourceB399 + difference 1 5) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2662) := by
    have ha : (tripleCharges (sourceA399 + difference 5 1) (sourceB399 + difference 1 5) sourceC399) = raw7251 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw7251; decide +kernel
    rw [ha]
    exact (canonical7251 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA399 + difference 5 2) (sourceB399 + difference 2 5) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA399 + difference 5 2) (sourceB399 + difference 2 5) sourceC399) = raw6412 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw6412; decide +kernel
    rw [ha]
    exact (canonical6412 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA399 + difference 5 3) (sourceB399 + difference 3 5) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA399 + difference 5 3) (sourceB399 + difference 3 5) sourceC399) = raw7252 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw7252; decide +kernel
    rw [ha]
    exact (canonical7252 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA399 + difference 5 4) (sourceB399 + difference 4 5) sourceC399) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA399 + difference 5 4) (sourceB399 + difference 4 5) sourceC399) = raw6740 := by
      apply Matrix.ext; unfold tripleCharges sourceA399 sourceB399 sourceC399 difference raw6740; decide +kernel
    rw [ha]
    exact (canonical6740 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA399 sourceB399 sourceC399
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm399, Integer.Sparse.eval]
  linarith only [hs]

def sourceA400 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceB400 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC400 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm400 : Integer.Sparse Master := [(Sum.inr 2693, 1), (Sum.inr 2694, 1), (Sum.inr 2697, 1), (Sum.inr 2722, 2), (Sum.inr 3015, 2), (Sum.inr 3016, 2), (Sum.inr 3018, 2), (Sum.inr 3038, 2), (Sum.inr 3063, 1), (Sum.inr 3065, 1), (Sum.inr 3067, 1), (Sum.inr 3068, 1), (Sum.inr 3075, 1), (Sum.inr 3077, 1), (Sum.inr 3086, 2), (Sum.inr 3088, 2), (Sum.inr 3101, 2), (Sum.inr 3196, 2), (Sum.inr 3197, 1), (Sum.inr 3209, 1), (Sum.inr 3223, 1)]

theorem sourceEq400 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm400 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA400 + difference 0 1) (sourceB400 + difference 1 0) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA400 + difference 0 1) (sourceB400 + difference 1 0) sourceC400) = raw7542 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw7542; decide +kernel
    rw [ha]
    exact (canonical7542 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA400 + difference 0 2) (sourceB400 + difference 2 0) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA400 + difference 0 2) (sourceB400 + difference 2 0) sourceC400) = raw6415 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw6415; decide +kernel
    rw [ha]
    exact (canonical6415 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA400 + difference 0 3) (sourceB400 + difference 3 0) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA400 + difference 0 3) (sourceB400 + difference 3 0) sourceC400) = raw7543 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw7543; decide +kernel
    rw [ha]
    exact (canonical7543 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA400 + difference 0 4) (sourceB400 + difference 4 0) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA400 + difference 0 4) (sourceB400 + difference 4 0) sourceC400) = raw7260 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw7260; decide +kernel
    rw [ha]
    exact (canonical7260 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA400 + difference 0 5) (sourceB400 + difference 5 0) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2693) := by
    have ha : (tripleCharges (sourceA400 + difference 0 5) (sourceB400 + difference 5 0) sourceC400) = raw7544 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw7544; decide +kernel
    rw [ha]
    exact (canonical7544 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA400 + difference 1 0) (sourceB400 + difference 0 1) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA400 + difference 1 0) (sourceB400 + difference 0 1) sourceC400) = raw5739 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw5739; decide +kernel
    rw [ha]
    exact (canonical5739 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA400 + difference 1 2) (sourceB400 + difference 2 1) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA400 + difference 1 2) (sourceB400 + difference 2 1) sourceC400) = raw6419 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw6419; decide +kernel
    rw [ha]
    exact (canonical6419 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA400 + difference 1 3) (sourceB400 + difference 3 1) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA400 + difference 1 3) (sourceB400 + difference 3 1) sourceC400) = raw7545 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw7545; decide +kernel
    rw [ha]
    exact (canonical7545 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA400 + difference 1 4) (sourceB400 + difference 4 1) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA400 + difference 1 4) (sourceB400 + difference 4 1) sourceC400) = raw5718 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw5718; decide +kernel
    rw [ha]
    exact (canonical5718 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA400 + difference 1 5) (sourceB400 + difference 5 1) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA400 + difference 1 5) (sourceB400 + difference 5 1) sourceC400) = raw7546 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw7546; decide +kernel
    rw [ha]
    exact (canonical7546 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA400 + difference 2 0) (sourceB400 + difference 0 2) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3196) := by
    have ha : (tripleCharges (sourceA400 + difference 2 0) (sourceB400 + difference 0 2) sourceC400) = raw7547 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw7547; decide +kernel
    rw [ha]
    exact (canonical7547 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA400 + difference 2 1) (sourceB400 + difference 1 2) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3018) := by
    have ha : (tripleCharges (sourceA400 + difference 2 1) (sourceB400 + difference 1 2) sourceC400) = raw7548 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw7548; decide +kernel
    rw [ha]
    exact (canonical7548 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA400 + difference 2 3) (sourceB400 + difference 3 2) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA400 + difference 2 3) (sourceB400 + difference 3 2) sourceC400) = raw7549 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw7549; decide +kernel
    rw [ha]
    exact (canonical7549 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA400 + difference 2 4) (sourceB400 + difference 4 2) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA400 + difference 2 4) (sourceB400 + difference 4 2) sourceC400) = raw7267 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw7267; decide +kernel
    rw [ha]
    exact (canonical7267 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA400 + difference 2 5) (sourceB400 + difference 5 2) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3015) := by
    have ha : (tripleCharges (sourceA400 + difference 2 5) (sourceB400 + difference 5 2) sourceC400) = raw7550 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw7550; decide +kernel
    rw [ha]
    exact (canonical7550 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA400 + difference 3 0) (sourceB400 + difference 0 3) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3196) := by
    have ha : (tripleCharges (sourceA400 + difference 3 0) (sourceB400 + difference 0 3) sourceC400) = raw7084 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw7084; decide +kernel
    rw [ha]
    exact (canonical7084 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA400 + difference 3 1) (sourceB400 + difference 1 3) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3018) := by
    have ha : (tripleCharges (sourceA400 + difference 3 1) (sourceB400 + difference 1 3) sourceC400) = raw7085 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw7085; decide +kernel
    rw [ha]
    exact (canonical7085 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA400 + difference 3 2) (sourceB400 + difference 2 3) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA400 + difference 3 2) (sourceB400 + difference 2 3) sourceC400) = raw6428 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw6428; decide +kernel
    rw [ha]
    exact (canonical6428 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA400 + difference 3 4) (sourceB400 + difference 4 3) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA400 + difference 3 4) (sourceB400 + difference 4 3) sourceC400) = raw6770 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw6770; decide +kernel
    rw [ha]
    exact (canonical6770 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA400 + difference 3 5) (sourceB400 + difference 5 3) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3015) := by
    have ha : (tripleCharges (sourceA400 + difference 3 5) (sourceB400 + difference 5 3) sourceC400) = raw7086 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw7086; decide +kernel
    rw [ha]
    exact (canonical7086 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA400 + difference 4 0) (sourceB400 + difference 0 4) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA400 + difference 4 0) (sourceB400 + difference 0 4) sourceC400) = raw6421 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw6421; decide +kernel
    rw [ha]
    exact (canonical6421 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA400 + difference 4 1) (sourceB400 + difference 1 4) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3067) := by
    have ha : (tripleCharges (sourceA400 + difference 4 1) (sourceB400 + difference 1 4) sourceC400) = raw6422 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw6422; decide +kernel
    rw [ha]
    exact (canonical6422 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA400 + difference 4 2) (sourceB400 + difference 2 4) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA400 + difference 4 2) (sourceB400 + difference 2 4) sourceC400) = raw6088 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw6088; decide +kernel
    rw [ha]
    exact (canonical6088 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA400 + difference 4 3) (sourceB400 + difference 3 4) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA400 + difference 4 3) (sourceB400 + difference 3 4) sourceC400) = raw6083 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw6083; decide +kernel
    rw [ha]
    exact (canonical6083 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA400 + difference 4 5) (sourceB400 + difference 5 4) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3063) := by
    have ha : (tripleCharges (sourceA400 + difference 4 5) (sourceB400 + difference 5 4) sourceC400) = raw6424 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw6424; decide +kernel
    rw [ha]
    exact (canonical6424 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA400 + difference 5 0) (sourceB400 + difference 0 5) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3209) := by
    have ha : (tripleCharges (sourceA400 + difference 5 0) (sourceB400 + difference 0 5) sourceC400) = raw7268 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw7268; decide +kernel
    rw [ha]
    exact (canonical7268 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA400 + difference 5 1) (sourceB400 + difference 1 5) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3068) := by
    have ha : (tripleCharges (sourceA400 + difference 5 1) (sourceB400 + difference 1 5) sourceC400) = raw7269 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw7269; decide +kernel
    rw [ha]
    exact (canonical7269 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA400 + difference 5 2) (sourceB400 + difference 2 5) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA400 + difference 5 2) (sourceB400 + difference 2 5) sourceC400) = raw6434 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw6434; decide +kernel
    rw [ha]
    exact (canonical6434 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA400 + difference 5 3) (sourceB400 + difference 3 5) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA400 + difference 5 3) (sourceB400 + difference 3 5) sourceC400) = raw7270 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw7270; decide +kernel
    rw [ha]
    exact (canonical7270 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA400 + difference 5 4) (sourceB400 + difference 4 5) sourceC400) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA400 + difference 5 4) (sourceB400 + difference 4 5) sourceC400) = raw6768 := by
      apply Matrix.ext; unfold tripleCharges sourceA400 sourceB400 sourceC400 difference raw6768; decide +kernel
    rw [ha]
    exact (canonical6768 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA400 sourceB400 sourceC400
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm400, Integer.Sparse.eval]
  linarith only [hs]

def sourceA401 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceB401 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC401 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm401 : Integer.Sparse Master := [(Sum.inr 2552, 1), (Sum.inr 3488, 1), (Sum.inr 3493, 1), (Sum.inr 3533, 2), (Sum.inr 3539, 1), (Sum.inr 4084, -1)]

theorem sourceEq401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm401 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA401 + difference 0 0) (sourceB401 + difference 0 0) sourceC401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA401 + difference 0 0) (sourceB401 + difference 0 0) sourceC401) = raw6450 := by
      apply Matrix.ext; unfold tripleCharges sourceA401 sourceB401 sourceC401 difference raw6450; decide +kernel
    rw [ha]
    exact (canonical6450 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA401 + difference 0 1) (sourceB401 + difference 1 0) sourceC401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3488) := by
    have ha : (tripleCharges (sourceA401 + difference 0 1) (sourceB401 + difference 1 0) sourceC401) = raw7551 := by
      apply Matrix.ext; unfold tripleCharges sourceA401 sourceB401 sourceC401 difference raw7551; decide +kernel
    rw [ha]
    exact (canonical7551 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA401 + difference 0 2) (sourceB401 + difference 2 0) sourceC401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA401 + difference 0 2) (sourceB401 + difference 2 0) sourceC401) = raw6437 := by
      apply Matrix.ext; unfold tripleCharges sourceA401 sourceB401 sourceC401 difference raw6437; decide +kernel
    rw [ha]
    exact (canonical6437 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA401 + difference 0 3) (sourceB401 + difference 3 0) sourceC401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA401 + difference 0 3) (sourceB401 + difference 3 0) sourceC401) = raw7552 := by
      apply Matrix.ext; unfold tripleCharges sourceA401 sourceB401 sourceC401 difference raw7552; decide +kernel
    rw [ha]
    exact (canonical7552 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA401 + difference 0 4) (sourceB401 + difference 4 0) sourceC401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3493) := by
    have ha : (tripleCharges (sourceA401 + difference 0 4) (sourceB401 + difference 4 0) sourceC401) = raw7278 := by
      apply Matrix.ext; unfold tripleCharges sourceA401 sourceB401 sourceC401 difference raw7278; decide +kernel
    rw [ha]
    exact (canonical7278 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA401 + difference 0 5) (sourceB401 + difference 5 0) sourceC401) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2552) := by
    have ha : (tripleCharges (sourceA401 + difference 0 5) (sourceB401 + difference 5 0) sourceC401) = raw7553 := by
      apply Matrix.ext; unfold tripleCharges sourceA401 sourceB401 sourceC401 difference raw7553; decide +kernel
    rw [ha]
    exact (canonical7553 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA401 + sourceB401) sourceC401) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA401 + sourceB401) sourceC401) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA401 sourceB401 sourceC401 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA401 sourceB401 sourceC401
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm401, Integer.Sparse.eval]
  linarith only [hs]

def sourceA402 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceB402 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC402 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm402 : Integer.Sparse Master := [(Sum.inr 2033, 1), (Sum.inr 2034, 2), (Sum.inr 2051, 1), (Sum.inr 2277, 1), (Sum.inr 3539, 1), (Sum.inr 4084, -1)]

theorem sourceEq402 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm402 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA402 + difference 0 0) (sourceB402 + difference 0 0) sourceC402) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA402 + difference 0 0) (sourceB402 + difference 0 0) sourceC402) = raw6450 := by
      apply Matrix.ext; unfold tripleCharges sourceA402 sourceB402 sourceC402 difference raw6450; decide +kernel
    rw [ha]
    exact (canonical6450 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA402 + difference 1 0) (sourceB402 + difference 0 1) sourceC402) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA402 + difference 1 0) (sourceB402 + difference 0 1) sourceC402) = raw5760 := by
      apply Matrix.ext; unfold tripleCharges sourceA402 sourceB402 sourceC402 difference raw5760; decide +kernel
    rw [ha]
    exact (canonical5760 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA402 + difference 2 0) (sourceB402 + difference 0 2) sourceC402) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2034) := by
    have ha : (tripleCharges (sourceA402 + difference 2 0) (sourceB402 + difference 0 2) sourceC402) = raw7554 := by
      apply Matrix.ext; unfold tripleCharges sourceA402 sourceB402 sourceC402 difference raw7554; decide +kernel
    rw [ha]
    exact (canonical7554 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA402 + difference 3 0) (sourceB402 + difference 0 3) sourceC402) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2034) := by
    have ha : (tripleCharges (sourceA402 + difference 3 0) (sourceB402 + difference 0 3) sourceC402) = raw7096 := by
      apply Matrix.ext; unfold tripleCharges sourceA402 sourceB402 sourceC402 difference raw7096; decide +kernel
    rw [ha]
    exact (canonical7096 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA402 + difference 4 0) (sourceB402 + difference 0 4) sourceC402) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2033) := by
    have ha : (tripleCharges (sourceA402 + difference 4 0) (sourceB402 + difference 0 4) sourceC402) = raw6440 := by
      apply Matrix.ext; unfold tripleCharges sourceA402 sourceB402 sourceC402 difference raw6440; decide +kernel
    rw [ha]
    exact (canonical6440 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA402 + difference 5 0) (sourceB402 + difference 0 5) sourceC402) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2051) := by
    have ha : (tripleCharges (sourceA402 + difference 5 0) (sourceB402 + difference 0 5) sourceC402) = raw7280 := by
      apply Matrix.ext; unfold tripleCharges sourceA402 sourceB402 sourceC402 difference raw7280; decide +kernel
    rw [ha]
    exact (canonical7280 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA402 + sourceB402) sourceC402) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA402 + sourceB402) sourceC402) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA402 sourceB402 sourceC402 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA402 sourceB402 sourceC402
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm402, Integer.Sparse.eval]
  linarith only [hs]

def sourceA403 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceB403 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC403 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm403 : Integer.Sparse Master := [(Sum.inr 2277, 1), (Sum.inr 2738, 1), (Sum.inr 3539, 1), (Sum.inr 3625, 1), (Sum.inr 3632, 2), (Sum.inr 4084, -1)]

theorem sourceEq403 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm403 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA403 + difference 1 0) (sourceB403 + difference 0 1) sourceC403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA403 + difference 1 0) (sourceB403 + difference 0 1) sourceC403) = raw5760 := by
      apply Matrix.ext; unfold tripleCharges sourceA403 sourceB403 sourceC403 difference raw5760; decide +kernel
    rw [ha]
    exact (canonical5760 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA403 + difference 1 1) (sourceB403 + difference 1 1) sourceC403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA403 + difference 1 1) (sourceB403 + difference 1 1) sourceC403) = raw6450 := by
      apply Matrix.ext; unfold tripleCharges sourceA403 sourceB403 sourceC403 difference raw6450; decide +kernel
    rw [ha]
    exact (canonical6450 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA403 + difference 1 2) (sourceB403 + difference 2 1) sourceC403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3632) := by
    have ha : (tripleCharges (sourceA403 + difference 1 2) (sourceB403 + difference 2 1) sourceC403) = raw6445 := by
      apply Matrix.ext; unfold tripleCharges sourceA403 sourceB403 sourceC403 difference raw6445; decide +kernel
    rw [ha]
    exact (canonical6445 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA403 + difference 1 3) (sourceB403 + difference 3 1) sourceC403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3632) := by
    have ha : (tripleCharges (sourceA403 + difference 1 3) (sourceB403 + difference 3 1) sourceC403) = raw7555 := by
      apply Matrix.ext; unfold tripleCharges sourceA403 sourceB403 sourceC403 difference raw7555; decide +kernel
    rw [ha]
    exact (canonical7555 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA403 + difference 1 4) (sourceB403 + difference 4 1) sourceC403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA403 + difference 1 4) (sourceB403 + difference 4 1) sourceC403) = raw5749 := by
      apply Matrix.ext; unfold tripleCharges sourceA403 sourceB403 sourceC403 difference raw5749; decide +kernel
    rw [ha]
    exact (canonical5749 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA403 + difference 1 5) (sourceB403 + difference 5 1) sourceC403) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA403 + difference 1 5) (sourceB403 + difference 5 1) sourceC403) = raw7556 := by
      apply Matrix.ext; unfold tripleCharges sourceA403 sourceB403 sourceC403 difference raw7556; decide +kernel
    rw [ha]
    exact (canonical7556 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA403 + sourceB403) sourceC403) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA403 + sourceB403) sourceC403) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA403 sourceB403 sourceC403 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA403 sourceB403 sourceC403
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm403, Integer.Sparse.eval]
  linarith only [hs]

def sourceA404 : Charge := ![1, -1, 1, 1, 0, -2]
def sourceB404 : Charge := ![2, 1, -1, -1, -1, 0]
def sourceC404 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm404 : Integer.Sparse Master := [(Sum.inr 3381, 1), (Sum.inr 3382, 2), (Sum.inr 3388, 1), (Sum.inr 3488, 1), (Sum.inr 3539, 1), (Sum.inr 4084, -1)]

theorem sourceEq404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm404 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA404 + difference 0 1) (sourceB404 + difference 1 0) sourceC404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3488) := by
    have ha : (tripleCharges (sourceA404 + difference 0 1) (sourceB404 + difference 1 0) sourceC404) = raw7551 := by
      apply Matrix.ext; unfold tripleCharges sourceA404 sourceB404 sourceC404 difference raw7551; decide +kernel
    rw [ha]
    exact (canonical7551 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA404 + difference 1 1) (sourceB404 + difference 1 1) sourceC404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA404 + difference 1 1) (sourceB404 + difference 1 1) sourceC404) = raw6450 := by
      apply Matrix.ext; unfold tripleCharges sourceA404 sourceB404 sourceC404 difference raw6450; decide +kernel
    rw [ha]
    exact (canonical6450 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA404 + difference 2 1) (sourceB404 + difference 1 2) sourceC404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3382) := by
    have ha : (tripleCharges (sourceA404 + difference 2 1) (sourceB404 + difference 1 2) sourceC404) = raw7557 := by
      apply Matrix.ext; unfold tripleCharges sourceA404 sourceB404 sourceC404 difference raw7557; decide +kernel
    rw [ha]
    exact (canonical7557 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA404 + difference 3 1) (sourceB404 + difference 1 3) sourceC404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3382) := by
    have ha : (tripleCharges (sourceA404 + difference 3 1) (sourceB404 + difference 1 3) sourceC404) = raw7098 := by
      apply Matrix.ext; unfold tripleCharges sourceA404 sourceB404 sourceC404 difference raw7098; decide +kernel
    rw [ha]
    exact (canonical7098 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA404 + difference 4 1) (sourceB404 + difference 1 4) sourceC404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3381) := by
    have ha : (tripleCharges (sourceA404 + difference 4 1) (sourceB404 + difference 1 4) sourceC404) = raw6447 := by
      apply Matrix.ext; unfold tripleCharges sourceA404 sourceB404 sourceC404 difference raw6447; decide +kernel
    rw [ha]
    exact (canonical6447 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA404 + difference 5 1) (sourceB404 + difference 1 5) sourceC404) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3388) := by
    have ha : (tripleCharges (sourceA404 + difference 5 1) (sourceB404 + difference 1 5) sourceC404) = raw7285 := by
      apply Matrix.ext; unfold tripleCharges sourceA404 sourceB404 sourceC404 difference raw7285; decide +kernel
    rw [ha]
    exact (canonical7285 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA404 + sourceB404) sourceC404) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA404 + sourceB404) sourceC404) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA404 sourceB404 sourceC404 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA404 sourceB404 sourceC404
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm404, Integer.Sparse.eval]
  linarith only [hs]

def sourceA405 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB405 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC405 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceForm405 : Integer.Sparse Master := [(Sum.inr 4619, 3), (Sum.inr 4621, 1), (Sum.inr 4627, 1), (Sum.inr 4871, 3), (Sum.inr 4899, 1), (Sum.inr 5170, 6), (Sum.inr 5176, 3), (Sum.inr 5302, 3), (Sum.inr 5306, 3), (Sum.inr 5308, 1), (Sum.inr 5443, 3), (Sum.inr 5455, 1), (Sum.inr 5456, 1)]

theorem sourceEq405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm405 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA405 + difference 0 1) (sourceB405 + difference 1 0) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA405 + difference 0 1) (sourceB405 + difference 1 0) sourceC405) = raw2652 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw2652; decide +kernel
    rw [ha]
    exact (canonical2652 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA405 + difference 0 2) (sourceB405 + difference 2 0) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA405 + difference 0 2) (sourceB405 + difference 2 0) sourceC405) = raw2653 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw2653; decide +kernel
    rw [ha]
    exact (canonical2653 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA405 + difference 0 3) (sourceB405 + difference 3 0) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA405 + difference 0 3) (sourceB405 + difference 3 0) sourceC405) = raw2654 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw2654; decide +kernel
    rw [ha]
    exact (canonical2654 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA405 + difference 0 4) (sourceB405 + difference 4 0) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5456) := by
    have ha : (tripleCharges (sourceA405 + difference 0 4) (sourceB405 + difference 4 0) sourceC405) = raw4379 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw4379; decide +kernel
    rw [ha]
    exact (canonical4379 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA405 + difference 0 5) (sourceB405 + difference 5 0) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA405 + difference 0 5) (sourceB405 + difference 5 0) sourceC405) = raw2655 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw2655; decide +kernel
    rw [ha]
    exact (canonical2655 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA405 + difference 1 0) (sourceB405 + difference 0 1) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA405 + difference 1 0) (sourceB405 + difference 0 1) sourceC405) = raw7558 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw7558; decide +kernel
    rw [ha]
    exact (canonical7558 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA405 + difference 1 2) (sourceB405 + difference 2 1) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA405 + difference 1 2) (sourceB405 + difference 2 1) sourceC405) = raw7559 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw7559; decide +kernel
    rw [ha]
    exact (canonical7559 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA405 + difference 1 3) (sourceB405 + difference 3 1) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA405 + difference 1 3) (sourceB405 + difference 3 1) sourceC405) = raw7560 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw7560; decide +kernel
    rw [ha]
    exact (canonical7560 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA405 + difference 1 4) (sourceB405 + difference 4 1) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA405 + difference 1 4) (sourceB405 + difference 4 1) sourceC405) = raw2636 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw2636; decide +kernel
    rw [ha]
    exact (canonical2636 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA405 + difference 1 5) (sourceB405 + difference 5 1) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA405 + difference 1 5) (sourceB405 + difference 5 1) sourceC405) = raw7561 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw7561; decide +kernel
    rw [ha]
    exact (canonical7561 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA405 + difference 2 0) (sourceB405 + difference 0 2) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA405 + difference 2 0) (sourceB405 + difference 0 2) sourceC405) = raw7562 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw7562; decide +kernel
    rw [ha]
    exact (canonical7562 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA405 + difference 2 1) (sourceB405 + difference 1 2) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA405 + difference 2 1) (sourceB405 + difference 1 2) sourceC405) = raw7563 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw7563; decide +kernel
    rw [ha]
    exact (canonical7563 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA405 + difference 2 3) (sourceB405 + difference 3 2) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA405 + difference 2 3) (sourceB405 + difference 3 2) sourceC405) = raw7564 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw7564; decide +kernel
    rw [ha]
    exact (canonical7564 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA405 + difference 2 4) (sourceB405 + difference 4 2) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA405 + difference 2 4) (sourceB405 + difference 4 2) sourceC405) = raw2641 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw2641; decide +kernel
    rw [ha]
    exact (canonical2641 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA405 + difference 2 5) (sourceB405 + difference 5 2) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA405 + difference 2 5) (sourceB405 + difference 5 2) sourceC405) = raw7565 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw7565; decide +kernel
    rw [ha]
    exact (canonical7565 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA405 + difference 3 0) (sourceB405 + difference 0 3) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4619) := by
    have ha : (tripleCharges (sourceA405 + difference 3 0) (sourceB405 + difference 0 3) sourceC405) = raw7566 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw7566; decide +kernel
    rw [ha]
    exact (canonical7566 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA405 + difference 3 1) (sourceB405 + difference 1 3) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA405 + difference 3 1) (sourceB405 + difference 1 3) sourceC405) = raw7567 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw7567; decide +kernel
    rw [ha]
    exact (canonical7567 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA405 + difference 3 2) (sourceB405 + difference 2 3) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA405 + difference 3 2) (sourceB405 + difference 2 3) sourceC405) = raw7568 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw7568; decide +kernel
    rw [ha]
    exact (canonical7568 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA405 + difference 3 4) (sourceB405 + difference 4 3) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA405 + difference 3 4) (sourceB405 + difference 4 3) sourceC405) = raw2646 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw2646; decide +kernel
    rw [ha]
    exact (canonical2646 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA405 + difference 3 5) (sourceB405 + difference 5 3) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA405 + difference 3 5) (sourceB405 + difference 5 3) sourceC405) = raw7569 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw7569; decide +kernel
    rw [ha]
    exact (canonical7569 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA405 + difference 4 0) (sourceB405 + difference 0 4) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4627) := by
    have ha : (tripleCharges (sourceA405 + difference 4 0) (sourceB405 + difference 0 4) sourceC405) = raw7570 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw7570; decide +kernel
    rw [ha]
    exact (canonical7570 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA405 + difference 4 1) (sourceB405 + difference 1 4) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA405 + difference 4 1) (sourceB405 + difference 1 4) sourceC405) = raw7571 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw7571; decide +kernel
    rw [ha]
    exact (canonical7571 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA405 + difference 4 2) (sourceB405 + difference 2 4) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA405 + difference 4 2) (sourceB405 + difference 2 4) sourceC405) = raw7572 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw7572; decide +kernel
    rw [ha]
    exact (canonical7572 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA405 + difference 4 3) (sourceB405 + difference 3 4) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA405 + difference 4 3) (sourceB405 + difference 3 4) sourceC405) = raw7573 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw7573; decide +kernel
    rw [ha]
    exact (canonical7573 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA405 + difference 4 5) (sourceB405 + difference 5 4) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA405 + difference 4 5) (sourceB405 + difference 5 4) sourceC405) = raw7574 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw7574; decide +kernel
    rw [ha]
    exact (canonical7574 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA405 + difference 5 0) (sourceB405 + difference 0 5) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4621) := by
    have ha : (tripleCharges (sourceA405 + difference 5 0) (sourceB405 + difference 0 5) sourceC405) = raw4392 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw4392; decide +kernel
    rw [ha]
    exact (canonical4392 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA405 + difference 5 1) (sourceB405 + difference 1 5) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA405 + difference 5 1) (sourceB405 + difference 1 5) sourceC405) = raw4393 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw4393; decide +kernel
    rw [ha]
    exact (canonical4393 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA405 + difference 5 2) (sourceB405 + difference 2 5) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA405 + difference 5 2) (sourceB405 + difference 2 5) sourceC405) = raw4394 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw4394; decide +kernel
    rw [ha]
    exact (canonical4394 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA405 + difference 5 3) (sourceB405 + difference 3 5) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4871) := by
    have ha : (tripleCharges (sourceA405 + difference 5 3) (sourceB405 + difference 3 5) sourceC405) = raw4395 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw4395; decide +kernel
    rw [ha]
    exact (canonical4395 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA405 + difference 5 4) (sourceB405 + difference 4 5) sourceC405) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA405 + difference 5 4) (sourceB405 + difference 4 5) sourceC405) = raw2656 := by
      apply Matrix.ext; unfold tripleCharges sourceA405 sourceB405 sourceC405 difference raw2656; decide +kernel
    rw [ha]
    exact (canonical2656 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA405 sourceB405 sourceC405
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm405, Integer.Sparse.eval]
  linarith only [hs]

def sourceA406 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB406 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceC406 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceForm406 : Integer.Sparse Master := [(Sum.inr 1294, 3), (Sum.inr 1297, 1), (Sum.inr 1311, 1), (Sum.inr 2112, 3), (Sum.inr 2281, 1), (Sum.inr 2954, 6), (Sum.inr 2968, 3), (Sum.inr 3054, 3), (Sum.inr 3120, 3), (Sum.inr 3124, 1), (Sum.inr 3889, 3), (Sum.inr 3916, 1), (Sum.inr 4019, 1)]

theorem sourceEq406 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm406 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA406 + difference 0 1) (sourceB406 + difference 1 0) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA406 + difference 0 1) (sourceB406 + difference 1 0) sourceC406) = raw7575 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7575; decide +kernel
    rw [ha]
    exact (canonical7575 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA406 + difference 0 2) (sourceB406 + difference 2 0) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA406 + difference 0 2) (sourceB406 + difference 2 0) sourceC406) = raw7576 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7576; decide +kernel
    rw [ha]
    exact (canonical7576 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA406 + difference 0 3) (sourceB406 + difference 3 0) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA406 + difference 0 3) (sourceB406 + difference 3 0) sourceC406) = raw7577 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7577; decide +kernel
    rw [ha]
    exact (canonical7577 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA406 + difference 0 4) (sourceB406 + difference 4 0) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3916) := by
    have ha : (tripleCharges (sourceA406 + difference 0 4) (sourceB406 + difference 4 0) sourceC406) = raw4405 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw4405; decide +kernel
    rw [ha]
    exact (canonical4405 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA406 + difference 0 5) (sourceB406 + difference 5 0) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4019) := by
    have ha : (tripleCharges (sourceA406 + difference 0 5) (sourceB406 + difference 5 0) sourceC406) = raw7578 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7578; decide +kernel
    rw [ha]
    exact (canonical7578 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA406 + difference 1 0) (sourceB406 + difference 0 1) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA406 + difference 1 0) (sourceB406 + difference 0 1) sourceC406) = raw7579 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7579; decide +kernel
    rw [ha]
    exact (canonical7579 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA406 + difference 1 2) (sourceB406 + difference 2 1) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA406 + difference 1 2) (sourceB406 + difference 2 1) sourceC406) = raw7580 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7580; decide +kernel
    rw [ha]
    exact (canonical7580 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA406 + difference 1 3) (sourceB406 + difference 3 1) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA406 + difference 1 3) (sourceB406 + difference 3 1) sourceC406) = raw7581 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7581; decide +kernel
    rw [ha]
    exact (canonical7581 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA406 + difference 1 4) (sourceB406 + difference 4 1) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA406 + difference 1 4) (sourceB406 + difference 4 1) sourceC406) = raw4410 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw4410; decide +kernel
    rw [ha]
    exact (canonical4410 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA406 + difference 1 5) (sourceB406 + difference 5 1) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA406 + difference 1 5) (sourceB406 + difference 5 1) sourceC406) = raw7582 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7582; decide +kernel
    rw [ha]
    exact (canonical7582 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA406 + difference 2 0) (sourceB406 + difference 0 2) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA406 + difference 2 0) (sourceB406 + difference 0 2) sourceC406) = raw7583 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7583; decide +kernel
    rw [ha]
    exact (canonical7583 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA406 + difference 2 1) (sourceB406 + difference 1 2) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA406 + difference 2 1) (sourceB406 + difference 1 2) sourceC406) = raw7584 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7584; decide +kernel
    rw [ha]
    exact (canonical7584 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA406 + difference 2 3) (sourceB406 + difference 3 2) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA406 + difference 2 3) (sourceB406 + difference 3 2) sourceC406) = raw7585 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7585; decide +kernel
    rw [ha]
    exact (canonical7585 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA406 + difference 2 4) (sourceB406 + difference 4 2) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA406 + difference 2 4) (sourceB406 + difference 4 2) sourceC406) = raw4415 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw4415; decide +kernel
    rw [ha]
    exact (canonical4415 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA406 + difference 2 5) (sourceB406 + difference 5 2) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA406 + difference 2 5) (sourceB406 + difference 5 2) sourceC406) = raw7586 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7586; decide +kernel
    rw [ha]
    exact (canonical7586 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA406 + difference 3 0) (sourceB406 + difference 0 3) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA406 + difference 3 0) (sourceB406 + difference 0 3) sourceC406) = raw7587 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7587; decide +kernel
    rw [ha]
    exact (canonical7587 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA406 + difference 3 1) (sourceB406 + difference 1 3) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA406 + difference 3 1) (sourceB406 + difference 1 3) sourceC406) = raw7588 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7588; decide +kernel
    rw [ha]
    exact (canonical7588 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA406 + difference 3 2) (sourceB406 + difference 2 3) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA406 + difference 3 2) (sourceB406 + difference 2 3) sourceC406) = raw7589 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7589; decide +kernel
    rw [ha]
    exact (canonical7589 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA406 + difference 3 4) (sourceB406 + difference 4 3) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA406 + difference 3 4) (sourceB406 + difference 4 3) sourceC406) = raw4420 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw4420; decide +kernel
    rw [ha]
    exact (canonical4420 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA406 + difference 3 5) (sourceB406 + difference 5 3) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA406 + difference 3 5) (sourceB406 + difference 5 3) sourceC406) = raw7590 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7590; decide +kernel
    rw [ha]
    exact (canonical7590 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA406 + difference 4 0) (sourceB406 + difference 0 4) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1311) := by
    have ha : (tripleCharges (sourceA406 + difference 4 0) (sourceB406 + difference 0 4) sourceC406) = raw7591 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7591; decide +kernel
    rw [ha]
    exact (canonical7591 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA406 + difference 4 1) (sourceB406 + difference 1 4) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA406 + difference 4 1) (sourceB406 + difference 1 4) sourceC406) = raw7592 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7592; decide +kernel
    rw [ha]
    exact (canonical7592 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA406 + difference 4 2) (sourceB406 + difference 2 4) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA406 + difference 4 2) (sourceB406 + difference 2 4) sourceC406) = raw7593 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7593; decide +kernel
    rw [ha]
    exact (canonical7593 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA406 + difference 4 3) (sourceB406 + difference 3 4) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2968) := by
    have ha : (tripleCharges (sourceA406 + difference 4 3) (sourceB406 + difference 3 4) sourceC406) = raw7594 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7594; decide +kernel
    rw [ha]
    exact (canonical7594 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA406 + difference 4 5) (sourceB406 + difference 5 4) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA406 + difference 4 5) (sourceB406 + difference 5 4) sourceC406) = raw7595 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7595; decide +kernel
    rw [ha]
    exact (canonical7595 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA406 + difference 5 0) (sourceB406 + difference 0 5) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1297) := by
    have ha : (tripleCharges (sourceA406 + difference 5 0) (sourceB406 + difference 0 5) sourceC406) = raw4421 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw4421; decide +kernel
    rw [ha]
    exact (canonical4421 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA406 + difference 5 1) (sourceB406 + difference 1 5) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA406 + difference 5 1) (sourceB406 + difference 1 5) sourceC406) = raw4422 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw4422; decide +kernel
    rw [ha]
    exact (canonical4422 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA406 + difference 5 2) (sourceB406 + difference 2 5) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA406 + difference 5 2) (sourceB406 + difference 2 5) sourceC406) = raw4423 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw4423; decide +kernel
    rw [ha]
    exact (canonical4423 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA406 + difference 5 3) (sourceB406 + difference 3 5) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA406 + difference 5 3) (sourceB406 + difference 3 5) sourceC406) = raw4424 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw4424; decide +kernel
    rw [ha]
    exact (canonical4424 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA406 + difference 5 4) (sourceB406 + difference 4 5) sourceC406) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA406 + difference 5 4) (sourceB406 + difference 4 5) sourceC406) = raw7596 := by
      apply Matrix.ext; unfold tripleCharges sourceA406 sourceB406 sourceC406 difference raw7596; decide +kernel
    rw [ha]
    exact (canonical7596 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA406 sourceB406 sourceC406
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm406, Integer.Sparse.eval]
  linarith only [hs]

def sourceA407 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB407 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC407 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceForm407 : Integer.Sparse Master := [(Sum.inr 4503, 3), (Sum.inr 4507, 1), (Sum.inr 4510, 1), (Sum.inr 5105, 6), (Sum.inr 5109, 3), (Sum.inr 5110, 3), (Sum.inr 5294, 3), (Sum.inr 5296, 1), (Sum.inr 5304, 3), (Sum.inr 5305, 1), (Sum.inr 5451, 3), (Sum.inr 5455, 1), (Sum.inr 5494, 1)]

theorem sourceEq407 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm407 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA407 + difference 0 1) (sourceB407 + difference 1 0) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA407 + difference 0 1) (sourceB407 + difference 1 0) sourceC407) = raw2872 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw2872; decide +kernel
    rw [ha]
    exact (canonical2872 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA407 + difference 0 2) (sourceB407 + difference 2 0) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA407 + difference 0 2) (sourceB407 + difference 2 0) sourceC407) = raw2873 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw2873; decide +kernel
    rw [ha]
    exact (canonical2873 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA407 + difference 0 3) (sourceB407 + difference 3 0) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5451) := by
    have ha : (tripleCharges (sourceA407 + difference 0 3) (sourceB407 + difference 3 0) sourceC407) = raw2874 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw2874; decide +kernel
    rw [ha]
    exact (canonical2874 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA407 + difference 0 4) (sourceB407 + difference 4 0) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA407 + difference 0 4) (sourceB407 + difference 4 0) sourceC407) = raw3230 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw3230; decide +kernel
    rw [ha]
    exact (canonical3230 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA407 + difference 0 5) (sourceB407 + difference 5 0) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5494) := by
    have ha : (tripleCharges (sourceA407 + difference 0 5) (sourceB407 + difference 5 0) sourceC407) = raw2875 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw2875; decide +kernel
    rw [ha]
    exact (canonical2875 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA407 + difference 1 0) (sourceB407 + difference 0 1) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA407 + difference 1 0) (sourceB407 + difference 0 1) sourceC407) = raw7597 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw7597; decide +kernel
    rw [ha]
    exact (canonical7597 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA407 + difference 1 2) (sourceB407 + difference 2 1) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA407 + difference 1 2) (sourceB407 + difference 2 1) sourceC407) = raw7598 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw7598; decide +kernel
    rw [ha]
    exact (canonical7598 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA407 + difference 1 3) (sourceB407 + difference 3 1) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA407 + difference 1 3) (sourceB407 + difference 3 1) sourceC407) = raw7599 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw7599; decide +kernel
    rw [ha]
    exact (canonical7599 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA407 + difference 1 4) (sourceB407 + difference 4 1) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA407 + difference 1 4) (sourceB407 + difference 4 1) sourceC407) = raw2856 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw2856; decide +kernel
    rw [ha]
    exact (canonical2856 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA407 + difference 1 5) (sourceB407 + difference 5 1) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA407 + difference 1 5) (sourceB407 + difference 5 1) sourceC407) = raw3213 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw3213; decide +kernel
    rw [ha]
    exact (canonical3213 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA407 + difference 2 0) (sourceB407 + difference 0 2) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA407 + difference 2 0) (sourceB407 + difference 0 2) sourceC407) = raw7600 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw7600; decide +kernel
    rw [ha]
    exact (canonical7600 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA407 + difference 2 1) (sourceB407 + difference 1 2) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA407 + difference 2 1) (sourceB407 + difference 1 2) sourceC407) = raw7601 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw7601; decide +kernel
    rw [ha]
    exact (canonical7601 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA407 + difference 2 3) (sourceB407 + difference 3 2) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA407 + difference 2 3) (sourceB407 + difference 3 2) sourceC407) = raw7602 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw7602; decide +kernel
    rw [ha]
    exact (canonical7602 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA407 + difference 2 4) (sourceB407 + difference 4 2) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA407 + difference 2 4) (sourceB407 + difference 4 2) sourceC407) = raw2861 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw2861; decide +kernel
    rw [ha]
    exact (canonical2861 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA407 + difference 2 5) (sourceB407 + difference 5 2) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA407 + difference 2 5) (sourceB407 + difference 5 2) sourceC407) = raw3217 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw3217; decide +kernel
    rw [ha]
    exact (canonical3217 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA407 + difference 3 0) (sourceB407 + difference 0 3) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA407 + difference 3 0) (sourceB407 + difference 0 3) sourceC407) = raw7603 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw7603; decide +kernel
    rw [ha]
    exact (canonical7603 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA407 + difference 3 1) (sourceB407 + difference 1 3) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA407 + difference 3 1) (sourceB407 + difference 1 3) sourceC407) = raw7604 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw7604; decide +kernel
    rw [ha]
    exact (canonical7604 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA407 + difference 3 2) (sourceB407 + difference 2 3) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA407 + difference 3 2) (sourceB407 + difference 2 3) sourceC407) = raw7605 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw7605; decide +kernel
    rw [ha]
    exact (canonical7605 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA407 + difference 3 4) (sourceB407 + difference 4 3) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA407 + difference 3 4) (sourceB407 + difference 4 3) sourceC407) = raw2866 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw2866; decide +kernel
    rw [ha]
    exact (canonical2866 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA407 + difference 3 5) (sourceB407 + difference 5 3) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA407 + difference 3 5) (sourceB407 + difference 5 3) sourceC407) = raw3221 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw3221; decide +kernel
    rw [ha]
    exact (canonical3221 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA407 + difference 4 0) (sourceB407 + difference 0 4) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4510) := by
    have ha : (tripleCharges (sourceA407 + difference 4 0) (sourceB407 + difference 0 4) sourceC407) = raw7606 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw7606; decide +kernel
    rw [ha]
    exact (canonical7606 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA407 + difference 4 1) (sourceB407 + difference 1 4) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA407 + difference 4 1) (sourceB407 + difference 1 4) sourceC407) = raw7607 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw7607; decide +kernel
    rw [ha]
    exact (canonical7607 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA407 + difference 4 2) (sourceB407 + difference 2 4) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA407 + difference 4 2) (sourceB407 + difference 2 4) sourceC407) = raw7608 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw7608; decide +kernel
    rw [ha]
    exact (canonical7608 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA407 + difference 4 3) (sourceB407 + difference 3 4) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA407 + difference 4 3) (sourceB407 + difference 3 4) sourceC407) = raw7609 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw7609; decide +kernel
    rw [ha]
    exact (canonical7609 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA407 + difference 4 5) (sourceB407 + difference 5 4) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5305) := by
    have ha : (tripleCharges (sourceA407 + difference 4 5) (sourceB407 + difference 5 4) sourceC407) = raw3225 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw3225; decide +kernel
    rw [ha]
    exact (canonical3225 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA407 + difference 5 0) (sourceB407 + difference 0 5) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4507) := by
    have ha : (tripleCharges (sourceA407 + difference 5 0) (sourceB407 + difference 0 5) sourceC407) = raw7610 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw7610; decide +kernel
    rw [ha]
    exact (canonical7610 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA407 + difference 5 1) (sourceB407 + difference 1 5) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA407 + difference 5 1) (sourceB407 + difference 1 5) sourceC407) = raw7611 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw7611; decide +kernel
    rw [ha]
    exact (canonical7611 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA407 + difference 5 2) (sourceB407 + difference 2 5) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA407 + difference 5 2) (sourceB407 + difference 2 5) sourceC407) = raw7612 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw7612; decide +kernel
    rw [ha]
    exact (canonical7612 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA407 + difference 5 3) (sourceB407 + difference 3 5) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA407 + difference 5 3) (sourceB407 + difference 3 5) sourceC407) = raw7613 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw7613; decide +kernel
    rw [ha]
    exact (canonical7613 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA407 + difference 5 4) (sourceB407 + difference 4 5) sourceC407) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA407 + difference 5 4) (sourceB407 + difference 4 5) sourceC407) = raw2876 := by
      apply Matrix.ext; unfold tripleCharges sourceA407 sourceB407 sourceC407 difference raw2876; decide +kernel
    rw [ha]
    exact (canonical2876 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA407 sourceB407 sourceC407
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm407, Integer.Sparse.eval]
  linarith only [hs]

def sourceA408 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB408 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC408 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceForm408 : Integer.Sparse Master := [(Sum.inr 1087, 3), (Sum.inr 1091, 1), (Sum.inr 1094, 1), (Sum.inr 2515, 6), (Sum.inr 2519, 3), (Sum.inr 2522, 3), (Sum.inr 2768, 3), (Sum.inr 2770, 1), (Sum.inr 2782, 3), (Sum.inr 2783, 1), (Sum.inr 3987, 3), (Sum.inr 4019, 1), (Sum.inr 4020, 1)]

theorem sourceEq408 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm408 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA408 + difference 0 1) (sourceB408 + difference 1 0) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA408 + difference 0 1) (sourceB408 + difference 1 0) sourceC408) = raw7614 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7614; decide +kernel
    rw [ha]
    exact (canonical7614 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA408 + difference 0 2) (sourceB408 + difference 2 0) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA408 + difference 0 2) (sourceB408 + difference 2 0) sourceC408) = raw7615 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7615; decide +kernel
    rw [ha]
    exact (canonical7615 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA408 + difference 0 3) (sourceB408 + difference 3 0) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3987) := by
    have ha : (tripleCharges (sourceA408 + difference 0 3) (sourceB408 + difference 3 0) sourceC408) = raw7616 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7616; decide +kernel
    rw [ha]
    exact (canonical7616 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA408 + difference 0 4) (sourceB408 + difference 4 0) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4019) := by
    have ha : (tripleCharges (sourceA408 + difference 0 4) (sourceB408 + difference 4 0) sourceC408) = raw7617 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7617; decide +kernel
    rw [ha]
    exact (canonical7617 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA408 + difference 0 5) (sourceB408 + difference 5 0) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4020) := by
    have ha : (tripleCharges (sourceA408 + difference 0 5) (sourceB408 + difference 5 0) sourceC408) = raw7618 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7618; decide +kernel
    rw [ha]
    exact (canonical7618 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA408 + difference 1 0) (sourceB408 + difference 0 1) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA408 + difference 1 0) (sourceB408 + difference 0 1) sourceC408) = raw7619 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7619; decide +kernel
    rw [ha]
    exact (canonical7619 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA408 + difference 1 2) (sourceB408 + difference 2 1) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA408 + difference 1 2) (sourceB408 + difference 2 1) sourceC408) = raw7620 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7620; decide +kernel
    rw [ha]
    exact (canonical7620 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA408 + difference 1 3) (sourceB408 + difference 3 1) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA408 + difference 1 3) (sourceB408 + difference 3 1) sourceC408) = raw7621 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7621; decide +kernel
    rw [ha]
    exact (canonical7621 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA408 + difference 1 4) (sourceB408 + difference 4 1) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA408 + difference 1 4) (sourceB408 + difference 4 1) sourceC408) = raw7622 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7622; decide +kernel
    rw [ha]
    exact (canonical7622 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA408 + difference 1 5) (sourceB408 + difference 5 1) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA408 + difference 1 5) (sourceB408 + difference 5 1) sourceC408) = raw7623 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7623; decide +kernel
    rw [ha]
    exact (canonical7623 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA408 + difference 2 0) (sourceB408 + difference 0 2) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA408 + difference 2 0) (sourceB408 + difference 0 2) sourceC408) = raw7624 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7624; decide +kernel
    rw [ha]
    exact (canonical7624 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA408 + difference 2 1) (sourceB408 + difference 1 2) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA408 + difference 2 1) (sourceB408 + difference 1 2) sourceC408) = raw7625 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7625; decide +kernel
    rw [ha]
    exact (canonical7625 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA408 + difference 2 3) (sourceB408 + difference 3 2) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA408 + difference 2 3) (sourceB408 + difference 3 2) sourceC408) = raw7626 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7626; decide +kernel
    rw [ha]
    exact (canonical7626 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA408 + difference 2 4) (sourceB408 + difference 4 2) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA408 + difference 2 4) (sourceB408 + difference 4 2) sourceC408) = raw7627 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7627; decide +kernel
    rw [ha]
    exact (canonical7627 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA408 + difference 2 5) (sourceB408 + difference 5 2) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA408 + difference 2 5) (sourceB408 + difference 5 2) sourceC408) = raw7628 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7628; decide +kernel
    rw [ha]
    exact (canonical7628 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA408 + difference 3 0) (sourceB408 + difference 0 3) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA408 + difference 3 0) (sourceB408 + difference 0 3) sourceC408) = raw7629 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7629; decide +kernel
    rw [ha]
    exact (canonical7629 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA408 + difference 3 1) (sourceB408 + difference 1 3) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA408 + difference 3 1) (sourceB408 + difference 1 3) sourceC408) = raw7630 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7630; decide +kernel
    rw [ha]
    exact (canonical7630 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA408 + difference 3 2) (sourceB408 + difference 2 3) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA408 + difference 3 2) (sourceB408 + difference 2 3) sourceC408) = raw7631 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7631; decide +kernel
    rw [ha]
    exact (canonical7631 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA408 + difference 3 4) (sourceB408 + difference 4 3) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA408 + difference 3 4) (sourceB408 + difference 4 3) sourceC408) = raw7632 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7632; decide +kernel
    rw [ha]
    exact (canonical7632 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA408 + difference 3 5) (sourceB408 + difference 5 3) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA408 + difference 3 5) (sourceB408 + difference 5 3) sourceC408) = raw7633 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7633; decide +kernel
    rw [ha]
    exact (canonical7633 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA408 + difference 4 0) (sourceB408 + difference 0 4) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1094) := by
    have ha : (tripleCharges (sourceA408 + difference 4 0) (sourceB408 + difference 0 4) sourceC408) = raw7634 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7634; decide +kernel
    rw [ha]
    exact (canonical7634 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA408 + difference 4 1) (sourceB408 + difference 1 4) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA408 + difference 4 1) (sourceB408 + difference 1 4) sourceC408) = raw7635 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7635; decide +kernel
    rw [ha]
    exact (canonical7635 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA408 + difference 4 2) (sourceB408 + difference 2 4) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA408 + difference 4 2) (sourceB408 + difference 2 4) sourceC408) = raw7636 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7636; decide +kernel
    rw [ha]
    exact (canonical7636 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA408 + difference 4 3) (sourceB408 + difference 3 4) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA408 + difference 4 3) (sourceB408 + difference 3 4) sourceC408) = raw7637 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7637; decide +kernel
    rw [ha]
    exact (canonical7637 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA408 + difference 4 5) (sourceB408 + difference 5 4) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA408 + difference 4 5) (sourceB408 + difference 5 4) sourceC408) = raw7638 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7638; decide +kernel
    rw [ha]
    exact (canonical7638 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA408 + difference 5 0) (sourceB408 + difference 0 5) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA408 + difference 5 0) (sourceB408 + difference 0 5) sourceC408) = raw7639 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7639; decide +kernel
    rw [ha]
    exact (canonical7639 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA408 + difference 5 1) (sourceB408 + difference 1 5) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA408 + difference 5 1) (sourceB408 + difference 1 5) sourceC408) = raw7640 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7640; decide +kernel
    rw [ha]
    exact (canonical7640 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA408 + difference 5 2) (sourceB408 + difference 2 5) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA408 + difference 5 2) (sourceB408 + difference 2 5) sourceC408) = raw7641 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7641; decide +kernel
    rw [ha]
    exact (canonical7641 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA408 + difference 5 3) (sourceB408 + difference 3 5) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA408 + difference 5 3) (sourceB408 + difference 3 5) sourceC408) = raw7642 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7642; decide +kernel
    rw [ha]
    exact (canonical7642 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA408 + difference 5 4) (sourceB408 + difference 4 5) sourceC408) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2770) := by
    have ha : (tripleCharges (sourceA408 + difference 5 4) (sourceB408 + difference 4 5) sourceC408) = raw7643 := by
      apply Matrix.ext; unfold tripleCharges sourceA408 sourceB408 sourceC408 difference raw7643; decide +kernel
    rw [ha]
    exact (canonical7643 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA408 sourceB408 sourceC408
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm408, Integer.Sparse.eval]
  linarith only [hs]

def sourceA409 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB409 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC409 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm409 : Integer.Sparse Master := [(Sum.inr 4896, 3), (Sum.inr 4899, 1), (Sum.inr 4901, 1), (Sum.inr 5260, 6), (Sum.inr 5275, 3), (Sum.inr 5276, 3), (Sum.inr 5291, 3), (Sum.inr 5294, 3), (Sum.inr 5295, 3), (Sum.inr 5305, 1), (Sum.inr 5308, 1), (Sum.inr 5309, 1), (Sum.inr 5311, 1)]

theorem sourceEq409 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm409 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA409 + difference 0 1) (sourceB409 + difference 1 0) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA409 + difference 0 1) (sourceB409 + difference 1 0) sourceC409) = raw6013 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw6013; decide +kernel
    rw [ha]
    exact (canonical6013 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA409 + difference 0 2) (sourceB409 + difference 2 0) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA409 + difference 0 2) (sourceB409 + difference 2 0) sourceC409) = raw7644 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw7644; decide +kernel
    rw [ha]
    exact (canonical7644 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA409 + difference 0 3) (sourceB409 + difference 3 0) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA409 + difference 0 3) (sourceB409 + difference 3 0) sourceC409) = raw7645 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw7645; decide +kernel
    rw [ha]
    exact (canonical7645 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA409 + difference 0 4) (sourceB409 + difference 4 0) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5308) := by
    have ha : (tripleCharges (sourceA409 + difference 0 4) (sourceB409 + difference 4 0) sourceC409) = raw7646 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw7646; decide +kernel
    rw [ha]
    exact (canonical7646 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA409 + difference 0 5) (sourceB409 + difference 5 0) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5305) := by
    have ha : (tripleCharges (sourceA409 + difference 0 5) (sourceB409 + difference 5 0) sourceC409) = raw7647 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw7647; decide +kernel
    rw [ha]
    exact (canonical7647 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA409 + difference 1 0) (sourceB409 + difference 0 1) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA409 + difference 1 0) (sourceB409 + difference 0 1) sourceC409) = raw7648 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw7648; decide +kernel
    rw [ha]
    exact (canonical7648 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA409 + difference 1 2) (sourceB409 + difference 2 1) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA409 + difference 1 2) (sourceB409 + difference 2 1) sourceC409) = raw7649 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw7649; decide +kernel
    rw [ha]
    exact (canonical7649 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA409 + difference 1 3) (sourceB409 + difference 3 1) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA409 + difference 1 3) (sourceB409 + difference 3 1) sourceC409) = raw7650 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw7650; decide +kernel
    rw [ha]
    exact (canonical7650 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA409 + difference 1 4) (sourceB409 + difference 4 1) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA409 + difference 1 4) (sourceB409 + difference 4 1) sourceC409) = raw7651 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw7651; decide +kernel
    rw [ha]
    exact (canonical7651 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA409 + difference 1 5) (sourceB409 + difference 5 1) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA409 + difference 1 5) (sourceB409 + difference 5 1) sourceC409) = raw7652 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw7652; decide +kernel
    rw [ha]
    exact (canonical7652 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA409 + difference 2 0) (sourceB409 + difference 0 2) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA409 + difference 2 0) (sourceB409 + difference 0 2) sourceC409) = raw7653 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw7653; decide +kernel
    rw [ha]
    exact (canonical7653 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA409 + difference 2 1) (sourceB409 + difference 1 2) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA409 + difference 2 1) (sourceB409 + difference 1 2) sourceC409) = raw6023 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw6023; decide +kernel
    rw [ha]
    exact (canonical6023 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA409 + difference 2 3) (sourceB409 + difference 3 2) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA409 + difference 2 3) (sourceB409 + difference 3 2) sourceC409) = raw7654 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw7654; decide +kernel
    rw [ha]
    exact (canonical7654 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA409 + difference 2 4) (sourceB409 + difference 4 2) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA409 + difference 2 4) (sourceB409 + difference 4 2) sourceC409) = raw7527 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw7527; decide +kernel
    rw [ha]
    exact (canonical7527 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA409 + difference 2 5) (sourceB409 + difference 5 2) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA409 + difference 2 5) (sourceB409 + difference 5 2) sourceC409) = raw7655 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw7655; decide +kernel
    rw [ha]
    exact (canonical7655 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA409 + difference 3 0) (sourceB409 + difference 0 3) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA409 + difference 3 0) (sourceB409 + difference 0 3) sourceC409) = raw6373 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw6373; decide +kernel
    rw [ha]
    exact (canonical6373 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA409 + difference 3 1) (sourceB409 + difference 1 3) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA409 + difference 3 1) (sourceB409 + difference 1 3) sourceC409) = raw6028 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw6028; decide +kernel
    rw [ha]
    exact (canonical6028 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA409 + difference 3 2) (sourceB409 + difference 2 3) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA409 + difference 3 2) (sourceB409 + difference 2 3) sourceC409) = raw6374 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw6374; decide +kernel
    rw [ha]
    exact (canonical6374 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA409 + difference 3 4) (sourceB409 + difference 4 3) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA409 + difference 3 4) (sourceB409 + difference 4 3) sourceC409) = raw6375 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw6375; decide +kernel
    rw [ha]
    exact (canonical6375 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA409 + difference 3 5) (sourceB409 + difference 5 3) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA409 + difference 3 5) (sourceB409 + difference 5 3) sourceC409) = raw6376 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw6376; decide +kernel
    rw [ha]
    exact (canonical6376 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA409 + difference 4 0) (sourceB409 + difference 0 4) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA409 + difference 4 0) (sourceB409 + difference 0 4) sourceC409) = raw6015 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw6015; decide +kernel
    rw [ha]
    exact (canonical6015 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA409 + difference 4 1) (sourceB409 + difference 1 4) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA409 + difference 4 1) (sourceB409 + difference 1 4) sourceC409) = raw6386 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw6386; decide +kernel
    rw [ha]
    exact (canonical6386 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA409 + difference 4 2) (sourceB409 + difference 2 4) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA409 + difference 4 2) (sourceB409 + difference 2 4) sourceC409) = raw6016 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw6016; decide +kernel
    rw [ha]
    exact (canonical6016 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA409 + difference 4 3) (sourceB409 + difference 3 4) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA409 + difference 4 3) (sourceB409 + difference 3 4) sourceC409) = raw6017 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw6017; decide +kernel
    rw [ha]
    exact (canonical6017 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA409 + difference 4 5) (sourceB409 + difference 5 4) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5311) := by
    have ha : (tripleCharges (sourceA409 + difference 4 5) (sourceB409 + difference 5 4) sourceC409) = raw6019 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw6019; decide +kernel
    rw [ha]
    exact (canonical6019 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA409 + difference 5 0) (sourceB409 + difference 0 5) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4901) := by
    have ha : (tripleCharges (sourceA409 + difference 5 0) (sourceB409 + difference 0 5) sourceC409) = raw7656 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw7656; decide +kernel
    rw [ha]
    exact (canonical7656 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA409 + difference 5 1) (sourceB409 + difference 1 5) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA409 + difference 5 1) (sourceB409 + difference 1 5) sourceC409) = raw6039 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw6039; decide +kernel
    rw [ha]
    exact (canonical6039 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA409 + difference 5 2) (sourceB409 + difference 2 5) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA409 + difference 5 2) (sourceB409 + difference 2 5) sourceC409) = raw7657 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw7657; decide +kernel
    rw [ha]
    exact (canonical7657 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA409 + difference 5 3) (sourceB409 + difference 3 5) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA409 + difference 5 3) (sourceB409 + difference 3 5) sourceC409) = raw7658 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw7658; decide +kernel
    rw [ha]
    exact (canonical7658 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA409 + difference 5 4) (sourceB409 + difference 4 5) sourceC409) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5309) := by
    have ha : (tripleCharges (sourceA409 + difference 5 4) (sourceB409 + difference 4 5) sourceC409) = raw7659 := by
      apply Matrix.ext; unfold tripleCharges sourceA409 sourceB409 sourceC409 difference raw7659; decide +kernel
    rw [ha]
    exact (canonical7659 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA409 sourceB409 sourceC409
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm409, Integer.Sparse.eval]
  linarith only [hs]

def sourceA410 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB410 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC410 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm410 : Integer.Sparse Master := [(Sum.inr 2266, 3), (Sum.inr 2293, 1), (Sum.inr 2294, 1), (Sum.inr 2724, 6), (Sum.inr 2743, 3), (Sum.inr 2744, 3), (Sum.inr 2768, 3), (Sum.inr 2769, 3), (Sum.inr 2787, 1), (Sum.inr 2789, 1), (Sum.inr 3103, 3), (Sum.inr 3124, 1), (Sum.inr 3125, 1)]

theorem sourceEq410 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm410 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA410 + difference 0 1) (sourceB410 + difference 1 0) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA410 + difference 0 1) (sourceB410 + difference 1 0) sourceC410) = raw6043 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw6043; decide +kernel
    rw [ha]
    exact (canonical6043 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA410 + difference 0 2) (sourceB410 + difference 2 0) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA410 + difference 0 2) (sourceB410 + difference 2 0) sourceC410) = raw7660 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw7660; decide +kernel
    rw [ha]
    exact (canonical7660 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA410 + difference 0 3) (sourceB410 + difference 3 0) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3103) := by
    have ha : (tripleCharges (sourceA410 + difference 0 3) (sourceB410 + difference 3 0) sourceC410) = raw7661 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw7661; decide +kernel
    rw [ha]
    exact (canonical7661 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA410 + difference 0 4) (sourceB410 + difference 4 0) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3124) := by
    have ha : (tripleCharges (sourceA410 + difference 0 4) (sourceB410 + difference 4 0) sourceC410) = raw7662 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw7662; decide +kernel
    rw [ha]
    exact (canonical7662 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA410 + difference 0 5) (sourceB410 + difference 5 0) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3125) := by
    have ha : (tripleCharges (sourceA410 + difference 0 5) (sourceB410 + difference 5 0) sourceC410) = raw7663 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw7663; decide +kernel
    rw [ha]
    exact (canonical7663 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA410 + difference 1 0) (sourceB410 + difference 0 1) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA410 + difference 1 0) (sourceB410 + difference 0 1) sourceC410) = raw7664 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw7664; decide +kernel
    rw [ha]
    exact (canonical7664 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA410 + difference 1 2) (sourceB410 + difference 2 1) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA410 + difference 1 2) (sourceB410 + difference 2 1) sourceC410) = raw7665 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw7665; decide +kernel
    rw [ha]
    exact (canonical7665 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA410 + difference 1 3) (sourceB410 + difference 3 1) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA410 + difference 1 3) (sourceB410 + difference 3 1) sourceC410) = raw7666 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw7666; decide +kernel
    rw [ha]
    exact (canonical7666 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA410 + difference 1 4) (sourceB410 + difference 4 1) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA410 + difference 1 4) (sourceB410 + difference 4 1) sourceC410) = raw7667 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw7667; decide +kernel
    rw [ha]
    exact (canonical7667 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA410 + difference 1 5) (sourceB410 + difference 5 1) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA410 + difference 1 5) (sourceB410 + difference 5 1) sourceC410) = raw7668 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw7668; decide +kernel
    rw [ha]
    exact (canonical7668 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA410 + difference 2 0) (sourceB410 + difference 0 2) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA410 + difference 2 0) (sourceB410 + difference 0 2) sourceC410) = raw7669 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw7669; decide +kernel
    rw [ha]
    exact (canonical7669 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA410 + difference 2 1) (sourceB410 + difference 1 2) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA410 + difference 2 1) (sourceB410 + difference 1 2) sourceC410) = raw6053 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw6053; decide +kernel
    rw [ha]
    exact (canonical6053 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA410 + difference 2 3) (sourceB410 + difference 3 2) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA410 + difference 2 3) (sourceB410 + difference 3 2) sourceC410) = raw7670 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw7670; decide +kernel
    rw [ha]
    exact (canonical7670 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA410 + difference 2 4) (sourceB410 + difference 4 2) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA410 + difference 2 4) (sourceB410 + difference 4 2) sourceC410) = raw7536 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw7536; decide +kernel
    rw [ha]
    exact (canonical7536 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA410 + difference 2 5) (sourceB410 + difference 5 2) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA410 + difference 2 5) (sourceB410 + difference 5 2) sourceC410) = raw7671 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw7671; decide +kernel
    rw [ha]
    exact (canonical7671 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA410 + difference 3 0) (sourceB410 + difference 0 3) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA410 + difference 3 0) (sourceB410 + difference 0 3) sourceC410) = raw6395 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw6395; decide +kernel
    rw [ha]
    exact (canonical6395 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA410 + difference 3 1) (sourceB410 + difference 1 3) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA410 + difference 3 1) (sourceB410 + difference 1 3) sourceC410) = raw6058 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw6058; decide +kernel
    rw [ha]
    exact (canonical6058 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA410 + difference 3 2) (sourceB410 + difference 2 3) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA410 + difference 3 2) (sourceB410 + difference 2 3) sourceC410) = raw6396 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw6396; decide +kernel
    rw [ha]
    exact (canonical6396 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA410 + difference 3 4) (sourceB410 + difference 4 3) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA410 + difference 3 4) (sourceB410 + difference 4 3) sourceC410) = raw6397 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw6397; decide +kernel
    rw [ha]
    exact (canonical6397 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA410 + difference 3 5) (sourceB410 + difference 5 3) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA410 + difference 3 5) (sourceB410 + difference 5 3) sourceC410) = raw6398 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw6398; decide +kernel
    rw [ha]
    exact (canonical6398 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA410 + difference 4 0) (sourceB410 + difference 0 4) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA410 + difference 4 0) (sourceB410 + difference 0 4) sourceC410) = raw6045 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw6045; decide +kernel
    rw [ha]
    exact (canonical6045 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA410 + difference 4 1) (sourceB410 + difference 1 4) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA410 + difference 4 1) (sourceB410 + difference 1 4) sourceC410) = raw6408 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw6408; decide +kernel
    rw [ha]
    exact (canonical6408 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA410 + difference 4 2) (sourceB410 + difference 2 4) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA410 + difference 4 2) (sourceB410 + difference 2 4) sourceC410) = raw6046 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw6046; decide +kernel
    rw [ha]
    exact (canonical6046 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA410 + difference 4 3) (sourceB410 + difference 3 4) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA410 + difference 4 3) (sourceB410 + difference 3 4) sourceC410) = raw6047 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw6047; decide +kernel
    rw [ha]
    exact (canonical6047 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA410 + difference 4 5) (sourceB410 + difference 5 4) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA410 + difference 4 5) (sourceB410 + difference 5 4) sourceC410) = raw6049 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw6049; decide +kernel
    rw [ha]
    exact (canonical6049 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA410 + difference 5 0) (sourceB410 + difference 0 5) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA410 + difference 5 0) (sourceB410 + difference 0 5) sourceC410) = raw7672 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw7672; decide +kernel
    rw [ha]
    exact (canonical7672 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA410 + difference 5 1) (sourceB410 + difference 1 5) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA410 + difference 5 1) (sourceB410 + difference 1 5) sourceC410) = raw6069 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw6069; decide +kernel
    rw [ha]
    exact (canonical6069 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA410 + difference 5 2) (sourceB410 + difference 2 5) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA410 + difference 5 2) (sourceB410 + difference 2 5) sourceC410) = raw7673 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw7673; decide +kernel
    rw [ha]
    exact (canonical7673 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA410 + difference 5 3) (sourceB410 + difference 3 5) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA410 + difference 5 3) (sourceB410 + difference 3 5) sourceC410) = raw7674 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw7674; decide +kernel
    rw [ha]
    exact (canonical7674 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA410 + difference 5 4) (sourceB410 + difference 4 5) sourceC410) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2787) := by
    have ha : (tripleCharges (sourceA410 + difference 5 4) (sourceB410 + difference 4 5) sourceC410) = raw7675 := by
      apply Matrix.ext; unfold tripleCharges sourceA410 sourceB410 sourceC410 difference raw7675; decide +kernel
    rw [ha]
    exact (canonical7675 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA410 sourceB410 sourceC410
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm410, Integer.Sparse.eval]
  linarith only [hs]

def sourceA411 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB411 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC411 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm411 : Integer.Sparse Master := [(Sum.inr 2765, 3), (Sum.inr 2777, 3), (Sum.inr 2778, 1), (Sum.inr 2783, 1), (Sum.inr 2786, 1), (Sum.inr 2789, 1), (Sum.inr 3086, 6), (Sum.inr 3098, 3), (Sum.inr 3101, 3), (Sum.inr 3110, 3), (Sum.inr 3123, 1), (Sum.inr 3225, 3), (Sum.inr 3231, 1)]

theorem sourceEq411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm411 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA411 + difference 0 1) (sourceB411 + difference 1 0) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA411 + difference 0 1) (sourceB411 + difference 1 0) sourceC411) = raw6073 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw6073; decide +kernel
    rw [ha]
    exact (canonical6073 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA411 + difference 0 2) (sourceB411 + difference 2 0) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA411 + difference 0 2) (sourceB411 + difference 2 0) sourceC411) = raw7676 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw7676; decide +kernel
    rw [ha]
    exact (canonical7676 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA411 + difference 0 3) (sourceB411 + difference 3 0) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2765) := by
    have ha : (tripleCharges (sourceA411 + difference 0 3) (sourceB411 + difference 3 0) sourceC411) = raw7677 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw7677; decide +kernel
    rw [ha]
    exact (canonical7677 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA411 + difference 0 4) (sourceB411 + difference 4 0) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2786) := by
    have ha : (tripleCharges (sourceA411 + difference 0 4) (sourceB411 + difference 4 0) sourceC411) = raw7678 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw7678; decide +kernel
    rw [ha]
    exact (canonical7678 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA411 + difference 0 5) (sourceB411 + difference 5 0) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA411 + difference 0 5) (sourceB411 + difference 5 0) sourceC411) = raw7679 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw7679; decide +kernel
    rw [ha]
    exact (canonical7679 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA411 + difference 1 0) (sourceB411 + difference 0 1) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA411 + difference 1 0) (sourceB411 + difference 0 1) sourceC411) = raw7680 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw7680; decide +kernel
    rw [ha]
    exact (canonical7680 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA411 + difference 1 2) (sourceB411 + difference 2 1) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA411 + difference 1 2) (sourceB411 + difference 2 1) sourceC411) = raw7681 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw7681; decide +kernel
    rw [ha]
    exact (canonical7681 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA411 + difference 1 3) (sourceB411 + difference 3 1) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA411 + difference 1 3) (sourceB411 + difference 3 1) sourceC411) = raw7682 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw7682; decide +kernel
    rw [ha]
    exact (canonical7682 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA411 + difference 1 4) (sourceB411 + difference 4 1) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA411 + difference 1 4) (sourceB411 + difference 4 1) sourceC411) = raw7683 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw7683; decide +kernel
    rw [ha]
    exact (canonical7683 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA411 + difference 1 5) (sourceB411 + difference 5 1) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA411 + difference 1 5) (sourceB411 + difference 5 1) sourceC411) = raw7684 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw7684; decide +kernel
    rw [ha]
    exact (canonical7684 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA411 + difference 2 0) (sourceB411 + difference 0 2) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA411 + difference 2 0) (sourceB411 + difference 0 2) sourceC411) = raw7685 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw7685; decide +kernel
    rw [ha]
    exact (canonical7685 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA411 + difference 2 1) (sourceB411 + difference 1 2) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA411 + difference 2 1) (sourceB411 + difference 1 2) sourceC411) = raw6083 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw6083; decide +kernel
    rw [ha]
    exact (canonical6083 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA411 + difference 2 3) (sourceB411 + difference 3 2) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA411 + difference 2 3) (sourceB411 + difference 3 2) sourceC411) = raw7686 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw7686; decide +kernel
    rw [ha]
    exact (canonical7686 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA411 + difference 2 4) (sourceB411 + difference 4 2) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA411 + difference 2 4) (sourceB411 + difference 4 2) sourceC411) = raw7545 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw7545; decide +kernel
    rw [ha]
    exact (canonical7545 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA411 + difference 2 5) (sourceB411 + difference 5 2) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA411 + difference 2 5) (sourceB411 + difference 5 2) sourceC411) = raw7687 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw7687; decide +kernel
    rw [ha]
    exact (canonical7687 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA411 + difference 3 0) (sourceB411 + difference 0 3) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA411 + difference 3 0) (sourceB411 + difference 0 3) sourceC411) = raw6417 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw6417; decide +kernel
    rw [ha]
    exact (canonical6417 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA411 + difference 3 1) (sourceB411 + difference 1 3) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA411 + difference 3 1) (sourceB411 + difference 1 3) sourceC411) = raw6088 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw6088; decide +kernel
    rw [ha]
    exact (canonical6088 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA411 + difference 3 2) (sourceB411 + difference 2 3) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA411 + difference 3 2) (sourceB411 + difference 2 3) sourceC411) = raw6418 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw6418; decide +kernel
    rw [ha]
    exact (canonical6418 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA411 + difference 3 4) (sourceB411 + difference 4 3) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA411 + difference 3 4) (sourceB411 + difference 4 3) sourceC411) = raw6419 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw6419; decide +kernel
    rw [ha]
    exact (canonical6419 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA411 + difference 3 5) (sourceB411 + difference 5 3) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA411 + difference 3 5) (sourceB411 + difference 5 3) sourceC411) = raw6420 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw6420; decide +kernel
    rw [ha]
    exact (canonical6420 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA411 + difference 4 0) (sourceB411 + difference 0 4) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2778) := by
    have ha : (tripleCharges (sourceA411 + difference 4 0) (sourceB411 + difference 0 4) sourceC411) = raw6075 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw6075; decide +kernel
    rw [ha]
    exact (canonical6075 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA411 + difference 4 1) (sourceB411 + difference 1 4) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA411 + difference 4 1) (sourceB411 + difference 1 4) sourceC411) = raw6430 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw6430; decide +kernel
    rw [ha]
    exact (canonical6430 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA411 + difference 4 2) (sourceB411 + difference 2 4) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA411 + difference 4 2) (sourceB411 + difference 2 4) sourceC411) = raw6076 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw6076; decide +kernel
    rw [ha]
    exact (canonical6076 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA411 + difference 4 3) (sourceB411 + difference 3 4) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA411 + difference 4 3) (sourceB411 + difference 3 4) sourceC411) = raw6077 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw6077; decide +kernel
    rw [ha]
    exact (canonical6077 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA411 + difference 4 5) (sourceB411 + difference 5 4) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2789) := by
    have ha : (tripleCharges (sourceA411 + difference 4 5) (sourceB411 + difference 5 4) sourceC411) = raw6079 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw6079; decide +kernel
    rw [ha]
    exact (canonical6079 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA411 + difference 5 0) (sourceB411 + difference 0 5) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3231) := by
    have ha : (tripleCharges (sourceA411 + difference 5 0) (sourceB411 + difference 0 5) sourceC411) = raw7688 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw7688; decide +kernel
    rw [ha]
    exact (canonical7688 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA411 + difference 5 1) (sourceB411 + difference 1 5) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA411 + difference 5 1) (sourceB411 + difference 1 5) sourceC411) = raw6099 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw6099; decide +kernel
    rw [ha]
    exact (canonical6099 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA411 + difference 5 2) (sourceB411 + difference 2 5) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA411 + difference 5 2) (sourceB411 + difference 2 5) sourceC411) = raw7689 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw7689; decide +kernel
    rw [ha]
    exact (canonical7689 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA411 + difference 5 3) (sourceB411 + difference 3 5) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA411 + difference 5 3) (sourceB411 + difference 3 5) sourceC411) = raw7690 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw7690; decide +kernel
    rw [ha]
    exact (canonical7690 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA411 + difference 5 4) (sourceB411 + difference 4 5) sourceC411) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3123) := by
    have ha : (tripleCharges (sourceA411 + difference 5 4) (sourceB411 + difference 4 5) sourceC411) = raw7691 := by
      apply Matrix.ext; unfold tripleCharges sourceA411 sourceB411 sourceC411 difference raw7691; decide +kernel
    rw [ha]
    exact (canonical7691 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA411 sourceB411 sourceC411
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm411, Integer.Sparse.eval]
  linarith only [hs]

def sourceA412 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB412 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC412 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm412 : Integer.Sparse Master := [(Sum.inr 2783, 1), (Sum.inr 3582, 3), (Sum.inr 3629, 1), (Sum.inr 3633, 1), (Sum.inr 4084, -1)]

theorem sourceEq412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm412 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA412 + difference 0 0) (sourceB412 + difference 0 0) sourceC412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3633) := by
    have ha : (tripleCharges (sourceA412 + difference 0 0) (sourceB412 + difference 0 0) sourceC412) = raw6121 := by
      apply Matrix.ext; unfold tripleCharges sourceA412 sourceB412 sourceC412 difference raw6121; decide +kernel
    rw [ha]
    exact (canonical6121 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA412 + difference 0 1) (sourceB412 + difference 1 0) sourceC412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA412 + difference 0 1) (sourceB412 + difference 1 0) sourceC412) = raw6104 := by
      apply Matrix.ext; unfold tripleCharges sourceA412 sourceB412 sourceC412 difference raw6104; decide +kernel
    rw [ha]
    exact (canonical6104 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA412 + difference 0 2) (sourceB412 + difference 2 0) sourceC412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA412 + difference 0 2) (sourceB412 + difference 2 0) sourceC412) = raw7692 := by
      apply Matrix.ext; unfold tripleCharges sourceA412 sourceB412 sourceC412 difference raw7692; decide +kernel
    rw [ha]
    exact (canonical7692 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA412 + difference 0 3) (sourceB412 + difference 3 0) sourceC412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA412 + difference 0 3) (sourceB412 + difference 3 0) sourceC412) = raw7693 := by
      apply Matrix.ext; unfold tripleCharges sourceA412 sourceB412 sourceC412 difference raw7693; decide +kernel
    rw [ha]
    exact (canonical7693 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA412 + difference 0 4) (sourceB412 + difference 4 0) sourceC412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3629) := by
    have ha : (tripleCharges (sourceA412 + difference 0 4) (sourceB412 + difference 4 0) sourceC412) = raw7694 := by
      apply Matrix.ext; unfold tripleCharges sourceA412 sourceB412 sourceC412 difference raw7694; decide +kernel
    rw [ha]
    exact (canonical7694 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA412 + difference 0 5) (sourceB412 + difference 5 0) sourceC412) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA412 + difference 0 5) (sourceB412 + difference 5 0) sourceC412) = raw7695 := by
      apply Matrix.ext; unfold tripleCharges sourceA412 sourceB412 sourceC412 difference raw7695; decide +kernel
    rw [ha]
    exact (canonical7695 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA412 + sourceB412) sourceC412) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA412 + sourceB412) sourceC412) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA412 sourceB412 sourceC412 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA412 sourceB412 sourceC412
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm412, Integer.Sparse.eval]
  linarith only [hs]

def sourceA413 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB413 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC413 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm413 : Integer.Sparse Master := [(Sum.inr 3629, 1), (Sum.inr 3632, 3), (Sum.inr 3633, 1), (Sum.inr 3635, 1), (Sum.inr 4084, -1)]

theorem sourceEq413 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm413 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA413 + difference 0 4) (sourceB413 + difference 4 0) sourceC413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3629) := by
    have ha : (tripleCharges (sourceA413 + difference 0 4) (sourceB413 + difference 4 0) sourceC413) = raw7694 := by
      apply Matrix.ext; unfold tripleCharges sourceA413 sourceB413 sourceC413 difference raw7694; decide +kernel
    rw [ha]
    exact (canonical7694 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA413 + difference 1 4) (sourceB413 + difference 4 1) sourceC413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3632) := by
    have ha : (tripleCharges (sourceA413 + difference 1 4) (sourceB413 + difference 4 1) sourceC413) = raw7696 := by
      apply Matrix.ext; unfold tripleCharges sourceA413 sourceB413 sourceC413 difference raw7696; decide +kernel
    rw [ha]
    exact (canonical7696 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA413 + difference 2 4) (sourceB413 + difference 4 2) sourceC413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3632) := by
    have ha : (tripleCharges (sourceA413 + difference 2 4) (sourceB413 + difference 4 2) sourceC413) = raw7555 := by
      apply Matrix.ext; unfold tripleCharges sourceA413 sourceB413 sourceC413 difference raw7555; decide +kernel
    rw [ha]
    exact (canonical7555 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA413 + difference 3 4) (sourceB413 + difference 4 3) sourceC413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3632) := by
    have ha : (tripleCharges (sourceA413 + difference 3 4) (sourceB413 + difference 4 3) sourceC413) = raw6445 := by
      apply Matrix.ext; unfold tripleCharges sourceA413 sourceB413 sourceC413 difference raw6445; decide +kernel
    rw [ha]
    exact (canonical6445 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA413 + difference 4 4) (sourceB413 + difference 4 4) sourceC413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3633) := by
    have ha : (tripleCharges (sourceA413 + difference 4 4) (sourceB413 + difference 4 4) sourceC413) = raw6121 := by
      apply Matrix.ext; unfold tripleCharges sourceA413 sourceB413 sourceC413 difference raw6121; decide +kernel
    rw [ha]
    exact (canonical6121 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA413 + difference 5 4) (sourceB413 + difference 4 5) sourceC413) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3635) := by
    have ha : (tripleCharges (sourceA413 + difference 5 4) (sourceB413 + difference 4 5) sourceC413) = raw7697 := by
      apply Matrix.ext; unfold tripleCharges sourceA413 sourceB413 sourceC413 difference raw7697; decide +kernel
    rw [ha]
    exact (canonical7697 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA413 + sourceB413) sourceC413) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA413 + sourceB413) sourceC413) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA413 sourceB413 sourceC413 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA413 sourceB413 sourceC413
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm413, Integer.Sparse.eval]
  linarith only [hs]

def sourceA414 : Charge := ![1, 0, 0, 0, 1, -2]
def sourceB414 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceC414 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm414 : Integer.Sparse Master := [(Sum.inr 2293, 1), (Sum.inr 3548, 3), (Sum.inr 3633, 1), (Sum.inr 3635, 1), (Sum.inr 4084, -1)]

theorem sourceEq414 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm414 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA414 + difference 5 0) (sourceB414 + difference 0 5) sourceC414) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2293) := by
    have ha : (tripleCharges (sourceA414 + difference 5 0) (sourceB414 + difference 0 5) sourceC414) = raw7698 := by
      apply Matrix.ext; unfold tripleCharges sourceA414 sourceB414 sourceC414 difference raw7698; decide +kernel
    rw [ha]
    exact (canonical7698 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA414 + difference 5 1) (sourceB414 + difference 1 5) sourceC414) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA414 + difference 5 1) (sourceB414 + difference 1 5) sourceC414) = raw6123 := by
      apply Matrix.ext; unfold tripleCharges sourceA414 sourceB414 sourceC414 difference raw6123; decide +kernel
    rw [ha]
    exact (canonical6123 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA414 + difference 5 2) (sourceB414 + difference 2 5) sourceC414) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA414 + difference 5 2) (sourceB414 + difference 2 5) sourceC414) = raw7699 := by
      apply Matrix.ext; unfold tripleCharges sourceA414 sourceB414 sourceC414 difference raw7699; decide +kernel
    rw [ha]
    exact (canonical7699 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA414 + difference 5 3) (sourceB414 + difference 3 5) sourceC414) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA414 + difference 5 3) (sourceB414 + difference 3 5) sourceC414) = raw7700 := by
      apply Matrix.ext; unfold tripleCharges sourceA414 sourceB414 sourceC414 difference raw7700; decide +kernel
    rw [ha]
    exact (canonical7700 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA414 + difference 5 4) (sourceB414 + difference 4 5) sourceC414) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3635) := by
    have ha : (tripleCharges (sourceA414 + difference 5 4) (sourceB414 + difference 4 5) sourceC414) = raw7697 := by
      apply Matrix.ext; unfold tripleCharges sourceA414 sourceB414 sourceC414 difference raw7697; decide +kernel
    rw [ha]
    exact (canonical7697 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA414 + difference 5 5) (sourceB414 + difference 5 5) sourceC414) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3633) := by
    have ha : (tripleCharges (sourceA414 + difference 5 5) (sourceB414 + difference 5 5) sourceC414) = raw6121 := by
      apply Matrix.ext; unfold tripleCharges sourceA414 sourceB414 sourceC414 difference raw6121; decide +kernel
    rw [ha]
    exact (canonical6121 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA414 + sourceB414) sourceC414) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA414 + sourceB414) sourceC414) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA414 sourceB414 sourceC414 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA414 sourceB414 sourceC414
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm414, Integer.Sparse.eval]
  linarith only [hs]

def sourceA415 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB415 : Charge := ![1, 0, 0, 0, 2, -3]
def sourceC415 : Charge := ![2, 0, 0, 0, -3, 1]
def sourceForm415 : Integer.Sparse Master := [(Sum.inr 4504, 3), (Sum.inr 4508, 1), (Sum.inr 4509, 1), (Sum.inr 4614, 3), (Sum.inr 4626, 1), (Sum.inr 4881, 3), (Sum.inr 4899, 1), (Sum.inr 5106, 6), (Sum.inr 5175, 3), (Sum.inr 5276, 3), (Sum.inr 5295, 3), (Sum.inr 5305, 1), (Sum.inr 5310, 1)]

theorem sourceEq415 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm415 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA415 + difference 0 1) (sourceB415 + difference 1 0) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA415 + difference 0 1) (sourceB415 + difference 1 0) sourceC415) = raw7701 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7701; decide +kernel
    rw [ha]
    exact (canonical7701 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA415 + difference 0 2) (sourceB415 + difference 2 0) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA415 + difference 0 2) (sourceB415 + difference 2 0) sourceC415) = raw7702 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7702; decide +kernel
    rw [ha]
    exact (canonical7702 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA415 + difference 0 3) (sourceB415 + difference 3 0) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA415 + difference 0 3) (sourceB415 + difference 3 0) sourceC415) = raw7703 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7703; decide +kernel
    rw [ha]
    exact (canonical7703 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA415 + difference 0 4) (sourceB415 + difference 4 0) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA415 + difference 0 4) (sourceB415 + difference 4 0) sourceC415) = raw7704 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7704; decide +kernel
    rw [ha]
    exact (canonical7704 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA415 + difference 0 5) (sourceB415 + difference 5 0) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA415 + difference 0 5) (sourceB415 + difference 5 0) sourceC415) = raw7705 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7705; decide +kernel
    rw [ha]
    exact (canonical7705 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA415 + difference 1 0) (sourceB415 + difference 0 1) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4614) := by
    have ha : (tripleCharges (sourceA415 + difference 1 0) (sourceB415 + difference 0 1) sourceC415) = raw7706 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7706; decide +kernel
    rw [ha]
    exact (canonical7706 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA415 + difference 1 2) (sourceB415 + difference 2 1) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5106) := by
    have ha : (tripleCharges (sourceA415 + difference 1 2) (sourceB415 + difference 2 1) sourceC415) = raw7707 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7707; decide +kernel
    rw [ha]
    exact (canonical7707 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA415 + difference 1 3) (sourceB415 + difference 3 1) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5106) := by
    have ha : (tripleCharges (sourceA415 + difference 1 3) (sourceB415 + difference 3 1) sourceC415) = raw7708 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7708; decide +kernel
    rw [ha]
    exact (canonical7708 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA415 + difference 1 4) (sourceB415 + difference 4 1) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4881) := by
    have ha : (tripleCharges (sourceA415 + difference 1 4) (sourceB415 + difference 4 1) sourceC415) = raw7709 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7709; decide +kernel
    rw [ha]
    exact (canonical7709 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA415 + difference 1 5) (sourceB415 + difference 5 1) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA415 + difference 1 5) (sourceB415 + difference 5 1) sourceC415) = raw7710 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7710; decide +kernel
    rw [ha]
    exact (canonical7710 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA415 + difference 2 0) (sourceB415 + difference 0 2) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4614) := by
    have ha : (tripleCharges (sourceA415 + difference 2 0) (sourceB415 + difference 0 2) sourceC415) = raw7711 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7711; decide +kernel
    rw [ha]
    exact (canonical7711 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA415 + difference 2 1) (sourceB415 + difference 1 2) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5106) := by
    have ha : (tripleCharges (sourceA415 + difference 2 1) (sourceB415 + difference 1 2) sourceC415) = raw7712 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7712; decide +kernel
    rw [ha]
    exact (canonical7712 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA415 + difference 2 3) (sourceB415 + difference 3 2) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5106) := by
    have ha : (tripleCharges (sourceA415 + difference 2 3) (sourceB415 + difference 3 2) sourceC415) = raw7713 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7713; decide +kernel
    rw [ha]
    exact (canonical7713 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA415 + difference 2 4) (sourceB415 + difference 4 2) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4881) := by
    have ha : (tripleCharges (sourceA415 + difference 2 4) (sourceB415 + difference 4 2) sourceC415) = raw7714 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7714; decide +kernel
    rw [ha]
    exact (canonical7714 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA415 + difference 2 5) (sourceB415 + difference 5 2) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA415 + difference 2 5) (sourceB415 + difference 5 2) sourceC415) = raw7715 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7715; decide +kernel
    rw [ha]
    exact (canonical7715 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA415 + difference 3 0) (sourceB415 + difference 0 3) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4614) := by
    have ha : (tripleCharges (sourceA415 + difference 3 0) (sourceB415 + difference 0 3) sourceC415) = raw7716 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7716; decide +kernel
    rw [ha]
    exact (canonical7716 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA415 + difference 3 1) (sourceB415 + difference 1 3) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5106) := by
    have ha : (tripleCharges (sourceA415 + difference 3 1) (sourceB415 + difference 1 3) sourceC415) = raw7717 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7717; decide +kernel
    rw [ha]
    exact (canonical7717 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA415 + difference 3 2) (sourceB415 + difference 2 3) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5106) := by
    have ha : (tripleCharges (sourceA415 + difference 3 2) (sourceB415 + difference 2 3) sourceC415) = raw7718 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7718; decide +kernel
    rw [ha]
    exact (canonical7718 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA415 + difference 3 4) (sourceB415 + difference 4 3) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4881) := by
    have ha : (tripleCharges (sourceA415 + difference 3 4) (sourceB415 + difference 4 3) sourceC415) = raw7719 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7719; decide +kernel
    rw [ha]
    exact (canonical7719 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA415 + difference 3 5) (sourceB415 + difference 5 3) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA415 + difference 3 5) (sourceB415 + difference 5 3) sourceC415) = raw7720 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7720; decide +kernel
    rw [ha]
    exact (canonical7720 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA415 + difference 4 0) (sourceB415 + difference 0 4) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4626) := by
    have ha : (tripleCharges (sourceA415 + difference 4 0) (sourceB415 + difference 0 4) sourceC415) = raw7721 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7721; decide +kernel
    rw [ha]
    exact (canonical7721 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA415 + difference 4 1) (sourceB415 + difference 1 4) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA415 + difference 4 1) (sourceB415 + difference 1 4) sourceC415) = raw7722 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7722; decide +kernel
    rw [ha]
    exact (canonical7722 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA415 + difference 4 2) (sourceB415 + difference 2 4) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA415 + difference 4 2) (sourceB415 + difference 2 4) sourceC415) = raw7723 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7723; decide +kernel
    rw [ha]
    exact (canonical7723 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA415 + difference 4 3) (sourceB415 + difference 3 4) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5175) := by
    have ha : (tripleCharges (sourceA415 + difference 4 3) (sourceB415 + difference 3 4) sourceC415) = raw7724 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7724; decide +kernel
    rw [ha]
    exact (canonical7724 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA415 + difference 4 5) (sourceB415 + difference 5 4) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5305) := by
    have ha : (tripleCharges (sourceA415 + difference 4 5) (sourceB415 + difference 5 4) sourceC415) = raw7725 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7725; decide +kernel
    rw [ha]
    exact (canonical7725 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA415 + difference 5 0) (sourceB415 + difference 0 5) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4509) := by
    have ha : (tripleCharges (sourceA415 + difference 5 0) (sourceB415 + difference 0 5) sourceC415) = raw7726 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7726; decide +kernel
    rw [ha]
    exact (canonical7726 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA415 + difference 5 1) (sourceB415 + difference 1 5) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4504) := by
    have ha : (tripleCharges (sourceA415 + difference 5 1) (sourceB415 + difference 1 5) sourceC415) = raw7727 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7727; decide +kernel
    rw [ha]
    exact (canonical7727 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA415 + difference 5 2) (sourceB415 + difference 2 5) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4504) := by
    have ha : (tripleCharges (sourceA415 + difference 5 2) (sourceB415 + difference 2 5) sourceC415) = raw7728 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7728; decide +kernel
    rw [ha]
    exact (canonical7728 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA415 + difference 5 3) (sourceB415 + difference 3 5) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4504) := by
    have ha : (tripleCharges (sourceA415 + difference 5 3) (sourceB415 + difference 3 5) sourceC415) = raw7729 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7729; decide +kernel
    rw [ha]
    exact (canonical7729 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA415 + difference 5 4) (sourceB415 + difference 4 5) sourceC415) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4508) := by
    have ha : (tripleCharges (sourceA415 + difference 5 4) (sourceB415 + difference 4 5) sourceC415) = raw7730 := by
      apply Matrix.ext; unfold tripleCharges sourceA415 sourceB415 sourceC415 difference raw7730; decide +kernel
    rw [ha]
    exact (canonical7730 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA415 sourceB415 sourceC415
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm415, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
