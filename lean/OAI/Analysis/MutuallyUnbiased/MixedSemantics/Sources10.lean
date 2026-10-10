import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical55

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA320 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB320 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC320 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm320 : Integer.Sparse Master := [(Sum.inr 2021, 1), (Sum.inr 2026, 1), (Sum.inr 2028, 1), (Sum.inr 2058, 1), (Sum.inr 2266, 1), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

theorem sourceEq320 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm320 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA320 + difference 0 0) (sourceB320 + difference 0 0) sourceC320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA320 + difference 0 0) (sourceB320 + difference 0 0) sourceC320) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA320 sourceB320 sourceC320 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA320 + difference 1 0) (sourceB320 + difference 0 1) sourceC320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA320 + difference 1 0) (sourceB320 + difference 0 1) sourceC320) = raw6790 := by
      apply Matrix.ext; unfold tripleCharges sourceA320 sourceB320 sourceC320 difference raw6790; decide +kernel
    rw [ha]
    exact (canonical6790 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA320 + difference 2 0) (sourceB320 + difference 0 2) sourceC320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA320 + difference 2 0) (sourceB320 + difference 0 2) sourceC320) = raw6791 := by
      apply Matrix.ext; unfold tripleCharges sourceA320 sourceB320 sourceC320 difference raw6791; decide +kernel
    rw [ha]
    exact (canonical6791 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA320 + difference 3 0) (sourceB320 + difference 0 3) sourceC320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA320 + difference 3 0) (sourceB320 + difference 0 3) sourceC320) = raw6792 := by
      apply Matrix.ext; unfold tripleCharges sourceA320 sourceB320 sourceC320 difference raw6792; decide +kernel
    rw [ha]
    exact (canonical6792 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA320 + difference 4 0) (sourceB320 + difference 0 4) sourceC320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA320 + difference 4 0) (sourceB320 + difference 0 4) sourceC320) = raw6793 := by
      apply Matrix.ext; unfold tripleCharges sourceA320 sourceB320 sourceC320 difference raw6793; decide +kernel
    rw [ha]
    exact (canonical6793 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA320 + difference 5 0) (sourceB320 + difference 0 5) sourceC320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA320 + difference 5 0) (sourceB320 + difference 0 5) sourceC320) = raw6794 := by
      apply Matrix.ext; unfold tripleCharges sourceA320 sourceB320 sourceC320 difference raw6794; decide +kernel
    rw [ha]
    exact (canonical6794 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA320 + sourceB320) sourceC320) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA320 + sourceB320) sourceC320) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA320 sourceB320 sourceC320 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA320 sourceB320 sourceC320
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm320, Integer.Sparse.eval]
  linarith only [hs]

def sourceA321 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB321 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC321 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm321 : Integer.Sparse Master := [(Sum.inr 2266, 1), (Sum.inr 3535, 2), (Sum.inr 3584, 1), (Sum.inr 3626, 1), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

theorem sourceEq321 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm321 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA321 + difference 1 0) (sourceB321 + difference 0 1) sourceC321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA321 + difference 1 0) (sourceB321 + difference 0 1) sourceC321) = raw6790 := by
      apply Matrix.ext; unfold tripleCharges sourceA321 sourceB321 sourceC321 difference raw6790; decide +kernel
    rw [ha]
    exact (canonical6790 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA321 + difference 1 1) (sourceB321 + difference 1 1) sourceC321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA321 + difference 1 1) (sourceB321 + difference 1 1) sourceC321) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA321 sourceB321 sourceC321 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA321 + difference 1 2) (sourceB321 + difference 2 1) sourceC321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA321 + difference 1 2) (sourceB321 + difference 2 1) sourceC321) = raw6795 := by
      apply Matrix.ext; unfold tripleCharges sourceA321 sourceB321 sourceC321 difference raw6795; decide +kernel
    rw [ha]
    exact (canonical6795 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA321 + difference 1 3) (sourceB321 + difference 3 1) sourceC321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA321 + difference 1 3) (sourceB321 + difference 3 1) sourceC321) = raw6796 := by
      apply Matrix.ext; unfold tripleCharges sourceA321 sourceB321 sourceC321 difference raw6796; decide +kernel
    rw [ha]
    exact (canonical6796 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA321 + difference 1 4) (sourceB321 + difference 4 1) sourceC321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA321 + difference 1 4) (sourceB321 + difference 4 1) sourceC321) = raw6797 := by
      apply Matrix.ext; unfold tripleCharges sourceA321 sourceB321 sourceC321 difference raw6797; decide +kernel
    rw [ha]
    exact (canonical6797 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA321 + difference 1 5) (sourceB321 + difference 5 1) sourceC321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA321 + difference 1 5) (sourceB321 + difference 5 1) sourceC321) = raw6798 := by
      apply Matrix.ext; unfold tripleCharges sourceA321 sourceB321 sourceC321 difference raw6798; decide +kernel
    rw [ha]
    exact (canonical6798 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA321 + sourceB321) sourceC321) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA321 + sourceB321) sourceC321) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA321 sourceB321 sourceC321 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA321 sourceB321 sourceC321
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm321, Integer.Sparse.eval]
  linarith only [hs]

def sourceA322 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB322 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC322 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm322 : Integer.Sparse Master := [(Sum.inr 3159, 1), (Sum.inr 3377, 1), (Sum.inr 3379, 1), (Sum.inr 3395, 2), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

theorem sourceEq322 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm322 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA322 + difference 0 1) (sourceB322 + difference 1 0) sourceC322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3395) := by
    have ha : (tripleCharges (sourceA322 + difference 0 1) (sourceB322 + difference 1 0) sourceC322) = raw6785 := by
      apply Matrix.ext; unfold tripleCharges sourceA322 sourceB322 sourceC322 difference raw6785; decide +kernel
    rw [ha]
    exact (canonical6785 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA322 + difference 1 1) (sourceB322 + difference 1 1) sourceC322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA322 + difference 1 1) (sourceB322 + difference 1 1) sourceC322) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA322 sourceB322 sourceC322 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA322 + difference 2 1) (sourceB322 + difference 1 2) sourceC322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3377) := by
    have ha : (tripleCharges (sourceA322 + difference 2 1) (sourceB322 + difference 1 2) sourceC322) = raw6799 := by
      apply Matrix.ext; unfold tripleCharges sourceA322 sourceB322 sourceC322 difference raw6799; decide +kernel
    rw [ha]
    exact (canonical6799 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA322 + difference 3 1) (sourceB322 + difference 1 3) sourceC322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3159) := by
    have ha : (tripleCharges (sourceA322 + difference 3 1) (sourceB322 + difference 1 3) sourceC322) = raw6800 := by
      apply Matrix.ext; unfold tripleCharges sourceA322 sourceB322 sourceC322 difference raw6800; decide +kernel
    rw [ha]
    exact (canonical6800 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA322 + difference 4 1) (sourceB322 + difference 1 4) sourceC322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3395) := by
    have ha : (tripleCharges (sourceA322 + difference 4 1) (sourceB322 + difference 1 4) sourceC322) = raw6801 := by
      apply Matrix.ext; unfold tripleCharges sourceA322 sourceB322 sourceC322 difference raw6801; decide +kernel
    rw [ha]
    exact (canonical6801 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA322 + difference 5 1) (sourceB322 + difference 1 5) sourceC322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3379) := by
    have ha : (tripleCharges (sourceA322 + difference 5 1) (sourceB322 + difference 1 5) sourceC322) = raw6802 := by
      apply Matrix.ext; unfold tripleCharges sourceA322 sourceB322 sourceC322 difference raw6802; decide +kernel
    rw [ha]
    exact (canonical6802 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA322 + sourceB322) sourceC322) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA322 + sourceB322) sourceC322) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA322 sourceB322 sourceC322 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA322 sourceB322 sourceC322
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm322, Integer.Sparse.eval]
  linarith only [hs]

def sourceA323 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB323 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC323 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm323 : Integer.Sparse Master := [(Sum.inr 2021, 1), (Sum.inr 3377, 1), (Sum.inr 3504, 1), (Sum.inr 3528, 1), (Sum.inr 3531, 1), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

theorem sourceEq323 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm323 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA323 + difference 2 0) (sourceB323 + difference 0 2) sourceC323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA323 + difference 2 0) (sourceB323 + difference 0 2) sourceC323) = raw6791 := by
      apply Matrix.ext; unfold tripleCharges sourceA323 sourceB323 sourceC323 difference raw6791; decide +kernel
    rw [ha]
    exact (canonical6791 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA323 + difference 2 1) (sourceB323 + difference 1 2) sourceC323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3377) := by
    have ha : (tripleCharges (sourceA323 + difference 2 1) (sourceB323 + difference 1 2) sourceC323) = raw6799 := by
      apply Matrix.ext; unfold tripleCharges sourceA323 sourceB323 sourceC323 difference raw6799; decide +kernel
    rw [ha]
    exact (canonical6799 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA323 + difference 2 2) (sourceB323 + difference 2 2) sourceC323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA323 + difference 2 2) (sourceB323 + difference 2 2) sourceC323) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA323 sourceB323 sourceC323 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA323 + difference 2 3) (sourceB323 + difference 3 2) sourceC323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA323 + difference 2 3) (sourceB323 + difference 3 2) sourceC323) = raw6803 := by
      apply Matrix.ext; unfold tripleCharges sourceA323 sourceB323 sourceC323 difference raw6803; decide +kernel
    rw [ha]
    exact (canonical6803 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA323 + difference 2 4) (sourceB323 + difference 4 2) sourceC323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3504) := by
    have ha : (tripleCharges (sourceA323 + difference 2 4) (sourceB323 + difference 4 2) sourceC323) = raw6804 := by
      apply Matrix.ext; unfold tripleCharges sourceA323 sourceB323 sourceC323 difference raw6804; decide +kernel
    rw [ha]
    exact (canonical6804 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA323 + difference 2 5) (sourceB323 + difference 5 2) sourceC323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA323 + difference 2 5) (sourceB323 + difference 5 2) sourceC323) = raw6805 := by
      apply Matrix.ext; unfold tripleCharges sourceA323 sourceB323 sourceC323 difference raw6805; decide +kernel
    rw [ha]
    exact (canonical6805 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA323 + sourceB323) sourceC323) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA323 + sourceB323) sourceC323) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA323 sourceB323 sourceC323 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA323 sourceB323 sourceC323
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm323, Integer.Sparse.eval]
  linarith only [hs]

def sourceA324 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB324 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC324 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm324 : Integer.Sparse Master := [(Sum.inr 3153, 1), (Sum.inr 3388, 1), (Sum.inr 3488, 1), (Sum.inr 3497, 1), (Sum.inr 3535, 2), (Sum.inr 4084, -1)]

theorem sourceEq324 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm324 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA324 + difference 0 2) (sourceB324 + difference 2 0) sourceC324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3388) := by
    have ha : (tripleCharges (sourceA324 + difference 0 2) (sourceB324 + difference 2 0) sourceC324) = raw6786 := by
      apply Matrix.ext; unfold tripleCharges sourceA324 sourceB324 sourceC324 difference raw6786; decide +kernel
    rw [ha]
    exact (canonical6786 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA324 + difference 1 2) (sourceB324 + difference 2 1) sourceC324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA324 + difference 1 2) (sourceB324 + difference 2 1) sourceC324) = raw6795 := by
      apply Matrix.ext; unfold tripleCharges sourceA324 sourceB324 sourceC324 difference raw6795; decide +kernel
    rw [ha]
    exact (canonical6795 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA324 + difference 2 2) (sourceB324 + difference 2 2) sourceC324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA324 + difference 2 2) (sourceB324 + difference 2 2) sourceC324) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA324 sourceB324 sourceC324 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA324 + difference 3 2) (sourceB324 + difference 2 3) sourceC324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3153) := by
    have ha : (tripleCharges (sourceA324 + difference 3 2) (sourceB324 + difference 2 3) sourceC324) = raw6806 := by
      apply Matrix.ext; unfold tripleCharges sourceA324 sourceB324 sourceC324 difference raw6806; decide +kernel
    rw [ha]
    exact (canonical6806 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA324 + difference 4 2) (sourceB324 + difference 2 4) sourceC324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3497) := by
    have ha : (tripleCharges (sourceA324 + difference 4 2) (sourceB324 + difference 2 4) sourceC324) = raw6807 := by
      apply Matrix.ext; unfold tripleCharges sourceA324 sourceB324 sourceC324 difference raw6807; decide +kernel
    rw [ha]
    exact (canonical6807 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA324 + difference 5 2) (sourceB324 + difference 2 5) sourceC324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3488) := by
    have ha : (tripleCharges (sourceA324 + difference 5 2) (sourceB324 + difference 2 5) sourceC324) = raw6808 := by
      apply Matrix.ext; unfold tripleCharges sourceA324 sourceB324 sourceC324 difference raw6808; decide +kernel
    rw [ha]
    exact (canonical6808 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA324 + sourceB324) sourceC324) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA324 + sourceB324) sourceC324) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA324 sourceB324 sourceC324 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA324 sourceB324 sourceC324
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm324, Integer.Sparse.eval]
  linarith only [hs]

def sourceA325 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB325 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC325 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm325 : Integer.Sparse Master := [(Sum.inr 2026, 1), (Sum.inr 3153, 1), (Sum.inr 3156, 1), (Sum.inr 3157, 1), (Sum.inr 3159, 1), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

theorem sourceEq325 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm325 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA325 + difference 3 0) (sourceB325 + difference 0 3) sourceC325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA325 + difference 3 0) (sourceB325 + difference 0 3) sourceC325) = raw6792 := by
      apply Matrix.ext; unfold tripleCharges sourceA325 sourceB325 sourceC325 difference raw6792; decide +kernel
    rw [ha]
    exact (canonical6792 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA325 + difference 3 1) (sourceB325 + difference 1 3) sourceC325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3159) := by
    have ha : (tripleCharges (sourceA325 + difference 3 1) (sourceB325 + difference 1 3) sourceC325) = raw6800 := by
      apply Matrix.ext; unfold tripleCharges sourceA325 sourceB325 sourceC325 difference raw6800; decide +kernel
    rw [ha]
    exact (canonical6800 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA325 + difference 3 2) (sourceB325 + difference 2 3) sourceC325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3153) := by
    have ha : (tripleCharges (sourceA325 + difference 3 2) (sourceB325 + difference 2 3) sourceC325) = raw6806 := by
      apply Matrix.ext; unfold tripleCharges sourceA325 sourceB325 sourceC325 difference raw6806; decide +kernel
    rw [ha]
    exact (canonical6806 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA325 + difference 3 3) (sourceB325 + difference 3 3) sourceC325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA325 + difference 3 3) (sourceB325 + difference 3 3) sourceC325) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA325 sourceB325 sourceC325 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA325 + difference 3 4) (sourceB325 + difference 4 3) sourceC325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3157) := by
    have ha : (tripleCharges (sourceA325 + difference 3 4) (sourceB325 + difference 4 3) sourceC325) = raw6809 := by
      apply Matrix.ext; unfold tripleCharges sourceA325 sourceB325 sourceC325 difference raw6809; decide +kernel
    rw [ha]
    exact (canonical6809 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA325 + difference 3 5) (sourceB325 + difference 5 3) sourceC325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3156) := by
    have ha : (tripleCharges (sourceA325 + difference 3 5) (sourceB325 + difference 5 3) sourceC325) = raw6810 := by
      apply Matrix.ext; unfold tripleCharges sourceA325 sourceB325 sourceC325 difference raw6810; decide +kernel
    rw [ha]
    exact (canonical6810 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA325 + sourceB325) sourceC325) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA325 + sourceB325) sourceC325) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA325 sourceB325 sourceC325 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA325 sourceB325 sourceC325
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm325, Integer.Sparse.eval]
  linarith only [hs]

def sourceA326 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB326 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC326 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm326 : Integer.Sparse Master := [(Sum.inr 3531, 1), (Sum.inr 3533, 1), (Sum.inr 3535, 1), (Sum.inr 3544, 2), (Sum.inr 3627, 1), (Sum.inr 4084, -1)]

theorem sourceEq326 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm326 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA326 + difference 0 3) (sourceB326 + difference 3 0) sourceC326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA326 + difference 0 3) (sourceB326 + difference 3 0) sourceC326) = raw6787 := by
      apply Matrix.ext; unfold tripleCharges sourceA326 sourceB326 sourceC326 difference raw6787; decide +kernel
    rw [ha]
    exact (canonical6787 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA326 + difference 1 3) (sourceB326 + difference 3 1) sourceC326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA326 + difference 1 3) (sourceB326 + difference 3 1) sourceC326) = raw6796 := by
      apply Matrix.ext; unfold tripleCharges sourceA326 sourceB326 sourceC326 difference raw6796; decide +kernel
    rw [ha]
    exact (canonical6796 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA326 + difference 2 3) (sourceB326 + difference 3 2) sourceC326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA326 + difference 2 3) (sourceB326 + difference 3 2) sourceC326) = raw6803 := by
      apply Matrix.ext; unfold tripleCharges sourceA326 sourceB326 sourceC326 difference raw6803; decide +kernel
    rw [ha]
    exact (canonical6803 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA326 + difference 3 3) (sourceB326 + difference 3 3) sourceC326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA326 + difference 3 3) (sourceB326 + difference 3 3) sourceC326) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA326 sourceB326 sourceC326 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA326 + difference 4 3) (sourceB326 + difference 3 4) sourceC326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA326 + difference 4 3) (sourceB326 + difference 3 4) sourceC326) = raw6456 := by
      apply Matrix.ext; unfold tripleCharges sourceA326 sourceB326 sourceC326 difference raw6456; decide +kernel
    rw [ha]
    exact (canonical6456 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA326 + difference 5 3) (sourceB326 + difference 3 5) sourceC326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA326 + difference 5 3) (sourceB326 + difference 3 5) sourceC326) = raw6811 := by
      apply Matrix.ext; unfold tripleCharges sourceA326 sourceB326 sourceC326 difference raw6811; decide +kernel
    rw [ha]
    exact (canonical6811 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA326 + sourceB326) sourceC326) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA326 + sourceB326) sourceC326) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA326 sourceB326 sourceC326 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA326 sourceB326 sourceC326
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm326, Integer.Sparse.eval]
  linarith only [hs]

def sourceA327 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB327 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC327 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm327 : Integer.Sparse Master := [(Sum.inr 2058, 1), (Sum.inr 3395, 1), (Sum.inr 3497, 1), (Sum.inr 3535, 1), (Sum.inr 3541, 1), (Sum.inr 3544, 1), (Sum.inr 4084, -1)]

theorem sourceEq327 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm327 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA327 + difference 4 0) (sourceB327 + difference 0 4) sourceC327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA327 + difference 4 0) (sourceB327 + difference 0 4) sourceC327) = raw6793 := by
      apply Matrix.ext; unfold tripleCharges sourceA327 sourceB327 sourceC327 difference raw6793; decide +kernel
    rw [ha]
    exact (canonical6793 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA327 + difference 4 1) (sourceB327 + difference 1 4) sourceC327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3395) := by
    have ha : (tripleCharges (sourceA327 + difference 4 1) (sourceB327 + difference 1 4) sourceC327) = raw6801 := by
      apply Matrix.ext; unfold tripleCharges sourceA327 sourceB327 sourceC327 difference raw6801; decide +kernel
    rw [ha]
    exact (canonical6801 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA327 + difference 4 2) (sourceB327 + difference 2 4) sourceC327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3497) := by
    have ha : (tripleCharges (sourceA327 + difference 4 2) (sourceB327 + difference 2 4) sourceC327) = raw6807 := by
      apply Matrix.ext; unfold tripleCharges sourceA327 sourceB327 sourceC327 difference raw6807; decide +kernel
    rw [ha]
    exact (canonical6807 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA327 + difference 4 3) (sourceB327 + difference 3 4) sourceC327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA327 + difference 4 3) (sourceB327 + difference 3 4) sourceC327) = raw6456 := by
      apply Matrix.ext; unfold tripleCharges sourceA327 sourceB327 sourceC327 difference raw6456; decide +kernel
    rw [ha]
    exact (canonical6456 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA327 + difference 4 4) (sourceB327 + difference 4 4) sourceC327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA327 + difference 4 4) (sourceB327 + difference 4 4) sourceC327) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA327 sourceB327 sourceC327 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA327 + difference 4 5) (sourceB327 + difference 5 4) sourceC327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA327 + difference 4 5) (sourceB327 + difference 5 4) sourceC327) = raw6454 := by
      apply Matrix.ext; unfold tripleCharges sourceA327 sourceB327 sourceC327 difference raw6454; decide +kernel
    rw [ha]
    exact (canonical6454 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA327 + sourceB327) sourceC327) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA327 + sourceB327) sourceC327) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA327 sourceB327 sourceC327 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA327 sourceB327 sourceC327
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm327, Integer.Sparse.eval]
  linarith only [hs]

def sourceA328 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB328 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC328 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm328 : Integer.Sparse Master := [(Sum.inr 3157, 1), (Sum.inr 3392, 1), (Sum.inr 3504, 1), (Sum.inr 3506, 1), (Sum.inr 3535, 1), (Sum.inr 3584, 1), (Sum.inr 4084, -1)]

theorem sourceEq328 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm328 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA328 + difference 0 4) (sourceB328 + difference 4 0) sourceC328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3392) := by
    have ha : (tripleCharges (sourceA328 + difference 0 4) (sourceB328 + difference 4 0) sourceC328) = raw6788 := by
      apply Matrix.ext; unfold tripleCharges sourceA328 sourceB328 sourceC328 difference raw6788; decide +kernel
    rw [ha]
    exact (canonical6788 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA328 + difference 1 4) (sourceB328 + difference 4 1) sourceC328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA328 + difference 1 4) (sourceB328 + difference 4 1) sourceC328) = raw6797 := by
      apply Matrix.ext; unfold tripleCharges sourceA328 sourceB328 sourceC328 difference raw6797; decide +kernel
    rw [ha]
    exact (canonical6797 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA328 + difference 2 4) (sourceB328 + difference 4 2) sourceC328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3504) := by
    have ha : (tripleCharges (sourceA328 + difference 2 4) (sourceB328 + difference 4 2) sourceC328) = raw6804 := by
      apply Matrix.ext; unfold tripleCharges sourceA328 sourceB328 sourceC328 difference raw6804; decide +kernel
    rw [ha]
    exact (canonical6804 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA328 + difference 3 4) (sourceB328 + difference 4 3) sourceC328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3157) := by
    have ha : (tripleCharges (sourceA328 + difference 3 4) (sourceB328 + difference 4 3) sourceC328) = raw6809 := by
      apply Matrix.ext; unfold tripleCharges sourceA328 sourceB328 sourceC328 difference raw6809; decide +kernel
    rw [ha]
    exact (canonical6809 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA328 + difference 4 4) (sourceB328 + difference 4 4) sourceC328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA328 + difference 4 4) (sourceB328 + difference 4 4) sourceC328) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA328 sourceB328 sourceC328 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA328 + difference 5 4) (sourceB328 + difference 4 5) sourceC328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3506) := by
    have ha : (tripleCharges (sourceA328 + difference 5 4) (sourceB328 + difference 4 5) sourceC328) = raw6812 := by
      apply Matrix.ext; unfold tripleCharges sourceA328 sourceB328 sourceC328 difference raw6812; decide +kernel
    rw [ha]
    exact (canonical6812 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA328 + sourceB328) sourceC328) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA328 + sourceB328) sourceC328) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA328 sourceB328 sourceC328 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA328 sourceB328 sourceC328
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm328, Integer.Sparse.eval]
  linarith only [hs]

def sourceA329 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB329 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC329 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm329 : Integer.Sparse Master := [(Sum.inr 2028, 1), (Sum.inr 3379, 1), (Sum.inr 3488, 1), (Sum.inr 3506, 1), (Sum.inr 3533, 1), (Sum.inr 3535, 1), (Sum.inr 4084, -1)]

theorem sourceEq329 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm329 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA329 + difference 5 0) (sourceB329 + difference 0 5) sourceC329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA329 + difference 5 0) (sourceB329 + difference 0 5) sourceC329) = raw6794 := by
      apply Matrix.ext; unfold tripleCharges sourceA329 sourceB329 sourceC329 difference raw6794; decide +kernel
    rw [ha]
    exact (canonical6794 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA329 + difference 5 1) (sourceB329 + difference 1 5) sourceC329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3379) := by
    have ha : (tripleCharges (sourceA329 + difference 5 1) (sourceB329 + difference 1 5) sourceC329) = raw6802 := by
      apply Matrix.ext; unfold tripleCharges sourceA329 sourceB329 sourceC329 difference raw6802; decide +kernel
    rw [ha]
    exact (canonical6802 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA329 + difference 5 2) (sourceB329 + difference 2 5) sourceC329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3488) := by
    have ha : (tripleCharges (sourceA329 + difference 5 2) (sourceB329 + difference 2 5) sourceC329) = raw6808 := by
      apply Matrix.ext; unfold tripleCharges sourceA329 sourceB329 sourceC329 difference raw6808; decide +kernel
    rw [ha]
    exact (canonical6808 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA329 + difference 5 3) (sourceB329 + difference 3 5) sourceC329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA329 + difference 5 3) (sourceB329 + difference 3 5) sourceC329) = raw6811 := by
      apply Matrix.ext; unfold tripleCharges sourceA329 sourceB329 sourceC329 difference raw6811; decide +kernel
    rw [ha]
    exact (canonical6811 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA329 + difference 5 4) (sourceB329 + difference 4 5) sourceC329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3506) := by
    have ha : (tripleCharges (sourceA329 + difference 5 4) (sourceB329 + difference 4 5) sourceC329) = raw6812 := by
      apply Matrix.ext; unfold tripleCharges sourceA329 sourceB329 sourceC329 difference raw6812; decide +kernel
    rw [ha]
    exact (canonical6812 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA329 + difference 5 5) (sourceB329 + difference 5 5) sourceC329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA329 + difference 5 5) (sourceB329 + difference 5 5) sourceC329) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA329 sourceB329 sourceC329 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA329 + sourceB329) sourceC329) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA329 + sourceB329) sourceC329) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA329 sourceB329 sourceC329 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA329 sourceB329 sourceC329
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm329, Integer.Sparse.eval]
  linarith only [hs]

def sourceA330 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB330 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC330 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceForm330 : Integer.Sparse Master := [(Sum.inr 4561, 1), (Sum.inr 4562, 1), (Sum.inr 4565, 1), (Sum.inr 4568, 1), (Sum.inr 4607, 1), (Sum.inr 4783, 1), (Sum.inr 4789, 1), (Sum.inr 4817, 1), (Sum.inr 4836, 1), (Sum.inr 5086, 1), (Sum.inr 5090, 1), (Sum.inr 5105, 1), (Sum.inr 5131, 1), (Sum.inr 5138, 1), (Sum.inr 5154, 1), (Sum.inr 5209, 1), (Sum.inr 5210, 2), (Sum.inr 5254, 1), (Sum.inr 5260, 1), (Sum.inr 5265, 1), (Sum.inr 5266, 1), (Sum.inr 5267, 1), (Sum.inr 5271, 1), (Sum.inr 5287, 1), (Sum.inr 5299, 1), (Sum.inr 5412, 2), (Sum.inr 5426, 1), (Sum.inr 5435, 1)]

theorem sourceEq330 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm330 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA330 + difference 0 1) (sourceB330 + difference 1 0) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA330 + difference 0 1) (sourceB330 + difference 1 0) sourceC330) = raw6813 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6813; decide +kernel
    rw [ha]
    exact (canonical6813 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA330 + difference 0 2) (sourceB330 + difference 2 0) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5426) := by
    have ha : (tripleCharges (sourceA330 + difference 0 2) (sourceB330 + difference 2 0) sourceC330) = raw6814 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6814; decide +kernel
    rw [ha]
    exact (canonical6814 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA330 + difference 0 3) (sourceB330 + difference 3 0) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA330 + difference 0 3) (sourceB330 + difference 3 0) sourceC330) = raw6815 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6815; decide +kernel
    rw [ha]
    exact (canonical6815 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA330 + difference 0 4) (sourceB330 + difference 4 0) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA330 + difference 0 4) (sourceB330 + difference 4 0) sourceC330) = raw6816 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6816; decide +kernel
    rw [ha]
    exact (canonical6816 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA330 + difference 0 5) (sourceB330 + difference 5 0) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA330 + difference 0 5) (sourceB330 + difference 5 0) sourceC330) = raw6817 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6817; decide +kernel
    rw [ha]
    exact (canonical6817 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA330 + difference 1 0) (sourceB330 + difference 0 1) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4568) := by
    have ha : (tripleCharges (sourceA330 + difference 1 0) (sourceB330 + difference 0 1) sourceC330) = raw6818 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6818; decide +kernel
    rw [ha]
    exact (canonical6818 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA330 + difference 1 2) (sourceB330 + difference 2 1) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5154) := by
    have ha : (tripleCharges (sourceA330 + difference 1 2) (sourceB330 + difference 2 1) sourceC330) = raw6819 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6819; decide +kernel
    rw [ha]
    exact (canonical6819 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA330 + difference 1 3) (sourceB330 + difference 3 1) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5210) := by
    have ha : (tripleCharges (sourceA330 + difference 1 3) (sourceB330 + difference 3 1) sourceC330) = raw6820 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6820; decide +kernel
    rw [ha]
    exact (canonical6820 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA330 + difference 1 4) (sourceB330 + difference 4 1) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA330 + difference 1 4) (sourceB330 + difference 4 1) sourceC330) = raw6821 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6821; decide +kernel
    rw [ha]
    exact (canonical6821 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA330 + difference 1 5) (sourceB330 + difference 5 1) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA330 + difference 1 5) (sourceB330 + difference 5 1) sourceC330) = raw6822 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6822; decide +kernel
    rw [ha]
    exact (canonical6822 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA330 + difference 2 0) (sourceB330 + difference 0 2) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4561) := by
    have ha : (tripleCharges (sourceA330 + difference 2 0) (sourceB330 + difference 0 2) sourceC330) = raw6823 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6823; decide +kernel
    rw [ha]
    exact (canonical6823 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA330 + difference 2 1) (sourceB330 + difference 1 2) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA330 + difference 2 1) (sourceB330 + difference 1 2) sourceC330) = raw6824 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6824; decide +kernel
    rw [ha]
    exact (canonical6824 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA330 + difference 2 3) (sourceB330 + difference 3 2) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5209) := by
    have ha : (tripleCharges (sourceA330 + difference 2 3) (sourceB330 + difference 3 2) sourceC330) = raw6825 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6825; decide +kernel
    rw [ha]
    exact (canonical6825 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA330 + difference 2 4) (sourceB330 + difference 4 2) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA330 + difference 2 4) (sourceB330 + difference 4 2) sourceC330) = raw6826 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6826; decide +kernel
    rw [ha]
    exact (canonical6826 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA330 + difference 2 5) (sourceB330 + difference 5 2) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA330 + difference 2 5) (sourceB330 + difference 5 2) sourceC330) = raw6827 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6827; decide +kernel
    rw [ha]
    exact (canonical6827 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA330 + difference 3 0) (sourceB330 + difference 0 3) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4607) := by
    have ha : (tripleCharges (sourceA330 + difference 3 0) (sourceB330 + difference 0 3) sourceC330) = raw6828 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6828; decide +kernel
    rw [ha]
    exact (canonical6828 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA330 + difference 3 1) (sourceB330 + difference 1 3) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA330 + difference 3 1) (sourceB330 + difference 1 3) sourceC330) = raw6829 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6829; decide +kernel
    rw [ha]
    exact (canonical6829 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA330 + difference 3 2) (sourceB330 + difference 2 3) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA330 + difference 3 2) (sourceB330 + difference 2 3) sourceC330) = raw6830 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6830; decide +kernel
    rw [ha]
    exact (canonical6830 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA330 + difference 3 4) (sourceB330 + difference 4 3) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA330 + difference 3 4) (sourceB330 + difference 4 3) sourceC330) = raw6831 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6831; decide +kernel
    rw [ha]
    exact (canonical6831 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA330 + difference 3 5) (sourceB330 + difference 5 3) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA330 + difference 3 5) (sourceB330 + difference 5 3) sourceC330) = raw6832 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6832; decide +kernel
    rw [ha]
    exact (canonical6832 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA330 + difference 4 0) (sourceB330 + difference 0 4) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4565) := by
    have ha : (tripleCharges (sourceA330 + difference 4 0) (sourceB330 + difference 0 4) sourceC330) = raw6833 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6833; decide +kernel
    rw [ha]
    exact (canonical6833 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA330 + difference 4 1) (sourceB330 + difference 1 4) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA330 + difference 4 1) (sourceB330 + difference 1 4) sourceC330) = raw6834 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6834; decide +kernel
    rw [ha]
    exact (canonical6834 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA330 + difference 4 2) (sourceB330 + difference 2 4) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5131) := by
    have ha : (tripleCharges (sourceA330 + difference 4 2) (sourceB330 + difference 2 4) sourceC330) = raw6835 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6835; decide +kernel
    rw [ha]
    exact (canonical6835 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA330 + difference 4 3) (sourceB330 + difference 3 4) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5210) := by
    have ha : (tripleCharges (sourceA330 + difference 4 3) (sourceB330 + difference 3 4) sourceC330) = raw6836 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6836; decide +kernel
    rw [ha]
    exact (canonical6836 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA330 + difference 4 5) (sourceB330 + difference 5 4) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA330 + difference 4 5) (sourceB330 + difference 5 4) sourceC330) = raw6837 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6837; decide +kernel
    rw [ha]
    exact (canonical6837 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA330 + difference 5 0) (sourceB330 + difference 0 5) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4562) := by
    have ha : (tripleCharges (sourceA330 + difference 5 0) (sourceB330 + difference 0 5) sourceC330) = raw6838 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6838; decide +kernel
    rw [ha]
    exact (canonical6838 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA330 + difference 5 1) (sourceB330 + difference 1 5) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA330 + difference 5 1) (sourceB330 + difference 1 5) sourceC330) = raw6839 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6839; decide +kernel
    rw [ha]
    exact (canonical6839 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA330 + difference 5 2) (sourceB330 + difference 2 5) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4783) := by
    have ha : (tripleCharges (sourceA330 + difference 5 2) (sourceB330 + difference 2 5) sourceC330) = raw6840 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6840; decide +kernel
    rw [ha]
    exact (canonical6840 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA330 + difference 5 3) (sourceB330 + difference 3 5) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4789) := by
    have ha : (tripleCharges (sourceA330 + difference 5 3) (sourceB330 + difference 3 5) sourceC330) = raw6841 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6841; decide +kernel
    rw [ha]
    exact (canonical6841 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA330 + difference 5 4) (sourceB330 + difference 4 5) sourceC330) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA330 + difference 5 4) (sourceB330 + difference 4 5) sourceC330) = raw6842 := by
      apply Matrix.ext; unfold tripleCharges sourceA330 sourceB330 sourceC330 difference raw6842; decide +kernel
    rw [ha]
    exact (canonical6842 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA330 sourceB330 sourceC330
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm330, Integer.Sparse.eval]
  linarith only [hs]

def sourceA331 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB331 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC331 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceForm331 : Integer.Sparse Master := [(Sum.inr 1178, 1), (Sum.inr 1179, 1), (Sum.inr 1182, 1), (Sum.inr 1185, 1), (Sum.inr 1261, 1), (Sum.inr 1992, 1), (Sum.inr 2004, 1), (Sum.inr 2035, 1), (Sum.inr 2197, 1), (Sum.inr 2833, 1), (Sum.inr 2835, 1), (Sum.inr 2838, 1), (Sum.inr 2905, 1), (Sum.inr 2907, 1), (Sum.inr 2933, 1), (Sum.inr 2974, 1), (Sum.inr 2979, 1), (Sum.inr 2997, 1), (Sum.inr 3016, 1), (Sum.inr 3025, 1), (Sum.inr 3037, 1), (Sum.inr 3039, 1), (Sum.inr 3051, 1), (Sum.inr 3086, 1), (Sum.inr 3109, 1), (Sum.inr 3541, 1), (Sum.inr 3814, 1), (Sum.inr 3841, 1), (Sum.inr 3853, 1), (Sum.inr 3856, 1)]

theorem sourceEq331 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm331 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA331 + difference 0 1) (sourceB331 + difference 1 0) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3856) := by
    have ha : (tripleCharges (sourceA331 + difference 0 1) (sourceB331 + difference 1 0) sourceC331) = raw6843 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6843; decide +kernel
    rw [ha]
    exact (canonical6843 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA331 + difference 0 2) (sourceB331 + difference 2 0) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3841) := by
    have ha : (tripleCharges (sourceA331 + difference 0 2) (sourceB331 + difference 2 0) sourceC331) = raw6844 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6844; decide +kernel
    rw [ha]
    exact (canonical6844 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA331 + difference 0 3) (sourceB331 + difference 3 0) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA331 + difference 0 3) (sourceB331 + difference 3 0) sourceC331) = raw6845 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6845; decide +kernel
    rw [ha]
    exact (canonical6845 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA331 + difference 0 4) (sourceB331 + difference 4 0) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA331 + difference 0 4) (sourceB331 + difference 4 0) sourceC331) = raw6846 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6846; decide +kernel
    rw [ha]
    exact (canonical6846 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA331 + difference 0 5) (sourceB331 + difference 5 0) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA331 + difference 0 5) (sourceB331 + difference 5 0) sourceC331) = raw6847 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6847; decide +kernel
    rw [ha]
    exact (canonical6847 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA331 + difference 1 0) (sourceB331 + difference 0 1) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1185) := by
    have ha : (tripleCharges (sourceA331 + difference 1 0) (sourceB331 + difference 0 1) sourceC331) = raw6848 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6848; decide +kernel
    rw [ha]
    exact (canonical6848 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA331 + difference 1 2) (sourceB331 + difference 2 1) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2907) := by
    have ha : (tripleCharges (sourceA331 + difference 1 2) (sourceB331 + difference 2 1) sourceC331) = raw6849 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6849; decide +kernel
    rw [ha]
    exact (canonical6849 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA331 + difference 1 3) (sourceB331 + difference 3 1) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2838) := by
    have ha : (tripleCharges (sourceA331 + difference 1 3) (sourceB331 + difference 3 1) sourceC331) = raw6850 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6850; decide +kernel
    rw [ha]
    exact (canonical6850 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA331 + difference 1 4) (sourceB331 + difference 4 1) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA331 + difference 1 4) (sourceB331 + difference 4 1) sourceC331) = raw6851 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6851; decide +kernel
    rw [ha]
    exact (canonical6851 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA331 + difference 1 5) (sourceB331 + difference 5 1) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA331 + difference 1 5) (sourceB331 + difference 5 1) sourceC331) = raw6852 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6852; decide +kernel
    rw [ha]
    exact (canonical6852 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA331 + difference 2 0) (sourceB331 + difference 0 2) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1178) := by
    have ha : (tripleCharges (sourceA331 + difference 2 0) (sourceB331 + difference 0 2) sourceC331) = raw6853 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6853; decide +kernel
    rw [ha]
    exact (canonical6853 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA331 + difference 2 1) (sourceB331 + difference 1 2) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA331 + difference 2 1) (sourceB331 + difference 1 2) sourceC331) = raw6854 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6854; decide +kernel
    rw [ha]
    exact (canonical6854 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA331 + difference 2 3) (sourceB331 + difference 3 2) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2833) := by
    have ha : (tripleCharges (sourceA331 + difference 2 3) (sourceB331 + difference 3 2) sourceC331) = raw6855 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6855; decide +kernel
    rw [ha]
    exact (canonical6855 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA331 + difference 2 4) (sourceB331 + difference 4 2) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA331 + difference 2 4) (sourceB331 + difference 4 2) sourceC331) = raw6856 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6856; decide +kernel
    rw [ha]
    exact (canonical6856 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA331 + difference 2 5) (sourceB331 + difference 5 2) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA331 + difference 2 5) (sourceB331 + difference 5 2) sourceC331) = raw6857 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6857; decide +kernel
    rw [ha]
    exact (canonical6857 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA331 + difference 3 0) (sourceB331 + difference 0 3) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1261) := by
    have ha : (tripleCharges (sourceA331 + difference 3 0) (sourceB331 + difference 0 3) sourceC331) = raw6858 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6858; decide +kernel
    rw [ha]
    exact (canonical6858 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA331 + difference 3 1) (sourceB331 + difference 1 3) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2997) := by
    have ha : (tripleCharges (sourceA331 + difference 3 1) (sourceB331 + difference 1 3) sourceC331) = raw6859 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6859; decide +kernel
    rw [ha]
    exact (canonical6859 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA331 + difference 3 2) (sourceB331 + difference 2 3) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2933) := by
    have ha : (tripleCharges (sourceA331 + difference 3 2) (sourceB331 + difference 2 3) sourceC331) = raw6860 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6860; decide +kernel
    rw [ha]
    exact (canonical6860 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA331 + difference 3 4) (sourceB331 + difference 4 3) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA331 + difference 3 4) (sourceB331 + difference 4 3) sourceC331) = raw6861 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6861; decide +kernel
    rw [ha]
    exact (canonical6861 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA331 + difference 3 5) (sourceB331 + difference 5 3) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA331 + difference 3 5) (sourceB331 + difference 5 3) sourceC331) = raw6862 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6862; decide +kernel
    rw [ha]
    exact (canonical6862 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA331 + difference 4 0) (sourceB331 + difference 0 4) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1182) := by
    have ha : (tripleCharges (sourceA331 + difference 4 0) (sourceB331 + difference 0 4) sourceC331) = raw6863 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6863; decide +kernel
    rw [ha]
    exact (canonical6863 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA331 + difference 4 1) (sourceB331 + difference 1 4) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2979) := by
    have ha : (tripleCharges (sourceA331 + difference 4 1) (sourceB331 + difference 1 4) sourceC331) = raw6864 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6864; decide +kernel
    rw [ha]
    exact (canonical6864 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA331 + difference 4 2) (sourceB331 + difference 2 4) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2905) := by
    have ha : (tripleCharges (sourceA331 + difference 4 2) (sourceB331 + difference 2 4) sourceC331) = raw6865 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6865; decide +kernel
    rw [ha]
    exact (canonical6865 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA331 + difference 4 3) (sourceB331 + difference 3 4) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2835) := by
    have ha : (tripleCharges (sourceA331 + difference 4 3) (sourceB331 + difference 3 4) sourceC331) = raw6866 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6866; decide +kernel
    rw [ha]
    exact (canonical6866 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA331 + difference 4 5) (sourceB331 + difference 5 4) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA331 + difference 4 5) (sourceB331 + difference 5 4) sourceC331) = raw6867 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6867; decide +kernel
    rw [ha]
    exact (canonical6867 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA331 + difference 5 0) (sourceB331 + difference 0 5) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1179) := by
    have ha : (tripleCharges (sourceA331 + difference 5 0) (sourceB331 + difference 0 5) sourceC331) = raw6868 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6868; decide +kernel
    rw [ha]
    exact (canonical6868 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA331 + difference 5 1) (sourceB331 + difference 1 5) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2035) := by
    have ha : (tripleCharges (sourceA331 + difference 5 1) (sourceB331 + difference 1 5) sourceC331) = raw6869 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6869; decide +kernel
    rw [ha]
    exact (canonical6869 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA331 + difference 5 2) (sourceB331 + difference 2 5) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1992) := by
    have ha : (tripleCharges (sourceA331 + difference 5 2) (sourceB331 + difference 2 5) sourceC331) = raw6870 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6870; decide +kernel
    rw [ha]
    exact (canonical6870 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA331 + difference 5 3) (sourceB331 + difference 3 5) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2004) := by
    have ha : (tripleCharges (sourceA331 + difference 5 3) (sourceB331 + difference 3 5) sourceC331) = raw6871 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6871; decide +kernel
    rw [ha]
    exact (canonical6871 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA331 + difference 5 4) (sourceB331 + difference 4 5) sourceC331) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA331 + difference 5 4) (sourceB331 + difference 4 5) sourceC331) = raw6872 := by
      apply Matrix.ext; unfold tripleCharges sourceA331 sourceB331 sourceC331 difference raw6872; decide +kernel
    rw [ha]
    exact (canonical6872 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA331 sourceB331 sourceC331
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm331, Integer.Sparse.eval]
  linarith only [hs]

def sourceA332 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB332 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC332 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceForm332 : Integer.Sparse Master := [(Sum.inr 2001, 1), (Sum.inr 2004, 1), (Sum.inr 2005, 1), (Sum.inr 2055, 1), (Sum.inr 2207, 1), (Sum.inr 2833, 1), (Sum.inr 2835, 1), (Sum.inr 2838, 1), (Sum.inr 3038, 1), (Sum.inr 3238, 1), (Sum.inr 3240, 1), (Sum.inr 3243, 1), (Sum.inr 3296, 1), (Sum.inr 3464, 1), (Sum.inr 3479, 1), (Sum.inr 3480, 1), (Sum.inr 3517, 1), (Sum.inr 3518, 1), (Sum.inr 3526, 1), (Sum.inr 3528, 1), (Sum.inr 3534, 1), (Sum.inr 3535, 1), (Sum.inr 3540, 1), (Sum.inr 3561, 1), (Sum.inr 3573, 1), (Sum.inr 3577, 1), (Sum.inr 3814, 1), (Sum.inr 3841, 1), (Sum.inr 3853, 1), (Sum.inr 3856, 1)]

theorem sourceEq332 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm332 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA332 + difference 0 1) (sourceB332 + difference 1 0) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA332 + difference 0 1) (sourceB332 + difference 1 0) sourceC332) = raw6873 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6873; decide +kernel
    rw [ha]
    exact (canonical6873 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA332 + difference 0 2) (sourceB332 + difference 2 0) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3841) := by
    have ha : (tripleCharges (sourceA332 + difference 0 2) (sourceB332 + difference 2 0) sourceC332) = raw6874 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6874; decide +kernel
    rw [ha]
    exact (canonical6874 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA332 + difference 0 3) (sourceB332 + difference 3 0) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA332 + difference 0 3) (sourceB332 + difference 3 0) sourceC332) = raw6875 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6875; decide +kernel
    rw [ha]
    exact (canonical6875 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA332 + difference 0 4) (sourceB332 + difference 4 0) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3856) := by
    have ha : (tripleCharges (sourceA332 + difference 0 4) (sourceB332 + difference 4 0) sourceC332) = raw6876 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6876; decide +kernel
    rw [ha]
    exact (canonical6876 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA332 + difference 0 5) (sourceB332 + difference 5 0) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA332 + difference 0 5) (sourceB332 + difference 5 0) sourceC332) = raw6877 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6877; decide +kernel
    rw [ha]
    exact (canonical6877 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA332 + difference 1 0) (sourceB332 + difference 0 1) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3240) := by
    have ha : (tripleCharges (sourceA332 + difference 1 0) (sourceB332 + difference 0 1) sourceC332) = raw6878 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6878; decide +kernel
    rw [ha]
    exact (canonical6878 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA332 + difference 1 2) (sourceB332 + difference 2 1) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3561) := by
    have ha : (tripleCharges (sourceA332 + difference 1 2) (sourceB332 + difference 2 1) sourceC332) = raw6879 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6879; decide +kernel
    rw [ha]
    exact (canonical6879 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA332 + difference 1 3) (sourceB332 + difference 3 1) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2835) := by
    have ha : (tripleCharges (sourceA332 + difference 1 3) (sourceB332 + difference 3 1) sourceC332) = raw6880 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6880; decide +kernel
    rw [ha]
    exact (canonical6880 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA332 + difference 1 4) (sourceB332 + difference 4 1) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3577) := by
    have ha : (tripleCharges (sourceA332 + difference 1 4) (sourceB332 + difference 4 1) sourceC332) = raw6881 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6881; decide +kernel
    rw [ha]
    exact (canonical6881 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA332 + difference 1 5) (sourceB332 + difference 5 1) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA332 + difference 1 5) (sourceB332 + difference 5 1) sourceC332) = raw6882 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6882; decide +kernel
    rw [ha]
    exact (canonical6882 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA332 + difference 2 0) (sourceB332 + difference 0 2) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3238) := by
    have ha : (tripleCharges (sourceA332 + difference 2 0) (sourceB332 + difference 0 2) sourceC332) = raw6883 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6883; decide +kernel
    rw [ha]
    exact (canonical6883 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA332 + difference 2 1) (sourceB332 + difference 1 2) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA332 + difference 2 1) (sourceB332 + difference 1 2) sourceC332) = raw6884 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6884; decide +kernel
    rw [ha]
    exact (canonical6884 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA332 + difference 2 3) (sourceB332 + difference 3 2) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2833) := by
    have ha : (tripleCharges (sourceA332 + difference 2 3) (sourceB332 + difference 3 2) sourceC332) = raw6885 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6885; decide +kernel
    rw [ha]
    exact (canonical6885 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA332 + difference 2 4) (sourceB332 + difference 4 2) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA332 + difference 2 4) (sourceB332 + difference 4 2) sourceC332) = raw6886 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6886; decide +kernel
    rw [ha]
    exact (canonical6886 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA332 + difference 2 5) (sourceB332 + difference 5 2) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA332 + difference 2 5) (sourceB332 + difference 5 2) sourceC332) = raw6887 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6887; decide +kernel
    rw [ha]
    exact (canonical6887 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA332 + difference 3 0) (sourceB332 + difference 0 3) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA332 + difference 3 0) (sourceB332 + difference 0 3) sourceC332) = raw6888 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6888; decide +kernel
    rw [ha]
    exact (canonical6888 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA332 + difference 3 1) (sourceB332 + difference 1 3) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3479) := by
    have ha : (tripleCharges (sourceA332 + difference 3 1) (sourceB332 + difference 1 3) sourceC332) = raw6889 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6889; decide +kernel
    rw [ha]
    exact (canonical6889 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA332 + difference 3 2) (sourceB332 + difference 2 3) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA332 + difference 3 2) (sourceB332 + difference 2 3) sourceC332) = raw6890 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6890; decide +kernel
    rw [ha]
    exact (canonical6890 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA332 + difference 3 4) (sourceB332 + difference 4 3) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA332 + difference 3 4) (sourceB332 + difference 4 3) sourceC332) = raw6891 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6891; decide +kernel
    rw [ha]
    exact (canonical6891 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA332 + difference 3 5) (sourceB332 + difference 5 3) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA332 + difference 3 5) (sourceB332 + difference 5 3) sourceC332) = raw6892 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6892; decide +kernel
    rw [ha]
    exact (canonical6892 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA332 + difference 4 0) (sourceB332 + difference 0 4) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3243) := by
    have ha : (tripleCharges (sourceA332 + difference 4 0) (sourceB332 + difference 0 4) sourceC332) = raw6893 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6893; decide +kernel
    rw [ha]
    exact (canonical6893 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA332 + difference 4 1) (sourceB332 + difference 1 4) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA332 + difference 4 1) (sourceB332 + difference 1 4) sourceC332) = raw6894 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6894; decide +kernel
    rw [ha]
    exact (canonical6894 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA332 + difference 4 2) (sourceB332 + difference 2 4) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3518) := by
    have ha : (tripleCharges (sourceA332 + difference 4 2) (sourceB332 + difference 2 4) sourceC332) = raw6895 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6895; decide +kernel
    rw [ha]
    exact (canonical6895 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA332 + difference 4 3) (sourceB332 + difference 3 4) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2838) := by
    have ha : (tripleCharges (sourceA332 + difference 4 3) (sourceB332 + difference 3 4) sourceC332) = raw6896 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6896; decide +kernel
    rw [ha]
    exact (canonical6896 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA332 + difference 4 5) (sourceB332 + difference 5 4) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA332 + difference 4 5) (sourceB332 + difference 5 4) sourceC332) = raw6897 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6897; decide +kernel
    rw [ha]
    exact (canonical6897 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA332 + difference 5 0) (sourceB332 + difference 0 5) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2005) := by
    have ha : (tripleCharges (sourceA332 + difference 5 0) (sourceB332 + difference 0 5) sourceC332) = raw6898 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6898; decide +kernel
    rw [ha]
    exact (canonical6898 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA332 + difference 5 1) (sourceB332 + difference 1 5) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA332 + difference 5 1) (sourceB332 + difference 1 5) sourceC332) = raw6899 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6899; decide +kernel
    rw [ha]
    exact (canonical6899 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA332 + difference 5 2) (sourceB332 + difference 2 5) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2001) := by
    have ha : (tripleCharges (sourceA332 + difference 5 2) (sourceB332 + difference 2 5) sourceC332) = raw6900 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6900; decide +kernel
    rw [ha]
    exact (canonical6900 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA332 + difference 5 3) (sourceB332 + difference 3 5) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2004) := by
    have ha : (tripleCharges (sourceA332 + difference 5 3) (sourceB332 + difference 3 5) sourceC332) = raw6901 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6901; decide +kernel
    rw [ha]
    exact (canonical6901 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA332 + difference 5 4) (sourceB332 + difference 4 5) sourceC332) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA332 + difference 5 4) (sourceB332 + difference 4 5) sourceC332) = raw6902 := by
      apply Matrix.ext; unfold tripleCharges sourceA332 sourceB332 sourceC332 difference raw6902; decide +kernel
    rw [ha]
    exact (canonical6902 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA332 sourceB332 sourceC332
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm332, Integer.Sparse.eval]
  linarith only [hs]

def sourceA333 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB333 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC333 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceForm333 : Integer.Sparse Master := [(Sum.inr 2732, 2), (Sum.inr 3814, 2), (Sum.inr 3841, 1), (Sum.inr 3906, 1), (Sum.inr 4092, -1)]

theorem sourceEq333 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm333 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA333 + difference 0 0) (sourceB333 + difference 0 0) sourceC333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA333 + difference 0 0) (sourceB333 + difference 0 0) sourceC333) = raw6903 := by
      apply Matrix.ext; unfold tripleCharges sourceA333 sourceB333 sourceC333 difference raw6903; decide +kernel
    rw [ha]
    exact (canonical6903 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA333 + difference 0 1) (sourceB333 + difference 1 0) sourceC333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA333 + difference 0 1) (sourceB333 + difference 1 0) sourceC333) = raw6904 := by
      apply Matrix.ext; unfold tripleCharges sourceA333 sourceB333 sourceC333 difference raw6904; decide +kernel
    rw [ha]
    exact (canonical6904 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA333 + difference 0 2) (sourceB333 + difference 2 0) sourceC333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3841) := by
    have ha : (tripleCharges (sourceA333 + difference 0 2) (sourceB333 + difference 2 0) sourceC333) = raw6905 := by
      apply Matrix.ext; unfold tripleCharges sourceA333 sourceB333 sourceC333 difference raw6905; decide +kernel
    rw [ha]
    exact (canonical6905 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA333 + difference 0 3) (sourceB333 + difference 3 0) sourceC333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA333 + difference 0 3) (sourceB333 + difference 3 0) sourceC333) = raw6906 := by
      apply Matrix.ext; unfold tripleCharges sourceA333 sourceB333 sourceC333 difference raw6906; decide +kernel
    rw [ha]
    exact (canonical6906 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA333 + difference 0 4) (sourceB333 + difference 4 0) sourceC333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA333 + difference 0 4) (sourceB333 + difference 4 0) sourceC333) = raw6907 := by
      apply Matrix.ext; unfold tripleCharges sourceA333 sourceB333 sourceC333 difference raw6907; decide +kernel
    rw [ha]
    exact (canonical6907 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA333 + difference 0 5) (sourceB333 + difference 5 0) sourceC333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3906) := by
    have ha : (tripleCharges (sourceA333 + difference 0 5) (sourceB333 + difference 5 0) sourceC333) = raw6908 := by
      apply Matrix.ext; unfold tripleCharges sourceA333 sourceB333 sourceC333 difference raw6908; decide +kernel
    rw [ha]
    exact (canonical6908 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA333 + sourceB333) sourceC333) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA333 + sourceB333) sourceC333) = raw6909 := by
      apply Matrix.ext; unfold doubleCharges sourceA333 sourceB333 sourceC333 raw6909; decide +kernel
    rw [ha]
    exact (canonical6909 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA333 sourceB333 sourceC333
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm333, Integer.Sparse.eval]
  linarith only [hs]

def sourceA334 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB334 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC334 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceForm334 : Integer.Sparse Master := [(Sum.inr 1223, 1), (Sum.inr 1225, 1), (Sum.inr 1226, 1), (Sum.inr 1241, 1), (Sum.inr 1278, 1), (Sum.inr 2732, 1), (Sum.inr 4092, -1)]

theorem sourceEq334 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm334 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA334 + difference 0 0) (sourceB334 + difference 0 0) sourceC334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA334 + difference 0 0) (sourceB334 + difference 0 0) sourceC334) = raw6903 := by
      apply Matrix.ext; unfold tripleCharges sourceA334 sourceB334 sourceC334 difference raw6903; decide +kernel
    rw [ha]
    exact (canonical6903 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA334 + difference 1 0) (sourceB334 + difference 0 1) sourceC334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1278) := by
    have ha : (tripleCharges (sourceA334 + difference 1 0) (sourceB334 + difference 0 1) sourceC334) = raw6910 := by
      apply Matrix.ext; unfold tripleCharges sourceA334 sourceB334 sourceC334 difference raw6910; decide +kernel
    rw [ha]
    exact (canonical6910 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA334 + difference 2 0) (sourceB334 + difference 0 2) sourceC334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1223) := by
    have ha : (tripleCharges (sourceA334 + difference 2 0) (sourceB334 + difference 0 2) sourceC334) = raw6911 := by
      apply Matrix.ext; unfold tripleCharges sourceA334 sourceB334 sourceC334 difference raw6911; decide +kernel
    rw [ha]
    exact (canonical6911 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA334 + difference 3 0) (sourceB334 + difference 0 3) sourceC334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA334 + difference 3 0) (sourceB334 + difference 0 3) sourceC334) = raw6912 := by
      apply Matrix.ext; unfold tripleCharges sourceA334 sourceB334 sourceC334 difference raw6912; decide +kernel
    rw [ha]
    exact (canonical6912 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA334 + difference 4 0) (sourceB334 + difference 0 4) sourceC334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1226) := by
    have ha : (tripleCharges (sourceA334 + difference 4 0) (sourceB334 + difference 0 4) sourceC334) = raw6913 := by
      apply Matrix.ext; unfold tripleCharges sourceA334 sourceB334 sourceC334 difference raw6913; decide +kernel
    rw [ha]
    exact (canonical6913 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA334 + difference 5 0) (sourceB334 + difference 0 5) sourceC334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1225) := by
    have ha : (tripleCharges (sourceA334 + difference 5 0) (sourceB334 + difference 0 5) sourceC334) = raw6914 := by
      apply Matrix.ext; unfold tripleCharges sourceA334 sourceB334 sourceC334 difference raw6914; decide +kernel
    rw [ha]
    exact (canonical6914 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA334 + sourceB334) sourceC334) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA334 + sourceB334) sourceC334) = raw6909 := by
      apply Matrix.ext; unfold doubleCharges sourceA334 sourceB334 sourceC334 raw6909; decide +kernel
    rw [ha]
    exact (canonical6909 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA334 sourceB334 sourceC334
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm334, Integer.Sparse.eval]
  linarith only [hs]

def sourceA335 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB335 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC335 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceForm335 : Integer.Sparse Master := [(Sum.inr 1278, 1), (Sum.inr 2578, 1), (Sum.inr 2649, 1), (Sum.inr 2732, 1), (Sum.inr 2758, 1), (Sum.inr 2773, 1), (Sum.inr 4092, -1)]

theorem sourceEq335 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm335 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA335 + difference 1 0) (sourceB335 + difference 0 1) sourceC335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1278) := by
    have ha : (tripleCharges (sourceA335 + difference 1 0) (sourceB335 + difference 0 1) sourceC335) = raw6910 := by
      apply Matrix.ext; unfold tripleCharges sourceA335 sourceB335 sourceC335 difference raw6910; decide +kernel
    rw [ha]
    exact (canonical6910 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA335 + difference 1 1) (sourceB335 + difference 1 1) sourceC335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA335 + difference 1 1) (sourceB335 + difference 1 1) sourceC335) = raw6903 := by
      apply Matrix.ext; unfold tripleCharges sourceA335 sourceB335 sourceC335 difference raw6903; decide +kernel
    rw [ha]
    exact (canonical6903 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA335 + difference 1 2) (sourceB335 + difference 2 1) sourceC335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2578) := by
    have ha : (tripleCharges (sourceA335 + difference 1 2) (sourceB335 + difference 2 1) sourceC335) = raw6915 := by
      apply Matrix.ext; unfold tripleCharges sourceA335 sourceB335 sourceC335 difference raw6915; decide +kernel
    rw [ha]
    exact (canonical6915 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA335 + difference 1 3) (sourceB335 + difference 3 1) sourceC335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2649) := by
    have ha : (tripleCharges (sourceA335 + difference 1 3) (sourceB335 + difference 3 1) sourceC335) = raw6916 := by
      apply Matrix.ext; unfold tripleCharges sourceA335 sourceB335 sourceC335 difference raw6916; decide +kernel
    rw [ha]
    exact (canonical6916 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA335 + difference 1 4) (sourceB335 + difference 4 1) sourceC335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2758) := by
    have ha : (tripleCharges (sourceA335 + difference 1 4) (sourceB335 + difference 4 1) sourceC335) = raw6917 := by
      apply Matrix.ext; unfold tripleCharges sourceA335 sourceB335 sourceC335 difference raw6917; decide +kernel
    rw [ha]
    exact (canonical6917 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA335 + difference 1 5) (sourceB335 + difference 5 1) sourceC335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA335 + difference 1 5) (sourceB335 + difference 5 1) sourceC335) = raw6918 := by
      apply Matrix.ext; unfold tripleCharges sourceA335 sourceB335 sourceC335 difference raw6918; decide +kernel
    rw [ha]
    exact (canonical6918 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA335 + sourceB335) sourceC335) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA335 + sourceB335) sourceC335) = raw6909 := by
      apply Matrix.ext; unfold doubleCharges sourceA335 sourceB335 sourceC335 raw6909; decide +kernel
    rw [ha]
    exact (canonical6909 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA335 sourceB335 sourceC335
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm335, Integer.Sparse.eval]
  linarith only [hs]

def sourceA336 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB336 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC336 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceForm336 : Integer.Sparse Master := [(Sum.inr 2494, 1), (Sum.inr 2497, 1), (Sum.inr 2499, 1), (Sum.inr 2515, 1), (Sum.inr 2732, 1), (Sum.inr 3814, 1), (Sum.inr 4092, -1)]

theorem sourceEq336 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm336 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA336 + difference 0 1) (sourceB336 + difference 1 0) sourceC336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA336 + difference 0 1) (sourceB336 + difference 1 0) sourceC336) = raw6904 := by
      apply Matrix.ext; unfold tripleCharges sourceA336 sourceB336 sourceC336 difference raw6904; decide +kernel
    rw [ha]
    exact (canonical6904 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA336 + difference 1 1) (sourceB336 + difference 1 1) sourceC336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA336 + difference 1 1) (sourceB336 + difference 1 1) sourceC336) = raw6903 := by
      apply Matrix.ext; unfold tripleCharges sourceA336 sourceB336 sourceC336 difference raw6903; decide +kernel
    rw [ha]
    exact (canonical6903 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA336 + difference 2 1) (sourceB336 + difference 1 2) sourceC336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA336 + difference 2 1) (sourceB336 + difference 1 2) sourceC336) = raw6919 := by
      apply Matrix.ext; unfold tripleCharges sourceA336 sourceB336 sourceC336 difference raw6919; decide +kernel
    rw [ha]
    exact (canonical6919 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA336 + difference 3 1) (sourceB336 + difference 1 3) sourceC336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA336 + difference 3 1) (sourceB336 + difference 1 3) sourceC336) = raw6920 := by
      apply Matrix.ext; unfold tripleCharges sourceA336 sourceB336 sourceC336 difference raw6920; decide +kernel
    rw [ha]
    exact (canonical6920 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA336 + difference 4 1) (sourceB336 + difference 1 4) sourceC336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2499) := by
    have ha : (tripleCharges (sourceA336 + difference 4 1) (sourceB336 + difference 1 4) sourceC336) = raw6921 := by
      apply Matrix.ext; unfold tripleCharges sourceA336 sourceB336 sourceC336 difference raw6921; decide +kernel
    rw [ha]
    exact (canonical6921 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA336 + difference 5 1) (sourceB336 + difference 1 5) sourceC336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA336 + difference 5 1) (sourceB336 + difference 1 5) sourceC336) = raw6922 := by
      apply Matrix.ext; unfold tripleCharges sourceA336 sourceB336 sourceC336 difference raw6922; decide +kernel
    rw [ha]
    exact (canonical6922 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA336 + sourceB336) sourceC336) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA336 + sourceB336) sourceC336) = raw6909 := by
      apply Matrix.ext; unfold doubleCharges sourceA336 sourceB336 sourceC336 raw6909; decide +kernel
    rw [ha]
    exact (canonical6909 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA336 sourceB336 sourceC336
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm336, Integer.Sparse.eval]
  linarith only [hs]

def sourceA337 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB337 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC337 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceForm337 : Integer.Sparse Master := [(Sum.inr 1223, 1), (Sum.inr 2494, 1), (Sum.inr 2646, 1), (Sum.inr 2714, 1), (Sum.inr 2730, 1), (Sum.inr 2732, 1), (Sum.inr 4092, -1)]

theorem sourceEq337 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm337 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA337 + difference 2 0) (sourceB337 + difference 0 2) sourceC337) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1223) := by
    have ha : (tripleCharges (sourceA337 + difference 2 0) (sourceB337 + difference 0 2) sourceC337) = raw6911 := by
      apply Matrix.ext; unfold tripleCharges sourceA337 sourceB337 sourceC337 difference raw6911; decide +kernel
    rw [ha]
    exact (canonical6911 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA337 + difference 2 1) (sourceB337 + difference 1 2) sourceC337) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA337 + difference 2 1) (sourceB337 + difference 1 2) sourceC337) = raw6919 := by
      apply Matrix.ext; unfold tripleCharges sourceA337 sourceB337 sourceC337 difference raw6919; decide +kernel
    rw [ha]
    exact (canonical6919 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA337 + difference 2 2) (sourceB337 + difference 2 2) sourceC337) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA337 + difference 2 2) (sourceB337 + difference 2 2) sourceC337) = raw6903 := by
      apply Matrix.ext; unfold tripleCharges sourceA337 sourceB337 sourceC337 difference raw6903; decide +kernel
    rw [ha]
    exact (canonical6903 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA337 + difference 2 3) (sourceB337 + difference 3 2) sourceC337) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2646) := by
    have ha : (tripleCharges (sourceA337 + difference 2 3) (sourceB337 + difference 3 2) sourceC337) = raw6923 := by
      apply Matrix.ext; unfold tripleCharges sourceA337 sourceB337 sourceC337 difference raw6923; decide +kernel
    rw [ha]
    exact (canonical6923 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA337 + difference 2 4) (sourceB337 + difference 4 2) sourceC337) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA337 + difference 2 4) (sourceB337 + difference 4 2) sourceC337) = raw6924 := by
      apply Matrix.ext; unfold tripleCharges sourceA337 sourceB337 sourceC337 difference raw6924; decide +kernel
    rw [ha]
    exact (canonical6924 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA337 + difference 2 5) (sourceB337 + difference 5 2) sourceC337) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA337 + difference 2 5) (sourceB337 + difference 5 2) sourceC337) = raw6925 := by
      apply Matrix.ext; unfold tripleCharges sourceA337 sourceB337 sourceC337 difference raw6925; decide +kernel
    rw [ha]
    exact (canonical6925 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA337 + sourceB337) sourceC337) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA337 + sourceB337) sourceC337) = raw6909 := by
      apply Matrix.ext; unfold doubleCharges sourceA337 sourceB337 sourceC337 raw6909; decide +kernel
    rw [ha]
    exact (canonical6909 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA337 sourceB337 sourceC337
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm337, Integer.Sparse.eval]
  linarith only [hs]

def sourceA338 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB338 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC338 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceForm338 : Integer.Sparse Master := [(Sum.inr 2548, 1), (Sum.inr 2549, 1), (Sum.inr 2557, 1), (Sum.inr 2578, 1), (Sum.inr 2732, 1), (Sum.inr 3841, 1), (Sum.inr 4092, -1)]

theorem sourceEq338 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm338 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA338 + difference 0 2) (sourceB338 + difference 2 0) sourceC338) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3841) := by
    have ha : (tripleCharges (sourceA338 + difference 0 2) (sourceB338 + difference 2 0) sourceC338) = raw6905 := by
      apply Matrix.ext; unfold tripleCharges sourceA338 sourceB338 sourceC338 difference raw6905; decide +kernel
    rw [ha]
    exact (canonical6905 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA338 + difference 1 2) (sourceB338 + difference 2 1) sourceC338) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2578) := by
    have ha : (tripleCharges (sourceA338 + difference 1 2) (sourceB338 + difference 2 1) sourceC338) = raw6915 := by
      apply Matrix.ext; unfold tripleCharges sourceA338 sourceB338 sourceC338 difference raw6915; decide +kernel
    rw [ha]
    exact (canonical6915 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA338 + difference 2 2) (sourceB338 + difference 2 2) sourceC338) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA338 + difference 2 2) (sourceB338 + difference 2 2) sourceC338) = raw6903 := by
      apply Matrix.ext; unfold tripleCharges sourceA338 sourceB338 sourceC338 difference raw6903; decide +kernel
    rw [ha]
    exact (canonical6903 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA338 + difference 3 2) (sourceB338 + difference 2 3) sourceC338) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2557) := by
    have ha : (tripleCharges (sourceA338 + difference 3 2) (sourceB338 + difference 2 3) sourceC338) = raw6926 := by
      apply Matrix.ext; unfold tripleCharges sourceA338 sourceB338 sourceC338 difference raw6926; decide +kernel
    rw [ha]
    exact (canonical6926 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA338 + difference 4 2) (sourceB338 + difference 2 4) sourceC338) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2549) := by
    have ha : (tripleCharges (sourceA338 + difference 4 2) (sourceB338 + difference 2 4) sourceC338) = raw6927 := by
      apply Matrix.ext; unfold tripleCharges sourceA338 sourceB338 sourceC338 difference raw6927; decide +kernel
    rw [ha]
    exact (canonical6927 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA338 + difference 5 2) (sourceB338 + difference 2 5) sourceC338) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2548) := by
    have ha : (tripleCharges (sourceA338 + difference 5 2) (sourceB338 + difference 2 5) sourceC338) = raw6928 := by
      apply Matrix.ext; unfold tripleCharges sourceA338 sourceB338 sourceC338 difference raw6928; decide +kernel
    rw [ha]
    exact (canonical6928 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA338 + sourceB338) sourceC338) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA338 + sourceB338) sourceC338) = raw6909 := by
      apply Matrix.ext; unfold doubleCharges sourceA338 sourceB338 sourceC338 raw6909; decide +kernel
    rw [ha]
    exact (canonical6909 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA338 sourceB338 sourceC338
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm338, Integer.Sparse.eval]
  linarith only [hs]

def sourceA339 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB339 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceC339 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceForm339 : Integer.Sparse Master := [(Sum.inr 2646, 1), (Sum.inr 2648, 1), (Sum.inr 2649, 2), (Sum.inr 2732, 2), (Sum.inr 4092, -1)]

theorem sourceEq339 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm339 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA339 + difference 0 3) (sourceB339 + difference 3 0) sourceC339) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA339 + difference 0 3) (sourceB339 + difference 3 0) sourceC339) = raw6906 := by
      apply Matrix.ext; unfold tripleCharges sourceA339 sourceB339 sourceC339 difference raw6906; decide +kernel
    rw [ha]
    exact (canonical6906 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA339 + difference 1 3) (sourceB339 + difference 3 1) sourceC339) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2649) := by
    have ha : (tripleCharges (sourceA339 + difference 1 3) (sourceB339 + difference 3 1) sourceC339) = raw6916 := by
      apply Matrix.ext; unfold tripleCharges sourceA339 sourceB339 sourceC339 difference raw6916; decide +kernel
    rw [ha]
    exact (canonical6916 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA339 + difference 2 3) (sourceB339 + difference 3 2) sourceC339) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2646) := by
    have ha : (tripleCharges (sourceA339 + difference 2 3) (sourceB339 + difference 3 2) sourceC339) = raw6923 := by
      apply Matrix.ext; unfold tripleCharges sourceA339 sourceB339 sourceC339 difference raw6923; decide +kernel
    rw [ha]
    exact (canonical6923 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA339 + difference 3 3) (sourceB339 + difference 3 3) sourceC339) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA339 + difference 3 3) (sourceB339 + difference 3 3) sourceC339) = raw6903 := by
      apply Matrix.ext; unfold tripleCharges sourceA339 sourceB339 sourceC339 difference raw6903; decide +kernel
    rw [ha]
    exact (canonical6903 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA339 + difference 4 3) (sourceB339 + difference 3 4) sourceC339) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2649) := by
    have ha : (tripleCharges (sourceA339 + difference 4 3) (sourceB339 + difference 3 4) sourceC339) = raw6929 := by
      apply Matrix.ext; unfold tripleCharges sourceA339 sourceB339 sourceC339 difference raw6929; decide +kernel
    rw [ha]
    exact (canonical6929 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA339 + difference 5 3) (sourceB339 + difference 3 5) sourceC339) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2648) := by
    have ha : (tripleCharges (sourceA339 + difference 5 3) (sourceB339 + difference 3 5) sourceC339) = raw6930 := by
      apply Matrix.ext; unfold tripleCharges sourceA339 sourceB339 sourceC339 difference raw6930; decide +kernel
    rw [ha]
    exact (canonical6930 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA339 + sourceB339) sourceC339) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA339 + sourceB339) sourceC339) = raw6909 := by
      apply Matrix.ext; unfold doubleCharges sourceA339 sourceB339 sourceC339 raw6909; decide +kernel
    rw [ha]
    exact (canonical6909 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA339 sourceB339 sourceC339
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm339, Integer.Sparse.eval]
  linarith only [hs]

def sourceA340 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB340 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC340 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceForm340 : Integer.Sparse Master := [(Sum.inr 4409, 1), (Sum.inr 4410, 1), (Sum.inr 4411, 1), (Sum.inr 4425, 1), (Sum.inr 4475, 1), (Sum.inr 5007, 1), (Sum.inr 5008, 1), (Sum.inr 5009, 1), (Sum.inr 5019, 1), (Sum.inr 5052, 1), (Sum.inr 5053, 1), (Sum.inr 5060, 1), (Sum.inr 5086, 1), (Sum.inr 5139, 1), (Sum.inr 5173, 1), (Sum.inr 5187, 1), (Sum.inr 5188, 1), (Sum.inr 5204, 1), (Sum.inr 5263, 1), (Sum.inr 5264, 1), (Sum.inr 5267, 1), (Sum.inr 5268, 1), (Sum.inr 5276, 1), (Sum.inr 5299, 1), (Sum.inr 5302, 1), (Sum.inr 5425, 1), (Sum.inr 5428, 1), (Sum.inr 5436, 1), (Sum.inr 5438, 1), (Sum.inr 5443, 1)]

theorem sourceEq340 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm340 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA340 + difference 0 1) (sourceB340 + difference 1 0) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA340 + difference 0 1) (sourceB340 + difference 1 0) sourceC340) = raw6931 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6931; decide +kernel
    rw [ha]
    exact (canonical6931 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA340 + difference 0 2) (sourceB340 + difference 2 0) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA340 + difference 0 2) (sourceB340 + difference 2 0) sourceC340) = raw6932 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6932; decide +kernel
    rw [ha]
    exact (canonical6932 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA340 + difference 0 3) (sourceB340 + difference 3 0) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA340 + difference 0 3) (sourceB340 + difference 3 0) sourceC340) = raw6933 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6933; decide +kernel
    rw [ha]
    exact (canonical6933 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA340 + difference 0 4) (sourceB340 + difference 4 0) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA340 + difference 0 4) (sourceB340 + difference 4 0) sourceC340) = raw6934 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6934; decide +kernel
    rw [ha]
    exact (canonical6934 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA340 + difference 0 5) (sourceB340 + difference 5 0) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA340 + difference 0 5) (sourceB340 + difference 5 0) sourceC340) = raw6935 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6935; decide +kernel
    rw [ha]
    exact (canonical6935 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA340 + difference 1 0) (sourceB340 + difference 0 1) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4475) := by
    have ha : (tripleCharges (sourceA340 + difference 1 0) (sourceB340 + difference 0 1) sourceC340) = raw6936 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6936; decide +kernel
    rw [ha]
    exact (canonical6936 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA340 + difference 1 2) (sourceB340 + difference 2 1) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA340 + difference 1 2) (sourceB340 + difference 2 1) sourceC340) = raw6937 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6937; decide +kernel
    rw [ha]
    exact (canonical6937 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA340 + difference 1 3) (sourceB340 + difference 3 1) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA340 + difference 1 3) (sourceB340 + difference 3 1) sourceC340) = raw6938 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6938; decide +kernel
    rw [ha]
    exact (canonical6938 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA340 + difference 1 4) (sourceB340 + difference 4 1) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA340 + difference 1 4) (sourceB340 + difference 4 1) sourceC340) = raw6939 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6939; decide +kernel
    rw [ha]
    exact (canonical6939 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA340 + difference 1 5) (sourceB340 + difference 5 1) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA340 + difference 1 5) (sourceB340 + difference 5 1) sourceC340) = raw6940 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6940; decide +kernel
    rw [ha]
    exact (canonical6940 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA340 + difference 2 0) (sourceB340 + difference 0 2) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4409) := by
    have ha : (tripleCharges (sourceA340 + difference 2 0) (sourceB340 + difference 0 2) sourceC340) = raw6941 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6941; decide +kernel
    rw [ha]
    exact (canonical6941 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA340 + difference 2 1) (sourceB340 + difference 1 2) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5007) := by
    have ha : (tripleCharges (sourceA340 + difference 2 1) (sourceB340 + difference 1 2) sourceC340) = raw6942 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6942; decide +kernel
    rw [ha]
    exact (canonical6942 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA340 + difference 2 3) (sourceB340 + difference 3 2) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA340 + difference 2 3) (sourceB340 + difference 3 2) sourceC340) = raw6943 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6943; decide +kernel
    rw [ha]
    exact (canonical6943 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA340 + difference 2 4) (sourceB340 + difference 4 2) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA340 + difference 2 4) (sourceB340 + difference 4 2) sourceC340) = raw6944 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6944; decide +kernel
    rw [ha]
    exact (canonical6944 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA340 + difference 2 5) (sourceB340 + difference 5 2) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5263) := by
    have ha : (tripleCharges (sourceA340 + difference 2 5) (sourceB340 + difference 5 2) sourceC340) = raw6945 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6945; decide +kernel
    rw [ha]
    exact (canonical6945 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA340 + difference 3 0) (sourceB340 + difference 0 3) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4425) := by
    have ha : (tripleCharges (sourceA340 + difference 3 0) (sourceB340 + difference 0 3) sourceC340) = raw6946 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6946; decide +kernel
    rw [ha]
    exact (canonical6946 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA340 + difference 3 1) (sourceB340 + difference 1 3) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5019) := by
    have ha : (tripleCharges (sourceA340 + difference 3 1) (sourceB340 + difference 1 3) sourceC340) = raw6947 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6947; decide +kernel
    rw [ha]
    exact (canonical6947 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA340 + difference 3 2) (sourceB340 + difference 2 3) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5060) := by
    have ha : (tripleCharges (sourceA340 + difference 3 2) (sourceB340 + difference 2 3) sourceC340) = raw6948 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6948; decide +kernel
    rw [ha]
    exact (canonical6948 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA340 + difference 3 4) (sourceB340 + difference 4 3) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA340 + difference 3 4) (sourceB340 + difference 4 3) sourceC340) = raw6949 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6949; decide +kernel
    rw [ha]
    exact (canonical6949 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA340 + difference 3 5) (sourceB340 + difference 5 3) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA340 + difference 3 5) (sourceB340 + difference 5 3) sourceC340) = raw6950 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6950; decide +kernel
    rw [ha]
    exact (canonical6950 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA340 + difference 4 0) (sourceB340 + difference 0 4) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4411) := by
    have ha : (tripleCharges (sourceA340 + difference 4 0) (sourceB340 + difference 0 4) sourceC340) = raw6951 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6951; decide +kernel
    rw [ha]
    exact (canonical6951 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA340 + difference 4 1) (sourceB340 + difference 1 4) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5009) := by
    have ha : (tripleCharges (sourceA340 + difference 4 1) (sourceB340 + difference 1 4) sourceC340) = raw6952 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6952; decide +kernel
    rw [ha]
    exact (canonical6952 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA340 + difference 4 2) (sourceB340 + difference 2 4) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5053) := by
    have ha : (tripleCharges (sourceA340 + difference 4 2) (sourceB340 + difference 2 4) sourceC340) = raw6953 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6953; decide +kernel
    rw [ha]
    exact (canonical6953 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA340 + difference 4 3) (sourceB340 + difference 3 4) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5188) := by
    have ha : (tripleCharges (sourceA340 + difference 4 3) (sourceB340 + difference 3 4) sourceC340) = raw6954 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6954; decide +kernel
    rw [ha]
    exact (canonical6954 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA340 + difference 4 5) (sourceB340 + difference 5 4) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA340 + difference 4 5) (sourceB340 + difference 5 4) sourceC340) = raw6955 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6955; decide +kernel
    rw [ha]
    exact (canonical6955 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA340 + difference 5 0) (sourceB340 + difference 0 5) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4410) := by
    have ha : (tripleCharges (sourceA340 + difference 5 0) (sourceB340 + difference 0 5) sourceC340) = raw6956 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6956; decide +kernel
    rw [ha]
    exact (canonical6956 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA340 + difference 5 1) (sourceB340 + difference 1 5) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5008) := by
    have ha : (tripleCharges (sourceA340 + difference 5 1) (sourceB340 + difference 1 5) sourceC340) = raw6957 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6957; decide +kernel
    rw [ha]
    exact (canonical6957 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA340 + difference 5 2) (sourceB340 + difference 2 5) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5052) := by
    have ha : (tripleCharges (sourceA340 + difference 5 2) (sourceB340 + difference 2 5) sourceC340) = raw6958 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6958; decide +kernel
    rw [ha]
    exact (canonical6958 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA340 + difference 5 3) (sourceB340 + difference 3 5) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5139) := by
    have ha : (tripleCharges (sourceA340 + difference 5 3) (sourceB340 + difference 3 5) sourceC340) = raw6959 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6959; decide +kernel
    rw [ha]
    exact (canonical6959 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA340 + difference 5 4) (sourceB340 + difference 4 5) sourceC340) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA340 + difference 5 4) (sourceB340 + difference 4 5) sourceC340) = raw6960 := by
      apply Matrix.ext; unfold tripleCharges sourceA340 sourceB340 sourceC340 difference raw6960; decide +kernel
    rw [ha]
    exact (canonical6960 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA340 sourceB340 sourceC340
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm340, Integer.Sparse.eval]
  linarith only [hs]

def sourceA341 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB341 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC341 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceForm341 : Integer.Sparse Master := [(Sum.inr 990, 1), (Sum.inr 991, 1), (Sum.inr 992, 1), (Sum.inr 1006, 1), (Sum.inr 1058, 1), (Sum.inr 2392, 1), (Sum.inr 2393, 1), (Sum.inr 2394, 1), (Sum.inr 2405, 1), (Sum.inr 2454, 1), (Sum.inr 2455, 1), (Sum.inr 2463, 1), (Sum.inr 2494, 1), (Sum.inr 2617, 1), (Sum.inr 2618, 1), (Sum.inr 2620, 1), (Sum.inr 2638, 1), (Sum.inr 2728, 1), (Sum.inr 2729, 1), (Sum.inr 2732, 1), (Sum.inr 2734, 1), (Sum.inr 2735, 1), (Sum.inr 2744, 1), (Sum.inr 2773, 1), (Sum.inr 2776, 1), (Sum.inr 3872, 1), (Sum.inr 3876, 1), (Sum.inr 3877, 1), (Sum.inr 3889, 1), (Sum.inr 4003, 1)]

theorem sourceEq341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm341 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA341 + difference 0 1) (sourceB341 + difference 1 0) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA341 + difference 0 1) (sourceB341 + difference 1 0) sourceC341) = raw6961 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6961; decide +kernel
    rw [ha]
    exact (canonical6961 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA341 + difference 0 2) (sourceB341 + difference 2 0) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA341 + difference 0 2) (sourceB341 + difference 2 0) sourceC341) = raw6962 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6962; decide +kernel
    rw [ha]
    exact (canonical6962 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA341 + difference 0 3) (sourceB341 + difference 3 0) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4003) := by
    have ha : (tripleCharges (sourceA341 + difference 0 3) (sourceB341 + difference 3 0) sourceC341) = raw6963 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6963; decide +kernel
    rw [ha]
    exact (canonical6963 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA341 + difference 0 4) (sourceB341 + difference 4 0) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA341 + difference 0 4) (sourceB341 + difference 4 0) sourceC341) = raw6964 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6964; decide +kernel
    rw [ha]
    exact (canonical6964 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA341 + difference 0 5) (sourceB341 + difference 5 0) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA341 + difference 0 5) (sourceB341 + difference 5 0) sourceC341) = raw6965 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6965; decide +kernel
    rw [ha]
    exact (canonical6965 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA341 + difference 1 0) (sourceB341 + difference 0 1) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1058) := by
    have ha : (tripleCharges (sourceA341 + difference 1 0) (sourceB341 + difference 0 1) sourceC341) = raw6966 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6966; decide +kernel
    rw [ha]
    exact (canonical6966 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA341 + difference 1 2) (sourceB341 + difference 2 1) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA341 + difference 1 2) (sourceB341 + difference 2 1) sourceC341) = raw6967 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6967; decide +kernel
    rw [ha]
    exact (canonical6967 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA341 + difference 1 3) (sourceB341 + difference 3 1) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2638) := by
    have ha : (tripleCharges (sourceA341 + difference 1 3) (sourceB341 + difference 3 1) sourceC341) = raw6968 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6968; decide +kernel
    rw [ha]
    exact (canonical6968 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA341 + difference 1 4) (sourceB341 + difference 4 1) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA341 + difference 1 4) (sourceB341 + difference 4 1) sourceC341) = raw6969 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6969; decide +kernel
    rw [ha]
    exact (canonical6969 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA341 + difference 1 5) (sourceB341 + difference 5 1) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA341 + difference 1 5) (sourceB341 + difference 5 1) sourceC341) = raw6970 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6970; decide +kernel
    rw [ha]
    exact (canonical6970 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA341 + difference 2 0) (sourceB341 + difference 0 2) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 990) := by
    have ha : (tripleCharges (sourceA341 + difference 2 0) (sourceB341 + difference 0 2) sourceC341) = raw6971 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6971; decide +kernel
    rw [ha]
    exact (canonical6971 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA341 + difference 2 1) (sourceB341 + difference 1 2) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2392) := by
    have ha : (tripleCharges (sourceA341 + difference 2 1) (sourceB341 + difference 1 2) sourceC341) = raw6972 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6972; decide +kernel
    rw [ha]
    exact (canonical6972 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA341 + difference 2 3) (sourceB341 + difference 3 2) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2617) := by
    have ha : (tripleCharges (sourceA341 + difference 2 3) (sourceB341 + difference 3 2) sourceC341) = raw6973 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6973; decide +kernel
    rw [ha]
    exact (canonical6973 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA341 + difference 2 4) (sourceB341 + difference 4 2) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA341 + difference 2 4) (sourceB341 + difference 4 2) sourceC341) = raw6974 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6974; decide +kernel
    rw [ha]
    exact (canonical6974 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA341 + difference 2 5) (sourceB341 + difference 5 2) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2728) := by
    have ha : (tripleCharges (sourceA341 + difference 2 5) (sourceB341 + difference 5 2) sourceC341) = raw6975 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6975; decide +kernel
    rw [ha]
    exact (canonical6975 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA341 + difference 3 0) (sourceB341 + difference 0 3) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1006) := by
    have ha : (tripleCharges (sourceA341 + difference 3 0) (sourceB341 + difference 0 3) sourceC341) = raw6976 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6976; decide +kernel
    rw [ha]
    exact (canonical6976 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA341 + difference 3 1) (sourceB341 + difference 1 3) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2405) := by
    have ha : (tripleCharges (sourceA341 + difference 3 1) (sourceB341 + difference 1 3) sourceC341) = raw6977 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6977; decide +kernel
    rw [ha]
    exact (canonical6977 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA341 + difference 3 2) (sourceB341 + difference 2 3) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2463) := by
    have ha : (tripleCharges (sourceA341 + difference 3 2) (sourceB341 + difference 2 3) sourceC341) = raw6978 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6978; decide +kernel
    rw [ha]
    exact (canonical6978 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA341 + difference 3 4) (sourceB341 + difference 4 3) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA341 + difference 3 4) (sourceB341 + difference 4 3) sourceC341) = raw6979 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6979; decide +kernel
    rw [ha]
    exact (canonical6979 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA341 + difference 3 5) (sourceB341 + difference 5 3) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA341 + difference 3 5) (sourceB341 + difference 5 3) sourceC341) = raw6980 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6980; decide +kernel
    rw [ha]
    exact (canonical6980 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA341 + difference 4 0) (sourceB341 + difference 0 4) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 992) := by
    have ha : (tripleCharges (sourceA341 + difference 4 0) (sourceB341 + difference 0 4) sourceC341) = raw6981 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6981; decide +kernel
    rw [ha]
    exact (canonical6981 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA341 + difference 4 1) (sourceB341 + difference 1 4) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2394) := by
    have ha : (tripleCharges (sourceA341 + difference 4 1) (sourceB341 + difference 1 4) sourceC341) = raw6982 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6982; decide +kernel
    rw [ha]
    exact (canonical6982 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA341 + difference 4 2) (sourceB341 + difference 2 4) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2455) := by
    have ha : (tripleCharges (sourceA341 + difference 4 2) (sourceB341 + difference 2 4) sourceC341) = raw6983 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6983; decide +kernel
    rw [ha]
    exact (canonical6983 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA341 + difference 4 3) (sourceB341 + difference 3 4) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2620) := by
    have ha : (tripleCharges (sourceA341 + difference 4 3) (sourceB341 + difference 3 4) sourceC341) = raw6984 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6984; decide +kernel
    rw [ha]
    exact (canonical6984 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA341 + difference 4 5) (sourceB341 + difference 5 4) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA341 + difference 4 5) (sourceB341 + difference 5 4) sourceC341) = raw6985 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6985; decide +kernel
    rw [ha]
    exact (canonical6985 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA341 + difference 5 0) (sourceB341 + difference 0 5) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 991) := by
    have ha : (tripleCharges (sourceA341 + difference 5 0) (sourceB341 + difference 0 5) sourceC341) = raw6986 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6986; decide +kernel
    rw [ha]
    exact (canonical6986 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA341 + difference 5 1) (sourceB341 + difference 1 5) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2393) := by
    have ha : (tripleCharges (sourceA341 + difference 5 1) (sourceB341 + difference 1 5) sourceC341) = raw6987 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6987; decide +kernel
    rw [ha]
    exact (canonical6987 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA341 + difference 5 2) (sourceB341 + difference 2 5) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2454) := by
    have ha : (tripleCharges (sourceA341 + difference 5 2) (sourceB341 + difference 2 5) sourceC341) = raw6988 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6988; decide +kernel
    rw [ha]
    exact (canonical6988 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA341 + difference 5 3) (sourceB341 + difference 3 5) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA341 + difference 5 3) (sourceB341 + difference 3 5) sourceC341) = raw6989 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6989; decide +kernel
    rw [ha]
    exact (canonical6989 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA341 + difference 5 4) (sourceB341 + difference 4 5) sourceC341) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA341 + difference 5 4) (sourceB341 + difference 4 5) sourceC341) = raw6990 := by
      apply Matrix.ext; unfold tripleCharges sourceA341 sourceB341 sourceC341 difference raw6990; decide +kernel
    rw [ha]
    exact (canonical6990 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA341 sourceB341 sourceC341
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm341, Integer.Sparse.eval]
  linarith only [hs]

def sourceA342 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB342 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC342 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceForm342 : Integer.Sparse Master := [(Sum.inr 1609, 1), (Sum.inr 1610, 1), (Sum.inr 1611, 1), (Sum.inr 1624, 1), (Sum.inr 1715, 1), (Sum.inr 2906, 1), (Sum.inr 2910, 1), (Sum.inr 2952, 1), (Sum.inr 3052, 1), (Sum.inr 3347, 1), (Sum.inr 3348, 1), (Sum.inr 3358, 1), (Sum.inr 3430, 1), (Sum.inr 3437, 1), (Sum.inr 3464, 1), (Sum.inr 3505, 1), (Sum.inr 3506, 1), (Sum.inr 3523, 1), (Sum.inr 3537, 1), (Sum.inr 3538, 1), (Sum.inr 3541, 1), (Sum.inr 3549, 1), (Sum.inr 3573, 1), (Sum.inr 3624, 1), (Sum.inr 3626, 1), (Sum.inr 3839, 1), (Sum.inr 3845, 1), (Sum.inr 3862, 1), (Sum.inr 3877, 1), (Sum.inr 3993, 1)]

theorem sourceEq342 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm342 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA342 + difference 0 1) (sourceB342 + difference 1 0) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA342 + difference 0 1) (sourceB342 + difference 1 0) sourceC342) = raw6991 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw6991; decide +kernel
    rw [ha]
    exact (canonical6991 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA342 + difference 0 2) (sourceB342 + difference 2 0) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA342 + difference 0 2) (sourceB342 + difference 2 0) sourceC342) = raw6992 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw6992; decide +kernel
    rw [ha]
    exact (canonical6992 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA342 + difference 0 3) (sourceB342 + difference 3 0) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA342 + difference 0 3) (sourceB342 + difference 3 0) sourceC342) = raw6993 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw6993; decide +kernel
    rw [ha]
    exact (canonical6993 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA342 + difference 0 4) (sourceB342 + difference 4 0) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA342 + difference 0 4) (sourceB342 + difference 4 0) sourceC342) = raw6994 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw6994; decide +kernel
    rw [ha]
    exact (canonical6994 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA342 + difference 0 5) (sourceB342 + difference 5 0) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA342 + difference 0 5) (sourceB342 + difference 5 0) sourceC342) = raw6995 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw6995; decide +kernel
    rw [ha]
    exact (canonical6995 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA342 + difference 1 0) (sourceB342 + difference 0 1) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA342 + difference 1 0) (sourceB342 + difference 0 1) sourceC342) = raw6996 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw6996; decide +kernel
    rw [ha]
    exact (canonical6996 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA342 + difference 1 2) (sourceB342 + difference 2 1) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA342 + difference 1 2) (sourceB342 + difference 2 1) sourceC342) = raw6997 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw6997; decide +kernel
    rw [ha]
    exact (canonical6997 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA342 + difference 1 3) (sourceB342 + difference 3 1) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3624) := by
    have ha : (tripleCharges (sourceA342 + difference 1 3) (sourceB342 + difference 3 1) sourceC342) = raw6998 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw6998; decide +kernel
    rw [ha]
    exact (canonical6998 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA342 + difference 1 4) (sourceB342 + difference 4 1) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA342 + difference 1 4) (sourceB342 + difference 4 1) sourceC342) = raw6999 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw6999; decide +kernel
    rw [ha]
    exact (canonical6999 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA342 + difference 1 5) (sourceB342 + difference 5 1) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA342 + difference 1 5) (sourceB342 + difference 5 1) sourceC342) = raw7000 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7000; decide +kernel
    rw [ha]
    exact (canonical7000 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA342 + difference 2 0) (sourceB342 + difference 0 2) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1609) := by
    have ha : (tripleCharges (sourceA342 + difference 2 0) (sourceB342 + difference 0 2) sourceC342) = raw7001 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7001; decide +kernel
    rw [ha]
    exact (canonical7001 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA342 + difference 2 1) (sourceB342 + difference 1 2) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3347) := by
    have ha : (tripleCharges (sourceA342 + difference 2 1) (sourceB342 + difference 1 2) sourceC342) = raw7002 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7002; decide +kernel
    rw [ha]
    exact (canonical7002 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA342 + difference 2 3) (sourceB342 + difference 3 2) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3537) := by
    have ha : (tripleCharges (sourceA342 + difference 2 3) (sourceB342 + difference 3 2) sourceC342) = raw7003 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7003; decide +kernel
    rw [ha]
    exact (canonical7003 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA342 + difference 2 4) (sourceB342 + difference 4 2) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA342 + difference 2 4) (sourceB342 + difference 4 2) sourceC342) = raw7004 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7004; decide +kernel
    rw [ha]
    exact (canonical7004 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA342 + difference 2 5) (sourceB342 + difference 5 2) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3505) := by
    have ha : (tripleCharges (sourceA342 + difference 2 5) (sourceB342 + difference 5 2) sourceC342) = raw7005 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7005; decide +kernel
    rw [ha]
    exact (canonical7005 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA342 + difference 3 0) (sourceB342 + difference 0 3) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1610) := by
    have ha : (tripleCharges (sourceA342 + difference 3 0) (sourceB342 + difference 0 3) sourceC342) = raw7006 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7006; decide +kernel
    rw [ha]
    exact (canonical7006 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA342 + difference 3 1) (sourceB342 + difference 1 3) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2910) := by
    have ha : (tripleCharges (sourceA342 + difference 3 1) (sourceB342 + difference 1 3) sourceC342) = raw7007 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7007; decide +kernel
    rw [ha]
    exact (canonical7007 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA342 + difference 3 2) (sourceB342 + difference 2 3) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2906) := by
    have ha : (tripleCharges (sourceA342 + difference 3 2) (sourceB342 + difference 2 3) sourceC342) = raw7008 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7008; decide +kernel
    rw [ha]
    exact (canonical7008 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA342 + difference 3 4) (sourceB342 + difference 4 3) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA342 + difference 3 4) (sourceB342 + difference 4 3) sourceC342) = raw7009 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7009; decide +kernel
    rw [ha]
    exact (canonical7009 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA342 + difference 3 5) (sourceB342 + difference 5 3) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA342 + difference 3 5) (sourceB342 + difference 5 3) sourceC342) = raw7010 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7010; decide +kernel
    rw [ha]
    exact (canonical7010 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA342 + difference 4 0) (sourceB342 + difference 0 4) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1611) := by
    have ha : (tripleCharges (sourceA342 + difference 4 0) (sourceB342 + difference 0 4) sourceC342) = raw7011 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7011; decide +kernel
    rw [ha]
    exact (canonical7011 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA342 + difference 4 1) (sourceB342 + difference 1 4) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3348) := by
    have ha : (tripleCharges (sourceA342 + difference 4 1) (sourceB342 + difference 1 4) sourceC342) = raw7012 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7012; decide +kernel
    rw [ha]
    exact (canonical7012 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA342 + difference 4 2) (sourceB342 + difference 2 4) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3430) := by
    have ha : (tripleCharges (sourceA342 + difference 4 2) (sourceB342 + difference 2 4) sourceC342) = raw7013 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7013; decide +kernel
    rw [ha]
    exact (canonical7013 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA342 + difference 4 3) (sourceB342 + difference 3 4) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA342 + difference 4 3) (sourceB342 + difference 3 4) sourceC342) = raw7014 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7014; decide +kernel
    rw [ha]
    exact (canonical7014 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA342 + difference 4 5) (sourceB342 + difference 5 4) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3506) := by
    have ha : (tripleCharges (sourceA342 + difference 4 5) (sourceB342 + difference 5 4) sourceC342) = raw7015 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7015; decide +kernel
    rw [ha]
    exact (canonical7015 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA342 + difference 5 0) (sourceB342 + difference 0 5) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1624) := by
    have ha : (tripleCharges (sourceA342 + difference 5 0) (sourceB342 + difference 0 5) sourceC342) = raw7016 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7016; decide +kernel
    rw [ha]
    exact (canonical7016 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA342 + difference 5 1) (sourceB342 + difference 1 5) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3358) := by
    have ha : (tripleCharges (sourceA342 + difference 5 1) (sourceB342 + difference 1 5) sourceC342) = raw7017 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7017; decide +kernel
    rw [ha]
    exact (canonical7017 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA342 + difference 5 2) (sourceB342 + difference 2 5) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3437) := by
    have ha : (tripleCharges (sourceA342 + difference 5 2) (sourceB342 + difference 2 5) sourceC342) = raw7018 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7018; decide +kernel
    rw [ha]
    exact (canonical7018 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA342 + difference 5 3) (sourceB342 + difference 3 5) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA342 + difference 5 3) (sourceB342 + difference 3 5) sourceC342) = raw7019 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7019; decide +kernel
    rw [ha]
    exact (canonical7019 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA342 + difference 5 4) (sourceB342 + difference 4 5) sourceC342) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA342 + difference 5 4) (sourceB342 + difference 4 5) sourceC342) = raw7020 := by
      apply Matrix.ext; unfold tripleCharges sourceA342 sourceB342 sourceC342 difference raw7020; decide +kernel
    rw [ha]
    exact (canonical7020 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA342 sourceB342 sourceC342
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm342, Integer.Sparse.eval]
  linarith only [hs]

def sourceA343 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB343 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC343 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceForm343 : Integer.Sparse Master := [(Sum.inr 3038, 1), (Sum.inr 3840, 1), (Sum.inr 3845, 1), (Sum.inr 3854, 1), (Sum.inr 3857, 1), (Sum.inr 3907, 1), (Sum.inr 4092, -1)]

theorem sourceEq343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm343 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA343 + difference 0 0) (sourceB343 + difference 0 0) sourceC343) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA343 + difference 0 0) (sourceB343 + difference 0 0) sourceC343) = raw7021 := by
      apply Matrix.ext; unfold tripleCharges sourceA343 sourceB343 sourceC343 difference raw7021; decide +kernel
    rw [ha]
    exact (canonical7021 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA343 + difference 0 1) (sourceB343 + difference 1 0) sourceC343) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA343 + difference 0 1) (sourceB343 + difference 1 0) sourceC343) = raw7022 := by
      apply Matrix.ext; unfold tripleCharges sourceA343 sourceB343 sourceC343 difference raw7022; decide +kernel
    rw [ha]
    exact (canonical7022 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA343 + difference 0 2) (sourceB343 + difference 2 0) sourceC343) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA343 + difference 0 2) (sourceB343 + difference 2 0) sourceC343) = raw7023 := by
      apply Matrix.ext; unfold tripleCharges sourceA343 sourceB343 sourceC343 difference raw7023; decide +kernel
    rw [ha]
    exact (canonical7023 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA343 + difference 0 3) (sourceB343 + difference 3 0) sourceC343) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA343 + difference 0 3) (sourceB343 + difference 3 0) sourceC343) = raw7024 := by
      apply Matrix.ext; unfold tripleCharges sourceA343 sourceB343 sourceC343 difference raw7024; decide +kernel
    rw [ha]
    exact (canonical7024 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA343 + difference 0 4) (sourceB343 + difference 4 0) sourceC343) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA343 + difference 0 4) (sourceB343 + difference 4 0) sourceC343) = raw7025 := by
      apply Matrix.ext; unfold tripleCharges sourceA343 sourceB343 sourceC343 difference raw7025; decide +kernel
    rw [ha]
    exact (canonical7025 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA343 + difference 0 5) (sourceB343 + difference 5 0) sourceC343) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA343 + difference 0 5) (sourceB343 + difference 5 0) sourceC343) = raw7026 := by
      apply Matrix.ext; unfold tripleCharges sourceA343 sourceB343 sourceC343 difference raw7026; decide +kernel
    rw [ha]
    exact (canonical7026 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA343 + sourceB343) sourceC343) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA343 + sourceB343) sourceC343) = raw7027 := by
      apply Matrix.ext; unfold doubleCharges sourceA343 sourceB343 sourceC343 raw7027; decide +kernel
    rw [ha]
    exact (canonical7027 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA343 sourceB343 sourceC343
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm343, Integer.Sparse.eval]
  linarith only [hs]

def sourceA344 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB344 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC344 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceForm344 : Integer.Sparse Master := [(Sum.inr 1357, 1), (Sum.inr 1359, 1), (Sum.inr 1362, 1), (Sum.inr 1367, 1), (Sum.inr 1422, 1), (Sum.inr 3038, 1), (Sum.inr 4092, -1)]

theorem sourceEq344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm344 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA344 + difference 0 0) (sourceB344 + difference 0 0) sourceC344) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA344 + difference 0 0) (sourceB344 + difference 0 0) sourceC344) = raw7021 := by
      apply Matrix.ext; unfold tripleCharges sourceA344 sourceB344 sourceC344 difference raw7021; decide +kernel
    rw [ha]
    exact (canonical7021 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA344 + difference 1 0) (sourceB344 + difference 0 1) sourceC344) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1367) := by
    have ha : (tripleCharges (sourceA344 + difference 1 0) (sourceB344 + difference 0 1) sourceC344) = raw7028 := by
      apply Matrix.ext; unfold tripleCharges sourceA344 sourceB344 sourceC344 difference raw7028; decide +kernel
    rw [ha]
    exact (canonical7028 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA344 + difference 2 0) (sourceB344 + difference 0 2) sourceC344) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1357) := by
    have ha : (tripleCharges (sourceA344 + difference 2 0) (sourceB344 + difference 0 2) sourceC344) = raw7029 := by
      apply Matrix.ext; unfold tripleCharges sourceA344 sourceB344 sourceC344 difference raw7029; decide +kernel
    rw [ha]
    exact (canonical7029 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA344 + difference 3 0) (sourceB344 + difference 0 3) sourceC344) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1422) := by
    have ha : (tripleCharges (sourceA344 + difference 3 0) (sourceB344 + difference 0 3) sourceC344) = raw7030 := by
      apply Matrix.ext; unfold tripleCharges sourceA344 sourceB344 sourceC344 difference raw7030; decide +kernel
    rw [ha]
    exact (canonical7030 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA344 + difference 4 0) (sourceB344 + difference 0 4) sourceC344) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1362) := by
    have ha : (tripleCharges (sourceA344 + difference 4 0) (sourceB344 + difference 0 4) sourceC344) = raw7031 := by
      apply Matrix.ext; unfold tripleCharges sourceA344 sourceB344 sourceC344 difference raw7031; decide +kernel
    rw [ha]
    exact (canonical7031 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA344 + difference 5 0) (sourceB344 + difference 0 5) sourceC344) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1359) := by
    have ha : (tripleCharges (sourceA344 + difference 5 0) (sourceB344 + difference 0 5) sourceC344) = raw7032 := by
      apply Matrix.ext; unfold tripleCharges sourceA344 sourceB344 sourceC344 difference raw7032; decide +kernel
    rw [ha]
    exact (canonical7032 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA344 + sourceB344) sourceC344) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA344 + sourceB344) sourceC344) = raw7027 := by
      apply Matrix.ext; unfold doubleCharges sourceA344 sourceB344 sourceC344 raw7027; decide +kernel
    rw [ha]
    exact (canonical7027 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA344 sourceB344 sourceC344
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm344, Integer.Sparse.eval]
  linarith only [hs]

def sourceA345 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB345 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC345 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceForm345 : Integer.Sparse Master := [(Sum.inr 1367, 1), (Sum.inr 2881, 1), (Sum.inr 2974, 1), (Sum.inr 3038, 1), (Sum.inr 3051, 1), (Sum.inr 3054, 1), (Sum.inr 4092, -1)]

theorem sourceEq345 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm345 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA345 + difference 1 0) (sourceB345 + difference 0 1) sourceC345) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1367) := by
    have ha : (tripleCharges (sourceA345 + difference 1 0) (sourceB345 + difference 0 1) sourceC345) = raw7028 := by
      apply Matrix.ext; unfold tripleCharges sourceA345 sourceB345 sourceC345 difference raw7028; decide +kernel
    rw [ha]
    exact (canonical7028 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA345 + difference 1 1) (sourceB345 + difference 1 1) sourceC345) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA345 + difference 1 1) (sourceB345 + difference 1 1) sourceC345) = raw7021 := by
      apply Matrix.ext; unfold tripleCharges sourceA345 sourceB345 sourceC345 difference raw7021; decide +kernel
    rw [ha]
    exact (canonical7021 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA345 + difference 1 2) (sourceB345 + difference 2 1) sourceC345) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA345 + difference 1 2) (sourceB345 + difference 2 1) sourceC345) = raw7033 := by
      apply Matrix.ext; unfold tripleCharges sourceA345 sourceB345 sourceC345 difference raw7033; decide +kernel
    rw [ha]
    exact (canonical7033 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA345 + difference 1 3) (sourceB345 + difference 3 1) sourceC345) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA345 + difference 1 3) (sourceB345 + difference 3 1) sourceC345) = raw7034 := by
      apply Matrix.ext; unfold tripleCharges sourceA345 sourceB345 sourceC345 difference raw7034; decide +kernel
    rw [ha]
    exact (canonical7034 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA345 + difference 1 4) (sourceB345 + difference 4 1) sourceC345) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA345 + difference 1 4) (sourceB345 + difference 4 1) sourceC345) = raw7035 := by
      apply Matrix.ext; unfold tripleCharges sourceA345 sourceB345 sourceC345 difference raw7035; decide +kernel
    rw [ha]
    exact (canonical7035 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA345 + difference 1 5) (sourceB345 + difference 5 1) sourceC345) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA345 + difference 1 5) (sourceB345 + difference 5 1) sourceC345) = raw7036 := by
      apply Matrix.ext; unfold tripleCharges sourceA345 sourceB345 sourceC345 difference raw7036; decide +kernel
    rw [ha]
    exact (canonical7036 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA345 + sourceB345) sourceC345) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA345 + sourceB345) sourceC345) = raw7027 := by
      apply Matrix.ext; unfold doubleCharges sourceA345 sourceB345 sourceC345 raw7027; decide +kernel
    rw [ha]
    exact (canonical7027 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA345 sourceB345 sourceC345
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm345, Integer.Sparse.eval]
  linarith only [hs]

def sourceA346 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB346 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC346 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceForm346 : Integer.Sparse Master := [(Sum.inr 2579, 1), (Sum.inr 2582, 1), (Sum.inr 3007, 1), (Sum.inr 3010, 1), (Sum.inr 3038, 1), (Sum.inr 3854, 1), (Sum.inr 4092, -1)]

theorem sourceEq346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm346 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA346 + difference 0 1) (sourceB346 + difference 1 0) sourceC346) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA346 + difference 0 1) (sourceB346 + difference 1 0) sourceC346) = raw7022 := by
      apply Matrix.ext; unfold tripleCharges sourceA346 sourceB346 sourceC346 difference raw7022; decide +kernel
    rw [ha]
    exact (canonical7022 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA346 + difference 1 1) (sourceB346 + difference 1 1) sourceC346) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA346 + difference 1 1) (sourceB346 + difference 1 1) sourceC346) = raw7021 := by
      apply Matrix.ext; unfold tripleCharges sourceA346 sourceB346 sourceC346 difference raw7021; decide +kernel
    rw [ha]
    exact (canonical7021 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA346 + difference 2 1) (sourceB346 + difference 1 2) sourceC346) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3007) := by
    have ha : (tripleCharges (sourceA346 + difference 2 1) (sourceB346 + difference 1 2) sourceC346) = raw7037 := by
      apply Matrix.ext; unfold tripleCharges sourceA346 sourceB346 sourceC346 difference raw7037; decide +kernel
    rw [ha]
    exact (canonical7037 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA346 + difference 3 1) (sourceB346 + difference 1 3) sourceC346) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2582) := by
    have ha : (tripleCharges (sourceA346 + difference 3 1) (sourceB346 + difference 1 3) sourceC346) = raw7038 := by
      apply Matrix.ext; unfold tripleCharges sourceA346 sourceB346 sourceC346 difference raw7038; decide +kernel
    rw [ha]
    exact (canonical7038 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA346 + difference 4 1) (sourceB346 + difference 1 4) sourceC346) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3010) := by
    have ha : (tripleCharges (sourceA346 + difference 4 1) (sourceB346 + difference 1 4) sourceC346) = raw7039 := by
      apply Matrix.ext; unfold tripleCharges sourceA346 sourceB346 sourceC346 difference raw7039; decide +kernel
    rw [ha]
    exact (canonical7039 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA346 + difference 5 1) (sourceB346 + difference 1 5) sourceC346) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2579) := by
    have ha : (tripleCharges (sourceA346 + difference 5 1) (sourceB346 + difference 1 5) sourceC346) = raw7040 := by
      apply Matrix.ext; unfold tripleCharges sourceA346 sourceB346 sourceC346 difference raw7040; decide +kernel
    rw [ha]
    exact (canonical7040 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA346 + sourceB346) sourceC346) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA346 + sourceB346) sourceC346) = raw7027 := by
      apply Matrix.ext; unfold doubleCharges sourceA346 sourceB346 sourceC346 raw7027; decide +kernel
    rw [ha]
    exact (canonical7027 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA346 sourceB346 sourceC346
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm346, Integer.Sparse.eval]
  linarith only [hs]

def sourceA347 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB347 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC347 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceForm347 : Integer.Sparse Master := [(Sum.inr 1357, 1), (Sum.inr 2861, 1), (Sum.inr 3007, 1), (Sum.inr 3036, 1), (Sum.inr 3038, 2), (Sum.inr 4092, -1)]

theorem sourceEq347 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm347 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA347 + difference 2 0) (sourceB347 + difference 0 2) sourceC347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1357) := by
    have ha : (tripleCharges (sourceA347 + difference 2 0) (sourceB347 + difference 0 2) sourceC347) = raw7029 := by
      apply Matrix.ext; unfold tripleCharges sourceA347 sourceB347 sourceC347 difference raw7029; decide +kernel
    rw [ha]
    exact (canonical7029 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA347 + difference 2 1) (sourceB347 + difference 1 2) sourceC347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3007) := by
    have ha : (tripleCharges (sourceA347 + difference 2 1) (sourceB347 + difference 1 2) sourceC347) = raw7037 := by
      apply Matrix.ext; unfold tripleCharges sourceA347 sourceB347 sourceC347 difference raw7037; decide +kernel
    rw [ha]
    exact (canonical7037 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA347 + difference 2 2) (sourceB347 + difference 2 2) sourceC347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA347 + difference 2 2) (sourceB347 + difference 2 2) sourceC347) = raw7021 := by
      apply Matrix.ext; unfold tripleCharges sourceA347 sourceB347 sourceC347 difference raw7021; decide +kernel
    rw [ha]
    exact (canonical7021 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA347 + difference 2 3) (sourceB347 + difference 3 2) sourceC347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2861) := by
    have ha : (tripleCharges (sourceA347 + difference 2 3) (sourceB347 + difference 3 2) sourceC347) = raw7041 := by
      apply Matrix.ext; unfold tripleCharges sourceA347 sourceB347 sourceC347 difference raw7041; decide +kernel
    rw [ha]
    exact (canonical7041 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA347 + difference 2 4) (sourceB347 + difference 4 2) sourceC347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA347 + difference 2 4) (sourceB347 + difference 4 2) sourceC347) = raw7042 := by
      apply Matrix.ext; unfold tripleCharges sourceA347 sourceB347 sourceC347 difference raw7042; decide +kernel
    rw [ha]
    exact (canonical7042 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA347 + difference 2 5) (sourceB347 + difference 5 2) sourceC347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3036) := by
    have ha : (tripleCharges (sourceA347 + difference 2 5) (sourceB347 + difference 5 2) sourceC347) = raw7043 := by
      apply Matrix.ext; unfold tripleCharges sourceA347 sourceB347 sourceC347 difference raw7043; decide +kernel
    rw [ha]
    exact (canonical7043 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA347 + sourceB347) sourceC347) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA347 + sourceB347) sourceC347) = raw7027 := by
      apply Matrix.ext; unfold doubleCharges sourceA347 sourceB347 sourceC347 raw7027; decide +kernel
    rw [ha]
    exact (canonical7027 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA347 sourceB347 sourceC347
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm347, Integer.Sparse.eval]
  linarith only [hs]

def sourceA348 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB348 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC348 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceForm348 : Integer.Sparse Master := [(Sum.inr 2547, 1), (Sum.inr 2580, 1), (Sum.inr 2971, 1), (Sum.inr 2974, 1), (Sum.inr 3038, 1), (Sum.inr 3840, 1), (Sum.inr 4092, -1)]

theorem sourceEq348 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm348 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA348 + difference 0 2) (sourceB348 + difference 2 0) sourceC348) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA348 + difference 0 2) (sourceB348 + difference 2 0) sourceC348) = raw7023 := by
      apply Matrix.ext; unfold tripleCharges sourceA348 sourceB348 sourceC348 difference raw7023; decide +kernel
    rw [ha]
    exact (canonical7023 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA348 + difference 1 2) (sourceB348 + difference 2 1) sourceC348) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA348 + difference 1 2) (sourceB348 + difference 2 1) sourceC348) = raw7033 := by
      apply Matrix.ext; unfold tripleCharges sourceA348 sourceB348 sourceC348 difference raw7033; decide +kernel
    rw [ha]
    exact (canonical7033 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA348 + difference 2 2) (sourceB348 + difference 2 2) sourceC348) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA348 + difference 2 2) (sourceB348 + difference 2 2) sourceC348) = raw7021 := by
      apply Matrix.ext; unfold tripleCharges sourceA348 sourceB348 sourceC348 difference raw7021; decide +kernel
    rw [ha]
    exact (canonical7021 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA348 + difference 3 2) (sourceB348 + difference 2 3) sourceC348) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2580) := by
    have ha : (tripleCharges (sourceA348 + difference 3 2) (sourceB348 + difference 2 3) sourceC348) = raw7044 := by
      apply Matrix.ext; unfold tripleCharges sourceA348 sourceB348 sourceC348 difference raw7044; decide +kernel
    rw [ha]
    exact (canonical7044 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA348 + difference 4 2) (sourceB348 + difference 2 4) sourceC348) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2971) := by
    have ha : (tripleCharges (sourceA348 + difference 4 2) (sourceB348 + difference 2 4) sourceC348) = raw7045 := by
      apply Matrix.ext; unfold tripleCharges sourceA348 sourceB348 sourceC348 difference raw7045; decide +kernel
    rw [ha]
    exact (canonical7045 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA348 + difference 5 2) (sourceB348 + difference 2 5) sourceC348) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2547) := by
    have ha : (tripleCharges (sourceA348 + difference 5 2) (sourceB348 + difference 2 5) sourceC348) = raw7046 := by
      apply Matrix.ext; unfold tripleCharges sourceA348 sourceB348 sourceC348 difference raw7046; decide +kernel
    rw [ha]
    exact (canonical7046 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA348 + sourceB348) sourceC348) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA348 + sourceB348) sourceC348) = raw7027 := by
      apply Matrix.ext; unfold doubleCharges sourceA348 sourceB348 sourceC348 raw7027; decide +kernel
    rw [ha]
    exact (canonical7027 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA348 sourceB348 sourceC348
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm348, Integer.Sparse.eval]
  linarith only [hs]

def sourceA349 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB349 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC349 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceForm349 : Integer.Sparse Master := [(Sum.inr 2558, 1), (Sum.inr 2861, 1), (Sum.inr 2867, 1), (Sum.inr 2881, 1), (Sum.inr 3038, 1), (Sum.inr 3845, 1), (Sum.inr 4092, -1)]

theorem sourceEq349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm349 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA349 + difference 0 3) (sourceB349 + difference 3 0) sourceC349) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA349 + difference 0 3) (sourceB349 + difference 3 0) sourceC349) = raw7024 := by
      apply Matrix.ext; unfold tripleCharges sourceA349 sourceB349 sourceC349 difference raw7024; decide +kernel
    rw [ha]
    exact (canonical7024 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA349 + difference 1 3) (sourceB349 + difference 3 1) sourceC349) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA349 + difference 1 3) (sourceB349 + difference 3 1) sourceC349) = raw7034 := by
      apply Matrix.ext; unfold tripleCharges sourceA349 sourceB349 sourceC349 difference raw7034; decide +kernel
    rw [ha]
    exact (canonical7034 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA349 + difference 2 3) (sourceB349 + difference 3 2) sourceC349) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2861) := by
    have ha : (tripleCharges (sourceA349 + difference 2 3) (sourceB349 + difference 3 2) sourceC349) = raw7041 := by
      apply Matrix.ext; unfold tripleCharges sourceA349 sourceB349 sourceC349 difference raw7041; decide +kernel
    rw [ha]
    exact (canonical7041 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA349 + difference 3 3) (sourceB349 + difference 3 3) sourceC349) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA349 + difference 3 3) (sourceB349 + difference 3 3) sourceC349) = raw7021 := by
      apply Matrix.ext; unfold tripleCharges sourceA349 sourceB349 sourceC349 difference raw7021; decide +kernel
    rw [ha]
    exact (canonical7021 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA349 + difference 4 3) (sourceB349 + difference 3 4) sourceC349) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2867) := by
    have ha : (tripleCharges (sourceA349 + difference 4 3) (sourceB349 + difference 3 4) sourceC349) = raw7047 := by
      apply Matrix.ext; unfold tripleCharges sourceA349 sourceB349 sourceC349 difference raw7047; decide +kernel
    rw [ha]
    exact (canonical7047 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA349 + difference 5 3) (sourceB349 + difference 3 5) sourceC349) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA349 + difference 5 3) (sourceB349 + difference 3 5) sourceC349) = raw7048 := by
      apply Matrix.ext; unfold tripleCharges sourceA349 sourceB349 sourceC349 difference raw7048; decide +kernel
    rw [ha]
    exact (canonical7048 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA349 + sourceB349) sourceC349) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA349 + sourceB349) sourceC349) = raw7027 := by
      apply Matrix.ext; unfold doubleCharges sourceA349 sourceB349 sourceC349 raw7027; decide +kernel
    rw [ha]
    exact (canonical7027 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA349 sourceB349 sourceC349
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm349, Integer.Sparse.eval]
  linarith only [hs]

def sourceA350 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB350 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC350 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceForm350 : Integer.Sparse Master := [(Sum.inr 1362, 1), (Sum.inr 2867, 1), (Sum.inr 2971, 1), (Sum.inr 3010, 1), (Sum.inr 3038, 1), (Sum.inr 3040, 1), (Sum.inr 4092, -1)]

theorem sourceEq350 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm350 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA350 + difference 4 0) (sourceB350 + difference 0 4) sourceC350) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1362) := by
    have ha : (tripleCharges (sourceA350 + difference 4 0) (sourceB350 + difference 0 4) sourceC350) = raw7031 := by
      apply Matrix.ext; unfold tripleCharges sourceA350 sourceB350 sourceC350 difference raw7031; decide +kernel
    rw [ha]
    exact (canonical7031 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA350 + difference 4 1) (sourceB350 + difference 1 4) sourceC350) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3010) := by
    have ha : (tripleCharges (sourceA350 + difference 4 1) (sourceB350 + difference 1 4) sourceC350) = raw7039 := by
      apply Matrix.ext; unfold tripleCharges sourceA350 sourceB350 sourceC350 difference raw7039; decide +kernel
    rw [ha]
    exact (canonical7039 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA350 + difference 4 2) (sourceB350 + difference 2 4) sourceC350) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2971) := by
    have ha : (tripleCharges (sourceA350 + difference 4 2) (sourceB350 + difference 2 4) sourceC350) = raw7045 := by
      apply Matrix.ext; unfold tripleCharges sourceA350 sourceB350 sourceC350 difference raw7045; decide +kernel
    rw [ha]
    exact (canonical7045 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA350 + difference 4 3) (sourceB350 + difference 3 4) sourceC350) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2867) := by
    have ha : (tripleCharges (sourceA350 + difference 4 3) (sourceB350 + difference 3 4) sourceC350) = raw7047 := by
      apply Matrix.ext; unfold tripleCharges sourceA350 sourceB350 sourceC350 difference raw7047; decide +kernel
    rw [ha]
    exact (canonical7047 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA350 + difference 4 4) (sourceB350 + difference 4 4) sourceC350) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA350 + difference 4 4) (sourceB350 + difference 4 4) sourceC350) = raw7021 := by
      apply Matrix.ext; unfold tripleCharges sourceA350 sourceB350 sourceC350 difference raw7021; decide +kernel
    rw [ha]
    exact (canonical7021 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA350 + difference 4 5) (sourceB350 + difference 5 4) sourceC350) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3040) := by
    have ha : (tripleCharges (sourceA350 + difference 4 5) (sourceB350 + difference 5 4) sourceC350) = raw7049 := by
      apply Matrix.ext; unfold tripleCharges sourceA350 sourceB350 sourceC350 difference raw7049; decide +kernel
    rw [ha]
    exact (canonical7049 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA350 + sourceB350) sourceC350) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA350 + sourceB350) sourceC350) = raw7027 := by
      apply Matrix.ext; unfold doubleCharges sourceA350 sourceB350 sourceC350 raw7027; decide +kernel
    rw [ha]
    exact (canonical7027 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA350 sourceB350 sourceC350
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm350, Integer.Sparse.eval]
  linarith only [hs]

def sourceA351 : Charge := ![1, -1, 0, 2, 0, -2]
def sourceB351 : Charge := ![2, 1, 0, -2, -1, 0]
def sourceC351 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm351 : Integer.Sparse Master := [(Sum.inr 4816, 1), (Sum.inr 4818, 1), (Sum.inr 4819, 1), (Sum.inr 4820, 1), (Sum.inr 4821, 1), (Sum.inr 4839, 1), (Sum.inr 4840, 1), (Sum.inr 4880, 1), (Sum.inr 4898, 1), (Sum.inr 5136, 1), (Sum.inr 5140, 1), (Sum.inr 5165, 1), (Sum.inr 5219, 1), (Sum.inr 5224, 1), (Sum.inr 5228, 1), (Sum.inr 5232, 1), (Sum.inr 5233, 1), (Sum.inr 5234, 1), (Sum.inr 5244, 1), (Sum.inr 5245, 1), (Sum.inr 5251, 1), (Sum.inr 5254, 1), (Sum.inr 5258, 1), (Sum.inr 5259, 1), (Sum.inr 5260, 1), (Sum.inr 5266, 1), (Sum.inr 5267, 1), (Sum.inr 5276, 1), (Sum.inr 5294, 1), (Sum.inr 5302, 1)]

theorem sourceEq351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm351 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA351 + difference 0 1) (sourceB351 + difference 1 0) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA351 + difference 0 1) (sourceB351 + difference 1 0) sourceC351) = raw7050 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw7050; decide +kernel
    rw [ha]
    exact (canonical7050 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA351 + difference 0 2) (sourceB351 + difference 2 0) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5219) := by
    have ha : (tripleCharges (sourceA351 + difference 0 2) (sourceB351 + difference 2 0) sourceC351) = raw7051 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw7051; decide +kernel
    rw [ha]
    exact (canonical7051 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA351 + difference 0 3) (sourceB351 + difference 3 0) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA351 + difference 0 3) (sourceB351 + difference 3 0) sourceC351) = raw6371 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw6371; decide +kernel
    rw [ha]
    exact (canonical6371 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA351 + difference 0 4) (sourceB351 + difference 4 0) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA351 + difference 0 4) (sourceB351 + difference 4 0) sourceC351) = raw6704 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw6704; decide +kernel
    rw [ha]
    exact (canonical6704 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA351 + difference 0 5) (sourceB351 + difference 5 0) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA351 + difference 0 5) (sourceB351 + difference 5 0) sourceC351) = raw7052 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw7052; decide +kernel
    rw [ha]
    exact (canonical7052 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA351 + difference 1 0) (sourceB351 + difference 0 1) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA351 + difference 1 0) (sourceB351 + difference 0 1) sourceC351) = raw7053 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw7053; decide +kernel
    rw [ha]
    exact (canonical7053 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA351 + difference 1 2) (sourceB351 + difference 2 1) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA351 + difference 1 2) (sourceB351 + difference 2 1) sourceC351) = raw7054 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw7054; decide +kernel
    rw [ha]
    exact (canonical7054 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA351 + difference 1 3) (sourceB351 + difference 3 1) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA351 + difference 1 3) (sourceB351 + difference 3 1) sourceC351) = raw6375 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw6375; decide +kernel
    rw [ha]
    exact (canonical6375 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA351 + difference 1 4) (sourceB351 + difference 4 1) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA351 + difference 1 4) (sourceB351 + difference 4 1) sourceC351) = raw6709 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw6709; decide +kernel
    rw [ha]
    exact (canonical6709 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA351 + difference 1 5) (sourceB351 + difference 5 1) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA351 + difference 1 5) (sourceB351 + difference 5 1) sourceC351) = raw7055 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw7055; decide +kernel
    rw [ha]
    exact (canonical7055 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA351 + difference 2 0) (sourceB351 + difference 0 2) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA351 + difference 2 0) (sourceB351 + difference 0 2) sourceC351) = raw7056 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw7056; decide +kernel
    rw [ha]
    exact (canonical7056 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA351 + difference 2 1) (sourceB351 + difference 1 2) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5224) := by
    have ha : (tripleCharges (sourceA351 + difference 2 1) (sourceB351 + difference 1 2) sourceC351) = raw7057 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw7057; decide +kernel
    rw [ha]
    exact (canonical7057 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA351 + difference 2 3) (sourceB351 + difference 3 2) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA351 + difference 2 3) (sourceB351 + difference 3 2) sourceC351) = raw6379 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw6379; decide +kernel
    rw [ha]
    exact (canonical6379 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA351 + difference 2 4) (sourceB351 + difference 4 2) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA351 + difference 2 4) (sourceB351 + difference 4 2) sourceC351) = raw6714 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw6714; decide +kernel
    rw [ha]
    exact (canonical6714 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA351 + difference 2 5) (sourceB351 + difference 5 2) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5136) := by
    have ha : (tripleCharges (sourceA351 + difference 2 5) (sourceB351 + difference 5 2) sourceC351) = raw7058 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw7058; decide +kernel
    rw [ha]
    exact (canonical7058 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA351 + difference 3 0) (sourceB351 + difference 0 3) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4819) := by
    have ha : (tripleCharges (sourceA351 + difference 3 0) (sourceB351 + difference 0 3) sourceC351) = raw7059 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw7059; decide +kernel
    rw [ha]
    exact (canonical7059 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA351 + difference 3 1) (sourceB351 + difference 1 3) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4820) := by
    have ha : (tripleCharges (sourceA351 + difference 3 1) (sourceB351 + difference 1 3) sourceC351) = raw7060 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw7060; decide +kernel
    rw [ha]
    exact (canonical7060 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA351 + difference 3 2) (sourceB351 + difference 2 3) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4818) := by
    have ha : (tripleCharges (sourceA351 + difference 3 2) (sourceB351 + difference 2 3) sourceC351) = raw7061 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw7061; decide +kernel
    rw [ha]
    exact (canonical7061 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA351 + difference 3 4) (sourceB351 + difference 4 3) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA351 + difference 3 4) (sourceB351 + difference 4 3) sourceC351) = raw6719 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw6719; decide +kernel
    rw [ha]
    exact (canonical6719 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA351 + difference 3 5) (sourceB351 + difference 5 3) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4840) := by
    have ha : (tripleCharges (sourceA351 + difference 3 5) (sourceB351 + difference 5 3) sourceC351) = raw7062 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw7062; decide +kernel
    rw [ha]
    exact (canonical7062 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA351 + difference 4 0) (sourceB351 + difference 0 4) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA351 + difference 4 0) (sourceB351 + difference 0 4) sourceC351) = raw6381 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw6381; decide +kernel
    rw [ha]
    exact (canonical6381 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA351 + difference 4 1) (sourceB351 + difference 1 4) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5234) := by
    have ha : (tripleCharges (sourceA351 + difference 4 1) (sourceB351 + difference 1 4) sourceC351) = raw6382 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw6382; decide +kernel
    rw [ha]
    exact (canonical6382 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA351 + difference 4 2) (sourceB351 + difference 2 4) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5245) := by
    have ha : (tripleCharges (sourceA351 + difference 4 2) (sourceB351 + difference 2 4) sourceC351) = raw6383 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw6383; decide +kernel
    rw [ha]
    exact (canonical6383 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA351 + difference 4 3) (sourceB351 + difference 3 4) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA351 + difference 4 3) (sourceB351 + difference 3 4) sourceC351) = raw6028 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw6028; decide +kernel
    rw [ha]
    exact (canonical6028 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA351 + difference 4 5) (sourceB351 + difference 5 4) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5165) := by
    have ha : (tripleCharges (sourceA351 + difference 4 5) (sourceB351 + difference 5 4) sourceC351) = raw6385 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw6385; decide +kernel
    rw [ha]
    exact (canonical6385 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA351 + difference 5 0) (sourceB351 + difference 0 5) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA351 + difference 5 0) (sourceB351 + difference 0 5) sourceC351) = raw6720 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw6720; decide +kernel
    rw [ha]
    exact (canonical6720 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA351 + difference 5 1) (sourceB351 + difference 1 5) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA351 + difference 5 1) (sourceB351 + difference 1 5) sourceC351) = raw6721 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw6721; decide +kernel
    rw [ha]
    exact (canonical6721 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA351 + difference 5 2) (sourceB351 + difference 2 5) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5244) := by
    have ha : (tripleCharges (sourceA351 + difference 5 2) (sourceB351 + difference 2 5) sourceC351) = raw6722 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw6722; decide +kernel
    rw [ha]
    exact (canonical6722 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA351 + difference 5 3) (sourceB351 + difference 3 5) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA351 + difference 5 3) (sourceB351 + difference 3 5) sourceC351) = raw6390 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw6390; decide +kernel
    rw [ha]
    exact (canonical6390 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA351 + difference 5 4) (sourceB351 + difference 4 5) sourceC351) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA351 + difference 5 4) (sourceB351 + difference 4 5) sourceC351) = raw7063 := by
      apply Matrix.ext; unfold tripleCharges sourceA351 sourceB351 sourceC351 difference raw7063; decide +kernel
    rw [ha]
    exact (canonical7063 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA351 sourceB351 sourceC351
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm351, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
