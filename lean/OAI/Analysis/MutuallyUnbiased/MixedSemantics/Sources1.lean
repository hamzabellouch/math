import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical30

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA32 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB32 : Charge := ![0, 0, 0, 0, 3, -3]
def sourceC32 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm32 : Integer.Sparse Master := [(Sum.inr 1092, 1), (Sum.inr 2063, 3), (Sum.inr 2285, 1), (Sum.inr 2294, 1), (Sum.inr 4085, -1)]

theorem sourceEq32 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm32 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA32 + difference 0 0) (sourceB32 + difference 0 0) sourceC32) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2285) := by
    have ha : (tripleCharges (sourceA32 + difference 0 0) (sourceB32 + difference 0 0) sourceC32) = raw3511 := by
      apply Matrix.ext; unfold tripleCharges sourceA32 sourceB32 sourceC32 difference raw3511; decide +kernel
    rw [ha]
    exact (canonical3511 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA32 + difference 0 1) (sourceB32 + difference 1 0) sourceC32) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA32 + difference 0 1) (sourceB32 + difference 1 0) sourceC32) = raw3512 := by
      apply Matrix.ext; unfold tripleCharges sourceA32 sourceB32 sourceC32 difference raw3512; decide +kernel
    rw [ha]
    exact (canonical3512 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA32 + difference 0 2) (sourceB32 + difference 2 0) sourceC32) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA32 + difference 0 2) (sourceB32 + difference 2 0) sourceC32) = raw3513 := by
      apply Matrix.ext; unfold tripleCharges sourceA32 sourceB32 sourceC32 difference raw3513; decide +kernel
    rw [ha]
    exact (canonical3513 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA32 + difference 0 3) (sourceB32 + difference 3 0) sourceC32) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA32 + difference 0 3) (sourceB32 + difference 3 0) sourceC32) = raw3514 := by
      apply Matrix.ext; unfold tripleCharges sourceA32 sourceB32 sourceC32 difference raw3514; decide +kernel
    rw [ha]
    exact (canonical3514 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA32 + difference 0 4) (sourceB32 + difference 4 0) sourceC32) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1092) := by
    have ha : (tripleCharges (sourceA32 + difference 0 4) (sourceB32 + difference 4 0) sourceC32) = raw3515 := by
      apply Matrix.ext; unfold tripleCharges sourceA32 sourceB32 sourceC32 difference raw3515; decide +kernel
    rw [ha]
    exact (canonical3515 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA32 + difference 0 5) (sourceB32 + difference 5 0) sourceC32) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA32 + difference 0 5) (sourceB32 + difference 5 0) sourceC32) = raw3516 := by
      apply Matrix.ext; unfold tripleCharges sourceA32 sourceB32 sourceC32 difference raw3516; decide +kernel
    rw [ha]
    exact (canonical3516 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA32 + sourceB32) sourceC32) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA32 + sourceB32) sourceC32) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA32 sourceB32 sourceC32 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA32 sourceB32 sourceC32
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm32, Integer.Sparse.eval]
  linarith only [hs]

def sourceA33 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB33 : Charge := ![0, 0, 0, 0, 3, -3]
def sourceC33 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm33 : Integer.Sparse Master := [(Sum.inr 1067, 3), (Sum.inr 1069, 1), (Sum.inr 1092, 1), (Sum.inr 2285, 1), (Sum.inr 4085, -1)]

theorem sourceEq33 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm33 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA33 + difference 0 0) (sourceB33 + difference 0 0) sourceC33) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2285) := by
    have ha : (tripleCharges (sourceA33 + difference 0 0) (sourceB33 + difference 0 0) sourceC33) = raw3511 := by
      apply Matrix.ext; unfold tripleCharges sourceA33 sourceB33 sourceC33 difference raw3511; decide +kernel
    rw [ha]
    exact (canonical3511 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA33 + difference 1 0) (sourceB33 + difference 0 1) sourceC33) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1067) := by
    have ha : (tripleCharges (sourceA33 + difference 1 0) (sourceB33 + difference 0 1) sourceC33) = raw3518 := by
      apply Matrix.ext; unfold tripleCharges sourceA33 sourceB33 sourceC33 difference raw3518; decide +kernel
    rw [ha]
    exact (canonical3518 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA33 + difference 2 0) (sourceB33 + difference 0 2) sourceC33) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1067) := by
    have ha : (tripleCharges (sourceA33 + difference 2 0) (sourceB33 + difference 0 2) sourceC33) = raw3519 := by
      apply Matrix.ext; unfold tripleCharges sourceA33 sourceB33 sourceC33 difference raw3519; decide +kernel
    rw [ha]
    exact (canonical3519 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA33 + difference 3 0) (sourceB33 + difference 0 3) sourceC33) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1067) := by
    have ha : (tripleCharges (sourceA33 + difference 3 0) (sourceB33 + difference 0 3) sourceC33) = raw3520 := by
      apply Matrix.ext; unfold tripleCharges sourceA33 sourceB33 sourceC33 difference raw3520; decide +kernel
    rw [ha]
    exact (canonical3520 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA33 + difference 4 0) (sourceB33 + difference 0 4) sourceC33) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1092) := by
    have ha : (tripleCharges (sourceA33 + difference 4 0) (sourceB33 + difference 0 4) sourceC33) = raw3521 := by
      apply Matrix.ext; unfold tripleCharges sourceA33 sourceB33 sourceC33 difference raw3521; decide +kernel
    rw [ha]
    exact (canonical3521 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA33 + difference 5 0) (sourceB33 + difference 0 5) sourceC33) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1069) := by
    have ha : (tripleCharges (sourceA33 + difference 5 0) (sourceB33 + difference 0 5) sourceC33) = raw3522 := by
      apply Matrix.ext; unfold tripleCharges sourceA33 sourceB33 sourceC33 difference raw3522; decide +kernel
    rw [ha]
    exact (canonical3522 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA33 + sourceB33) sourceC33) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA33 + sourceB33) sourceC33) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA33 sourceB33 sourceC33 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA33 sourceB33 sourceC33
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm33, Integer.Sparse.eval]
  linarith only [hs]

def sourceA34 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB34 : Charge := ![0, 0, 0, 0, 3, -3]
def sourceC34 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm34 : Integer.Sparse Master := [(Sum.inr 1067, 2), (Sum.inr 2041, 2), (Sum.inr 2284, 1), (Sum.inr 2285, 1), (Sum.inr 4085, -1)]

theorem sourceEq34 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm34 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA34 + difference 1 0) (sourceB34 + difference 0 1) sourceC34) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1067) := by
    have ha : (tripleCharges (sourceA34 + difference 1 0) (sourceB34 + difference 0 1) sourceC34) = raw3518 := by
      apply Matrix.ext; unfold tripleCharges sourceA34 sourceB34 sourceC34 difference raw3518; decide +kernel
    rw [ha]
    exact (canonical3518 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA34 + difference 1 1) (sourceB34 + difference 1 1) sourceC34) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2285) := by
    have ha : (tripleCharges (sourceA34 + difference 1 1) (sourceB34 + difference 1 1) sourceC34) = raw3511 := by
      apply Matrix.ext; unfold tripleCharges sourceA34 sourceB34 sourceC34 difference raw3511; decide +kernel
    rw [ha]
    exact (canonical3511 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA34 + difference 1 2) (sourceB34 + difference 2 1) sourceC34) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2041) := by
    have ha : (tripleCharges (sourceA34 + difference 1 2) (sourceB34 + difference 2 1) sourceC34) = raw3523 := by
      apply Matrix.ext; unfold tripleCharges sourceA34 sourceB34 sourceC34 difference raw3523; decide +kernel
    rw [ha]
    exact (canonical3523 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA34 + difference 1 3) (sourceB34 + difference 3 1) sourceC34) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2041) := by
    have ha : (tripleCharges (sourceA34 + difference 1 3) (sourceB34 + difference 3 1) sourceC34) = raw3524 := by
      apply Matrix.ext; unfold tripleCharges sourceA34 sourceB34 sourceC34 difference raw3524; decide +kernel
    rw [ha]
    exact (canonical3524 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA34 + difference 1 4) (sourceB34 + difference 4 1) sourceC34) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1067) := by
    have ha : (tripleCharges (sourceA34 + difference 1 4) (sourceB34 + difference 4 1) sourceC34) = raw3525 := by
      apply Matrix.ext; unfold tripleCharges sourceA34 sourceB34 sourceC34 difference raw3525; decide +kernel
    rw [ha]
    exact (canonical3525 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA34 + difference 1 5) (sourceB34 + difference 5 1) sourceC34) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA34 + difference 1 5) (sourceB34 + difference 5 1) sourceC34) = raw3526 := by
      apply Matrix.ext; unfold tripleCharges sourceA34 sourceB34 sourceC34 difference raw3526; decide +kernel
    rw [ha]
    exact (canonical3526 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA34 + sourceB34) sourceC34) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA34 + sourceB34) sourceC34) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA34 sourceB34 sourceC34 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA34 sourceB34 sourceC34
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm34, Integer.Sparse.eval]
  linarith only [hs]

def sourceA35 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB35 : Charge := ![0, 0, 0, 0, 3, -3]
def sourceC35 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm35 : Integer.Sparse Master := [(Sum.inr 1459, 1), (Sum.inr 2041, 2), (Sum.inr 2063, 2), (Sum.inr 2285, 1), (Sum.inr 4085, -1)]

theorem sourceEq35 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm35 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA35 + difference 0 1) (sourceB35 + difference 1 0) sourceC35) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA35 + difference 0 1) (sourceB35 + difference 1 0) sourceC35) = raw3512 := by
      apply Matrix.ext; unfold tripleCharges sourceA35 sourceB35 sourceC35 difference raw3512; decide +kernel
    rw [ha]
    exact (canonical3512 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA35 + difference 1 1) (sourceB35 + difference 1 1) sourceC35) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2285) := by
    have ha : (tripleCharges (sourceA35 + difference 1 1) (sourceB35 + difference 1 1) sourceC35) = raw3511 := by
      apply Matrix.ext; unfold tripleCharges sourceA35 sourceB35 sourceC35 difference raw3511; decide +kernel
    rw [ha]
    exact (canonical3511 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA35 + difference 2 1) (sourceB35 + difference 1 2) sourceC35) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2041) := by
    have ha : (tripleCharges (sourceA35 + difference 2 1) (sourceB35 + difference 1 2) sourceC35) = raw3527 := by
      apply Matrix.ext; unfold tripleCharges sourceA35 sourceB35 sourceC35 difference raw3527; decide +kernel
    rw [ha]
    exact (canonical3527 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA35 + difference 3 1) (sourceB35 + difference 1 3) sourceC35) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2041) := by
    have ha : (tripleCharges (sourceA35 + difference 3 1) (sourceB35 + difference 1 3) sourceC35) = raw3528 := by
      apply Matrix.ext; unfold tripleCharges sourceA35 sourceB35 sourceC35 difference raw3528; decide +kernel
    rw [ha]
    exact (canonical3528 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA35 + difference 4 1) (sourceB35 + difference 1 4) sourceC35) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA35 + difference 4 1) (sourceB35 + difference 1 4) sourceC35) = raw3529 := by
      apply Matrix.ext; unfold tripleCharges sourceA35 sourceB35 sourceC35 difference raw3529; decide +kernel
    rw [ha]
    exact (canonical3529 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA35 + difference 5 1) (sourceB35 + difference 1 5) sourceC35) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1459) := by
    have ha : (tripleCharges (sourceA35 + difference 5 1) (sourceB35 + difference 1 5) sourceC35) = raw3530 := by
      apply Matrix.ext; unfold tripleCharges sourceA35 sourceB35 sourceC35 difference raw3530; decide +kernel
    rw [ha]
    exact (canonical3530 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA35 + sourceB35) sourceC35) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA35 + sourceB35) sourceC35) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA35 sourceB35 sourceC35 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA35 sourceB35 sourceC35
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm35, Integer.Sparse.eval]
  linarith only [hs]

def sourceA36 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB36 : Charge := ![0, 0, 0, 0, 3, -3]
def sourceC36 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceForm36 : Integer.Sparse Master := [(Sum.inr 1069, 2), (Sum.inr 1459, 3), (Sum.inr 2285, 1), (Sum.inr 4085, -1)]

theorem sourceEq36 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm36 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA36 + difference 5 0) (sourceB36 + difference 0 5) sourceC36) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1069) := by
    have ha : (tripleCharges (sourceA36 + difference 5 0) (sourceB36 + difference 0 5) sourceC36) = raw3522 := by
      apply Matrix.ext; unfold tripleCharges sourceA36 sourceB36 sourceC36 difference raw3522; decide +kernel
    rw [ha]
    exact (canonical3522 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA36 + difference 5 1) (sourceB36 + difference 1 5) sourceC36) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1459) := by
    have ha : (tripleCharges (sourceA36 + difference 5 1) (sourceB36 + difference 1 5) sourceC36) = raw3530 := by
      apply Matrix.ext; unfold tripleCharges sourceA36 sourceB36 sourceC36 difference raw3530; decide +kernel
    rw [ha]
    exact (canonical3530 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA36 + difference 5 2) (sourceB36 + difference 2 5) sourceC36) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1459) := by
    have ha : (tripleCharges (sourceA36 + difference 5 2) (sourceB36 + difference 2 5) sourceC36) = raw3531 := by
      apply Matrix.ext; unfold tripleCharges sourceA36 sourceB36 sourceC36 difference raw3531; decide +kernel
    rw [ha]
    exact (canonical3531 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA36 + difference 5 3) (sourceB36 + difference 3 5) sourceC36) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1459) := by
    have ha : (tripleCharges (sourceA36 + difference 5 3) (sourceB36 + difference 3 5) sourceC36) = raw3532 := by
      apply Matrix.ext; unfold tripleCharges sourceA36 sourceB36 sourceC36 difference raw3532; decide +kernel
    rw [ha]
    exact (canonical3532 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA36 + difference 5 4) (sourceB36 + difference 4 5) sourceC36) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1069) := by
    have ha : (tripleCharges (sourceA36 + difference 5 4) (sourceB36 + difference 4 5) sourceC36) = raw3533 := by
      apply Matrix.ext; unfold tripleCharges sourceA36 sourceB36 sourceC36 difference raw3533; decide +kernel
    rw [ha]
    exact (canonical3533 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA36 + difference 5 5) (sourceB36 + difference 5 5) sourceC36) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2285) := by
    have ha : (tripleCharges (sourceA36 + difference 5 5) (sourceB36 + difference 5 5) sourceC36) = raw3511 := by
      apply Matrix.ext; unfold tripleCharges sourceA36 sourceB36 sourceC36 difference raw3511; decide +kernel
    rw [ha]
    exact (canonical3511 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA36 + sourceB36) sourceC36) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA36 + sourceB36) sourceC36) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA36 sourceB36 sourceC36 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA36 sourceB36 sourceC36
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm36, Integer.Sparse.eval]
  linarith only [hs]

def sourceA37 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB37 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC37 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceForm37 : Integer.Sparse Master := [(Sum.inr 4260, 2), (Sum.inr 4262, 1), (Sum.inr 4271, 1), (Sum.inr 4277, 1), (Sum.inr 4447, 2), (Sum.inr 4464, 1), (Sum.inr 4478, 1), (Sum.inr 4734, 2), (Sum.inr 4743, 2), (Sum.inr 4748, 2), (Sum.inr 4808, 2), (Sum.inr 4819, 2), (Sum.inr 4844, 1), (Sum.inr 4872, 1), (Sum.inr 4880, 2), (Sum.inr 4881, 1), (Sum.inr 4884, 1), (Sum.inr 4891, 2), (Sum.inr 4896, 1), (Sum.inr 4898, 1), (Sum.inr 5302, 1)]

theorem sourceEq37 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm37 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA37 + difference 0 1) (sourceB37 + difference 1 0) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA37 + difference 0 1) (sourceB37 + difference 1 0) sourceC37) = raw3534 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3534; decide +kernel
    rw [ha]
    exact (canonical3534 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA37 + difference 0 2) (sourceB37 + difference 2 0) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA37 + difference 0 2) (sourceB37 + difference 2 0) sourceC37) = raw3535 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3535; decide +kernel
    rw [ha]
    exact (canonical3535 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA37 + difference 0 3) (sourceB37 + difference 3 0) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4884) := by
    have ha : (tripleCharges (sourceA37 + difference 0 3) (sourceB37 + difference 3 0) sourceC37) = raw3536 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3536; decide +kernel
    rw [ha]
    exact (canonical3536 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA37 + difference 0 4) (sourceB37 + difference 4 0) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4881) := by
    have ha : (tripleCharges (sourceA37 + difference 0 4) (sourceB37 + difference 4 0) sourceC37) = raw3537 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3537; decide +kernel
    rw [ha]
    exact (canonical3537 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA37 + difference 0 5) (sourceB37 + difference 5 0) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA37 + difference 0 5) (sourceB37 + difference 5 0) sourceC37) = raw3538 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3538; decide +kernel
    rw [ha]
    exact (canonical3538 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA37 + difference 1 0) (sourceB37 + difference 0 1) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4447) := by
    have ha : (tripleCharges (sourceA37 + difference 1 0) (sourceB37 + difference 0 1) sourceC37) = raw3539 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3539; decide +kernel
    rw [ha]
    exact (canonical3539 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA37 + difference 1 2) (sourceB37 + difference 2 1) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4734) := by
    have ha : (tripleCharges (sourceA37 + difference 1 2) (sourceB37 + difference 2 1) sourceC37) = raw3540 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3540; decide +kernel
    rw [ha]
    exact (canonical3540 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA37 + difference 1 3) (sourceB37 + difference 3 1) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4748) := by
    have ha : (tripleCharges (sourceA37 + difference 1 3) (sourceB37 + difference 3 1) sourceC37) = raw3541 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3541; decide +kernel
    rw [ha]
    exact (canonical3541 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA37 + difference 1 4) (sourceB37 + difference 4 1) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4743) := by
    have ha : (tripleCharges (sourceA37 + difference 1 4) (sourceB37 + difference 4 1) sourceC37) = raw3542 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3542; decide +kernel
    rw [ha]
    exact (canonical3542 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA37 + difference 1 5) (sourceB37 + difference 5 1) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA37 + difference 1 5) (sourceB37 + difference 5 1) sourceC37) = raw3543 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3543; decide +kernel
    rw [ha]
    exact (canonical3543 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA37 + difference 2 0) (sourceB37 + difference 0 2) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4447) := by
    have ha : (tripleCharges (sourceA37 + difference 2 0) (sourceB37 + difference 0 2) sourceC37) = raw3544 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3544; decide +kernel
    rw [ha]
    exact (canonical3544 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA37 + difference 2 1) (sourceB37 + difference 1 2) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4734) := by
    have ha : (tripleCharges (sourceA37 + difference 2 1) (sourceB37 + difference 1 2) sourceC37) = raw3545 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3545; decide +kernel
    rw [ha]
    exact (canonical3545 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA37 + difference 2 3) (sourceB37 + difference 3 2) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4748) := by
    have ha : (tripleCharges (sourceA37 + difference 2 3) (sourceB37 + difference 3 2) sourceC37) = raw3546 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3546; decide +kernel
    rw [ha]
    exact (canonical3546 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA37 + difference 2 4) (sourceB37 + difference 4 2) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4743) := by
    have ha : (tripleCharges (sourceA37 + difference 2 4) (sourceB37 + difference 4 2) sourceC37) = raw3547 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3547; decide +kernel
    rw [ha]
    exact (canonical3547 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA37 + difference 2 5) (sourceB37 + difference 5 2) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA37 + difference 2 5) (sourceB37 + difference 5 2) sourceC37) = raw3548 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3548; decide +kernel
    rw [ha]
    exact (canonical3548 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA37 + difference 3 0) (sourceB37 + difference 0 3) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4478) := by
    have ha : (tripleCharges (sourceA37 + difference 3 0) (sourceB37 + difference 0 3) sourceC37) = raw3549 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3549; decide +kernel
    rw [ha]
    exact (canonical3549 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA37 + difference 3 1) (sourceB37 + difference 1 3) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4819) := by
    have ha : (tripleCharges (sourceA37 + difference 3 1) (sourceB37 + difference 1 3) sourceC37) = raw3550 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3550; decide +kernel
    rw [ha]
    exact (canonical3550 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA37 + difference 3 2) (sourceB37 + difference 2 3) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4819) := by
    have ha : (tripleCharges (sourceA37 + difference 3 2) (sourceB37 + difference 2 3) sourceC37) = raw3551 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3551; decide +kernel
    rw [ha]
    exact (canonical3551 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA37 + difference 3 4) (sourceB37 + difference 4 3) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA37 + difference 3 4) (sourceB37 + difference 4 3) sourceC37) = raw3552 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3552; decide +kernel
    rw [ha]
    exact (canonical3552 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA37 + difference 3 5) (sourceB37 + difference 5 3) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA37 + difference 3 5) (sourceB37 + difference 5 3) sourceC37) = raw3553 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3553; decide +kernel
    rw [ha]
    exact (canonical3553 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA37 + difference 4 0) (sourceB37 + difference 0 4) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4464) := by
    have ha : (tripleCharges (sourceA37 + difference 4 0) (sourceB37 + difference 0 4) sourceC37) = raw3554 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3554; decide +kernel
    rw [ha]
    exact (canonical3554 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA37 + difference 4 1) (sourceB37 + difference 1 4) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA37 + difference 4 1) (sourceB37 + difference 1 4) sourceC37) = raw3555 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3555; decide +kernel
    rw [ha]
    exact (canonical3555 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA37 + difference 4 2) (sourceB37 + difference 2 4) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA37 + difference 4 2) (sourceB37 + difference 2 4) sourceC37) = raw3556 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3556; decide +kernel
    rw [ha]
    exact (canonical3556 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA37 + difference 4 3) (sourceB37 + difference 3 4) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4872) := by
    have ha : (tripleCharges (sourceA37 + difference 4 3) (sourceB37 + difference 3 4) sourceC37) = raw3557 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3557; decide +kernel
    rw [ha]
    exact (canonical3557 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA37 + difference 4 5) (sourceB37 + difference 5 4) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA37 + difference 4 5) (sourceB37 + difference 5 4) sourceC37) = raw3558 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3558; decide +kernel
    rw [ha]
    exact (canonical3558 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA37 + difference 5 0) (sourceB37 + difference 0 5) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4262) := by
    have ha : (tripleCharges (sourceA37 + difference 5 0) (sourceB37 + difference 0 5) sourceC37) = raw3559 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3559; decide +kernel
    rw [ha]
    exact (canonical3559 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA37 + difference 5 1) (sourceB37 + difference 1 5) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4260) := by
    have ha : (tripleCharges (sourceA37 + difference 5 1) (sourceB37 + difference 1 5) sourceC37) = raw3560 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3560; decide +kernel
    rw [ha]
    exact (canonical3560 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA37 + difference 5 2) (sourceB37 + difference 2 5) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4260) := by
    have ha : (tripleCharges (sourceA37 + difference 5 2) (sourceB37 + difference 2 5) sourceC37) = raw3561 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3561; decide +kernel
    rw [ha]
    exact (canonical3561 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA37 + difference 5 3) (sourceB37 + difference 3 5) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4277) := by
    have ha : (tripleCharges (sourceA37 + difference 5 3) (sourceB37 + difference 3 5) sourceC37) = raw3562 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3562; decide +kernel
    rw [ha]
    exact (canonical3562 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA37 + difference 5 4) (sourceB37 + difference 4 5) sourceC37) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4271) := by
    have ha : (tripleCharges (sourceA37 + difference 5 4) (sourceB37 + difference 4 5) sourceC37) = raw3563 := by
      apply Matrix.ext; unfold tripleCharges sourceA37 sourceB37 sourceC37 difference raw3563; decide +kernel
    rw [ha]
    exact (canonical3563 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA37 sourceB37 sourceC37
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm37, Integer.Sparse.eval]
  linarith only [hs]

def sourceA38 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB38 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC38 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceForm38 : Integer.Sparse Master := [(Sum.inr 795, 2), (Sum.inr 797, 1), (Sum.inr 814, 1), (Sum.inr 829, 1), (Sum.inr 1355, 2), (Sum.inr 1369, 1), (Sum.inr 1408, 1), (Sum.inr 1903, 2), (Sum.inr 1916, 2), (Sum.inr 1927, 2), (Sum.inr 2037, 2), (Sum.inr 2063, 1), (Sum.inr 2092, 2), (Sum.inr 2113, 1), (Sum.inr 2254, 2), (Sum.inr 2267, 1), (Sum.inr 2280, 1), (Sum.inr 3054, 1), (Sum.inr 3222, 2), (Sum.inr 3224, 1), (Sum.inr 3225, 1)]

theorem sourceEq38 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm38 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA38 + difference 0 1) (sourceB38 + difference 1 0) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA38 + difference 0 1) (sourceB38 + difference 1 0) sourceC38) = raw3564 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3564; decide +kernel
    rw [ha]
    exact (canonical3564 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA38 + difference 0 2) (sourceB38 + difference 2 0) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA38 + difference 0 2) (sourceB38 + difference 2 0) sourceC38) = raw3565 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3565; decide +kernel
    rw [ha]
    exact (canonical3565 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA38 + difference 0 3) (sourceB38 + difference 3 0) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2280) := by
    have ha : (tripleCharges (sourceA38 + difference 0 3) (sourceB38 + difference 3 0) sourceC38) = raw3566 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3566; decide +kernel
    rw [ha]
    exact (canonical3566 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA38 + difference 0 4) (sourceB38 + difference 4 0) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA38 + difference 0 4) (sourceB38 + difference 4 0) sourceC38) = raw3567 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3567; decide +kernel
    rw [ha]
    exact (canonical3567 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA38 + difference 0 5) (sourceB38 + difference 5 0) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA38 + difference 0 5) (sourceB38 + difference 5 0) sourceC38) = raw3568 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3568; decide +kernel
    rw [ha]
    exact (canonical3568 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA38 + difference 1 0) (sourceB38 + difference 0 1) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1355) := by
    have ha : (tripleCharges (sourceA38 + difference 1 0) (sourceB38 + difference 0 1) sourceC38) = raw3569 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3569; decide +kernel
    rw [ha]
    exact (canonical3569 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA38 + difference 1 2) (sourceB38 + difference 2 1) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1903) := by
    have ha : (tripleCharges (sourceA38 + difference 1 2) (sourceB38 + difference 2 1) sourceC38) = raw3570 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3570; decide +kernel
    rw [ha]
    exact (canonical3570 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA38 + difference 1 3) (sourceB38 + difference 3 1) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1927) := by
    have ha : (tripleCharges (sourceA38 + difference 1 3) (sourceB38 + difference 3 1) sourceC38) = raw3571 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3571; decide +kernel
    rw [ha]
    exact (canonical3571 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA38 + difference 1 4) (sourceB38 + difference 4 1) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1916) := by
    have ha : (tripleCharges (sourceA38 + difference 1 4) (sourceB38 + difference 4 1) sourceC38) = raw3572 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3572; decide +kernel
    rw [ha]
    exact (canonical3572 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA38 + difference 1 5) (sourceB38 + difference 5 1) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA38 + difference 1 5) (sourceB38 + difference 5 1) sourceC38) = raw3573 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3573; decide +kernel
    rw [ha]
    exact (canonical3573 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA38 + difference 2 0) (sourceB38 + difference 0 2) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1355) := by
    have ha : (tripleCharges (sourceA38 + difference 2 0) (sourceB38 + difference 0 2) sourceC38) = raw3574 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3574; decide +kernel
    rw [ha]
    exact (canonical3574 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA38 + difference 2 1) (sourceB38 + difference 1 2) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1903) := by
    have ha : (tripleCharges (sourceA38 + difference 2 1) (sourceB38 + difference 1 2) sourceC38) = raw3575 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3575; decide +kernel
    rw [ha]
    exact (canonical3575 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA38 + difference 2 3) (sourceB38 + difference 3 2) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1927) := by
    have ha : (tripleCharges (sourceA38 + difference 2 3) (sourceB38 + difference 3 2) sourceC38) = raw3576 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3576; decide +kernel
    rw [ha]
    exact (canonical3576 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA38 + difference 2 4) (sourceB38 + difference 4 2) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1916) := by
    have ha : (tripleCharges (sourceA38 + difference 2 4) (sourceB38 + difference 4 2) sourceC38) = raw3577 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3577; decide +kernel
    rw [ha]
    exact (canonical3577 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA38 + difference 2 5) (sourceB38 + difference 5 2) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA38 + difference 2 5) (sourceB38 + difference 5 2) sourceC38) = raw3578 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3578; decide +kernel
    rw [ha]
    exact (canonical3578 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA38 + difference 3 0) (sourceB38 + difference 0 3) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1369) := by
    have ha : (tripleCharges (sourceA38 + difference 3 0) (sourceB38 + difference 0 3) sourceC38) = raw3579 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3579; decide +kernel
    rw [ha]
    exact (canonical3579 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA38 + difference 3 1) (sourceB38 + difference 1 3) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2037) := by
    have ha : (tripleCharges (sourceA38 + difference 3 1) (sourceB38 + difference 1 3) sourceC38) = raw3580 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3580; decide +kernel
    rw [ha]
    exact (canonical3580 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA38 + difference 3 2) (sourceB38 + difference 2 3) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2037) := by
    have ha : (tripleCharges (sourceA38 + difference 3 2) (sourceB38 + difference 2 3) sourceC38) = raw3581 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3581; decide +kernel
    rw [ha]
    exact (canonical3581 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA38 + difference 3 4) (sourceB38 + difference 4 3) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA38 + difference 3 4) (sourceB38 + difference 4 3) sourceC38) = raw3582 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3582; decide +kernel
    rw [ha]
    exact (canonical3582 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA38 + difference 3 5) (sourceB38 + difference 5 3) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3224) := by
    have ha : (tripleCharges (sourceA38 + difference 3 5) (sourceB38 + difference 5 3) sourceC38) = raw3583 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3583; decide +kernel
    rw [ha]
    exact (canonical3583 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA38 + difference 4 0) (sourceB38 + difference 0 4) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA38 + difference 4 0) (sourceB38 + difference 0 4) sourceC38) = raw3584 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3584; decide +kernel
    rw [ha]
    exact (canonical3584 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA38 + difference 4 1) (sourceB38 + difference 1 4) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA38 + difference 4 1) (sourceB38 + difference 1 4) sourceC38) = raw3585 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3585; decide +kernel
    rw [ha]
    exact (canonical3585 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA38 + difference 4 2) (sourceB38 + difference 2 4) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA38 + difference 4 2) (sourceB38 + difference 2 4) sourceC38) = raw3586 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3586; decide +kernel
    rw [ha]
    exact (canonical3586 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA38 + difference 4 3) (sourceB38 + difference 3 4) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2113) := by
    have ha : (tripleCharges (sourceA38 + difference 4 3) (sourceB38 + difference 3 4) sourceC38) = raw3587 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3587; decide +kernel
    rw [ha]
    exact (canonical3587 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA38 + difference 4 5) (sourceB38 + difference 5 4) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA38 + difference 4 5) (sourceB38 + difference 5 4) sourceC38) = raw3588 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3588; decide +kernel
    rw [ha]
    exact (canonical3588 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA38 + difference 5 0) (sourceB38 + difference 0 5) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 797) := by
    have ha : (tripleCharges (sourceA38 + difference 5 0) (sourceB38 + difference 0 5) sourceC38) = raw3589 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3589; decide +kernel
    rw [ha]
    exact (canonical3589 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA38 + difference 5 1) (sourceB38 + difference 1 5) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 795) := by
    have ha : (tripleCharges (sourceA38 + difference 5 1) (sourceB38 + difference 1 5) sourceC38) = raw3590 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3590; decide +kernel
    rw [ha]
    exact (canonical3590 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA38 + difference 5 2) (sourceB38 + difference 2 5) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 795) := by
    have ha : (tripleCharges (sourceA38 + difference 5 2) (sourceB38 + difference 2 5) sourceC38) = raw3591 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3591; decide +kernel
    rw [ha]
    exact (canonical3591 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA38 + difference 5 3) (sourceB38 + difference 3 5) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 829) := by
    have ha : (tripleCharges (sourceA38 + difference 5 3) (sourceB38 + difference 3 5) sourceC38) = raw3592 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3592; decide +kernel
    rw [ha]
    exact (canonical3592 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA38 + difference 5 4) (sourceB38 + difference 4 5) sourceC38) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 814) := by
    have ha : (tripleCharges (sourceA38 + difference 5 4) (sourceB38 + difference 4 5) sourceC38) = raw3593 := by
      apply Matrix.ext; unfold tripleCharges sourceA38 sourceB38 sourceC38 difference raw3593; decide +kernel
    rw [ha]
    exact (canonical3593 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA38 sourceB38 sourceC38
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm38, Integer.Sparse.eval]
  linarith only [hs]

def sourceA39 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB39 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC39 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceForm39 : Integer.Sparse Master := [(Sum.inr 835, 2), (Sum.inr 836, 1), (Sum.inr 838, 1), (Sum.inr 854, 1), (Sum.inr 1718, 2), (Sum.inr 1745, 1), (Sum.inr 1746, 1), (Sum.inr 1931, 2), (Sum.inr 1932, 2), (Sum.inr 1934, 2), (Sum.inr 2133, 2), (Sum.inr 2134, 1), (Sum.inr 2138, 1), (Sum.inr 2220, 2), (Sum.inr 2221, 2), (Sum.inr 2222, 1), (Sum.inr 2253, 2), (Sum.inr 2278, 1), (Sum.inr 2279, 1), (Sum.inr 2282, 1), (Sum.inr 2776, 1)]

theorem sourceEq39 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm39 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA39 + difference 0 1) (sourceB39 + difference 1 0) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA39 + difference 0 1) (sourceB39 + difference 1 0) sourceC39) = raw3594 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3594; decide +kernel
    rw [ha]
    exact (canonical3594 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA39 + difference 0 2) (sourceB39 + difference 2 0) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA39 + difference 0 2) (sourceB39 + difference 2 0) sourceC39) = raw3595 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3595; decide +kernel
    rw [ha]
    exact (canonical3595 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA39 + difference 0 3) (sourceB39 + difference 3 0) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2138) := by
    have ha : (tripleCharges (sourceA39 + difference 0 3) (sourceB39 + difference 3 0) sourceC39) = raw3596 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3596; decide +kernel
    rw [ha]
    exact (canonical3596 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA39 + difference 0 4) (sourceB39 + difference 4 0) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2134) := by
    have ha : (tripleCharges (sourceA39 + difference 0 4) (sourceB39 + difference 4 0) sourceC39) = raw3597 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3597; decide +kernel
    rw [ha]
    exact (canonical3597 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA39 + difference 0 5) (sourceB39 + difference 5 0) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA39 + difference 0 5) (sourceB39 + difference 5 0) sourceC39) = raw3598 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3598; decide +kernel
    rw [ha]
    exact (canonical3598 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA39 + difference 1 0) (sourceB39 + difference 0 1) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1718) := by
    have ha : (tripleCharges (sourceA39 + difference 1 0) (sourceB39 + difference 0 1) sourceC39) = raw3599 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3599; decide +kernel
    rw [ha]
    exact (canonical3599 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA39 + difference 1 2) (sourceB39 + difference 2 1) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1931) := by
    have ha : (tripleCharges (sourceA39 + difference 1 2) (sourceB39 + difference 2 1) sourceC39) = raw3600 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3600; decide +kernel
    rw [ha]
    exact (canonical3600 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA39 + difference 1 3) (sourceB39 + difference 3 1) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1934) := by
    have ha : (tripleCharges (sourceA39 + difference 1 3) (sourceB39 + difference 3 1) sourceC39) = raw3601 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3601; decide +kernel
    rw [ha]
    exact (canonical3601 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA39 + difference 1 4) (sourceB39 + difference 4 1) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1932) := by
    have ha : (tripleCharges (sourceA39 + difference 1 4) (sourceB39 + difference 4 1) sourceC39) = raw3602 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3602; decide +kernel
    rw [ha]
    exact (canonical3602 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA39 + difference 1 5) (sourceB39 + difference 5 1) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA39 + difference 1 5) (sourceB39 + difference 5 1) sourceC39) = raw3603 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3603; decide +kernel
    rw [ha]
    exact (canonical3603 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA39 + difference 2 0) (sourceB39 + difference 0 2) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1718) := by
    have ha : (tripleCharges (sourceA39 + difference 2 0) (sourceB39 + difference 0 2) sourceC39) = raw3604 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3604; decide +kernel
    rw [ha]
    exact (canonical3604 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA39 + difference 2 1) (sourceB39 + difference 1 2) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1931) := by
    have ha : (tripleCharges (sourceA39 + difference 2 1) (sourceB39 + difference 1 2) sourceC39) = raw3605 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3605; decide +kernel
    rw [ha]
    exact (canonical3605 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA39 + difference 2 3) (sourceB39 + difference 3 2) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1934) := by
    have ha : (tripleCharges (sourceA39 + difference 2 3) (sourceB39 + difference 3 2) sourceC39) = raw3606 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3606; decide +kernel
    rw [ha]
    exact (canonical3606 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA39 + difference 2 4) (sourceB39 + difference 4 2) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1932) := by
    have ha : (tripleCharges (sourceA39 + difference 2 4) (sourceB39 + difference 4 2) sourceC39) = raw3607 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3607; decide +kernel
    rw [ha]
    exact (canonical3607 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA39 + difference 2 5) (sourceB39 + difference 5 2) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA39 + difference 2 5) (sourceB39 + difference 5 2) sourceC39) = raw3608 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3608; decide +kernel
    rw [ha]
    exact (canonical3608 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA39 + difference 3 0) (sourceB39 + difference 0 3) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA39 + difference 3 0) (sourceB39 + difference 0 3) sourceC39) = raw3609 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3609; decide +kernel
    rw [ha]
    exact (canonical3609 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA39 + difference 3 1) (sourceB39 + difference 1 3) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2221) := by
    have ha : (tripleCharges (sourceA39 + difference 3 1) (sourceB39 + difference 1 3) sourceC39) = raw3610 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3610; decide +kernel
    rw [ha]
    exact (canonical3610 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA39 + difference 3 2) (sourceB39 + difference 2 3) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2221) := by
    have ha : (tripleCharges (sourceA39 + difference 3 2) (sourceB39 + difference 2 3) sourceC39) = raw3611 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3611; decide +kernel
    rw [ha]
    exact (canonical3611 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA39 + difference 3 4) (sourceB39 + difference 4 3) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2222) := by
    have ha : (tripleCharges (sourceA39 + difference 3 4) (sourceB39 + difference 4 3) sourceC39) = raw3612 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3612; decide +kernel
    rw [ha]
    exact (canonical3612 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA39 + difference 3 5) (sourceB39 + difference 5 3) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA39 + difference 3 5) (sourceB39 + difference 5 3) sourceC39) = raw3613 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3613; decide +kernel
    rw [ha]
    exact (canonical3613 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA39 + difference 4 0) (sourceB39 + difference 0 4) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA39 + difference 4 0) (sourceB39 + difference 0 4) sourceC39) = raw3614 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3614; decide +kernel
    rw [ha]
    exact (canonical3614 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA39 + difference 4 1) (sourceB39 + difference 1 4) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA39 + difference 4 1) (sourceB39 + difference 1 4) sourceC39) = raw3615 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3615; decide +kernel
    rw [ha]
    exact (canonical3615 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA39 + difference 4 2) (sourceB39 + difference 2 4) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA39 + difference 4 2) (sourceB39 + difference 2 4) sourceC39) = raw3616 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3616; decide +kernel
    rw [ha]
    exact (canonical3616 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA39 + difference 4 3) (sourceB39 + difference 3 4) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2282) := by
    have ha : (tripleCharges (sourceA39 + difference 4 3) (sourceB39 + difference 3 4) sourceC39) = raw3617 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3617; decide +kernel
    rw [ha]
    exact (canonical3617 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA39 + difference 4 5) (sourceB39 + difference 5 4) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA39 + difference 4 5) (sourceB39 + difference 5 4) sourceC39) = raw3618 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3618; decide +kernel
    rw [ha]
    exact (canonical3618 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA39 + difference 5 0) (sourceB39 + difference 0 5) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 854) := by
    have ha : (tripleCharges (sourceA39 + difference 5 0) (sourceB39 + difference 0 5) sourceC39) = raw3619 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3619; decide +kernel
    rw [ha]
    exact (canonical3619 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA39 + difference 5 1) (sourceB39 + difference 1 5) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 835) := by
    have ha : (tripleCharges (sourceA39 + difference 5 1) (sourceB39 + difference 1 5) sourceC39) = raw3620 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3620; decide +kernel
    rw [ha]
    exact (canonical3620 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA39 + difference 5 2) (sourceB39 + difference 2 5) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 835) := by
    have ha : (tripleCharges (sourceA39 + difference 5 2) (sourceB39 + difference 2 5) sourceC39) = raw3621 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3621; decide +kernel
    rw [ha]
    exact (canonical3621 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA39 + difference 5 3) (sourceB39 + difference 3 5) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 838) := by
    have ha : (tripleCharges (sourceA39 + difference 5 3) (sourceB39 + difference 3 5) sourceC39) = raw3622 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3622; decide +kernel
    rw [ha]
    exact (canonical3622 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA39 + difference 5 4) (sourceB39 + difference 4 5) sourceC39) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 836) := by
    have ha : (tripleCharges (sourceA39 + difference 5 4) (sourceB39 + difference 4 5) sourceC39) = raw3623 := by
      apply Matrix.ext; unfold tripleCharges sourceA39 sourceB39 sourceC39 difference raw3623; decide +kernel
    rw [ha]
    exact (canonical3623 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA39 sourceB39 sourceC39
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm39, Integer.Sparse.eval]
  linarith only [hs]

def sourceA40 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB40 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC40 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceForm40 : Integer.Sparse Master := [(Sum.inr 2255, 1), (Sum.inr 2520, 1), (Sum.inr 3156, 2), (Sum.inr 3161, 1), (Sum.inr 3626, 1), (Sum.inr 4084, -1)]

theorem sourceEq40 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm40 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA40 + difference 0 0) (sourceB40 + difference 0 0) sourceC40) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA40 + difference 0 0) (sourceB40 + difference 0 0) sourceC40) = raw3624 := by
      apply Matrix.ext; unfold tripleCharges sourceA40 sourceB40 sourceC40 difference raw3624; decide +kernel
    rw [ha]
    exact (canonical3624 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA40 + difference 0 1) (sourceB40 + difference 1 0) sourceC40) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3156) := by
    have ha : (tripleCharges (sourceA40 + difference 0 1) (sourceB40 + difference 1 0) sourceC40) = raw3625 := by
      apply Matrix.ext; unfold tripleCharges sourceA40 sourceB40 sourceC40 difference raw3625; decide +kernel
    rw [ha]
    exact (canonical3625 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA40 + difference 0 2) (sourceB40 + difference 2 0) sourceC40) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3156) := by
    have ha : (tripleCharges (sourceA40 + difference 0 2) (sourceB40 + difference 2 0) sourceC40) = raw3626 := by
      apply Matrix.ext; unfold tripleCharges sourceA40 sourceB40 sourceC40 difference raw3626; decide +kernel
    rw [ha]
    exact (canonical3626 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA40 + difference 0 3) (sourceB40 + difference 3 0) sourceC40) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3161) := by
    have ha : (tripleCharges (sourceA40 + difference 0 3) (sourceB40 + difference 3 0) sourceC40) = raw3627 := by
      apply Matrix.ext; unfold tripleCharges sourceA40 sourceB40 sourceC40 difference raw3627; decide +kernel
    rw [ha]
    exact (canonical3627 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA40 + difference 0 4) (sourceB40 + difference 4 0) sourceC40) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA40 + difference 0 4) (sourceB40 + difference 4 0) sourceC40) = raw3628 := by
      apply Matrix.ext; unfold tripleCharges sourceA40 sourceB40 sourceC40 difference raw3628; decide +kernel
    rw [ha]
    exact (canonical3628 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA40 + difference 0 5) (sourceB40 + difference 5 0) sourceC40) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA40 + difference 0 5) (sourceB40 + difference 5 0) sourceC40) = raw3629 := by
      apply Matrix.ext; unfold tripleCharges sourceA40 sourceB40 sourceC40 difference raw3629; decide +kernel
    rw [ha]
    exact (canonical3629 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA40 + sourceB40) sourceC40) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA40 + sourceB40) sourceC40) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA40 sourceB40 sourceC40 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA40 sourceB40 sourceC40
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm40, Integer.Sparse.eval]
  linarith only [hs]

def sourceA41 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB41 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC41 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceForm41 : Integer.Sparse Master := [(Sum.inr 1029, 2), (Sum.inr 1031, 1), (Sum.inr 1047, 1), (Sum.inr 1061, 1), (Sum.inr 2255, 1), (Sum.inr 4084, -1)]

theorem sourceEq41 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm41 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA41 + difference 0 0) (sourceB41 + difference 0 0) sourceC41) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA41 + difference 0 0) (sourceB41 + difference 0 0) sourceC41) = raw3624 := by
      apply Matrix.ext; unfold tripleCharges sourceA41 sourceB41 sourceC41 difference raw3624; decide +kernel
    rw [ha]
    exact (canonical3624 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA41 + difference 1 0) (sourceB41 + difference 0 1) sourceC41) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1029) := by
    have ha : (tripleCharges (sourceA41 + difference 1 0) (sourceB41 + difference 0 1) sourceC41) = raw3631 := by
      apply Matrix.ext; unfold tripleCharges sourceA41 sourceB41 sourceC41 difference raw3631; decide +kernel
    rw [ha]
    exact (canonical3631 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA41 + difference 2 0) (sourceB41 + difference 0 2) sourceC41) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1029) := by
    have ha : (tripleCharges (sourceA41 + difference 2 0) (sourceB41 + difference 0 2) sourceC41) = raw3632 := by
      apply Matrix.ext; unfold tripleCharges sourceA41 sourceB41 sourceC41 difference raw3632; decide +kernel
    rw [ha]
    exact (canonical3632 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA41 + difference 3 0) (sourceB41 + difference 0 3) sourceC41) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1061) := by
    have ha : (tripleCharges (sourceA41 + difference 3 0) (sourceB41 + difference 0 3) sourceC41) = raw3633 := by
      apply Matrix.ext; unfold tripleCharges sourceA41 sourceB41 sourceC41 difference raw3633; decide +kernel
    rw [ha]
    exact (canonical3633 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA41 + difference 4 0) (sourceB41 + difference 0 4) sourceC41) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA41 + difference 4 0) (sourceB41 + difference 0 4) sourceC41) = raw3634 := by
      apply Matrix.ext; unfold tripleCharges sourceA41 sourceB41 sourceC41 difference raw3634; decide +kernel
    rw [ha]
    exact (canonical3634 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA41 + difference 5 0) (sourceB41 + difference 0 5) sourceC41) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1031) := by
    have ha : (tripleCharges (sourceA41 + difference 5 0) (sourceB41 + difference 0 5) sourceC41) = raw3635 := by
      apply Matrix.ext; unfold tripleCharges sourceA41 sourceB41 sourceC41 difference raw3635; decide +kernel
    rw [ha]
    exact (canonical3635 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA41 + sourceB41) sourceC41) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA41 + sourceB41) sourceC41) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA41 sourceB41 sourceC41 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA41 sourceB41 sourceC41
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm41, Integer.Sparse.eval]
  linarith only [hs]

def sourceA42 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB42 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC42 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceForm42 : Integer.Sparse Master := [(Sum.inr 1029, 1), (Sum.inr 2013, 1), (Sum.inr 2096, 1), (Sum.inr 2125, 1), (Sum.inr 2253, 1), (Sum.inr 2255, 1), (Sum.inr 4084, -1)]

theorem sourceEq42 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm42 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA42 + difference 1 0) (sourceB42 + difference 0 1) sourceC42) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1029) := by
    have ha : (tripleCharges (sourceA42 + difference 1 0) (sourceB42 + difference 0 1) sourceC42) = raw3631 := by
      apply Matrix.ext; unfold tripleCharges sourceA42 sourceB42 sourceC42 difference raw3631; decide +kernel
    rw [ha]
    exact (canonical3631 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA42 + difference 1 1) (sourceB42 + difference 1 1) sourceC42) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA42 + difference 1 1) (sourceB42 + difference 1 1) sourceC42) = raw3624 := by
      apply Matrix.ext; unfold tripleCharges sourceA42 sourceB42 sourceC42 difference raw3624; decide +kernel
    rw [ha]
    exact (canonical3624 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA42 + difference 1 2) (sourceB42 + difference 2 1) sourceC42) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2013) := by
    have ha : (tripleCharges (sourceA42 + difference 1 2) (sourceB42 + difference 2 1) sourceC42) = raw3636 := by
      apply Matrix.ext; unfold tripleCharges sourceA42 sourceB42 sourceC42 difference raw3636; decide +kernel
    rw [ha]
    exact (canonical3636 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA42 + difference 1 3) (sourceB42 + difference 3 1) sourceC42) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2096) := by
    have ha : (tripleCharges (sourceA42 + difference 1 3) (sourceB42 + difference 3 1) sourceC42) = raw3637 := by
      apply Matrix.ext; unfold tripleCharges sourceA42 sourceB42 sourceC42 difference raw3637; decide +kernel
    rw [ha]
    exact (canonical3637 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA42 + difference 1 4) (sourceB42 + difference 4 1) sourceC42) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2125) := by
    have ha : (tripleCharges (sourceA42 + difference 1 4) (sourceB42 + difference 4 1) sourceC42) = raw3638 := by
      apply Matrix.ext; unfold tripleCharges sourceA42 sourceB42 sourceC42 difference raw3638; decide +kernel
    rw [ha]
    exact (canonical3638 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA42 + difference 1 5) (sourceB42 + difference 5 1) sourceC42) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA42 + difference 1 5) (sourceB42 + difference 5 1) sourceC42) = raw3639 := by
      apply Matrix.ext; unfold tripleCharges sourceA42 sourceB42 sourceC42 difference raw3639; decide +kernel
    rw [ha]
    exact (canonical3639 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA42 + sourceB42) sourceC42) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA42 + sourceB42) sourceC42) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA42 sourceB42 sourceC42 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA42 sourceB42 sourceC42
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm42, Integer.Sparse.eval]
  linarith only [hs]

def sourceA43 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB43 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC43 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceForm43 : Integer.Sparse Master := [(Sum.inr 1458, 1), (Sum.inr 2013, 1), (Sum.inr 2026, 1), (Sum.inr 2037, 1), (Sum.inr 2255, 1), (Sum.inr 3156, 1), (Sum.inr 4084, -1)]

theorem sourceEq43 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm43 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA43 + difference 0 1) (sourceB43 + difference 1 0) sourceC43) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3156) := by
    have ha : (tripleCharges (sourceA43 + difference 0 1) (sourceB43 + difference 1 0) sourceC43) = raw3625 := by
      apply Matrix.ext; unfold tripleCharges sourceA43 sourceB43 sourceC43 difference raw3625; decide +kernel
    rw [ha]
    exact (canonical3625 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA43 + difference 1 1) (sourceB43 + difference 1 1) sourceC43) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA43 + difference 1 1) (sourceB43 + difference 1 1) sourceC43) = raw3624 := by
      apply Matrix.ext; unfold tripleCharges sourceA43 sourceB43 sourceC43 difference raw3624; decide +kernel
    rw [ha]
    exact (canonical3624 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA43 + difference 2 1) (sourceB43 + difference 1 2) sourceC43) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2013) := by
    have ha : (tripleCharges (sourceA43 + difference 2 1) (sourceB43 + difference 1 2) sourceC43) = raw3640 := by
      apply Matrix.ext; unfold tripleCharges sourceA43 sourceB43 sourceC43 difference raw3640; decide +kernel
    rw [ha]
    exact (canonical3640 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA43 + difference 3 1) (sourceB43 + difference 1 3) sourceC43) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2037) := by
    have ha : (tripleCharges (sourceA43 + difference 3 1) (sourceB43 + difference 1 3) sourceC43) = raw3641 := by
      apply Matrix.ext; unfold tripleCharges sourceA43 sourceB43 sourceC43 difference raw3641; decide +kernel
    rw [ha]
    exact (canonical3641 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA43 + difference 4 1) (sourceB43 + difference 1 4) sourceC43) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA43 + difference 4 1) (sourceB43 + difference 1 4) sourceC43) = raw3642 := by
      apply Matrix.ext; unfold tripleCharges sourceA43 sourceB43 sourceC43 difference raw3642; decide +kernel
    rw [ha]
    exact (canonical3642 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA43 + difference 5 1) (sourceB43 + difference 1 5) sourceC43) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1458) := by
    have ha : (tripleCharges (sourceA43 + difference 5 1) (sourceB43 + difference 1 5) sourceC43) = raw3643 := by
      apply Matrix.ext; unfold tripleCharges sourceA43 sourceB43 sourceC43 difference raw3643; decide +kernel
    rw [ha]
    exact (canonical3643 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA43 + sourceB43) sourceC43) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA43 + sourceB43) sourceC43) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA43 sourceB43 sourceC43 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA43 sourceB43 sourceC43
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm43, Integer.Sparse.eval]
  linarith only [hs]

def sourceA44 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB44 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC44 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceForm44 : Integer.Sparse Master := [(Sum.inr 1061, 1), (Sum.inr 2037, 2), (Sum.inr 2136, 1), (Sum.inr 2255, 1), (Sum.inr 2279, 1), (Sum.inr 4084, -1)]

theorem sourceEq44 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm44 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA44 + difference 3 0) (sourceB44 + difference 0 3) sourceC44) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1061) := by
    have ha : (tripleCharges (sourceA44 + difference 3 0) (sourceB44 + difference 0 3) sourceC44) = raw3633 := by
      apply Matrix.ext; unfold tripleCharges sourceA44 sourceB44 sourceC44 difference raw3633; decide +kernel
    rw [ha]
    exact (canonical3633 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA44 + difference 3 1) (sourceB44 + difference 1 3) sourceC44) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2037) := by
    have ha : (tripleCharges (sourceA44 + difference 3 1) (sourceB44 + difference 1 3) sourceC44) = raw3641 := by
      apply Matrix.ext; unfold tripleCharges sourceA44 sourceB44 sourceC44 difference raw3641; decide +kernel
    rw [ha]
    exact (canonical3641 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA44 + difference 3 2) (sourceB44 + difference 2 3) sourceC44) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2037) := by
    have ha : (tripleCharges (sourceA44 + difference 3 2) (sourceB44 + difference 2 3) sourceC44) = raw3644 := by
      apply Matrix.ext; unfold tripleCharges sourceA44 sourceB44 sourceC44 difference raw3644; decide +kernel
    rw [ha]
    exact (canonical3644 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA44 + difference 3 3) (sourceB44 + difference 3 3) sourceC44) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA44 + difference 3 3) (sourceB44 + difference 3 3) sourceC44) = raw3624 := by
      apply Matrix.ext; unfold tripleCharges sourceA44 sourceB44 sourceC44 difference raw3624; decide +kernel
    rw [ha]
    exact (canonical3624 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA44 + difference 3 4) (sourceB44 + difference 4 3) sourceC44) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2136) := by
    have ha : (tripleCharges (sourceA44 + difference 3 4) (sourceB44 + difference 4 3) sourceC44) = raw3645 := by
      apply Matrix.ext; unfold tripleCharges sourceA44 sourceB44 sourceC44 difference raw3645; decide +kernel
    rw [ha]
    exact (canonical3645 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA44 + difference 3 5) (sourceB44 + difference 5 3) sourceC44) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA44 + difference 3 5) (sourceB44 + difference 5 3) sourceC44) = raw3646 := by
      apply Matrix.ext; unfold tripleCharges sourceA44 sourceB44 sourceC44 difference raw3646; decide +kernel
    rw [ha]
    exact (canonical3646 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA44 + sourceB44) sourceC44) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA44 + sourceB44) sourceC44) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA44 sourceB44 sourceC44 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA44 sourceB44 sourceC44
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm44, Integer.Sparse.eval]
  linarith only [hs]

def sourceA45 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB45 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC45 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceForm45 : Integer.Sparse Master := [(Sum.inr 1462, 1), (Sum.inr 2096, 2), (Sum.inr 2113, 1), (Sum.inr 2255, 1), (Sum.inr 3161, 1), (Sum.inr 4084, -1)]

theorem sourceEq45 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm45 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA45 + difference 0 3) (sourceB45 + difference 3 0) sourceC45) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3161) := by
    have ha : (tripleCharges (sourceA45 + difference 0 3) (sourceB45 + difference 3 0) sourceC45) = raw3627 := by
      apply Matrix.ext; unfold tripleCharges sourceA45 sourceB45 sourceC45 difference raw3627; decide +kernel
    rw [ha]
    exact (canonical3627 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA45 + difference 1 3) (sourceB45 + difference 3 1) sourceC45) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2096) := by
    have ha : (tripleCharges (sourceA45 + difference 1 3) (sourceB45 + difference 3 1) sourceC45) = raw3637 := by
      apply Matrix.ext; unfold tripleCharges sourceA45 sourceB45 sourceC45 difference raw3637; decide +kernel
    rw [ha]
    exact (canonical3637 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA45 + difference 2 3) (sourceB45 + difference 3 2) sourceC45) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2096) := by
    have ha : (tripleCharges (sourceA45 + difference 2 3) (sourceB45 + difference 3 2) sourceC45) = raw3647 := by
      apply Matrix.ext; unfold tripleCharges sourceA45 sourceB45 sourceC45 difference raw3647; decide +kernel
    rw [ha]
    exact (canonical3647 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA45 + difference 3 3) (sourceB45 + difference 3 3) sourceC45) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA45 + difference 3 3) (sourceB45 + difference 3 3) sourceC45) = raw3624 := by
      apply Matrix.ext; unfold tripleCharges sourceA45 sourceB45 sourceC45 difference raw3624; decide +kernel
    rw [ha]
    exact (canonical3624 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA45 + difference 4 3) (sourceB45 + difference 3 4) sourceC45) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2113) := by
    have ha : (tripleCharges (sourceA45 + difference 4 3) (sourceB45 + difference 3 4) sourceC45) = raw3648 := by
      apply Matrix.ext; unfold tripleCharges sourceA45 sourceB45 sourceC45 difference raw3648; decide +kernel
    rw [ha]
    exact (canonical3648 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA45 + difference 5 3) (sourceB45 + difference 3 5) sourceC45) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1462) := by
    have ha : (tripleCharges (sourceA45 + difference 5 3) (sourceB45 + difference 3 5) sourceC45) = raw3649 := by
      apply Matrix.ext; unfold tripleCharges sourceA45 sourceB45 sourceC45 difference raw3649; decide +kernel
    rw [ha]
    exact (canonical3649 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA45 + sourceB45) sourceC45) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA45 + sourceB45) sourceC45) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA45 sourceB45 sourceC45 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA45 sourceB45 sourceC45
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm45, Integer.Sparse.eval]
  linarith only [hs]

def sourceA46 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB46 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC46 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceForm46 : Integer.Sparse Master := [(Sum.inr 1047, 1), (Sum.inr 2026, 2), (Sum.inr 2113, 1), (Sum.inr 2255, 1), (Sum.inr 2266, 1), (Sum.inr 4084, -1)]

theorem sourceEq46 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm46 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA46 + difference 4 0) (sourceB46 + difference 0 4) sourceC46) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA46 + difference 4 0) (sourceB46 + difference 0 4) sourceC46) = raw3634 := by
      apply Matrix.ext; unfold tripleCharges sourceA46 sourceB46 sourceC46 difference raw3634; decide +kernel
    rw [ha]
    exact (canonical3634 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA46 + difference 4 1) (sourceB46 + difference 1 4) sourceC46) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA46 + difference 4 1) (sourceB46 + difference 1 4) sourceC46) = raw3642 := by
      apply Matrix.ext; unfold tripleCharges sourceA46 sourceB46 sourceC46 difference raw3642; decide +kernel
    rw [ha]
    exact (canonical3642 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA46 + difference 4 2) (sourceB46 + difference 2 4) sourceC46) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA46 + difference 4 2) (sourceB46 + difference 2 4) sourceC46) = raw3650 := by
      apply Matrix.ext; unfold tripleCharges sourceA46 sourceB46 sourceC46 difference raw3650; decide +kernel
    rw [ha]
    exact (canonical3650 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA46 + difference 4 3) (sourceB46 + difference 3 4) sourceC46) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2113) := by
    have ha : (tripleCharges (sourceA46 + difference 4 3) (sourceB46 + difference 3 4) sourceC46) = raw3648 := by
      apply Matrix.ext; unfold tripleCharges sourceA46 sourceB46 sourceC46 difference raw3648; decide +kernel
    rw [ha]
    exact (canonical3648 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA46 + difference 4 4) (sourceB46 + difference 4 4) sourceC46) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA46 + difference 4 4) (sourceB46 + difference 4 4) sourceC46) = raw3624 := by
      apply Matrix.ext; unfold tripleCharges sourceA46 sourceB46 sourceC46 difference raw3624; decide +kernel
    rw [ha]
    exact (canonical3624 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA46 + difference 4 5) (sourceB46 + difference 5 4) sourceC46) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA46 + difference 4 5) (sourceB46 + difference 5 4) sourceC46) = raw3651 := by
      apply Matrix.ext; unfold tripleCharges sourceA46 sourceB46 sourceC46 difference raw3651; decide +kernel
    rw [ha]
    exact (canonical3651 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA46 + sourceB46) sourceC46) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA46 + sourceB46) sourceC46) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA46 sourceB46 sourceC46 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA46 sourceB46 sourceC46
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm46, Integer.Sparse.eval]
  linarith only [hs]

def sourceA47 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB47 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC47 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceForm47 : Integer.Sparse Master := [(Sum.inr 1461, 1), (Sum.inr 2125, 2), (Sum.inr 2136, 1), (Sum.inr 2255, 1), (Sum.inr 2520, 1), (Sum.inr 4084, -1)]

theorem sourceEq47 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm47 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA47 + difference 0 4) (sourceB47 + difference 4 0) sourceC47) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2520) := by
    have ha : (tripleCharges (sourceA47 + difference 0 4) (sourceB47 + difference 4 0) sourceC47) = raw3628 := by
      apply Matrix.ext; unfold tripleCharges sourceA47 sourceB47 sourceC47 difference raw3628; decide +kernel
    rw [ha]
    exact (canonical3628 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA47 + difference 1 4) (sourceB47 + difference 4 1) sourceC47) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2125) := by
    have ha : (tripleCharges (sourceA47 + difference 1 4) (sourceB47 + difference 4 1) sourceC47) = raw3638 := by
      apply Matrix.ext; unfold tripleCharges sourceA47 sourceB47 sourceC47 difference raw3638; decide +kernel
    rw [ha]
    exact (canonical3638 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA47 + difference 2 4) (sourceB47 + difference 4 2) sourceC47) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2125) := by
    have ha : (tripleCharges (sourceA47 + difference 2 4) (sourceB47 + difference 4 2) sourceC47) = raw3652 := by
      apply Matrix.ext; unfold tripleCharges sourceA47 sourceB47 sourceC47 difference raw3652; decide +kernel
    rw [ha]
    exact (canonical3652 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA47 + difference 3 4) (sourceB47 + difference 4 3) sourceC47) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2136) := by
    have ha : (tripleCharges (sourceA47 + difference 3 4) (sourceB47 + difference 4 3) sourceC47) = raw3645 := by
      apply Matrix.ext; unfold tripleCharges sourceA47 sourceB47 sourceC47 difference raw3645; decide +kernel
    rw [ha]
    exact (canonical3645 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA47 + difference 4 4) (sourceB47 + difference 4 4) sourceC47) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA47 + difference 4 4) (sourceB47 + difference 4 4) sourceC47) = raw3624 := by
      apply Matrix.ext; unfold tripleCharges sourceA47 sourceB47 sourceC47 difference raw3624; decide +kernel
    rw [ha]
    exact (canonical3624 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA47 + difference 5 4) (sourceB47 + difference 4 5) sourceC47) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1461) := by
    have ha : (tripleCharges (sourceA47 + difference 5 4) (sourceB47 + difference 4 5) sourceC47) = raw3653 := by
      apply Matrix.ext; unfold tripleCharges sourceA47 sourceB47 sourceC47 difference raw3653; decide +kernel
    rw [ha]
    exact (canonical3653 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA47 + sourceB47) sourceC47) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA47 + sourceB47) sourceC47) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA47 sourceB47 sourceC47 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA47 sourceB47 sourceC47
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm47, Integer.Sparse.eval]
  linarith only [hs]

def sourceA48 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB48 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceC48 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceForm48 : Integer.Sparse Master := [(Sum.inr 1031, 1), (Sum.inr 1458, 2), (Sum.inr 1461, 1), (Sum.inr 1462, 1), (Sum.inr 2255, 1), (Sum.inr 4084, -1)]

theorem sourceEq48 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm48 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA48 + difference 5 0) (sourceB48 + difference 0 5) sourceC48) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1031) := by
    have ha : (tripleCharges (sourceA48 + difference 5 0) (sourceB48 + difference 0 5) sourceC48) = raw3635 := by
      apply Matrix.ext; unfold tripleCharges sourceA48 sourceB48 sourceC48 difference raw3635; decide +kernel
    rw [ha]
    exact (canonical3635 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA48 + difference 5 1) (sourceB48 + difference 1 5) sourceC48) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1458) := by
    have ha : (tripleCharges (sourceA48 + difference 5 1) (sourceB48 + difference 1 5) sourceC48) = raw3643 := by
      apply Matrix.ext; unfold tripleCharges sourceA48 sourceB48 sourceC48 difference raw3643; decide +kernel
    rw [ha]
    exact (canonical3643 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA48 + difference 5 2) (sourceB48 + difference 2 5) sourceC48) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1458) := by
    have ha : (tripleCharges (sourceA48 + difference 5 2) (sourceB48 + difference 2 5) sourceC48) = raw3654 := by
      apply Matrix.ext; unfold tripleCharges sourceA48 sourceB48 sourceC48 difference raw3654; decide +kernel
    rw [ha]
    exact (canonical3654 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA48 + difference 5 3) (sourceB48 + difference 3 5) sourceC48) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1462) := by
    have ha : (tripleCharges (sourceA48 + difference 5 3) (sourceB48 + difference 3 5) sourceC48) = raw3649 := by
      apply Matrix.ext; unfold tripleCharges sourceA48 sourceB48 sourceC48 difference raw3649; decide +kernel
    rw [ha]
    exact (canonical3649 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA48 + difference 5 4) (sourceB48 + difference 4 5) sourceC48) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1461) := by
    have ha : (tripleCharges (sourceA48 + difference 5 4) (sourceB48 + difference 4 5) sourceC48) = raw3653 := by
      apply Matrix.ext; unfold tripleCharges sourceA48 sourceB48 sourceC48 difference raw3653; decide +kernel
    rw [ha]
    exact (canonical3653 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA48 + difference 5 5) (sourceB48 + difference 5 5) sourceC48) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA48 + difference 5 5) (sourceB48 + difference 5 5) sourceC48) = raw3624 := by
      apply Matrix.ext; unfold tripleCharges sourceA48 sourceB48 sourceC48 difference raw3624; decide +kernel
    rw [ha]
    exact (canonical3624 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA48 + sourceB48) sourceC48) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA48 + sourceB48) sourceC48) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA48 sourceB48 sourceC48 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA48 sourceB48 sourceC48
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm48, Integer.Sparse.eval]
  linarith only [hs]

def sourceA49 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceB49 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC49 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm49 : Integer.Sparse Master := [(Sum.inr 4483, 4), (Sum.inr 4484, 2), (Sum.inr 4485, 2), (Sum.inr 4500, 2), (Sum.inr 4751, 2), (Sum.inr 4822, 2), (Sum.inr 4823, 2), (Sum.inr 4836, 4), (Sum.inr 4886, 2), (Sum.inr 4890, 2), (Sum.inr 4892, 3), (Sum.inr 4899, 2), (Sum.inr 4900, 1)]

theorem sourceEq49 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm49 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA49 + difference 0 1) (sourceB49 + difference 1 0) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA49 + difference 0 1) (sourceB49 + difference 1 0) sourceC49) = raw3655 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3655; decide +kernel
    rw [ha]
    exact (canonical3655 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA49 + difference 0 2) (sourceB49 + difference 2 0) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA49 + difference 0 2) (sourceB49 + difference 2 0) sourceC49) = raw3656 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3656; decide +kernel
    rw [ha]
    exact (canonical3656 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA49 + difference 0 3) (sourceB49 + difference 3 0) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA49 + difference 0 3) (sourceB49 + difference 3 0) sourceC49) = raw3657 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3657; decide +kernel
    rw [ha]
    exact (canonical3657 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA49 + difference 0 4) (sourceB49 + difference 4 0) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA49 + difference 0 4) (sourceB49 + difference 4 0) sourceC49) = raw3658 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3658; decide +kernel
    rw [ha]
    exact (canonical3658 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA49 + difference 0 5) (sourceB49 + difference 5 0) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA49 + difference 0 5) (sourceB49 + difference 5 0) sourceC49) = raw3659 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3659; decide +kernel
    rw [ha]
    exact (canonical3659 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA49 + difference 1 0) (sourceB49 + difference 0 1) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4483) := by
    have ha : (tripleCharges (sourceA49 + difference 1 0) (sourceB49 + difference 0 1) sourceC49) = raw3660 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3660; decide +kernel
    rw [ha]
    exact (canonical3660 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA49 + difference 1 2) (sourceB49 + difference 2 1) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4822) := by
    have ha : (tripleCharges (sourceA49 + difference 1 2) (sourceB49 + difference 2 1) sourceC49) = raw3661 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3661; decide +kernel
    rw [ha]
    exact (canonical3661 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA49 + difference 1 3) (sourceB49 + difference 3 1) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA49 + difference 1 3) (sourceB49 + difference 3 1) sourceC49) = raw3662 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3662; decide +kernel
    rw [ha]
    exact (canonical3662 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA49 + difference 1 4) (sourceB49 + difference 4 1) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4886) := by
    have ha : (tripleCharges (sourceA49 + difference 1 4) (sourceB49 + difference 4 1) sourceC49) = raw3663 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3663; decide +kernel
    rw [ha]
    exact (canonical3663 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA49 + difference 1 5) (sourceB49 + difference 5 1) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4483) := by
    have ha : (tripleCharges (sourceA49 + difference 1 5) (sourceB49 + difference 5 1) sourceC49) = raw3664 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3664; decide +kernel
    rw [ha]
    exact (canonical3664 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA49 + difference 2 0) (sourceB49 + difference 0 2) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4483) := by
    have ha : (tripleCharges (sourceA49 + difference 2 0) (sourceB49 + difference 0 2) sourceC49) = raw3665 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3665; decide +kernel
    rw [ha]
    exact (canonical3665 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA49 + difference 2 1) (sourceB49 + difference 1 2) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4822) := by
    have ha : (tripleCharges (sourceA49 + difference 2 1) (sourceB49 + difference 1 2) sourceC49) = raw3666 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3666; decide +kernel
    rw [ha]
    exact (canonical3666 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA49 + difference 2 3) (sourceB49 + difference 3 2) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA49 + difference 2 3) (sourceB49 + difference 3 2) sourceC49) = raw3667 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3667; decide +kernel
    rw [ha]
    exact (canonical3667 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA49 + difference 2 4) (sourceB49 + difference 4 2) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4886) := by
    have ha : (tripleCharges (sourceA49 + difference 2 4) (sourceB49 + difference 4 2) sourceC49) = raw3668 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3668; decide +kernel
    rw [ha]
    exact (canonical3668 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA49 + difference 2 5) (sourceB49 + difference 5 2) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4483) := by
    have ha : (tripleCharges (sourceA49 + difference 2 5) (sourceB49 + difference 5 2) sourceC49) = raw3669 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3669; decide +kernel
    rw [ha]
    exact (canonical3669 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA49 + difference 3 0) (sourceB49 + difference 0 3) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4485) := by
    have ha : (tripleCharges (sourceA49 + difference 3 0) (sourceB49 + difference 0 3) sourceC49) = raw3670 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3670; decide +kernel
    rw [ha]
    exact (canonical3670 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA49 + difference 3 1) (sourceB49 + difference 1 3) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4823) := by
    have ha : (tripleCharges (sourceA49 + difference 3 1) (sourceB49 + difference 1 3) sourceC49) = raw3671 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3671; decide +kernel
    rw [ha]
    exact (canonical3671 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA49 + difference 3 2) (sourceB49 + difference 2 3) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4823) := by
    have ha : (tripleCharges (sourceA49 + difference 3 2) (sourceB49 + difference 2 3) sourceC49) = raw3672 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3672; decide +kernel
    rw [ha]
    exact (canonical3672 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA49 + difference 3 4) (sourceB49 + difference 4 3) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4892) := by
    have ha : (tripleCharges (sourceA49 + difference 3 4) (sourceB49 + difference 4 3) sourceC49) = raw3673 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3673; decide +kernel
    rw [ha]
    exact (canonical3673 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA49 + difference 3 5) (sourceB49 + difference 5 3) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4485) := by
    have ha : (tripleCharges (sourceA49 + difference 3 5) (sourceB49 + difference 5 3) sourceC49) = raw3674 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3674; decide +kernel
    rw [ha]
    exact (canonical3674 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA49 + difference 4 0) (sourceB49 + difference 0 4) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4484) := by
    have ha : (tripleCharges (sourceA49 + difference 4 0) (sourceB49 + difference 0 4) sourceC49) = raw3675 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3675; decide +kernel
    rw [ha]
    exact (canonical3675 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA49 + difference 4 1) (sourceB49 + difference 1 4) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4751) := by
    have ha : (tripleCharges (sourceA49 + difference 4 1) (sourceB49 + difference 1 4) sourceC49) = raw3676 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3676; decide +kernel
    rw [ha]
    exact (canonical3676 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA49 + difference 4 2) (sourceB49 + difference 2 4) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4751) := by
    have ha : (tripleCharges (sourceA49 + difference 4 2) (sourceB49 + difference 2 4) sourceC49) = raw3677 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3677; decide +kernel
    rw [ha]
    exact (canonical3677 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA49 + difference 4 3) (sourceB49 + difference 3 4) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4900) := by
    have ha : (tripleCharges (sourceA49 + difference 4 3) (sourceB49 + difference 3 4) sourceC49) = raw3678 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3678; decide +kernel
    rw [ha]
    exact (canonical3678 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA49 + difference 4 5) (sourceB49 + difference 5 4) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4484) := by
    have ha : (tripleCharges (sourceA49 + difference 4 5) (sourceB49 + difference 5 4) sourceC49) = raw3679 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3679; decide +kernel
    rw [ha]
    exact (canonical3679 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA49 + difference 5 0) (sourceB49 + difference 0 5) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4500) := by
    have ha : (tripleCharges (sourceA49 + difference 5 0) (sourceB49 + difference 0 5) sourceC49) = raw3680 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3680; decide +kernel
    rw [ha]
    exact (canonical3680 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA49 + difference 5 1) (sourceB49 + difference 1 5) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA49 + difference 5 1) (sourceB49 + difference 1 5) sourceC49) = raw3681 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3681; decide +kernel
    rw [ha]
    exact (canonical3681 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA49 + difference 5 2) (sourceB49 + difference 2 5) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA49 + difference 5 2) (sourceB49 + difference 2 5) sourceC49) = raw3682 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3682; decide +kernel
    rw [ha]
    exact (canonical3682 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA49 + difference 5 3) (sourceB49 + difference 3 5) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4899) := by
    have ha : (tripleCharges (sourceA49 + difference 5 3) (sourceB49 + difference 3 5) sourceC49) = raw3683 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3683; decide +kernel
    rw [ha]
    exact (canonical3683 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA49 + difference 5 4) (sourceB49 + difference 4 5) sourceC49) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4890) := by
    have ha : (tripleCharges (sourceA49 + difference 5 4) (sourceB49 + difference 4 5) sourceC49) = raw3684 := by
      apply Matrix.ext; unfold tripleCharges sourceA49 sourceB49 sourceC49 difference raw3684; decide +kernel
    rw [ha]
    exact (canonical3684 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA49 sourceB49 sourceC49
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm49, Integer.Sparse.eval]
  linarith only [hs]

def sourceA50 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceB50 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC50 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm50 : Integer.Sparse Master := [(Sum.inr 1351, 2), (Sum.inr 1352, 1), (Sum.inr 1353, 1), (Sum.inr 1436, 1), (Sum.inr 1702, 2), (Sum.inr 1716, 1), (Sum.inr 1719, 1), (Sum.inr 1733, 1), (Sum.inr 1933, 2), (Sum.inr 2188, 2), (Sum.inr 2197, 2), (Sum.inr 2210, 2), (Sum.inr 2235, 2), (Sum.inr 2247, 1), (Sum.inr 2255, 3), (Sum.inr 2281, 1), (Sum.inr 2285, 1), (Sum.inr 2716, 2), (Sum.inr 2755, 1), (Sum.inr 2778, 1)]

theorem sourceEq50 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm50 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA50 + difference 0 1) (sourceB50 + difference 1 0) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA50 + difference 0 1) (sourceB50 + difference 1 0) sourceC50) = raw3685 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3685; decide +kernel
    rw [ha]
    exact (canonical3685 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA50 + difference 0 2) (sourceB50 + difference 2 0) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA50 + difference 0 2) (sourceB50 + difference 2 0) sourceC50) = raw3686 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3686; decide +kernel
    rw [ha]
    exact (canonical3686 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA50 + difference 0 3) (sourceB50 + difference 3 0) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2778) := by
    have ha : (tripleCharges (sourceA50 + difference 0 3) (sourceB50 + difference 3 0) sourceC50) = raw3687 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3687; decide +kernel
    rw [ha]
    exact (canonical3687 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA50 + difference 0 4) (sourceB50 + difference 4 0) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2755) := by
    have ha : (tripleCharges (sourceA50 + difference 0 4) (sourceB50 + difference 4 0) sourceC50) = raw3688 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3688; decide +kernel
    rw [ha]
    exact (canonical3688 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA50 + difference 0 5) (sourceB50 + difference 5 0) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1436) := by
    have ha : (tripleCharges (sourceA50 + difference 0 5) (sourceB50 + difference 5 0) sourceC50) = raw3689 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3689; decide +kernel
    rw [ha]
    exact (canonical3689 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA50 + difference 1 0) (sourceB50 + difference 0 1) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1702) := by
    have ha : (tripleCharges (sourceA50 + difference 1 0) (sourceB50 + difference 0 1) sourceC50) = raw3690 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3690; decide +kernel
    rw [ha]
    exact (canonical3690 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA50 + difference 1 2) (sourceB50 + difference 2 1) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2188) := by
    have ha : (tripleCharges (sourceA50 + difference 1 2) (sourceB50 + difference 2 1) sourceC50) = raw3691 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3691; decide +kernel
    rw [ha]
    exact (canonical3691 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA50 + difference 1 3) (sourceB50 + difference 3 1) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA50 + difference 1 3) (sourceB50 + difference 3 1) sourceC50) = raw3692 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3692; decide +kernel
    rw [ha]
    exact (canonical3692 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA50 + difference 1 4) (sourceB50 + difference 4 1) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA50 + difference 1 4) (sourceB50 + difference 4 1) sourceC50) = raw3693 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3693; decide +kernel
    rw [ha]
    exact (canonical3693 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA50 + difference 1 5) (sourceB50 + difference 5 1) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1351) := by
    have ha : (tripleCharges (sourceA50 + difference 1 5) (sourceB50 + difference 5 1) sourceC50) = raw3694 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3694; decide +kernel
    rw [ha]
    exact (canonical3694 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA50 + difference 2 0) (sourceB50 + difference 0 2) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1702) := by
    have ha : (tripleCharges (sourceA50 + difference 2 0) (sourceB50 + difference 0 2) sourceC50) = raw3695 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3695; decide +kernel
    rw [ha]
    exact (canonical3695 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA50 + difference 2 1) (sourceB50 + difference 1 2) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2188) := by
    have ha : (tripleCharges (sourceA50 + difference 2 1) (sourceB50 + difference 1 2) sourceC50) = raw3696 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3696; decide +kernel
    rw [ha]
    exact (canonical3696 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA50 + difference 2 3) (sourceB50 + difference 3 2) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA50 + difference 2 3) (sourceB50 + difference 3 2) sourceC50) = raw3697 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3697; decide +kernel
    rw [ha]
    exact (canonical3697 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA50 + difference 2 4) (sourceB50 + difference 4 2) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA50 + difference 2 4) (sourceB50 + difference 4 2) sourceC50) = raw3698 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3698; decide +kernel
    rw [ha]
    exact (canonical3698 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA50 + difference 2 5) (sourceB50 + difference 5 2) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1351) := by
    have ha : (tripleCharges (sourceA50 + difference 2 5) (sourceB50 + difference 5 2) sourceC50) = raw3699 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3699; decide +kernel
    rw [ha]
    exact (canonical3699 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA50 + difference 3 0) (sourceB50 + difference 0 3) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1733) := by
    have ha : (tripleCharges (sourceA50 + difference 3 0) (sourceB50 + difference 0 3) sourceC50) = raw3700 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3700; decide +kernel
    rw [ha]
    exact (canonical3700 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA50 + difference 3 1) (sourceB50 + difference 1 3) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2210) := by
    have ha : (tripleCharges (sourceA50 + difference 3 1) (sourceB50 + difference 1 3) sourceC50) = raw3701 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3701; decide +kernel
    rw [ha]
    exact (canonical3701 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA50 + difference 3 2) (sourceB50 + difference 2 3) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2210) := by
    have ha : (tripleCharges (sourceA50 + difference 3 2) (sourceB50 + difference 2 3) sourceC50) = raw3702 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3702; decide +kernel
    rw [ha]
    exact (canonical3702 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA50 + difference 3 4) (sourceB50 + difference 4 3) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2255) := by
    have ha : (tripleCharges (sourceA50 + difference 3 4) (sourceB50 + difference 4 3) sourceC50) = raw3703 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3703; decide +kernel
    rw [ha]
    exact (canonical3703 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA50 + difference 3 5) (sourceB50 + difference 5 3) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1353) := by
    have ha : (tripleCharges (sourceA50 + difference 3 5) (sourceB50 + difference 5 3) sourceC50) = raw3704 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3704; decide +kernel
    rw [ha]
    exact (canonical3704 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA50 + difference 4 0) (sourceB50 + difference 0 4) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1719) := by
    have ha : (tripleCharges (sourceA50 + difference 4 0) (sourceB50 + difference 0 4) sourceC50) = raw3705 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3705; decide +kernel
    rw [ha]
    exact (canonical3705 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA50 + difference 4 1) (sourceB50 + difference 1 4) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1933) := by
    have ha : (tripleCharges (sourceA50 + difference 4 1) (sourceB50 + difference 1 4) sourceC50) = raw3706 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3706; decide +kernel
    rw [ha]
    exact (canonical3706 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA50 + difference 4 2) (sourceB50 + difference 2 4) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1933) := by
    have ha : (tripleCharges (sourceA50 + difference 4 2) (sourceB50 + difference 2 4) sourceC50) = raw3707 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3707; decide +kernel
    rw [ha]
    exact (canonical3707 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA50 + difference 4 3) (sourceB50 + difference 3 4) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2285) := by
    have ha : (tripleCharges (sourceA50 + difference 4 3) (sourceB50 + difference 3 4) sourceC50) = raw3708 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3708; decide +kernel
    rw [ha]
    exact (canonical3708 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA50 + difference 4 5) (sourceB50 + difference 5 4) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1352) := by
    have ha : (tripleCharges (sourceA50 + difference 4 5) (sourceB50 + difference 5 4) sourceC50) = raw3709 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3709; decide +kernel
    rw [ha]
    exact (canonical3709 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA50 + difference 5 0) (sourceB50 + difference 0 5) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1716) := by
    have ha : (tripleCharges (sourceA50 + difference 5 0) (sourceB50 + difference 0 5) sourceC50) = raw3710 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3710; decide +kernel
    rw [ha]
    exact (canonical3710 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA50 + difference 5 1) (sourceB50 + difference 1 5) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA50 + difference 5 1) (sourceB50 + difference 1 5) sourceC50) = raw3711 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3711; decide +kernel
    rw [ha]
    exact (canonical3711 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA50 + difference 5 2) (sourceB50 + difference 2 5) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA50 + difference 5 2) (sourceB50 + difference 2 5) sourceC50) = raw3712 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3712; decide +kernel
    rw [ha]
    exact (canonical3712 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA50 + difference 5 3) (sourceB50 + difference 3 5) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2281) := by
    have ha : (tripleCharges (sourceA50 + difference 5 3) (sourceB50 + difference 3 5) sourceC50) = raw3713 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3713; decide +kernel
    rw [ha]
    exact (canonical3713 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA50 + difference 5 4) (sourceB50 + difference 4 5) sourceC50) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2247) := by
    have ha : (tripleCharges (sourceA50 + difference 5 4) (sourceB50 + difference 4 5) sourceC50) = raw3714 := by
      apply Matrix.ext; unfold tripleCharges sourceA50 sourceB50 sourceC50 difference raw3714; decide +kernel
    rw [ha]
    exact (canonical3714 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA50 sourceB50 sourceC50
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm50, Integer.Sparse.eval]
  linarith only [hs]

def sourceA51 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceB51 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC51 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm51 : Integer.Sparse Master := [(Sum.inr 1084, 1), (Sum.inr 2055, 2), (Sum.inr 2284, 1), (Sum.inr 2290, 1), (Sum.inr 2294, 1), (Sum.inr 4085, -1)]

theorem sourceEq51 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm51 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA51 + difference 0 0) (sourceB51 + difference 0 0) sourceC51) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA51 + difference 0 0) (sourceB51 + difference 0 0) sourceC51) = raw3715 := by
      apply Matrix.ext; unfold tripleCharges sourceA51 sourceB51 sourceC51 difference raw3715; decide +kernel
    rw [ha]
    exact (canonical3715 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA51 + difference 0 1) (sourceB51 + difference 1 0) sourceC51) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA51 + difference 0 1) (sourceB51 + difference 1 0) sourceC51) = raw3716 := by
      apply Matrix.ext; unfold tripleCharges sourceA51 sourceB51 sourceC51 difference raw3716; decide +kernel
    rw [ha]
    exact (canonical3716 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA51 + difference 0 2) (sourceB51 + difference 2 0) sourceC51) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA51 + difference 0 2) (sourceB51 + difference 2 0) sourceC51) = raw3717 := by
      apply Matrix.ext; unfold tripleCharges sourceA51 sourceB51 sourceC51 difference raw3717; decide +kernel
    rw [ha]
    exact (canonical3717 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA51 + difference 0 3) (sourceB51 + difference 3 0) sourceC51) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA51 + difference 0 3) (sourceB51 + difference 3 0) sourceC51) = raw3718 := by
      apply Matrix.ext; unfold tripleCharges sourceA51 sourceB51 sourceC51 difference raw3718; decide +kernel
    rw [ha]
    exact (canonical3718 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA51 + difference 0 4) (sourceB51 + difference 4 0) sourceC51) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2290) := by
    have ha : (tripleCharges (sourceA51 + difference 0 4) (sourceB51 + difference 4 0) sourceC51) = raw3719 := by
      apply Matrix.ext; unfold tripleCharges sourceA51 sourceB51 sourceC51 difference raw3719; decide +kernel
    rw [ha]
    exact (canonical3719 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA51 + difference 0 5) (sourceB51 + difference 5 0) sourceC51) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1084) := by
    have ha : (tripleCharges (sourceA51 + difference 0 5) (sourceB51 + difference 5 0) sourceC51) = raw3720 := by
      apply Matrix.ext; unfold tripleCharges sourceA51 sourceB51 sourceC51 difference raw3720; decide +kernel
    rw [ha]
    exact (canonical3720 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA51 + sourceB51) sourceC51) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA51 + sourceB51) sourceC51) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA51 sourceB51 sourceC51 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA51 sourceB51 sourceC51
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm51, Integer.Sparse.eval]
  linarith only [hs]

def sourceA52 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceB52 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC52 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm52 : Integer.Sparse Master := [(Sum.inr 1066, 2), (Sum.inr 1067, 1), (Sum.inr 1068, 1), (Sum.inr 1084, 1), (Sum.inr 2284, 1), (Sum.inr 4085, -1)]

theorem sourceEq52 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm52 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA52 + difference 0 0) (sourceB52 + difference 0 0) sourceC52) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA52 + difference 0 0) (sourceB52 + difference 0 0) sourceC52) = raw3715 := by
      apply Matrix.ext; unfold tripleCharges sourceA52 sourceB52 sourceC52 difference raw3715; decide +kernel
    rw [ha]
    exact (canonical3715 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA52 + difference 1 0) (sourceB52 + difference 0 1) sourceC52) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1066) := by
    have ha : (tripleCharges (sourceA52 + difference 1 0) (sourceB52 + difference 0 1) sourceC52) = raw3722 := by
      apply Matrix.ext; unfold tripleCharges sourceA52 sourceB52 sourceC52 difference raw3722; decide +kernel
    rw [ha]
    exact (canonical3722 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA52 + difference 2 0) (sourceB52 + difference 0 2) sourceC52) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1066) := by
    have ha : (tripleCharges (sourceA52 + difference 2 0) (sourceB52 + difference 0 2) sourceC52) = raw3723 := by
      apply Matrix.ext; unfold tripleCharges sourceA52 sourceB52 sourceC52 difference raw3723; decide +kernel
    rw [ha]
    exact (canonical3723 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA52 + difference 3 0) (sourceB52 + difference 0 3) sourceC52) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1068) := by
    have ha : (tripleCharges (sourceA52 + difference 3 0) (sourceB52 + difference 0 3) sourceC52) = raw3724 := by
      apply Matrix.ext; unfold tripleCharges sourceA52 sourceB52 sourceC52 difference raw3724; decide +kernel
    rw [ha]
    exact (canonical3724 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA52 + difference 4 0) (sourceB52 + difference 0 4) sourceC52) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1067) := by
    have ha : (tripleCharges (sourceA52 + difference 4 0) (sourceB52 + difference 0 4) sourceC52) = raw3725 := by
      apply Matrix.ext; unfold tripleCharges sourceA52 sourceB52 sourceC52 difference raw3725; decide +kernel
    rw [ha]
    exact (canonical3725 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA52 + difference 5 0) (sourceB52 + difference 0 5) sourceC52) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1084) := by
    have ha : (tripleCharges (sourceA52 + difference 5 0) (sourceB52 + difference 0 5) sourceC52) = raw3726 := by
      apply Matrix.ext; unfold tripleCharges sourceA52 sourceB52 sourceC52 difference raw3726; decide +kernel
    rw [ha]
    exact (canonical3726 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA52 + sourceB52) sourceC52) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA52 + sourceB52) sourceC52) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA52 sourceB52 sourceC52 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA52 sourceB52 sourceC52
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm52, Integer.Sparse.eval]
  linarith only [hs]

def sourceA53 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceB53 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC53 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm53 : Integer.Sparse Master := [(Sum.inr 1066, 2), (Sum.inr 2040, 1), (Sum.inr 2283, 1), (Sum.inr 2284, 2), (Sum.inr 4085, -1)]

theorem sourceEq53 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm53 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA53 + difference 1 0) (sourceB53 + difference 0 1) sourceC53) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1066) := by
    have ha : (tripleCharges (sourceA53 + difference 1 0) (sourceB53 + difference 0 1) sourceC53) = raw3722 := by
      apply Matrix.ext; unfold tripleCharges sourceA53 sourceB53 sourceC53 difference raw3722; decide +kernel
    rw [ha]
    exact (canonical3722 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA53 + difference 1 1) (sourceB53 + difference 1 1) sourceC53) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA53 + difference 1 1) (sourceB53 + difference 1 1) sourceC53) = raw3715 := by
      apply Matrix.ext; unfold tripleCharges sourceA53 sourceB53 sourceC53 difference raw3715; decide +kernel
    rw [ha]
    exact (canonical3715 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA53 + difference 1 2) (sourceB53 + difference 2 1) sourceC53) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2040) := by
    have ha : (tripleCharges (sourceA53 + difference 1 2) (sourceB53 + difference 2 1) sourceC53) = raw3727 := by
      apply Matrix.ext; unfold tripleCharges sourceA53 sourceB53 sourceC53 difference raw3727; decide +kernel
    rw [ha]
    exact (canonical3727 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA53 + difference 1 3) (sourceB53 + difference 3 1) sourceC53) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA53 + difference 1 3) (sourceB53 + difference 3 1) sourceC53) = raw3728 := by
      apply Matrix.ext; unfold tripleCharges sourceA53 sourceB53 sourceC53 difference raw3728; decide +kernel
    rw [ha]
    exact (canonical3728 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA53 + difference 1 4) (sourceB53 + difference 4 1) sourceC53) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2283) := by
    have ha : (tripleCharges (sourceA53 + difference 1 4) (sourceB53 + difference 4 1) sourceC53) = raw3729 := by
      apply Matrix.ext; unfold tripleCharges sourceA53 sourceB53 sourceC53 difference raw3729; decide +kernel
    rw [ha]
    exact (canonical3729 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA53 + difference 1 5) (sourceB53 + difference 5 1) sourceC53) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1066) := by
    have ha : (tripleCharges (sourceA53 + difference 1 5) (sourceB53 + difference 5 1) sourceC53) = raw3730 := by
      apply Matrix.ext; unfold tripleCharges sourceA53 sourceB53 sourceC53 difference raw3730; decide +kernel
    rw [ha]
    exact (canonical3730 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA53 + sourceB53) sourceC53) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA53 + sourceB53) sourceC53) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA53 sourceB53 sourceC53 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA53 sourceB53 sourceC53
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm53, Integer.Sparse.eval]
  linarith only [hs]

def sourceA54 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceB54 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC54 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm54 : Integer.Sparse Master := [(Sum.inr 2040, 1), (Sum.inr 2041, 1), (Sum.inr 2042, 1), (Sum.inr 2055, 2), (Sum.inr 2284, 1), (Sum.inr 4085, -1)]

theorem sourceEq54 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm54 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA54 + difference 0 1) (sourceB54 + difference 1 0) sourceC54) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA54 + difference 0 1) (sourceB54 + difference 1 0) sourceC54) = raw3716 := by
      apply Matrix.ext; unfold tripleCharges sourceA54 sourceB54 sourceC54 difference raw3716; decide +kernel
    rw [ha]
    exact (canonical3716 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA54 + difference 1 1) (sourceB54 + difference 1 1) sourceC54) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA54 + difference 1 1) (sourceB54 + difference 1 1) sourceC54) = raw3715 := by
      apply Matrix.ext; unfold tripleCharges sourceA54 sourceB54 sourceC54 difference raw3715; decide +kernel
    rw [ha]
    exact (canonical3715 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA54 + difference 2 1) (sourceB54 + difference 1 2) sourceC54) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2040) := by
    have ha : (tripleCharges (sourceA54 + difference 2 1) (sourceB54 + difference 1 2) sourceC54) = raw3731 := by
      apply Matrix.ext; unfold tripleCharges sourceA54 sourceB54 sourceC54 difference raw3731; decide +kernel
    rw [ha]
    exact (canonical3731 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA54 + difference 3 1) (sourceB54 + difference 1 3) sourceC54) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2042) := by
    have ha : (tripleCharges (sourceA54 + difference 3 1) (sourceB54 + difference 1 3) sourceC54) = raw3732 := by
      apply Matrix.ext; unfold tripleCharges sourceA54 sourceB54 sourceC54 difference raw3732; decide +kernel
    rw [ha]
    exact (canonical3732 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA54 + difference 4 1) (sourceB54 + difference 1 4) sourceC54) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2041) := by
    have ha : (tripleCharges (sourceA54 + difference 4 1) (sourceB54 + difference 1 4) sourceC54) = raw3733 := by
      apply Matrix.ext; unfold tripleCharges sourceA54 sourceB54 sourceC54 difference raw3733; decide +kernel
    rw [ha]
    exact (canonical3733 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA54 + difference 5 1) (sourceB54 + difference 1 5) sourceC54) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA54 + difference 5 1) (sourceB54 + difference 1 5) sourceC54) = raw3734 := by
      apply Matrix.ext; unfold tripleCharges sourceA54 sourceB54 sourceC54 difference raw3734; decide +kernel
    rw [ha]
    exact (canonical3734 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA54 + sourceB54) sourceC54) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA54 + sourceB54) sourceC54) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA54 sourceB54 sourceC54 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA54 sourceB54 sourceC54
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm54, Integer.Sparse.eval]
  linarith only [hs]

def sourceA55 : Charge := ![0, 0, 0, 1, 2, -3]
def sourceB55 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC55 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceForm55 : Integer.Sparse Master := [(Sum.inr 1068, 2), (Sum.inr 2042, 2), (Sum.inr 2284, 2), (Sum.inr 4085, -1)]

theorem sourceEq55 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm55 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA55 + difference 3 0) (sourceB55 + difference 0 3) sourceC55) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1068) := by
    have ha : (tripleCharges (sourceA55 + difference 3 0) (sourceB55 + difference 0 3) sourceC55) = raw3724 := by
      apply Matrix.ext; unfold tripleCharges sourceA55 sourceB55 sourceC55 difference raw3724; decide +kernel
    rw [ha]
    exact (canonical3724 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA55 + difference 3 1) (sourceB55 + difference 1 3) sourceC55) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2042) := by
    have ha : (tripleCharges (sourceA55 + difference 3 1) (sourceB55 + difference 1 3) sourceC55) = raw3732 := by
      apply Matrix.ext; unfold tripleCharges sourceA55 sourceB55 sourceC55 difference raw3732; decide +kernel
    rw [ha]
    exact (canonical3732 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA55 + difference 3 2) (sourceB55 + difference 2 3) sourceC55) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2042) := by
    have ha : (tripleCharges (sourceA55 + difference 3 2) (sourceB55 + difference 2 3) sourceC55) = raw3735 := by
      apply Matrix.ext; unfold tripleCharges sourceA55 sourceB55 sourceC55 difference raw3735; decide +kernel
    rw [ha]
    exact (canonical3735 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA55 + difference 3 3) (sourceB55 + difference 3 3) sourceC55) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA55 + difference 3 3) (sourceB55 + difference 3 3) sourceC55) = raw3715 := by
      apply Matrix.ext; unfold tripleCharges sourceA55 sourceB55 sourceC55 difference raw3715; decide +kernel
    rw [ha]
    exact (canonical3715 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA55 + difference 3 4) (sourceB55 + difference 4 3) sourceC55) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2284) := by
    have ha : (tripleCharges (sourceA55 + difference 3 4) (sourceB55 + difference 4 3) sourceC55) = raw3736 := by
      apply Matrix.ext; unfold tripleCharges sourceA55 sourceB55 sourceC55 difference raw3736; decide +kernel
    rw [ha]
    exact (canonical3736 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA55 + difference 3 5) (sourceB55 + difference 5 3) sourceC55) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1068) := by
    have ha : (tripleCharges (sourceA55 + difference 3 5) (sourceB55 + difference 5 3) sourceC55) = raw3737 := by
      apply Matrix.ext; unfold tripleCharges sourceA55 sourceB55 sourceC55 difference raw3737; decide +kernel
    rw [ha]
    exact (canonical3737 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA55 + sourceB55) sourceC55) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA55 + sourceB55) sourceC55) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA55 sourceB55 sourceC55 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA55 sourceB55 sourceC55
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm55, Integer.Sparse.eval]
  linarith only [hs]

def sourceA56 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB56 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC56 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceForm56 : Integer.Sparse Master := [(Sum.inr 4245, 1), (Sum.inr 4247, 1), (Sum.inr 4254, 3), (Sum.inr 4433, 1), (Sum.inr 4442, 3), (Sum.inr 4730, 3), (Sum.inr 4793, 3), (Sum.inr 4808, 6), (Sum.inr 4878, 1), (Sum.inr 4879, 3), (Sum.inr 4885, 1), (Sum.inr 4889, 3), (Sum.inr 5301, 1)]

theorem sourceEq56 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm56 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA56 + difference 0 1) (sourceB56 + difference 1 0) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4878) := by
    have ha : (tripleCharges (sourceA56 + difference 0 1) (sourceB56 + difference 1 0) sourceC56) = raw3738 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3738; decide +kernel
    rw [ha]
    exact (canonical3738 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA56 + difference 0 2) (sourceB56 + difference 2 0) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA56 + difference 0 2) (sourceB56 + difference 2 0) sourceC56) = raw3739 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3739; decide +kernel
    rw [ha]
    exact (canonical3739 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA56 + difference 0 3) (sourceB56 + difference 3 0) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA56 + difference 0 3) (sourceB56 + difference 3 0) sourceC56) = raw3740 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3740; decide +kernel
    rw [ha]
    exact (canonical3740 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA56 + difference 0 4) (sourceB56 + difference 4 0) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4879) := by
    have ha : (tripleCharges (sourceA56 + difference 0 4) (sourceB56 + difference 4 0) sourceC56) = raw3741 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3741; decide +kernel
    rw [ha]
    exact (canonical3741 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA56 + difference 0 5) (sourceB56 + difference 5 0) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA56 + difference 0 5) (sourceB56 + difference 5 0) sourceC56) = raw3742 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3742; decide +kernel
    rw [ha]
    exact (canonical3742 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA56 + difference 1 0) (sourceB56 + difference 0 1) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4433) := by
    have ha : (tripleCharges (sourceA56 + difference 1 0) (sourceB56 + difference 0 1) sourceC56) = raw3743 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3743; decide +kernel
    rw [ha]
    exact (canonical3743 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA56 + difference 1 2) (sourceB56 + difference 2 1) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4730) := by
    have ha : (tripleCharges (sourceA56 + difference 1 2) (sourceB56 + difference 2 1) sourceC56) = raw3744 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3744; decide +kernel
    rw [ha]
    exact (canonical3744 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA56 + difference 1 3) (sourceB56 + difference 3 1) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4730) := by
    have ha : (tripleCharges (sourceA56 + difference 1 3) (sourceB56 + difference 3 1) sourceC56) = raw3745 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3745; decide +kernel
    rw [ha]
    exact (canonical3745 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA56 + difference 1 4) (sourceB56 + difference 4 1) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4730) := by
    have ha : (tripleCharges (sourceA56 + difference 1 4) (sourceB56 + difference 4 1) sourceC56) = raw3746 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3746; decide +kernel
    rw [ha]
    exact (canonical3746 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA56 + difference 1 5) (sourceB56 + difference 5 1) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA56 + difference 1 5) (sourceB56 + difference 5 1) sourceC56) = raw3747 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3747; decide +kernel
    rw [ha]
    exact (canonical3747 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA56 + difference 2 0) (sourceB56 + difference 0 2) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA56 + difference 2 0) (sourceB56 + difference 0 2) sourceC56) = raw3748 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3748; decide +kernel
    rw [ha]
    exact (canonical3748 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA56 + difference 2 1) (sourceB56 + difference 1 2) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4793) := by
    have ha : (tripleCharges (sourceA56 + difference 2 1) (sourceB56 + difference 1 2) sourceC56) = raw3749 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3749; decide +kernel
    rw [ha]
    exact (canonical3749 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA56 + difference 2 3) (sourceB56 + difference 3 2) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA56 + difference 2 3) (sourceB56 + difference 3 2) sourceC56) = raw3750 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3750; decide +kernel
    rw [ha]
    exact (canonical3750 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA56 + difference 2 4) (sourceB56 + difference 4 2) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA56 + difference 2 4) (sourceB56 + difference 4 2) sourceC56) = raw3751 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3751; decide +kernel
    rw [ha]
    exact (canonical3751 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA56 + difference 2 5) (sourceB56 + difference 5 2) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA56 + difference 2 5) (sourceB56 + difference 5 2) sourceC56) = raw3752 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3752; decide +kernel
    rw [ha]
    exact (canonical3752 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA56 + difference 3 0) (sourceB56 + difference 0 3) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA56 + difference 3 0) (sourceB56 + difference 0 3) sourceC56) = raw3753 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3753; decide +kernel
    rw [ha]
    exact (canonical3753 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA56 + difference 3 1) (sourceB56 + difference 1 3) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4793) := by
    have ha : (tripleCharges (sourceA56 + difference 3 1) (sourceB56 + difference 1 3) sourceC56) = raw3754 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3754; decide +kernel
    rw [ha]
    exact (canonical3754 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA56 + difference 3 2) (sourceB56 + difference 2 3) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA56 + difference 3 2) (sourceB56 + difference 2 3) sourceC56) = raw3755 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3755; decide +kernel
    rw [ha]
    exact (canonical3755 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA56 + difference 3 4) (sourceB56 + difference 4 3) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA56 + difference 3 4) (sourceB56 + difference 4 3) sourceC56) = raw3756 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3756; decide +kernel
    rw [ha]
    exact (canonical3756 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA56 + difference 3 5) (sourceB56 + difference 5 3) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA56 + difference 3 5) (sourceB56 + difference 5 3) sourceC56) = raw3757 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3757; decide +kernel
    rw [ha]
    exact (canonical3757 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA56 + difference 4 0) (sourceB56 + difference 0 4) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4442) := by
    have ha : (tripleCharges (sourceA56 + difference 4 0) (sourceB56 + difference 0 4) sourceC56) = raw3758 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3758; decide +kernel
    rw [ha]
    exact (canonical3758 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA56 + difference 4 1) (sourceB56 + difference 1 4) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4793) := by
    have ha : (tripleCharges (sourceA56 + difference 4 1) (sourceB56 + difference 1 4) sourceC56) = raw3759 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3759; decide +kernel
    rw [ha]
    exact (canonical3759 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA56 + difference 4 2) (sourceB56 + difference 2 4) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA56 + difference 4 2) (sourceB56 + difference 2 4) sourceC56) = raw3760 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3760; decide +kernel
    rw [ha]
    exact (canonical3760 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA56 + difference 4 3) (sourceB56 + difference 3 4) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA56 + difference 4 3) (sourceB56 + difference 3 4) sourceC56) = raw3761 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3761; decide +kernel
    rw [ha]
    exact (canonical3761 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA56 + difference 4 5) (sourceB56 + difference 5 4) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA56 + difference 4 5) (sourceB56 + difference 5 4) sourceC56) = raw3762 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3762; decide +kernel
    rw [ha]
    exact (canonical3762 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA56 + difference 5 0) (sourceB56 + difference 0 5) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4247) := by
    have ha : (tripleCharges (sourceA56 + difference 5 0) (sourceB56 + difference 0 5) sourceC56) = raw3763 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3763; decide +kernel
    rw [ha]
    exact (canonical3763 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA56 + difference 5 1) (sourceB56 + difference 1 5) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4245) := by
    have ha : (tripleCharges (sourceA56 + difference 5 1) (sourceB56 + difference 1 5) sourceC56) = raw3764 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3764; decide +kernel
    rw [ha]
    exact (canonical3764 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA56 + difference 5 2) (sourceB56 + difference 2 5) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4254) := by
    have ha : (tripleCharges (sourceA56 + difference 5 2) (sourceB56 + difference 2 5) sourceC56) = raw3765 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3765; decide +kernel
    rw [ha]
    exact (canonical3765 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA56 + difference 5 3) (sourceB56 + difference 3 5) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4254) := by
    have ha : (tripleCharges (sourceA56 + difference 5 3) (sourceB56 + difference 3 5) sourceC56) = raw3766 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3766; decide +kernel
    rw [ha]
    exact (canonical3766 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA56 + difference 5 4) (sourceB56 + difference 4 5) sourceC56) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4254) := by
    have ha : (tripleCharges (sourceA56 + difference 5 4) (sourceB56 + difference 4 5) sourceC56) = raw3767 := by
      apply Matrix.ext; unfold tripleCharges sourceA56 sourceB56 sourceC56 difference raw3767; decide +kernel
    rw [ha]
    exact (canonical3767 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA56 sourceB56 sourceC56
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm56, Integer.Sparse.eval]
  linarith only [hs]

def sourceA57 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB57 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC57 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceForm57 : Integer.Sparse Master := [(Sum.inr 777, 1), (Sum.inr 779, 1), (Sum.inr 788, 3), (Sum.inr 1376, 1), (Sum.inr 1385, 3), (Sum.inr 1899, 3), (Sum.inr 2010, 3), (Sum.inr 2026, 6), (Sum.inr 2234, 1), (Sum.inr 2246, 3), (Sum.inr 3053, 1), (Sum.inr 3221, 1), (Sum.inr 3223, 3)]

theorem sourceEq57 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm57 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA57 + difference 0 1) (sourceB57 + difference 1 0) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2234) := by
    have ha : (tripleCharges (sourceA57 + difference 0 1) (sourceB57 + difference 1 0) sourceC57) = raw3768 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3768; decide +kernel
    rw [ha]
    exact (canonical3768 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA57 + difference 0 2) (sourceB57 + difference 2 0) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA57 + difference 0 2) (sourceB57 + difference 2 0) sourceC57) = raw3769 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3769; decide +kernel
    rw [ha]
    exact (canonical3769 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA57 + difference 0 3) (sourceB57 + difference 3 0) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA57 + difference 0 3) (sourceB57 + difference 3 0) sourceC57) = raw3770 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3770; decide +kernel
    rw [ha]
    exact (canonical3770 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA57 + difference 0 4) (sourceB57 + difference 4 0) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2246) := by
    have ha : (tripleCharges (sourceA57 + difference 0 4) (sourceB57 + difference 4 0) sourceC57) = raw3771 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3771; decide +kernel
    rw [ha]
    exact (canonical3771 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA57 + difference 0 5) (sourceB57 + difference 5 0) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA57 + difference 0 5) (sourceB57 + difference 5 0) sourceC57) = raw3772 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3772; decide +kernel
    rw [ha]
    exact (canonical3772 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA57 + difference 1 0) (sourceB57 + difference 0 1) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1376) := by
    have ha : (tripleCharges (sourceA57 + difference 1 0) (sourceB57 + difference 0 1) sourceC57) = raw3773 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3773; decide +kernel
    rw [ha]
    exact (canonical3773 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA57 + difference 1 2) (sourceB57 + difference 2 1) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1899) := by
    have ha : (tripleCharges (sourceA57 + difference 1 2) (sourceB57 + difference 2 1) sourceC57) = raw3774 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3774; decide +kernel
    rw [ha]
    exact (canonical3774 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA57 + difference 1 3) (sourceB57 + difference 3 1) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1899) := by
    have ha : (tripleCharges (sourceA57 + difference 1 3) (sourceB57 + difference 3 1) sourceC57) = raw3775 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3775; decide +kernel
    rw [ha]
    exact (canonical3775 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA57 + difference 1 4) (sourceB57 + difference 4 1) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1899) := by
    have ha : (tripleCharges (sourceA57 + difference 1 4) (sourceB57 + difference 4 1) sourceC57) = raw3776 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3776; decide +kernel
    rw [ha]
    exact (canonical3776 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA57 + difference 1 5) (sourceB57 + difference 5 1) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA57 + difference 1 5) (sourceB57 + difference 5 1) sourceC57) = raw3777 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3777; decide +kernel
    rw [ha]
    exact (canonical3777 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA57 + difference 2 0) (sourceB57 + difference 0 2) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1385) := by
    have ha : (tripleCharges (sourceA57 + difference 2 0) (sourceB57 + difference 0 2) sourceC57) = raw3778 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3778; decide +kernel
    rw [ha]
    exact (canonical3778 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA57 + difference 2 1) (sourceB57 + difference 1 2) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA57 + difference 2 1) (sourceB57 + difference 1 2) sourceC57) = raw3779 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3779; decide +kernel
    rw [ha]
    exact (canonical3779 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA57 + difference 2 3) (sourceB57 + difference 3 2) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA57 + difference 2 3) (sourceB57 + difference 3 2) sourceC57) = raw3780 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3780; decide +kernel
    rw [ha]
    exact (canonical3780 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA57 + difference 2 4) (sourceB57 + difference 4 2) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA57 + difference 2 4) (sourceB57 + difference 4 2) sourceC57) = raw3781 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3781; decide +kernel
    rw [ha]
    exact (canonical3781 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA57 + difference 2 5) (sourceB57 + difference 5 2) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA57 + difference 2 5) (sourceB57 + difference 5 2) sourceC57) = raw3782 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3782; decide +kernel
    rw [ha]
    exact (canonical3782 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA57 + difference 3 0) (sourceB57 + difference 0 3) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1385) := by
    have ha : (tripleCharges (sourceA57 + difference 3 0) (sourceB57 + difference 0 3) sourceC57) = raw3783 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3783; decide +kernel
    rw [ha]
    exact (canonical3783 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA57 + difference 3 1) (sourceB57 + difference 1 3) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA57 + difference 3 1) (sourceB57 + difference 1 3) sourceC57) = raw3784 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3784; decide +kernel
    rw [ha]
    exact (canonical3784 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA57 + difference 3 2) (sourceB57 + difference 2 3) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA57 + difference 3 2) (sourceB57 + difference 2 3) sourceC57) = raw3785 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3785; decide +kernel
    rw [ha]
    exact (canonical3785 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA57 + difference 3 4) (sourceB57 + difference 4 3) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA57 + difference 3 4) (sourceB57 + difference 4 3) sourceC57) = raw3786 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3786; decide +kernel
    rw [ha]
    exact (canonical3786 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA57 + difference 3 5) (sourceB57 + difference 5 3) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA57 + difference 3 5) (sourceB57 + difference 5 3) sourceC57) = raw3787 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3787; decide +kernel
    rw [ha]
    exact (canonical3787 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA57 + difference 4 0) (sourceB57 + difference 0 4) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1385) := by
    have ha : (tripleCharges (sourceA57 + difference 4 0) (sourceB57 + difference 0 4) sourceC57) = raw3788 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3788; decide +kernel
    rw [ha]
    exact (canonical3788 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA57 + difference 4 1) (sourceB57 + difference 1 4) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA57 + difference 4 1) (sourceB57 + difference 1 4) sourceC57) = raw3789 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3789; decide +kernel
    rw [ha]
    exact (canonical3789 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA57 + difference 4 2) (sourceB57 + difference 2 4) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA57 + difference 4 2) (sourceB57 + difference 2 4) sourceC57) = raw3790 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3790; decide +kernel
    rw [ha]
    exact (canonical3790 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA57 + difference 4 3) (sourceB57 + difference 3 4) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA57 + difference 4 3) (sourceB57 + difference 3 4) sourceC57) = raw3791 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3791; decide +kernel
    rw [ha]
    exact (canonical3791 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA57 + difference 4 5) (sourceB57 + difference 5 4) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA57 + difference 4 5) (sourceB57 + difference 5 4) sourceC57) = raw3792 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3792; decide +kernel
    rw [ha]
    exact (canonical3792 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA57 + difference 5 0) (sourceB57 + difference 0 5) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 779) := by
    have ha : (tripleCharges (sourceA57 + difference 5 0) (sourceB57 + difference 0 5) sourceC57) = raw3793 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3793; decide +kernel
    rw [ha]
    exact (canonical3793 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA57 + difference 5 1) (sourceB57 + difference 1 5) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 777) := by
    have ha : (tripleCharges (sourceA57 + difference 5 1) (sourceB57 + difference 1 5) sourceC57) = raw3794 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3794; decide +kernel
    rw [ha]
    exact (canonical3794 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA57 + difference 5 2) (sourceB57 + difference 2 5) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 788) := by
    have ha : (tripleCharges (sourceA57 + difference 5 2) (sourceB57 + difference 2 5) sourceC57) = raw3795 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3795; decide +kernel
    rw [ha]
    exact (canonical3795 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA57 + difference 5 3) (sourceB57 + difference 3 5) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 788) := by
    have ha : (tripleCharges (sourceA57 + difference 5 3) (sourceB57 + difference 3 5) sourceC57) = raw3796 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3796; decide +kernel
    rw [ha]
    exact (canonical3796 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA57 + difference 5 4) (sourceB57 + difference 4 5) sourceC57) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 788) := by
    have ha : (tripleCharges (sourceA57 + difference 5 4) (sourceB57 + difference 4 5) sourceC57) = raw3797 := by
      apply Matrix.ext; unfold tripleCharges sourceA57 sourceB57 sourceC57 difference raw3797; decide +kernel
    rw [ha]
    exact (canonical3797 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA57 sourceB57 sourceC57
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm57, Integer.Sparse.eval]
  linarith only [hs]

def sourceA58 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB58 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC58 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceForm58 : Integer.Sparse Master := [(Sum.inr 833, 1), (Sum.inr 834, 3), (Sum.inr 846, 1), (Sum.inr 1717, 1), (Sum.inr 1744, 3), (Sum.inr 1930, 3), (Sum.inr 2131, 1), (Sum.inr 2132, 3), (Sum.inr 2219, 3), (Sum.inr 2220, 6), (Sum.inr 2252, 1), (Sum.inr 2277, 3), (Sum.inr 2775, 1)]

theorem sourceEq58 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm58 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA58 + difference 0 1) (sourceB58 + difference 1 0) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2131) := by
    have ha : (tripleCharges (sourceA58 + difference 0 1) (sourceB58 + difference 1 0) sourceC58) = raw3798 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3798; decide +kernel
    rw [ha]
    exact (canonical3798 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA58 + difference 0 2) (sourceB58 + difference 2 0) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2132) := by
    have ha : (tripleCharges (sourceA58 + difference 0 2) (sourceB58 + difference 2 0) sourceC58) = raw3799 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3799; decide +kernel
    rw [ha]
    exact (canonical3799 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA58 + difference 0 3) (sourceB58 + difference 3 0) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2132) := by
    have ha : (tripleCharges (sourceA58 + difference 0 3) (sourceB58 + difference 3 0) sourceC58) = raw3800 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3800; decide +kernel
    rw [ha]
    exact (canonical3800 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA58 + difference 0 4) (sourceB58 + difference 4 0) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2132) := by
    have ha : (tripleCharges (sourceA58 + difference 0 4) (sourceB58 + difference 4 0) sourceC58) = raw3801 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3801; decide +kernel
    rw [ha]
    exact (canonical3801 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA58 + difference 0 5) (sourceB58 + difference 5 0) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2775) := by
    have ha : (tripleCharges (sourceA58 + difference 0 5) (sourceB58 + difference 5 0) sourceC58) = raw3802 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3802; decide +kernel
    rw [ha]
    exact (canonical3802 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA58 + difference 1 0) (sourceB58 + difference 0 1) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1717) := by
    have ha : (tripleCharges (sourceA58 + difference 1 0) (sourceB58 + difference 0 1) sourceC58) = raw3803 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3803; decide +kernel
    rw [ha]
    exact (canonical3803 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA58 + difference 1 2) (sourceB58 + difference 2 1) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1930) := by
    have ha : (tripleCharges (sourceA58 + difference 1 2) (sourceB58 + difference 2 1) sourceC58) = raw3804 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3804; decide +kernel
    rw [ha]
    exact (canonical3804 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA58 + difference 1 3) (sourceB58 + difference 3 1) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1930) := by
    have ha : (tripleCharges (sourceA58 + difference 1 3) (sourceB58 + difference 3 1) sourceC58) = raw3805 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3805; decide +kernel
    rw [ha]
    exact (canonical3805 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA58 + difference 1 4) (sourceB58 + difference 4 1) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1930) := by
    have ha : (tripleCharges (sourceA58 + difference 1 4) (sourceB58 + difference 4 1) sourceC58) = raw3806 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3806; decide +kernel
    rw [ha]
    exact (canonical3806 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA58 + difference 1 5) (sourceB58 + difference 5 1) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2252) := by
    have ha : (tripleCharges (sourceA58 + difference 1 5) (sourceB58 + difference 5 1) sourceC58) = raw3807 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3807; decide +kernel
    rw [ha]
    exact (canonical3807 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA58 + difference 2 0) (sourceB58 + difference 0 2) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA58 + difference 2 0) (sourceB58 + difference 0 2) sourceC58) = raw3808 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3808; decide +kernel
    rw [ha]
    exact (canonical3808 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA58 + difference 2 1) (sourceB58 + difference 1 2) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2219) := by
    have ha : (tripleCharges (sourceA58 + difference 2 1) (sourceB58 + difference 1 2) sourceC58) = raw3809 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3809; decide +kernel
    rw [ha]
    exact (canonical3809 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA58 + difference 2 3) (sourceB58 + difference 3 2) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA58 + difference 2 3) (sourceB58 + difference 3 2) sourceC58) = raw3810 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3810; decide +kernel
    rw [ha]
    exact (canonical3810 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA58 + difference 2 4) (sourceB58 + difference 4 2) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA58 + difference 2 4) (sourceB58 + difference 4 2) sourceC58) = raw3811 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3811; decide +kernel
    rw [ha]
    exact (canonical3811 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA58 + difference 2 5) (sourceB58 + difference 5 2) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA58 + difference 2 5) (sourceB58 + difference 5 2) sourceC58) = raw3812 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3812; decide +kernel
    rw [ha]
    exact (canonical3812 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA58 + difference 3 0) (sourceB58 + difference 0 3) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA58 + difference 3 0) (sourceB58 + difference 0 3) sourceC58) = raw3813 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3813; decide +kernel
    rw [ha]
    exact (canonical3813 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA58 + difference 3 1) (sourceB58 + difference 1 3) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2219) := by
    have ha : (tripleCharges (sourceA58 + difference 3 1) (sourceB58 + difference 1 3) sourceC58) = raw3814 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3814; decide +kernel
    rw [ha]
    exact (canonical3814 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA58 + difference 3 2) (sourceB58 + difference 2 3) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA58 + difference 3 2) (sourceB58 + difference 2 3) sourceC58) = raw3815 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3815; decide +kernel
    rw [ha]
    exact (canonical3815 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA58 + difference 3 4) (sourceB58 + difference 4 3) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA58 + difference 3 4) (sourceB58 + difference 4 3) sourceC58) = raw3816 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3816; decide +kernel
    rw [ha]
    exact (canonical3816 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA58 + difference 3 5) (sourceB58 + difference 5 3) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA58 + difference 3 5) (sourceB58 + difference 5 3) sourceC58) = raw3817 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3817; decide +kernel
    rw [ha]
    exact (canonical3817 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA58 + difference 4 0) (sourceB58 + difference 0 4) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA58 + difference 4 0) (sourceB58 + difference 0 4) sourceC58) = raw3818 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3818; decide +kernel
    rw [ha]
    exact (canonical3818 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA58 + difference 4 1) (sourceB58 + difference 1 4) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2219) := by
    have ha : (tripleCharges (sourceA58 + difference 4 1) (sourceB58 + difference 1 4) sourceC58) = raw3819 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3819; decide +kernel
    rw [ha]
    exact (canonical3819 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA58 + difference 4 2) (sourceB58 + difference 2 4) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA58 + difference 4 2) (sourceB58 + difference 2 4) sourceC58) = raw3820 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3820; decide +kernel
    rw [ha]
    exact (canonical3820 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA58 + difference 4 3) (sourceB58 + difference 3 4) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA58 + difference 4 3) (sourceB58 + difference 3 4) sourceC58) = raw3821 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3821; decide +kernel
    rw [ha]
    exact (canonical3821 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA58 + difference 4 5) (sourceB58 + difference 5 4) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA58 + difference 4 5) (sourceB58 + difference 5 4) sourceC58) = raw3822 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3822; decide +kernel
    rw [ha]
    exact (canonical3822 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA58 + difference 5 0) (sourceB58 + difference 0 5) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 846) := by
    have ha : (tripleCharges (sourceA58 + difference 5 0) (sourceB58 + difference 0 5) sourceC58) = raw3823 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3823; decide +kernel
    rw [ha]
    exact (canonical3823 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA58 + difference 5 1) (sourceB58 + difference 1 5) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 833) := by
    have ha : (tripleCharges (sourceA58 + difference 5 1) (sourceB58 + difference 1 5) sourceC58) = raw3824 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3824; decide +kernel
    rw [ha]
    exact (canonical3824 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA58 + difference 5 2) (sourceB58 + difference 2 5) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 834) := by
    have ha : (tripleCharges (sourceA58 + difference 5 2) (sourceB58 + difference 2 5) sourceC58) = raw3825 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3825; decide +kernel
    rw [ha]
    exact (canonical3825 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA58 + difference 5 3) (sourceB58 + difference 3 5) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 834) := by
    have ha : (tripleCharges (sourceA58 + difference 5 3) (sourceB58 + difference 3 5) sourceC58) = raw3826 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3826; decide +kernel
    rw [ha]
    exact (canonical3826 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA58 + difference 5 4) (sourceB58 + difference 4 5) sourceC58) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 834) := by
    have ha : (tripleCharges (sourceA58 + difference 5 4) (sourceB58 + difference 4 5) sourceC58) = raw3827 := by
      apply Matrix.ext; unfold tripleCharges sourceA58 sourceB58 sourceC58 difference raw3827; decide +kernel
    rw [ha]
    exact (canonical3827 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA58 sourceB58 sourceC58
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm58, Integer.Sparse.eval]
  linarith only [hs]

def sourceA59 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB59 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC59 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceForm59 : Integer.Sparse Master := [(Sum.inr 2235, 1), (Sum.inr 3155, 1), (Sum.inr 3158, 3), (Sum.inr 3619, 1), (Sum.inr 4083, -1)]

theorem sourceEq59 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm59 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA59 + difference 0 0) (sourceB59 + difference 0 0) sourceC59) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA59 + difference 0 0) (sourceB59 + difference 0 0) sourceC59) = raw3828 := by
      apply Matrix.ext; unfold tripleCharges sourceA59 sourceB59 sourceC59 difference raw3828; decide +kernel
    rw [ha]
    exact (canonical3828 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA59 + difference 0 1) (sourceB59 + difference 1 0) sourceC59) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3155) := by
    have ha : (tripleCharges (sourceA59 + difference 0 1) (sourceB59 + difference 1 0) sourceC59) = raw3829 := by
      apply Matrix.ext; unfold tripleCharges sourceA59 sourceB59 sourceC59 difference raw3829; decide +kernel
    rw [ha]
    exact (canonical3829 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA59 + difference 0 2) (sourceB59 + difference 2 0) sourceC59) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3158) := by
    have ha : (tripleCharges (sourceA59 + difference 0 2) (sourceB59 + difference 2 0) sourceC59) = raw3830 := by
      apply Matrix.ext; unfold tripleCharges sourceA59 sourceB59 sourceC59 difference raw3830; decide +kernel
    rw [ha]
    exact (canonical3830 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA59 + difference 0 3) (sourceB59 + difference 3 0) sourceC59) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3158) := by
    have ha : (tripleCharges (sourceA59 + difference 0 3) (sourceB59 + difference 3 0) sourceC59) = raw3831 := by
      apply Matrix.ext; unfold tripleCharges sourceA59 sourceB59 sourceC59 difference raw3831; decide +kernel
    rw [ha]
    exact (canonical3831 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA59 + difference 0 4) (sourceB59 + difference 4 0) sourceC59) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3158) := by
    have ha : (tripleCharges (sourceA59 + difference 0 4) (sourceB59 + difference 4 0) sourceC59) = raw3832 := by
      apply Matrix.ext; unfold tripleCharges sourceA59 sourceB59 sourceC59 difference raw3832; decide +kernel
    rw [ha]
    exact (canonical3832 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA59 + difference 0 5) (sourceB59 + difference 5 0) sourceC59) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3619) := by
    have ha : (tripleCharges (sourceA59 + difference 0 5) (sourceB59 + difference 5 0) sourceC59) = raw3833 := by
      apply Matrix.ext; unfold tripleCharges sourceA59 sourceB59 sourceC59 difference raw3833; decide +kernel
    rw [ha]
    exact (canonical3833 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA59 + sourceB59) sourceC59) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA59 + sourceB59) sourceC59) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA59 sourceB59 sourceC59 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA59 sourceB59 sourceC59
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm59, Integer.Sparse.eval]
  linarith only [hs]

def sourceA60 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB60 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC60 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceForm60 : Integer.Sparse Master := [(Sum.inr 1014, 1), (Sum.inr 1016, 1), (Sum.inr 1024, 3), (Sum.inr 2235, 1), (Sum.inr 4083, -1)]

theorem sourceEq60 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm60 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA60 + difference 0 0) (sourceB60 + difference 0 0) sourceC60) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA60 + difference 0 0) (sourceB60 + difference 0 0) sourceC60) = raw3828 := by
      apply Matrix.ext; unfold tripleCharges sourceA60 sourceB60 sourceC60 difference raw3828; decide +kernel
    rw [ha]
    exact (canonical3828 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA60 + difference 1 0) (sourceB60 + difference 0 1) sourceC60) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1014) := by
    have ha : (tripleCharges (sourceA60 + difference 1 0) (sourceB60 + difference 0 1) sourceC60) = raw3835 := by
      apply Matrix.ext; unfold tripleCharges sourceA60 sourceB60 sourceC60 difference raw3835; decide +kernel
    rw [ha]
    exact (canonical3835 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA60 + difference 2 0) (sourceB60 + difference 0 2) sourceC60) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA60 + difference 2 0) (sourceB60 + difference 0 2) sourceC60) = raw3836 := by
      apply Matrix.ext; unfold tripleCharges sourceA60 sourceB60 sourceC60 difference raw3836; decide +kernel
    rw [ha]
    exact (canonical3836 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA60 + difference 3 0) (sourceB60 + difference 0 3) sourceC60) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA60 + difference 3 0) (sourceB60 + difference 0 3) sourceC60) = raw3837 := by
      apply Matrix.ext; unfold tripleCharges sourceA60 sourceB60 sourceC60 difference raw3837; decide +kernel
    rw [ha]
    exact (canonical3837 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA60 + difference 4 0) (sourceB60 + difference 0 4) sourceC60) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA60 + difference 4 0) (sourceB60 + difference 0 4) sourceC60) = raw3838 := by
      apply Matrix.ext; unfold tripleCharges sourceA60 sourceB60 sourceC60 difference raw3838; decide +kernel
    rw [ha]
    exact (canonical3838 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA60 + difference 5 0) (sourceB60 + difference 0 5) sourceC60) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1016) := by
    have ha : (tripleCharges (sourceA60 + difference 5 0) (sourceB60 + difference 0 5) sourceC60) = raw3839 := by
      apply Matrix.ext; unfold tripleCharges sourceA60 sourceB60 sourceC60 difference raw3839; decide +kernel
    rw [ha]
    exact (canonical3839 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA60 + sourceB60) sourceC60) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA60 + sourceB60) sourceC60) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA60 sourceB60 sourceC60 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA60 sourceB60 sourceC60
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm60, Integer.Sparse.eval]
  linarith only [hs]

def sourceA61 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB61 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC61 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceForm61 : Integer.Sparse Master := [(Sum.inr 1014, 1), (Sum.inr 2083, 3), (Sum.inr 2233, 1), (Sum.inr 2235, 1), (Sum.inr 4083, -1)]

theorem sourceEq61 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm61 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA61 + difference 1 0) (sourceB61 + difference 0 1) sourceC61) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1014) := by
    have ha : (tripleCharges (sourceA61 + difference 1 0) (sourceB61 + difference 0 1) sourceC61) = raw3835 := by
      apply Matrix.ext; unfold tripleCharges sourceA61 sourceB61 sourceC61 difference raw3835; decide +kernel
    rw [ha]
    exact (canonical3835 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA61 + difference 1 1) (sourceB61 + difference 1 1) sourceC61) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA61 + difference 1 1) (sourceB61 + difference 1 1) sourceC61) = raw3828 := by
      apply Matrix.ext; unfold tripleCharges sourceA61 sourceB61 sourceC61 difference raw3828; decide +kernel
    rw [ha]
    exact (canonical3828 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA61 + difference 1 2) (sourceB61 + difference 2 1) sourceC61) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2083) := by
    have ha : (tripleCharges (sourceA61 + difference 1 2) (sourceB61 + difference 2 1) sourceC61) = raw3840 := by
      apply Matrix.ext; unfold tripleCharges sourceA61 sourceB61 sourceC61 difference raw3840; decide +kernel
    rw [ha]
    exact (canonical3840 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA61 + difference 1 3) (sourceB61 + difference 3 1) sourceC61) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2083) := by
    have ha : (tripleCharges (sourceA61 + difference 1 3) (sourceB61 + difference 3 1) sourceC61) = raw3841 := by
      apply Matrix.ext; unfold tripleCharges sourceA61 sourceB61 sourceC61 difference raw3841; decide +kernel
    rw [ha]
    exact (canonical3841 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA61 + difference 1 4) (sourceB61 + difference 4 1) sourceC61) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2083) := by
    have ha : (tripleCharges (sourceA61 + difference 1 4) (sourceB61 + difference 4 1) sourceC61) = raw3842 := by
      apply Matrix.ext; unfold tripleCharges sourceA61 sourceB61 sourceC61 difference raw3842; decide +kernel
    rw [ha]
    exact (canonical3842 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA61 + difference 1 5) (sourceB61 + difference 5 1) sourceC61) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA61 + difference 1 5) (sourceB61 + difference 5 1) sourceC61) = raw3843 := by
      apply Matrix.ext; unfold tripleCharges sourceA61 sourceB61 sourceC61 difference raw3843; decide +kernel
    rw [ha]
    exact (canonical3843 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA61 + sourceB61) sourceC61) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA61 + sourceB61) sourceC61) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA61 sourceB61 sourceC61 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA61 sourceB61 sourceC61
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm61, Integer.Sparse.eval]
  linarith only [hs]

def sourceA62 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB62 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC62 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceForm62 : Integer.Sparse Master := [(Sum.inr 1457, 1), (Sum.inr 2010, 3), (Sum.inr 2235, 1), (Sum.inr 3155, 1), (Sum.inr 4083, -1)]

theorem sourceEq62 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm62 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA62 + difference 0 1) (sourceB62 + difference 1 0) sourceC62) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3155) := by
    have ha : (tripleCharges (sourceA62 + difference 0 1) (sourceB62 + difference 1 0) sourceC62) = raw3829 := by
      apply Matrix.ext; unfold tripleCharges sourceA62 sourceB62 sourceC62 difference raw3829; decide +kernel
    rw [ha]
    exact (canonical3829 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA62 + difference 1 1) (sourceB62 + difference 1 1) sourceC62) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA62 + difference 1 1) (sourceB62 + difference 1 1) sourceC62) = raw3828 := by
      apply Matrix.ext; unfold tripleCharges sourceA62 sourceB62 sourceC62 difference raw3828; decide +kernel
    rw [ha]
    exact (canonical3828 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA62 + difference 2 1) (sourceB62 + difference 1 2) sourceC62) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA62 + difference 2 1) (sourceB62 + difference 1 2) sourceC62) = raw3844 := by
      apply Matrix.ext; unfold tripleCharges sourceA62 sourceB62 sourceC62 difference raw3844; decide +kernel
    rw [ha]
    exact (canonical3844 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA62 + difference 3 1) (sourceB62 + difference 1 3) sourceC62) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA62 + difference 3 1) (sourceB62 + difference 1 3) sourceC62) = raw3845 := by
      apply Matrix.ext; unfold tripleCharges sourceA62 sourceB62 sourceC62 difference raw3845; decide +kernel
    rw [ha]
    exact (canonical3845 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA62 + difference 4 1) (sourceB62 + difference 1 4) sourceC62) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA62 + difference 4 1) (sourceB62 + difference 1 4) sourceC62) = raw3846 := by
      apply Matrix.ext; unfold tripleCharges sourceA62 sourceB62 sourceC62 difference raw3846; decide +kernel
    rw [ha]
    exact (canonical3846 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA62 + difference 5 1) (sourceB62 + difference 1 5) sourceC62) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1457) := by
    have ha : (tripleCharges (sourceA62 + difference 5 1) (sourceB62 + difference 1 5) sourceC62) = raw3847 := by
      apply Matrix.ext; unfold tripleCharges sourceA62 sourceB62 sourceC62 difference raw3847; decide +kernel
    rw [ha]
    exact (canonical3847 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA62 + sourceB62) sourceC62) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA62 + sourceB62) sourceC62) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA62 sourceB62 sourceC62 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA62 sourceB62 sourceC62
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm62, Integer.Sparse.eval]
  linarith only [hs]

def sourceA63 : Charge := ![-3, 0, 0, 0, 0, 3]
def sourceB63 : Charge := ![0, 0, 1, 1, 1, -3]
def sourceC63 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceForm63 : Integer.Sparse Master := [(Sum.inr 1024, 1), (Sum.inr 2010, 1), (Sum.inr 2092, 2), (Sum.inr 2235, 1), (Sum.inr 2245, 1), (Sum.inr 4083, -1)]

theorem sourceEq63 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm63 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA63 + difference 2 0) (sourceB63 + difference 0 2) sourceC63) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA63 + difference 2 0) (sourceB63 + difference 0 2) sourceC63) = raw3836 := by
      apply Matrix.ext; unfold tripleCharges sourceA63 sourceB63 sourceC63 difference raw3836; decide +kernel
    rw [ha]
    exact (canonical3836 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA63 + difference 2 1) (sourceB63 + difference 1 2) sourceC63) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2010) := by
    have ha : (tripleCharges (sourceA63 + difference 2 1) (sourceB63 + difference 1 2) sourceC63) = raw3844 := by
      apply Matrix.ext; unfold tripleCharges sourceA63 sourceB63 sourceC63 difference raw3844; decide +kernel
    rw [ha]
    exact (canonical3844 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA63 + difference 2 2) (sourceB63 + difference 2 2) sourceC63) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA63 + difference 2 2) (sourceB63 + difference 2 2) sourceC63) = raw3828 := by
      apply Matrix.ext; unfold tripleCharges sourceA63 sourceB63 sourceC63 difference raw3828; decide +kernel
    rw [ha]
    exact (canonical3828 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA63 + difference 2 3) (sourceB63 + difference 3 2) sourceC63) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA63 + difference 2 3) (sourceB63 + difference 3 2) sourceC63) = raw3848 := by
      apply Matrix.ext; unfold tripleCharges sourceA63 sourceB63 sourceC63 difference raw3848; decide +kernel
    rw [ha]
    exact (canonical3848 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA63 + difference 2 4) (sourceB63 + difference 4 2) sourceC63) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA63 + difference 2 4) (sourceB63 + difference 4 2) sourceC63) = raw3849 := by
      apply Matrix.ext; unfold tripleCharges sourceA63 sourceB63 sourceC63 difference raw3849; decide +kernel
    rw [ha]
    exact (canonical3849 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA63 + difference 2 5) (sourceB63 + difference 5 2) sourceC63) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA63 + difference 2 5) (sourceB63 + difference 5 2) sourceC63) = raw3850 := by
      apply Matrix.ext; unfold tripleCharges sourceA63 sourceB63 sourceC63 difference raw3850; decide +kernel
    rw [ha]
    exact (canonical3850 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA63 + sourceB63) sourceC63) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA63 + sourceB63) sourceC63) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA63 sourceB63 sourceC63 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA63 sourceB63 sourceC63
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm63, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
