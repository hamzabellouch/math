import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical112
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical113
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical114
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical115

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA864 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB864 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC864 : Charge := ![2, 1, -1, -2, 0, 0]
def sourceForm864 : Integer.Sparse Master := [(Sum.inr 2474, 1), (Sum.inr 2475, 1), (Sum.inr 2481, 1), (Sum.inr 2494, 1), (Sum.inr 2714, 1), (Sum.inr 3803, 1), (Sum.inr 4092, -1)]

theorem sourceEq864 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm864 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA864 + difference 0 0) (sourceB864 + difference 0 0) sourceC864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA864 + difference 0 0) (sourceB864 + difference 0 0) sourceC864) = raw14437 := by
      apply Matrix.ext; unfold tripleCharges sourceA864 sourceB864 sourceC864 difference raw14437; decide +kernel
    rw [ha]
    exact (canonical14437 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA864 + difference 1 0) (sourceB864 + difference 0 1) sourceC864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA864 + difference 1 0) (sourceB864 + difference 0 1) sourceC864) = raw14444 := by
      apply Matrix.ext; unfold tripleCharges sourceA864 sourceB864 sourceC864 difference raw14444; decide +kernel
    rw [ha]
    exact (canonical14444 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA864 + difference 2 0) (sourceB864 + difference 0 2) sourceC864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA864 + difference 2 0) (sourceB864 + difference 0 2) sourceC864) = raw14445 := by
      apply Matrix.ext; unfold tripleCharges sourceA864 sourceB864 sourceC864 difference raw14445; decide +kernel
    rw [ha]
    exact (canonical14445 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA864 + difference 3 0) (sourceB864 + difference 0 3) sourceC864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA864 + difference 3 0) (sourceB864 + difference 0 3) sourceC864) = raw14446 := by
      apply Matrix.ext; unfold tripleCharges sourceA864 sourceB864 sourceC864 difference raw14446; decide +kernel
    rw [ha]
    exact (canonical14446 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA864 + difference 4 0) (sourceB864 + difference 0 4) sourceC864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2475) := by
    have ha : (tripleCharges (sourceA864 + difference 4 0) (sourceB864 + difference 0 4) sourceC864) = raw14447 := by
      apply Matrix.ext; unfold tripleCharges sourceA864 sourceB864 sourceC864 difference raw14447; decide +kernel
    rw [ha]
    exact (canonical14447 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA864 + difference 5 0) (sourceB864 + difference 0 5) sourceC864) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2474) := by
    have ha : (tripleCharges (sourceA864 + difference 5 0) (sourceB864 + difference 0 5) sourceC864) = raw14448 := by
      apply Matrix.ext; unfold tripleCharges sourceA864 sourceB864 sourceC864 difference raw14448; decide +kernel
    rw [ha]
    exact (canonical14448 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA864 + sourceB864) sourceC864) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA864 + sourceB864) sourceC864) = raw14443 := by
      apply Matrix.ext; unfold doubleCharges sourceA864 sourceB864 sourceC864 raw14443; decide +kernel
    rw [ha]
    exact (canonical14443 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA864 sourceB864 sourceC864
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm864, Integer.Sparse.eval]
  linarith only [hs]

def sourceA865 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB865 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC865 : Charge := ![2, 1, -1, -2, 0, 0]
def sourceForm865 : Integer.Sparse Master := [(Sum.inr 2494, 1), (Sum.inr 2714, 1), (Sum.inr 3698, 1), (Sum.inr 3803, 1), (Sum.inr 3812, 1), (Sum.inr 3814, 1), (Sum.inr 4092, -1)]

theorem sourceEq865 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm865 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA865 + difference 1 0) (sourceB865 + difference 0 1) sourceC865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA865 + difference 1 0) (sourceB865 + difference 0 1) sourceC865) = raw14444 := by
      apply Matrix.ext; unfold tripleCharges sourceA865 sourceB865 sourceC865 difference raw14444; decide +kernel
    rw [ha]
    exact (canonical14444 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA865 + difference 1 1) (sourceB865 + difference 1 1) sourceC865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA865 + difference 1 1) (sourceB865 + difference 1 1) sourceC865) = raw14437 := by
      apply Matrix.ext; unfold tripleCharges sourceA865 sourceB865 sourceC865 difference raw14437; decide +kernel
    rw [ha]
    exact (canonical14437 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA865 + difference 1 2) (sourceB865 + difference 2 1) sourceC865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3698) := by
    have ha : (tripleCharges (sourceA865 + difference 1 2) (sourceB865 + difference 2 1) sourceC865) = raw14449 := by
      apply Matrix.ext; unfold tripleCharges sourceA865 sourceB865 sourceC865 difference raw14449; decide +kernel
    rw [ha]
    exact (canonical14449 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA865 + difference 1 3) (sourceB865 + difference 3 1) sourceC865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA865 + difference 1 3) (sourceB865 + difference 3 1) sourceC865) = raw14450 := by
      apply Matrix.ext; unfold tripleCharges sourceA865 sourceB865 sourceC865 difference raw14450; decide +kernel
    rw [ha]
    exact (canonical14450 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA865 + difference 1 4) (sourceB865 + difference 4 1) sourceC865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA865 + difference 1 4) (sourceB865 + difference 4 1) sourceC865) = raw14451 := by
      apply Matrix.ext; unfold tripleCharges sourceA865 sourceB865 sourceC865 difference raw14451; decide +kernel
    rw [ha]
    exact (canonical14451 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA865 + difference 1 5) (sourceB865 + difference 5 1) sourceC865) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA865 + difference 1 5) (sourceB865 + difference 5 1) sourceC865) = raw14452 := by
      apply Matrix.ext; unfold tripleCharges sourceA865 sourceB865 sourceC865 difference raw14452; decide +kernel
    rw [ha]
    exact (canonical14452 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA865 + sourceB865) sourceC865) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA865 + sourceB865) sourceC865) = raw14443 := by
      apply Matrix.ext; unfold doubleCharges sourceA865 sourceB865 sourceC865 raw14443; decide +kernel
    rw [ha]
    exact (canonical14443 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA865 sourceB865 sourceC865
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm865, Integer.Sparse.eval]
  linarith only [hs]

def sourceA866 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB866 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC866 : Charge := ![2, 1, -1, -2, 0, 0]
def sourceForm866 : Integer.Sparse Master := [(Sum.inr 3217, 1), (Sum.inr 3686, 1), (Sum.inr 3691, 1), (Sum.inr 3698, 1), (Sum.inr 3788, 1), (Sum.inr 3803, 1), (Sum.inr 4092, -1)]

theorem sourceEq866 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm866 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA866 + difference 0 1) (sourceB866 + difference 1 0) sourceC866) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA866 + difference 0 1) (sourceB866 + difference 1 0) sourceC866) = raw14438 := by
      apply Matrix.ext; unfold tripleCharges sourceA866 sourceB866 sourceC866 difference raw14438; decide +kernel
    rw [ha]
    exact (canonical14438 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA866 + difference 1 1) (sourceB866 + difference 1 1) sourceC866) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA866 + difference 1 1) (sourceB866 + difference 1 1) sourceC866) = raw14437 := by
      apply Matrix.ext; unfold tripleCharges sourceA866 sourceB866 sourceC866 difference raw14437; decide +kernel
    rw [ha]
    exact (canonical14437 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA866 + difference 2 1) (sourceB866 + difference 1 2) sourceC866) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3698) := by
    have ha : (tripleCharges (sourceA866 + difference 2 1) (sourceB866 + difference 1 2) sourceC866) = raw14453 := by
      apply Matrix.ext; unfold tripleCharges sourceA866 sourceB866 sourceC866 difference raw14453; decide +kernel
    rw [ha]
    exact (canonical14453 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA866 + difference 3 1) (sourceB866 + difference 1 3) sourceC866) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA866 + difference 3 1) (sourceB866 + difference 1 3) sourceC866) = raw14454 := by
      apply Matrix.ext; unfold tripleCharges sourceA866 sourceB866 sourceC866 difference raw14454; decide +kernel
    rw [ha]
    exact (canonical14454 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA866 + difference 4 1) (sourceB866 + difference 1 4) sourceC866) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3686) := by
    have ha : (tripleCharges (sourceA866 + difference 4 1) (sourceB866 + difference 1 4) sourceC866) = raw14455 := by
      apply Matrix.ext; unfold tripleCharges sourceA866 sourceB866 sourceC866 difference raw14455; decide +kernel
    rw [ha]
    exact (canonical14455 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA866 + difference 5 1) (sourceB866 + difference 1 5) sourceC866) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3217) := by
    have ha : (tripleCharges (sourceA866 + difference 5 1) (sourceB866 + difference 1 5) sourceC866) = raw14456 := by
      apply Matrix.ext; unfold tripleCharges sourceA866 sourceB866 sourceC866 difference raw14456; decide +kernel
    rw [ha]
    exact (canonical14456 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA866 + sourceB866) sourceC866) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA866 + sourceB866) sourceC866) = raw14443 := by
      apply Matrix.ext; unfold doubleCharges sourceA866 sourceB866 sourceC866 raw14443; decide +kernel
    rw [ha]
    exact (canonical14443 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA866 sourceB866 sourceC866
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm866, Integer.Sparse.eval]
  linarith only [hs]

def sourceA867 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB867 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceC867 : Charge := ![2, 1, -1, -2, 0, 0]
def sourceForm867 : Integer.Sparse Master := [(Sum.inr 2475, 2), (Sum.inr 3686, 2), (Sum.inr 3803, 2), (Sum.inr 4092, -1)]

theorem sourceEq867 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm867 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA867 + difference 4 0) (sourceB867 + difference 0 4) sourceC867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2475) := by
    have ha : (tripleCharges (sourceA867 + difference 4 0) (sourceB867 + difference 0 4) sourceC867) = raw14447 := by
      apply Matrix.ext; unfold tripleCharges sourceA867 sourceB867 sourceC867 difference raw14447; decide +kernel
    rw [ha]
    exact (canonical14447 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA867 + difference 4 1) (sourceB867 + difference 1 4) sourceC867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3686) := by
    have ha : (tripleCharges (sourceA867 + difference 4 1) (sourceB867 + difference 1 4) sourceC867) = raw14455 := by
      apply Matrix.ext; unfold tripleCharges sourceA867 sourceB867 sourceC867 difference raw14455; decide +kernel
    rw [ha]
    exact (canonical14455 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA867 + difference 4 2) (sourceB867 + difference 2 4) sourceC867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3686) := by
    have ha : (tripleCharges (sourceA867 + difference 4 2) (sourceB867 + difference 2 4) sourceC867) = raw14457 := by
      apply Matrix.ext; unfold tripleCharges sourceA867 sourceB867 sourceC867 difference raw14457; decide +kernel
    rw [ha]
    exact (canonical14457 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA867 + difference 4 3) (sourceB867 + difference 3 4) sourceC867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2475) := by
    have ha : (tripleCharges (sourceA867 + difference 4 3) (sourceB867 + difference 3 4) sourceC867) = raw14458 := by
      apply Matrix.ext; unfold tripleCharges sourceA867 sourceB867 sourceC867 difference raw14458; decide +kernel
    rw [ha]
    exact (canonical14458 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA867 + difference 4 4) (sourceB867 + difference 4 4) sourceC867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA867 + difference 4 4) (sourceB867 + difference 4 4) sourceC867) = raw14437 := by
      apply Matrix.ext; unfold tripleCharges sourceA867 sourceB867 sourceC867 difference raw14437; decide +kernel
    rw [ha]
    exact (canonical14437 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA867 + difference 4 5) (sourceB867 + difference 5 4) sourceC867) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA867 + difference 4 5) (sourceB867 + difference 5 4) sourceC867) = raw14459 := by
      apply Matrix.ext; unfold tripleCharges sourceA867 sourceB867 sourceC867 difference raw14459; decide +kernel
    rw [ha]
    exact (canonical14459 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA867 + sourceB867) sourceC867) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA867 + sourceB867) sourceC867) = raw14443 := by
      apply Matrix.ext; unfold doubleCharges sourceA867 sourceB867 sourceC867 raw14443; decide +kernel
    rw [ha]
    exact (canonical14443 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA867 sourceB867 sourceC867
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm867, Integer.Sparse.eval]
  linarith only [hs]

def sourceA868 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB868 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC868 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceForm868 : Integer.Sparse Master := [(Sum.inr 4812, 1), (Sum.inr 4813, 1), (Sum.inr 4816, 1), (Sum.inr 4824, 1), (Sum.inr 4852, 1), (Sum.inr 5129, 1), (Sum.inr 5138, 1), (Sum.inr 5146, 1), (Sum.inr 5260, 1), (Sum.inr 5357, 1), (Sum.inr 5358, 1), (Sum.inr 5360, 1), (Sum.inr 5376, 1), (Sum.inr 5378, 1), (Sum.inr 5381, 2), (Sum.inr 5397, 2), (Sum.inr 5411, 1), (Sum.inr 5412, 1), (Sum.inr 5420, 1), (Sum.inr 5421, 1), (Sum.inr 5423, 1), (Sum.inr 5424, 1), (Sum.inr 5426, 1), (Sum.inr 5430, 1), (Sum.inr 5434, 1), (Sum.inr 5436, 1), (Sum.inr 5445, 1), (Sum.inr 5477, 1)]

theorem sourceEq868 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm868 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA868 + difference 0 1) (sourceB868 + difference 1 0) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5420) := by
    have ha : (tripleCharges (sourceA868 + difference 0 1) (sourceB868 + difference 1 0) sourceC868) = raw14460 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14460; decide +kernel
    rw [ha]
    exact (canonical14460 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA868 + difference 0 2) (sourceB868 + difference 2 0) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA868 + difference 0 2) (sourceB868 + difference 2 0) sourceC868) = raw14461 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14461; decide +kernel
    rw [ha]
    exact (canonical14461 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA868 + difference 0 3) (sourceB868 + difference 3 0) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA868 + difference 0 3) (sourceB868 + difference 3 0) sourceC868) = raw14462 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14462; decide +kernel
    rw [ha]
    exact (canonical14462 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA868 + difference 0 4) (sourceB868 + difference 4 0) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA868 + difference 0 4) (sourceB868 + difference 4 0) sourceC868) = raw14463 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14463; decide +kernel
    rw [ha]
    exact (canonical14463 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA868 + difference 0 5) (sourceB868 + difference 5 0) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5477) := by
    have ha : (tripleCharges (sourceA868 + difference 0 5) (sourceB868 + difference 5 0) sourceC868) = raw14464 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14464; decide +kernel
    rw [ha]
    exact (canonical14464 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA868 + difference 1 0) (sourceB868 + difference 0 1) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA868 + difference 1 0) (sourceB868 + difference 0 1) sourceC868) = raw14465 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14465; decide +kernel
    rw [ha]
    exact (canonical14465 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA868 + difference 1 2) (sourceB868 + difference 2 1) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA868 + difference 1 2) (sourceB868 + difference 2 1) sourceC868) = raw14466 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14466; decide +kernel
    rw [ha]
    exact (canonical14466 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA868 + difference 1 3) (sourceB868 + difference 3 1) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA868 + difference 1 3) (sourceB868 + difference 3 1) sourceC868) = raw14467 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14467; decide +kernel
    rw [ha]
    exact (canonical14467 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA868 + difference 1 4) (sourceB868 + difference 4 1) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA868 + difference 1 4) (sourceB868 + difference 4 1) sourceC868) = raw14468 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14468; decide +kernel
    rw [ha]
    exact (canonical14468 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA868 + difference 1 5) (sourceB868 + difference 5 1) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA868 + difference 1 5) (sourceB868 + difference 5 1) sourceC868) = raw14469 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14469; decide +kernel
    rw [ha]
    exact (canonical14469 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA868 + difference 2 0) (sourceB868 + difference 0 2) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5146) := by
    have ha : (tripleCharges (sourceA868 + difference 2 0) (sourceB868 + difference 0 2) sourceC868) = raw14470 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14470; decide +kernel
    rw [ha]
    exact (canonical14470 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA868 + difference 2 1) (sourceB868 + difference 1 2) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5357) := by
    have ha : (tripleCharges (sourceA868 + difference 2 1) (sourceB868 + difference 1 2) sourceC868) = raw14471 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14471; decide +kernel
    rw [ha]
    exact (canonical14471 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA868 + difference 2 3) (sourceB868 + difference 3 2) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5358) := by
    have ha : (tripleCharges (sourceA868 + difference 2 3) (sourceB868 + difference 3 2) sourceC868) = raw14472 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14472; decide +kernel
    rw [ha]
    exact (canonical14472 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA868 + difference 2 4) (sourceB868 + difference 4 2) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA868 + difference 2 4) (sourceB868 + difference 4 2) sourceC868) = raw14473 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14473; decide +kernel
    rw [ha]
    exact (canonical14473 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA868 + difference 2 5) (sourceB868 + difference 5 2) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA868 + difference 2 5) (sourceB868 + difference 5 2) sourceC868) = raw14474 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14474; decide +kernel
    rw [ha]
    exact (canonical14474 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA868 + difference 3 0) (sourceB868 + difference 0 3) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5138) := by
    have ha : (tripleCharges (sourceA868 + difference 3 0) (sourceB868 + difference 0 3) sourceC868) = raw14475 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14475; decide +kernel
    rw [ha]
    exact (canonical14475 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA868 + difference 3 1) (sourceB868 + difference 1 3) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA868 + difference 3 1) (sourceB868 + difference 1 3) sourceC868) = raw14476 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14476; decide +kernel
    rw [ha]
    exact (canonical14476 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA868 + difference 3 2) (sourceB868 + difference 2 3) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA868 + difference 3 2) (sourceB868 + difference 2 3) sourceC868) = raw14477 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14477; decide +kernel
    rw [ha]
    exact (canonical14477 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA868 + difference 3 4) (sourceB868 + difference 4 3) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5426) := by
    have ha : (tripleCharges (sourceA868 + difference 3 4) (sourceB868 + difference 4 3) sourceC868) = raw14478 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14478; decide +kernel
    rw [ha]
    exact (canonical14478 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA868 + difference 3 5) (sourceB868 + difference 5 3) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA868 + difference 3 5) (sourceB868 + difference 5 3) sourceC868) = raw14479 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14479; decide +kernel
    rw [ha]
    exact (canonical14479 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA868 + difference 4 0) (sourceB868 + difference 0 4) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5129) := by
    have ha : (tripleCharges (sourceA868 + difference 4 0) (sourceB868 + difference 0 4) sourceC868) = raw14480 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14480; decide +kernel
    rw [ha]
    exact (canonical14480 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA868 + difference 4 1) (sourceB868 + difference 1 4) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5376) := by
    have ha : (tripleCharges (sourceA868 + difference 4 1) (sourceB868 + difference 1 4) sourceC868) = raw14481 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14481; decide +kernel
    rw [ha]
    exact (canonical14481 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA868 + difference 4 2) (sourceB868 + difference 2 4) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5378) := by
    have ha : (tripleCharges (sourceA868 + difference 4 2) (sourceB868 + difference 2 4) sourceC868) = raw14482 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14482; decide +kernel
    rw [ha]
    exact (canonical14482 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA868 + difference 4 3) (sourceB868 + difference 3 4) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5381) := by
    have ha : (tripleCharges (sourceA868 + difference 4 3) (sourceB868 + difference 3 4) sourceC868) = raw14483 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14483; decide +kernel
    rw [ha]
    exact (canonical14483 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA868 + difference 4 5) (sourceB868 + difference 5 4) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5423) := by
    have ha : (tripleCharges (sourceA868 + difference 4 5) (sourceB868 + difference 5 4) sourceC868) = raw14484 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14484; decide +kernel
    rw [ha]
    exact (canonical14484 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA868 + difference 5 0) (sourceB868 + difference 0 5) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4824) := by
    have ha : (tripleCharges (sourceA868 + difference 5 0) (sourceB868 + difference 0 5) sourceC868) = raw14485 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14485; decide +kernel
    rw [ha]
    exact (canonical14485 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA868 + difference 5 1) (sourceB868 + difference 1 5) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4812) := by
    have ha : (tripleCharges (sourceA868 + difference 5 1) (sourceB868 + difference 1 5) sourceC868) = raw14486 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14486; decide +kernel
    rw [ha]
    exact (canonical14486 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA868 + difference 5 2) (sourceB868 + difference 2 5) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA868 + difference 5 2) (sourceB868 + difference 2 5) sourceC868) = raw14487 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14487; decide +kernel
    rw [ha]
    exact (canonical14487 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA868 + difference 5 3) (sourceB868 + difference 3 5) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4813) := by
    have ha : (tripleCharges (sourceA868 + difference 5 3) (sourceB868 + difference 3 5) sourceC868) = raw14488 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14488; decide +kernel
    rw [ha]
    exact (canonical14488 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA868 + difference 5 4) (sourceB868 + difference 4 5) sourceC868) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA868 + difference 5 4) (sourceB868 + difference 4 5) sourceC868) = raw14489 := by
      apply Matrix.ext; unfold tripleCharges sourceA868 sourceB868 sourceC868 difference raw14489; decide +kernel
    rw [ha]
    exact (canonical14489 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA868 sourceB868 sourceC868
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm868, Integer.Sparse.eval]
  linarith only [hs]

def sourceA869 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB869 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC869 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceForm869 : Integer.Sparse Master := [(Sum.inr 2071, 1), (Sum.inr 2072, 1), (Sum.inr 2078, 1), (Sum.inr 2089, 1), (Sum.inr 2196, 1), (Sum.inr 2916, 1), (Sum.inr 2922, 1), (Sum.inr 2933, 1), (Sum.inr 3086, 1), (Sum.inr 3715, 1), (Sum.inr 3718, 1), (Sum.inr 3722, 1), (Sum.inr 3723, 1), (Sum.inr 3727, 1), (Sum.inr 3752, 1), (Sum.inr 3762, 1), (Sum.inr 3796, 1), (Sum.inr 3814, 1), (Sum.inr 3830, 1), (Sum.inr 3841, 1), (Sum.inr 3870, 1), (Sum.inr 3873, 1), (Sum.inr 3877, 1), (Sum.inr 3880, 1), (Sum.inr 3883, 1), (Sum.inr 3971, 1), (Sum.inr 3972, 1), (Sum.inr 3982, 1), (Sum.inr 3990, 1), (Sum.inr 4032, 1)]

theorem sourceEq869 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm869 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA869 + difference 0 1) (sourceB869 + difference 1 0) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3870) := by
    have ha : (tripleCharges (sourceA869 + difference 0 1) (sourceB869 + difference 1 0) sourceC869) = raw14490 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14490; decide +kernel
    rw [ha]
    exact (canonical14490 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA869 + difference 0 2) (sourceB869 + difference 2 0) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA869 + difference 0 2) (sourceB869 + difference 2 0) sourceC869) = raw14491 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14491; decide +kernel
    rw [ha]
    exact (canonical14491 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA869 + difference 0 3) (sourceB869 + difference 3 0) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA869 + difference 0 3) (sourceB869 + difference 3 0) sourceC869) = raw14492 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14492; decide +kernel
    rw [ha]
    exact (canonical14492 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA869 + difference 0 4) (sourceB869 + difference 4 0) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA869 + difference 0 4) (sourceB869 + difference 4 0) sourceC869) = raw14493 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14493; decide +kernel
    rw [ha]
    exact (canonical14493 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA869 + difference 0 5) (sourceB869 + difference 5 0) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3971) := by
    have ha : (tripleCharges (sourceA869 + difference 0 5) (sourceB869 + difference 5 0) sourceC869) = raw14494 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14494; decide +kernel
    rw [ha]
    exact (canonical14494 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA869 + difference 1 0) (sourceB869 + difference 0 1) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA869 + difference 1 0) (sourceB869 + difference 0 1) sourceC869) = raw14495 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14495; decide +kernel
    rw [ha]
    exact (canonical14495 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA869 + difference 1 2) (sourceB869 + difference 2 1) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA869 + difference 1 2) (sourceB869 + difference 2 1) sourceC869) = raw14496 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14496; decide +kernel
    rw [ha]
    exact (canonical14496 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA869 + difference 1 3) (sourceB869 + difference 3 1) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA869 + difference 1 3) (sourceB869 + difference 3 1) sourceC869) = raw14497 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14497; decide +kernel
    rw [ha]
    exact (canonical14497 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA869 + difference 1 4) (sourceB869 + difference 4 1) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA869 + difference 1 4) (sourceB869 + difference 4 1) sourceC869) = raw14498 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14498; decide +kernel
    rw [ha]
    exact (canonical14498 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA869 + difference 1 5) (sourceB869 + difference 5 1) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA869 + difference 1 5) (sourceB869 + difference 5 1) sourceC869) = raw14499 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14499; decide +kernel
    rw [ha]
    exact (canonical14499 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA869 + difference 2 0) (sourceB869 + difference 0 2) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2922) := by
    have ha : (tripleCharges (sourceA869 + difference 2 0) (sourceB869 + difference 0 2) sourceC869) = raw14500 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14500; decide +kernel
    rw [ha]
    exact (canonical14500 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA869 + difference 2 1) (sourceB869 + difference 1 2) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3718) := by
    have ha : (tripleCharges (sourceA869 + difference 2 1) (sourceB869 + difference 1 2) sourceC869) = raw14501 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14501; decide +kernel
    rw [ha]
    exact (canonical14501 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA869 + difference 2 3) (sourceB869 + difference 3 2) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3752) := by
    have ha : (tripleCharges (sourceA869 + difference 2 3) (sourceB869 + difference 3 2) sourceC869) = raw14502 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14502; decide +kernel
    rw [ha]
    exact (canonical14502 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA869 + difference 2 4) (sourceB869 + difference 4 2) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA869 + difference 2 4) (sourceB869 + difference 4 2) sourceC869) = raw14503 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14503; decide +kernel
    rw [ha]
    exact (canonical14503 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA869 + difference 2 5) (sourceB869 + difference 5 2) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA869 + difference 2 5) (sourceB869 + difference 5 2) sourceC869) = raw14504 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14504; decide +kernel
    rw [ha]
    exact (canonical14504 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA869 + difference 3 0) (sourceB869 + difference 0 3) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2933) := by
    have ha : (tripleCharges (sourceA869 + difference 3 0) (sourceB869 + difference 0 3) sourceC869) = raw14505 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14505; decide +kernel
    rw [ha]
    exact (canonical14505 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA869 + difference 3 1) (sourceB869 + difference 1 3) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3723) := by
    have ha : (tripleCharges (sourceA869 + difference 3 1) (sourceB869 + difference 1 3) sourceC869) = raw14506 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14506; decide +kernel
    rw [ha]
    exact (canonical14506 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA869 + difference 3 2) (sourceB869 + difference 2 3) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3830) := by
    have ha : (tripleCharges (sourceA869 + difference 3 2) (sourceB869 + difference 2 3) sourceC869) = raw14507 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14507; decide +kernel
    rw [ha]
    exact (canonical14507 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA869 + difference 3 4) (sourceB869 + difference 4 3) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3841) := by
    have ha : (tripleCharges (sourceA869 + difference 3 4) (sourceB869 + difference 4 3) sourceC869) = raw14508 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14508; decide +kernel
    rw [ha]
    exact (canonical14508 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA869 + difference 3 5) (sourceB869 + difference 5 3) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA869 + difference 3 5) (sourceB869 + difference 5 3) sourceC869) = raw14509 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14509; decide +kernel
    rw [ha]
    exact (canonical14509 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA869 + difference 4 0) (sourceB869 + difference 0 4) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA869 + difference 4 0) (sourceB869 + difference 0 4) sourceC869) = raw14510 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14510; decide +kernel
    rw [ha]
    exact (canonical14510 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA869 + difference 4 1) (sourceB869 + difference 1 4) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3715) := by
    have ha : (tripleCharges (sourceA869 + difference 4 1) (sourceB869 + difference 1 4) sourceC869) = raw14511 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14511; decide +kernel
    rw [ha]
    exact (canonical14511 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA869 + difference 4 2) (sourceB869 + difference 2 4) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3727) := by
    have ha : (tripleCharges (sourceA869 + difference 4 2) (sourceB869 + difference 2 4) sourceC869) = raw14512 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14512; decide +kernel
    rw [ha]
    exact (canonical14512 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA869 + difference 4 3) (sourceB869 + difference 3 4) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3722) := by
    have ha : (tripleCharges (sourceA869 + difference 4 3) (sourceB869 + difference 3 4) sourceC869) = raw14513 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14513; decide +kernel
    rw [ha]
    exact (canonical14513 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA869 + difference 4 5) (sourceB869 + difference 5 4) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4032) := by
    have ha : (tripleCharges (sourceA869 + difference 4 5) (sourceB869 + difference 5 4) sourceC869) = raw14514 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14514; decide +kernel
    rw [ha]
    exact (canonical14514 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA869 + difference 5 0) (sourceB869 + difference 0 5) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2071) := by
    have ha : (tripleCharges (sourceA869 + difference 5 0) (sourceB869 + difference 0 5) sourceC869) = raw14515 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14515; decide +kernel
    rw [ha]
    exact (canonical14515 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA869 + difference 5 1) (sourceB869 + difference 1 5) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2072) := by
    have ha : (tripleCharges (sourceA869 + difference 5 1) (sourceB869 + difference 1 5) sourceC869) = raw14516 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14516; decide +kernel
    rw [ha]
    exact (canonical14516 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA869 + difference 5 2) (sourceB869 + difference 2 5) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA869 + difference 5 2) (sourceB869 + difference 2 5) sourceC869) = raw14517 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14517; decide +kernel
    rw [ha]
    exact (canonical14517 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA869 + difference 5 3) (sourceB869 + difference 3 5) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2078) := by
    have ha : (tripleCharges (sourceA869 + difference 5 3) (sourceB869 + difference 3 5) sourceC869) = raw14518 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14518; decide +kernel
    rw [ha]
    exact (canonical14518 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA869 + difference 5 4) (sourceB869 + difference 4 5) sourceC869) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA869 + difference 5 4) (sourceB869 + difference 4 5) sourceC869) = raw14519 := by
      apply Matrix.ext; unfold tripleCharges sourceA869 sourceB869 sourceC869 difference raw14519; decide +kernel
    rw [ha]
    exact (canonical14519 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA869 sourceB869 sourceC869
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm869, Integer.Sparse.eval]
  linarith only [hs]

def sourceA870 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB870 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC870 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceForm870 : Integer.Sparse Master := [(Sum.inr 2030, 1), (Sum.inr 2031, 1), (Sum.inr 2034, 1), (Sum.inr 2043, 1), (Sum.inr 2250, 1), (Sum.inr 3516, 1), (Sum.inr 3517, 1), (Sum.inr 3540, 1), (Sum.inr 3560, 1), (Sum.inr 3695, 1), (Sum.inr 3696, 1), (Sum.inr 3698, 1), (Sum.inr 3795, 1), (Sum.inr 3796, 1), (Sum.inr 3813, 1), (Sum.inr 3826, 1), (Sum.inr 3827, 1), (Sum.inr 3830, 1), (Sum.inr 3833, 1), (Sum.inr 3834, 2), (Sum.inr 3837, 1), (Sum.inr 3838, 1), (Sum.inr 3841, 1), (Sum.inr 3852, 1), (Sum.inr 3854, 1), (Sum.inr 3856, 1), (Sum.inr 3871, 1), (Sum.inr 3880, 1), (Sum.inr 3989, 1)]

theorem sourceEq870 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm870 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA870 + difference 0 1) (sourceB870 + difference 1 0) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3826) := by
    have ha : (tripleCharges (sourceA870 + difference 0 1) (sourceB870 + difference 1 0) sourceC870) = raw14520 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14520; decide +kernel
    rw [ha]
    exact (canonical14520 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA870 + difference 0 2) (sourceB870 + difference 2 0) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA870 + difference 0 2) (sourceB870 + difference 2 0) sourceC870) = raw14521 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14521; decide +kernel
    rw [ha]
    exact (canonical14521 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA870 + difference 0 3) (sourceB870 + difference 3 0) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3827) := by
    have ha : (tripleCharges (sourceA870 + difference 0 3) (sourceB870 + difference 3 0) sourceC870) = raw14522 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14522; decide +kernel
    rw [ha]
    exact (canonical14522 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA870 + difference 0 4) (sourceB870 + difference 4 0) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3830) := by
    have ha : (tripleCharges (sourceA870 + difference 0 4) (sourceB870 + difference 4 0) sourceC870) = raw14523 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14523; decide +kernel
    rw [ha]
    exact (canonical14523 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA870 + difference 0 5) (sourceB870 + difference 5 0) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3989) := by
    have ha : (tripleCharges (sourceA870 + difference 0 5) (sourceB870 + difference 5 0) sourceC870) = raw14524 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14524; decide +kernel
    rw [ha]
    exact (canonical14524 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA870 + difference 1 0) (sourceB870 + difference 0 1) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA870 + difference 1 0) (sourceB870 + difference 0 1) sourceC870) = raw14525 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14525; decide +kernel
    rw [ha]
    exact (canonical14525 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA870 + difference 1 2) (sourceB870 + difference 2 1) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA870 + difference 1 2) (sourceB870 + difference 2 1) sourceC870) = raw14526 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14526; decide +kernel
    rw [ha]
    exact (canonical14526 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA870 + difference 1 3) (sourceB870 + difference 3 1) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA870 + difference 1 3) (sourceB870 + difference 3 1) sourceC870) = raw14527 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14527; decide +kernel
    rw [ha]
    exact (canonical14527 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA870 + difference 1 4) (sourceB870 + difference 4 1) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3856) := by
    have ha : (tripleCharges (sourceA870 + difference 1 4) (sourceB870 + difference 4 1) sourceC870) = raw14528 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14528; decide +kernel
    rw [ha]
    exact (canonical14528 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA870 + difference 1 5) (sourceB870 + difference 5 1) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA870 + difference 1 5) (sourceB870 + difference 5 1) sourceC870) = raw14529 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14529; decide +kernel
    rw [ha]
    exact (canonical14529 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA870 + difference 2 0) (sourceB870 + difference 0 2) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3560) := by
    have ha : (tripleCharges (sourceA870 + difference 2 0) (sourceB870 + difference 0 2) sourceC870) = raw14530 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14530; decide +kernel
    rw [ha]
    exact (canonical14530 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA870 + difference 2 1) (sourceB870 + difference 1 2) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3695) := by
    have ha : (tripleCharges (sourceA870 + difference 2 1) (sourceB870 + difference 1 2) sourceC870) = raw14531 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14531; decide +kernel
    rw [ha]
    exact (canonical14531 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA870 + difference 2 3) (sourceB870 + difference 3 2) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3696) := by
    have ha : (tripleCharges (sourceA870 + difference 2 3) (sourceB870 + difference 3 2) sourceC870) = raw14532 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14532; decide +kernel
    rw [ha]
    exact (canonical14532 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA870 + difference 2 4) (sourceB870 + difference 4 2) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3698) := by
    have ha : (tripleCharges (sourceA870 + difference 2 4) (sourceB870 + difference 4 2) sourceC870) = raw14533 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14533; decide +kernel
    rw [ha]
    exact (canonical14533 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA870 + difference 2 5) (sourceB870 + difference 5 2) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA870 + difference 2 5) (sourceB870 + difference 5 2) sourceC870) = raw14534 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14534; decide +kernel
    rw [ha]
    exact (canonical14534 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA870 + difference 3 0) (sourceB870 + difference 0 3) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA870 + difference 3 0) (sourceB870 + difference 0 3) sourceC870) = raw14535 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14535; decide +kernel
    rw [ha]
    exact (canonical14535 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA870 + difference 3 1) (sourceB870 + difference 1 3) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA870 + difference 3 1) (sourceB870 + difference 1 3) sourceC870) = raw14536 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14536; decide +kernel
    rw [ha]
    exact (canonical14536 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA870 + difference 3 2) (sourceB870 + difference 2 3) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA870 + difference 3 2) (sourceB870 + difference 2 3) sourceC870) = raw14537 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14537; decide +kernel
    rw [ha]
    exact (canonical14537 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA870 + difference 3 4) (sourceB870 + difference 4 3) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3841) := by
    have ha : (tripleCharges (sourceA870 + difference 3 4) (sourceB870 + difference 4 3) sourceC870) = raw14538 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14538; decide +kernel
    rw [ha]
    exact (canonical14538 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA870 + difference 3 5) (sourceB870 + difference 5 3) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA870 + difference 3 5) (sourceB870 + difference 5 3) sourceC870) = raw14539 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14539; decide +kernel
    rw [ha]
    exact (canonical14539 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA870 + difference 4 0) (sourceB870 + difference 0 4) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA870 + difference 4 0) (sourceB870 + difference 0 4) sourceC870) = raw14540 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14540; decide +kernel
    rw [ha]
    exact (canonical14540 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA870 + difference 4 1) (sourceB870 + difference 1 4) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3833) := by
    have ha : (tripleCharges (sourceA870 + difference 4 1) (sourceB870 + difference 1 4) sourceC870) = raw14541 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14541; decide +kernel
    rw [ha]
    exact (canonical14541 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA870 + difference 4 2) (sourceB870 + difference 2 4) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3795) := by
    have ha : (tripleCharges (sourceA870 + difference 4 2) (sourceB870 + difference 2 4) sourceC870) = raw14542 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14542; decide +kernel
    rw [ha]
    exact (canonical14542 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA870 + difference 4 3) (sourceB870 + difference 3 4) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3834) := by
    have ha : (tripleCharges (sourceA870 + difference 4 3) (sourceB870 + difference 3 4) sourceC870) = raw14543 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14543; decide +kernel
    rw [ha]
    exact (canonical14543 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA870 + difference 4 5) (sourceB870 + difference 5 4) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3837) := by
    have ha : (tripleCharges (sourceA870 + difference 4 5) (sourceB870 + difference 5 4) sourceC870) = raw14544 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14544; decide +kernel
    rw [ha]
    exact (canonical14544 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA870 + difference 5 0) (sourceB870 + difference 0 5) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2043) := by
    have ha : (tripleCharges (sourceA870 + difference 5 0) (sourceB870 + difference 0 5) sourceC870) = raw14545 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14545; decide +kernel
    rw [ha]
    exact (canonical14545 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA870 + difference 5 1) (sourceB870 + difference 1 5) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2030) := by
    have ha : (tripleCharges (sourceA870 + difference 5 1) (sourceB870 + difference 1 5) sourceC870) = raw14546 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14546; decide +kernel
    rw [ha]
    exact (canonical14546 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA870 + difference 5 2) (sourceB870 + difference 2 5) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA870 + difference 5 2) (sourceB870 + difference 2 5) sourceC870) = raw14547 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14547; decide +kernel
    rw [ha]
    exact (canonical14547 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA870 + difference 5 3) (sourceB870 + difference 3 5) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2031) := by
    have ha : (tripleCharges (sourceA870 + difference 5 3) (sourceB870 + difference 3 5) sourceC870) = raw14548 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14548; decide +kernel
    rw [ha]
    exact (canonical14548 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA870 + difference 5 4) (sourceB870 + difference 4 5) sourceC870) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2034) := by
    have ha : (tripleCharges (sourceA870 + difference 5 4) (sourceB870 + difference 4 5) sourceC870) = raw14549 := by
      apply Matrix.ext; unfold tripleCharges sourceA870 sourceB870 sourceC870 difference raw14549; decide +kernel
    rw [ha]
    exact (canonical14549 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA870 sourceB870 sourceC870
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm870, Integer.Sparse.eval]
  linarith only [hs]

def sourceA871 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB871 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC871 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceForm871 : Integer.Sparse Master := [(Sum.inr 3782, 1), (Sum.inr 3839, 1), (Sum.inr 3946, 1), (Sum.inr 4022, 1), (Sum.inr 4024, 1), (Sum.inr 4044, 1), (Sum.inr 4092, -1)]

theorem sourceEq871 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm871 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA871 + difference 0 0) (sourceB871 + difference 0 0) sourceC871) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA871 + difference 0 0) (sourceB871 + difference 0 0) sourceC871) = raw14550 := by
      apply Matrix.ext; unfold tripleCharges sourceA871 sourceB871 sourceC871 difference raw14550; decide +kernel
    rw [ha]
    exact (canonical14550 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA871 + difference 0 1) (sourceB871 + difference 1 0) sourceC871) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4022) := by
    have ha : (tripleCharges (sourceA871 + difference 0 1) (sourceB871 + difference 1 0) sourceC871) = raw14551 := by
      apply Matrix.ext; unfold tripleCharges sourceA871 sourceB871 sourceC871 difference raw14551; decide +kernel
    rw [ha]
    exact (canonical14551 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA871 + difference 0 2) (sourceB871 + difference 2 0) sourceC871) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA871 + difference 0 2) (sourceB871 + difference 2 0) sourceC871) = raw14552 := by
      apply Matrix.ext; unfold tripleCharges sourceA871 sourceB871 sourceC871 difference raw14552; decide +kernel
    rw [ha]
    exact (canonical14552 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA871 + difference 0 3) (sourceB871 + difference 3 0) sourceC871) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3946) := by
    have ha : (tripleCharges (sourceA871 + difference 0 3) (sourceB871 + difference 3 0) sourceC871) = raw14553 := by
      apply Matrix.ext; unfold tripleCharges sourceA871 sourceB871 sourceC871 difference raw14553; decide +kernel
    rw [ha]
    exact (canonical14553 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA871 + difference 0 4) (sourceB871 + difference 4 0) sourceC871) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA871 + difference 0 4) (sourceB871 + difference 4 0) sourceC871) = raw14554 := by
      apply Matrix.ext; unfold tripleCharges sourceA871 sourceB871 sourceC871 difference raw14554; decide +kernel
    rw [ha]
    exact (canonical14554 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA871 + difference 0 5) (sourceB871 + difference 5 0) sourceC871) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4044) := by
    have ha : (tripleCharges (sourceA871 + difference 0 5) (sourceB871 + difference 5 0) sourceC871) = raw14555 := by
      apply Matrix.ext; unfold tripleCharges sourceA871 sourceB871 sourceC871 difference raw14555; decide +kernel
    rw [ha]
    exact (canonical14555 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA871 + sourceB871) sourceC871) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA871 + sourceB871) sourceC871) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA871 sourceB871 sourceC871 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA871 sourceB871 sourceC871
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm871, Integer.Sparse.eval]
  linarith only [hs]

def sourceA872 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB872 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC872 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceForm872 : Integer.Sparse Master := [(Sum.inr 3168, 1), (Sum.inr 3715, 1), (Sum.inr 3722, 1), (Sum.inr 3725, 1), (Sum.inr 3839, 1), (Sum.inr 4022, 1), (Sum.inr 4092, -1)]

theorem sourceEq872 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm872 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA872 + difference 0 1) (sourceB872 + difference 1 0) sourceC872) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4022) := by
    have ha : (tripleCharges (sourceA872 + difference 0 1) (sourceB872 + difference 1 0) sourceC872) = raw14551 := by
      apply Matrix.ext; unfold tripleCharges sourceA872 sourceB872 sourceC872 difference raw14551; decide +kernel
    rw [ha]
    exact (canonical14551 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA872 + difference 1 1) (sourceB872 + difference 1 1) sourceC872) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA872 + difference 1 1) (sourceB872 + difference 1 1) sourceC872) = raw14550 := by
      apply Matrix.ext; unfold tripleCharges sourceA872 sourceB872 sourceC872 difference raw14550; decide +kernel
    rw [ha]
    exact (canonical14550 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA872 + difference 2 1) (sourceB872 + difference 1 2) sourceC872) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3725) := by
    have ha : (tripleCharges (sourceA872 + difference 2 1) (sourceB872 + difference 1 2) sourceC872) = raw14557 := by
      apply Matrix.ext; unfold tripleCharges sourceA872 sourceB872 sourceC872 difference raw14557; decide +kernel
    rw [ha]
    exact (canonical14557 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA872 + difference 3 1) (sourceB872 + difference 1 3) sourceC872) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3722) := by
    have ha : (tripleCharges (sourceA872 + difference 3 1) (sourceB872 + difference 1 3) sourceC872) = raw14558 := by
      apply Matrix.ext; unfold tripleCharges sourceA872 sourceB872 sourceC872 difference raw14558; decide +kernel
    rw [ha]
    exact (canonical14558 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA872 + difference 4 1) (sourceB872 + difference 1 4) sourceC872) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3715) := by
    have ha : (tripleCharges (sourceA872 + difference 4 1) (sourceB872 + difference 1 4) sourceC872) = raw14559 := by
      apply Matrix.ext; unfold tripleCharges sourceA872 sourceB872 sourceC872 difference raw14559; decide +kernel
    rw [ha]
    exact (canonical14559 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA872 + difference 5 1) (sourceB872 + difference 1 5) sourceC872) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3168) := by
    have ha : (tripleCharges (sourceA872 + difference 5 1) (sourceB872 + difference 1 5) sourceC872) = raw14560 := by
      apply Matrix.ext; unfold tripleCharges sourceA872 sourceB872 sourceC872 difference raw14560; decide +kernel
    rw [ha]
    exact (canonical14560 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA872 + sourceB872) sourceC872) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA872 + sourceB872) sourceC872) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA872 sourceB872 sourceC872 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA872 sourceB872 sourceC872
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm872, Integer.Sparse.eval]
  linarith only [hs]

def sourceA873 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB873 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC873 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceForm873 : Integer.Sparse Master := [(Sum.inr 2568, 1), (Sum.inr 3725, 1), (Sum.inr 3780, 1), (Sum.inr 3828, 1), (Sum.inr 3839, 1), (Sum.inr 3848, 1), (Sum.inr 4092, -1)]

theorem sourceEq873 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm873 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA873 + difference 2 0) (sourceB873 + difference 0 2) sourceC873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2568) := by
    have ha : (tripleCharges (sourceA873 + difference 2 0) (sourceB873 + difference 0 2) sourceC873) = raw14561 := by
      apply Matrix.ext; unfold tripleCharges sourceA873 sourceB873 sourceC873 difference raw14561; decide +kernel
    rw [ha]
    exact (canonical14561 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA873 + difference 2 1) (sourceB873 + difference 1 2) sourceC873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3725) := by
    have ha : (tripleCharges (sourceA873 + difference 2 1) (sourceB873 + difference 1 2) sourceC873) = raw14557 := by
      apply Matrix.ext; unfold tripleCharges sourceA873 sourceB873 sourceC873 difference raw14557; decide +kernel
    rw [ha]
    exact (canonical14557 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA873 + difference 2 2) (sourceB873 + difference 2 2) sourceC873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA873 + difference 2 2) (sourceB873 + difference 2 2) sourceC873) = raw14550 := by
      apply Matrix.ext; unfold tripleCharges sourceA873 sourceB873 sourceC873 difference raw14550; decide +kernel
    rw [ha]
    exact (canonical14550 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA873 + difference 2 3) (sourceB873 + difference 3 2) sourceC873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3828) := by
    have ha : (tripleCharges (sourceA873 + difference 2 3) (sourceB873 + difference 3 2) sourceC873) = raw14562 := by
      apply Matrix.ext; unfold tripleCharges sourceA873 sourceB873 sourceC873 difference raw14562; decide +kernel
    rw [ha]
    exact (canonical14562 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA873 + difference 2 4) (sourceB873 + difference 4 2) sourceC873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3780) := by
    have ha : (tripleCharges (sourceA873 + difference 2 4) (sourceB873 + difference 4 2) sourceC873) = raw14563 := by
      apply Matrix.ext; unfold tripleCharges sourceA873 sourceB873 sourceC873 difference raw14563; decide +kernel
    rw [ha]
    exact (canonical14563 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA873 + difference 2 5) (sourceB873 + difference 5 2) sourceC873) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA873 + difference 2 5) (sourceB873 + difference 5 2) sourceC873) = raw14564 := by
      apply Matrix.ext; unfold tripleCharges sourceA873 sourceB873 sourceC873 difference raw14564; decide +kernel
    rw [ha]
    exact (canonical14564 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA873 + sourceB873) sourceC873) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA873 + sourceB873) sourceC873) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA873 sourceB873 sourceC873 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA873 sourceB873 sourceC873
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm873, Integer.Sparse.eval]
  linarith only [hs]

def sourceA874 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB874 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC874 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceForm874 : Integer.Sparse Master := [(Sum.inr 3170, 1), (Sum.inr 3719, 1), (Sum.inr 3782, 1), (Sum.inr 3809, 1), (Sum.inr 3839, 1), (Sum.inr 4024, 1), (Sum.inr 4092, -1)]

theorem sourceEq874 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm874 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA874 + difference 0 2) (sourceB874 + difference 2 0) sourceC874) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA874 + difference 0 2) (sourceB874 + difference 2 0) sourceC874) = raw14552 := by
      apply Matrix.ext; unfold tripleCharges sourceA874 sourceB874 sourceC874 difference raw14552; decide +kernel
    rw [ha]
    exact (canonical14552 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA874 + difference 1 2) (sourceB874 + difference 2 1) sourceC874) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA874 + difference 1 2) (sourceB874 + difference 2 1) sourceC874) = raw14565 := by
      apply Matrix.ext; unfold tripleCharges sourceA874 sourceB874 sourceC874 difference raw14565; decide +kernel
    rw [ha]
    exact (canonical14565 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA874 + difference 2 2) (sourceB874 + difference 2 2) sourceC874) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA874 + difference 2 2) (sourceB874 + difference 2 2) sourceC874) = raw14550 := by
      apply Matrix.ext; unfold tripleCharges sourceA874 sourceB874 sourceC874 difference raw14550; decide +kernel
    rw [ha]
    exact (canonical14550 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA874 + difference 3 2) (sourceB874 + difference 2 3) sourceC874) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA874 + difference 3 2) (sourceB874 + difference 2 3) sourceC874) = raw14566 := by
      apply Matrix.ext; unfold tripleCharges sourceA874 sourceB874 sourceC874 difference raw14566; decide +kernel
    rw [ha]
    exact (canonical14566 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA874 + difference 4 2) (sourceB874 + difference 2 4) sourceC874) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA874 + difference 4 2) (sourceB874 + difference 2 4) sourceC874) = raw14567 := by
      apply Matrix.ext; unfold tripleCharges sourceA874 sourceB874 sourceC874 difference raw14567; decide +kernel
    rw [ha]
    exact (canonical14567 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA874 + difference 5 2) (sourceB874 + difference 2 5) sourceC874) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA874 + difference 5 2) (sourceB874 + difference 2 5) sourceC874) = raw14568 := by
      apply Matrix.ext; unfold tripleCharges sourceA874 sourceB874 sourceC874 difference raw14568; decide +kernel
    rw [ha]
    exact (canonical14568 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA874 + sourceB874) sourceC874) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA874 + sourceB874) sourceC874) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA874 sourceB874 sourceC874 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA874 sourceB874 sourceC874
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm874, Integer.Sparse.eval]
  linarith only [hs]

def sourceA875 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB875 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC875 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceForm875 : Integer.Sparse Master := [(Sum.inr 2557, 1), (Sum.inr 3722, 1), (Sum.inr 3782, 1), (Sum.inr 3839, 1), (Sum.inr 3841, 1), (Sum.inr 3843, 1), (Sum.inr 4092, -1)]

theorem sourceEq875 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm875 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA875 + difference 3 0) (sourceB875 + difference 0 3) sourceC875) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2557) := by
    have ha : (tripleCharges (sourceA875 + difference 3 0) (sourceB875 + difference 0 3) sourceC875) = raw14569 := by
      apply Matrix.ext; unfold tripleCharges sourceA875 sourceB875 sourceC875 difference raw14569; decide +kernel
    rw [ha]
    exact (canonical14569 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA875 + difference 3 1) (sourceB875 + difference 1 3) sourceC875) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3722) := by
    have ha : (tripleCharges (sourceA875 + difference 3 1) (sourceB875 + difference 1 3) sourceC875) = raw14558 := by
      apply Matrix.ext; unfold tripleCharges sourceA875 sourceB875 sourceC875 difference raw14558; decide +kernel
    rw [ha]
    exact (canonical14558 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA875 + difference 3 2) (sourceB875 + difference 2 3) sourceC875) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA875 + difference 3 2) (sourceB875 + difference 2 3) sourceC875) = raw14566 := by
      apply Matrix.ext; unfold tripleCharges sourceA875 sourceB875 sourceC875 difference raw14566; decide +kernel
    rw [ha]
    exact (canonical14566 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA875 + difference 3 3) (sourceB875 + difference 3 3) sourceC875) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA875 + difference 3 3) (sourceB875 + difference 3 3) sourceC875) = raw14550 := by
      apply Matrix.ext; unfold tripleCharges sourceA875 sourceB875 sourceC875 difference raw14550; decide +kernel
    rw [ha]
    exact (canonical14550 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA875 + difference 3 4) (sourceB875 + difference 4 3) sourceC875) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3841) := by
    have ha : (tripleCharges (sourceA875 + difference 3 4) (sourceB875 + difference 4 3) sourceC875) = raw14570 := by
      apply Matrix.ext; unfold tripleCharges sourceA875 sourceB875 sourceC875 difference raw14570; decide +kernel
    rw [ha]
    exact (canonical14570 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA875 + difference 3 5) (sourceB875 + difference 5 3) sourceC875) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA875 + difference 3 5) (sourceB875 + difference 5 3) sourceC875) = raw14571 := by
      apply Matrix.ext; unfold tripleCharges sourceA875 sourceB875 sourceC875 difference raw14571; decide +kernel
    rw [ha]
    exact (canonical14571 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA875 + sourceB875) sourceC875) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA875 + sourceB875) sourceC875) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA875 sourceB875 sourceC875 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA875 sourceB875 sourceC875
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm875, Integer.Sparse.eval]
  linarith only [hs]

def sourceA876 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB876 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC876 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceForm876 : Integer.Sparse Master := [(Sum.inr 3175, 1), (Sum.inr 3723, 1), (Sum.inr 3828, 1), (Sum.inr 3839, 1), (Sum.inr 3877, 1), (Sum.inr 3946, 1), (Sum.inr 4092, -1)]

theorem sourceEq876 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm876 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA876 + difference 0 3) (sourceB876 + difference 3 0) sourceC876) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3946) := by
    have ha : (tripleCharges (sourceA876 + difference 0 3) (sourceB876 + difference 3 0) sourceC876) = raw14553 := by
      apply Matrix.ext; unfold tripleCharges sourceA876 sourceB876 sourceC876 difference raw14553; decide +kernel
    rw [ha]
    exact (canonical14553 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA876 + difference 1 3) (sourceB876 + difference 3 1) sourceC876) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA876 + difference 1 3) (sourceB876 + difference 3 1) sourceC876) = raw14572 := by
      apply Matrix.ext; unfold tripleCharges sourceA876 sourceB876 sourceC876 difference raw14572; decide +kernel
    rw [ha]
    exact (canonical14572 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA876 + difference 2 3) (sourceB876 + difference 3 2) sourceC876) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3828) := by
    have ha : (tripleCharges (sourceA876 + difference 2 3) (sourceB876 + difference 3 2) sourceC876) = raw14562 := by
      apply Matrix.ext; unfold tripleCharges sourceA876 sourceB876 sourceC876 difference raw14562; decide +kernel
    rw [ha]
    exact (canonical14562 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA876 + difference 3 3) (sourceB876 + difference 3 3) sourceC876) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA876 + difference 3 3) (sourceB876 + difference 3 3) sourceC876) = raw14550 := by
      apply Matrix.ext; unfold tripleCharges sourceA876 sourceB876 sourceC876 difference raw14550; decide +kernel
    rw [ha]
    exact (canonical14550 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA876 + difference 4 3) (sourceB876 + difference 3 4) sourceC876) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3723) := by
    have ha : (tripleCharges (sourceA876 + difference 4 3) (sourceB876 + difference 3 4) sourceC876) = raw14573 := by
      apply Matrix.ext; unfold tripleCharges sourceA876 sourceB876 sourceC876 difference raw14573; decide +kernel
    rw [ha]
    exact (canonical14573 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA876 + difference 5 3) (sourceB876 + difference 3 5) sourceC876) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3175) := by
    have ha : (tripleCharges (sourceA876 + difference 5 3) (sourceB876 + difference 3 5) sourceC876) = raw14574 := by
      apply Matrix.ext; unfold tripleCharges sourceA876 sourceB876 sourceC876 difference raw14574; decide +kernel
    rw [ha]
    exact (canonical14574 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA876 + sourceB876) sourceC876) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA876 + sourceB876) sourceC876) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA876 sourceB876 sourceC876 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA876 sourceB876 sourceC876
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm876, Integer.Sparse.eval]
  linarith only [hs]

def sourceA877 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB877 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC877 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceForm877 : Integer.Sparse Master := [(Sum.inr 2545, 1), (Sum.inr 3715, 1), (Sum.inr 3719, 1), (Sum.inr 3723, 1), (Sum.inr 3837, 1), (Sum.inr 3839, 1), (Sum.inr 4092, -1)]

theorem sourceEq877 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm877 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA877 + difference 4 0) (sourceB877 + difference 0 4) sourceC877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2545) := by
    have ha : (tripleCharges (sourceA877 + difference 4 0) (sourceB877 + difference 0 4) sourceC877) = raw14575 := by
      apply Matrix.ext; unfold tripleCharges sourceA877 sourceB877 sourceC877 difference raw14575; decide +kernel
    rw [ha]
    exact (canonical14575 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA877 + difference 4 1) (sourceB877 + difference 1 4) sourceC877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3715) := by
    have ha : (tripleCharges (sourceA877 + difference 4 1) (sourceB877 + difference 1 4) sourceC877) = raw14559 := by
      apply Matrix.ext; unfold tripleCharges sourceA877 sourceB877 sourceC877 difference raw14559; decide +kernel
    rw [ha]
    exact (canonical14559 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA877 + difference 4 2) (sourceB877 + difference 2 4) sourceC877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA877 + difference 4 2) (sourceB877 + difference 2 4) sourceC877) = raw14567 := by
      apply Matrix.ext; unfold tripleCharges sourceA877 sourceB877 sourceC877 difference raw14567; decide +kernel
    rw [ha]
    exact (canonical14567 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA877 + difference 4 3) (sourceB877 + difference 3 4) sourceC877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3723) := by
    have ha : (tripleCharges (sourceA877 + difference 4 3) (sourceB877 + difference 3 4) sourceC877) = raw14573 := by
      apply Matrix.ext; unfold tripleCharges sourceA877 sourceB877 sourceC877 difference raw14573; decide +kernel
    rw [ha]
    exact (canonical14573 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA877 + difference 4 4) (sourceB877 + difference 4 4) sourceC877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA877 + difference 4 4) (sourceB877 + difference 4 4) sourceC877) = raw14550 := by
      apply Matrix.ext; unfold tripleCharges sourceA877 sourceB877 sourceC877 difference raw14550; decide +kernel
    rw [ha]
    exact (canonical14550 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA877 + difference 4 5) (sourceB877 + difference 5 4) sourceC877) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3837) := by
    have ha : (tripleCharges (sourceA877 + difference 4 5) (sourceB877 + difference 5 4) sourceC877) = raw14576 := by
      apply Matrix.ext; unfold tripleCharges sourceA877 sourceB877 sourceC877 difference raw14576; decide +kernel
    rw [ha]
    exact (canonical14576 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA877 + sourceB877) sourceC877) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA877 + sourceB877) sourceC877) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA877 sourceB877 sourceC877 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA877 sourceB877 sourceC877
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm877, Integer.Sparse.eval]
  linarith only [hs]

def sourceA878 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB878 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC878 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceForm878 : Integer.Sparse Master := [(Sum.inr 3196, 1), (Sum.inr 3780, 1), (Sum.inr 3782, 1), (Sum.inr 3814, 1), (Sum.inr 3839, 1), (Sum.inr 3841, 1), (Sum.inr 4092, -1)]

theorem sourceEq878 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm878 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA878 + difference 0 4) (sourceB878 + difference 4 0) sourceC878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA878 + difference 0 4) (sourceB878 + difference 4 0) sourceC878) = raw14554 := by
      apply Matrix.ext; unfold tripleCharges sourceA878 sourceB878 sourceC878 difference raw14554; decide +kernel
    rw [ha]
    exact (canonical14554 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA878 + difference 1 4) (sourceB878 + difference 4 1) sourceC878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA878 + difference 1 4) (sourceB878 + difference 4 1) sourceC878) = raw14577 := by
      apply Matrix.ext; unfold tripleCharges sourceA878 sourceB878 sourceC878 difference raw14577; decide +kernel
    rw [ha]
    exact (canonical14577 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA878 + difference 2 4) (sourceB878 + difference 4 2) sourceC878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3780) := by
    have ha : (tripleCharges (sourceA878 + difference 2 4) (sourceB878 + difference 4 2) sourceC878) = raw14563 := by
      apply Matrix.ext; unfold tripleCharges sourceA878 sourceB878 sourceC878 difference raw14563; decide +kernel
    rw [ha]
    exact (canonical14563 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA878 + difference 3 4) (sourceB878 + difference 4 3) sourceC878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3841) := by
    have ha : (tripleCharges (sourceA878 + difference 3 4) (sourceB878 + difference 4 3) sourceC878) = raw14570 := by
      apply Matrix.ext; unfold tripleCharges sourceA878 sourceB878 sourceC878 difference raw14570; decide +kernel
    rw [ha]
    exact (canonical14570 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA878 + difference 4 4) (sourceB878 + difference 4 4) sourceC878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA878 + difference 4 4) (sourceB878 + difference 4 4) sourceC878) = raw14550 := by
      apply Matrix.ext; unfold tripleCharges sourceA878 sourceB878 sourceC878 difference raw14550; decide +kernel
    rw [ha]
    exact (canonical14550 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA878 + difference 5 4) (sourceB878 + difference 4 5) sourceC878) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3196) := by
    have ha : (tripleCharges (sourceA878 + difference 5 4) (sourceB878 + difference 4 5) sourceC878) = raw14578 := by
      apply Matrix.ext; unfold tripleCharges sourceA878 sourceB878 sourceC878 difference raw14578; decide +kernel
    rw [ha]
    exact (canonical14578 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA878 + sourceB878) sourceC878) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA878 + sourceB878) sourceC878) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA878 sourceB878 sourceC878 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA878 sourceB878 sourceC878
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm878, Integer.Sparse.eval]
  linarith only [hs]

def sourceA879 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB879 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceC879 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceForm879 : Integer.Sparse Master := [(Sum.inr 2544, 1), (Sum.inr 3168, 1), (Sum.inr 3170, 1), (Sum.inr 3175, 1), (Sum.inr 3196, 1), (Sum.inr 3839, 1), (Sum.inr 4092, -1)]

theorem sourceEq879 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm879 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA879 + difference 5 0) (sourceB879 + difference 0 5) sourceC879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2544) := by
    have ha : (tripleCharges (sourceA879 + difference 5 0) (sourceB879 + difference 0 5) sourceC879) = raw14579 := by
      apply Matrix.ext; unfold tripleCharges sourceA879 sourceB879 sourceC879 difference raw14579; decide +kernel
    rw [ha]
    exact (canonical14579 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA879 + difference 5 1) (sourceB879 + difference 1 5) sourceC879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3168) := by
    have ha : (tripleCharges (sourceA879 + difference 5 1) (sourceB879 + difference 1 5) sourceC879) = raw14560 := by
      apply Matrix.ext; unfold tripleCharges sourceA879 sourceB879 sourceC879 difference raw14560; decide +kernel
    rw [ha]
    exact (canonical14560 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA879 + difference 5 2) (sourceB879 + difference 2 5) sourceC879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA879 + difference 5 2) (sourceB879 + difference 2 5) sourceC879) = raw14568 := by
      apply Matrix.ext; unfold tripleCharges sourceA879 sourceB879 sourceC879 difference raw14568; decide +kernel
    rw [ha]
    exact (canonical14568 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA879 + difference 5 3) (sourceB879 + difference 3 5) sourceC879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3175) := by
    have ha : (tripleCharges (sourceA879 + difference 5 3) (sourceB879 + difference 3 5) sourceC879) = raw14574 := by
      apply Matrix.ext; unfold tripleCharges sourceA879 sourceB879 sourceC879 difference raw14574; decide +kernel
    rw [ha]
    exact (canonical14574 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA879 + difference 5 4) (sourceB879 + difference 4 5) sourceC879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3196) := by
    have ha : (tripleCharges (sourceA879 + difference 5 4) (sourceB879 + difference 4 5) sourceC879) = raw14578 := by
      apply Matrix.ext; unfold tripleCharges sourceA879 sourceB879 sourceC879 difference raw14578; decide +kernel
    rw [ha]
    exact (canonical14578 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA879 + difference 5 5) (sourceB879 + difference 5 5) sourceC879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA879 + difference 5 5) (sourceB879 + difference 5 5) sourceC879) = raw14550 := by
      apply Matrix.ext; unfold tripleCharges sourceA879 sourceB879 sourceC879 difference raw14550; decide +kernel
    rw [ha]
    exact (canonical14550 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA879 + sourceB879) sourceC879) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA879 + sourceB879) sourceC879) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA879 sourceB879 sourceC879 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA879 sourceB879 sourceC879
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm879, Integer.Sparse.eval]
  linarith only [hs]

def sourceA880 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB880 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC880 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceForm880 : Integer.Sparse Master := [(Sum.inr 4780, 1), (Sum.inr 4781, 1), (Sum.inr 4785, 1), (Sum.inr 4803, 1), (Sum.inr 4815, 1), (Sum.inr 5121, 1), (Sum.inr 5122, 1), (Sum.inr 5144, 1), (Sum.inr 5182, 1), (Sum.inr 5187, 1), (Sum.inr 5191, 1), (Sum.inr 5219, 1), (Sum.inr 5251, 1), (Sum.inr 5343, 1), (Sum.inr 5347, 1), (Sum.inr 5353, 1), (Sum.inr 5359, 1), (Sum.inr 5403, 1), (Sum.inr 5406, 1), (Sum.inr 5419, 1), (Sum.inr 5422, 1), (Sum.inr 5425, 2), (Sum.inr 5430, 2), (Sum.inr 5431, 1), (Sum.inr 5433, 1), (Sum.inr 5437, 1), (Sum.inr 5445, 1), (Sum.inr 5478, 1)]

theorem sourceEq880 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm880 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA880 + difference 0 1) (sourceB880 + difference 1 0) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA880 + difference 0 1) (sourceB880 + difference 1 0) sourceC880) = raw14580 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14580; decide +kernel
    rw [ha]
    exact (canonical14580 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA880 + difference 0 2) (sourceB880 + difference 2 0) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA880 + difference 0 2) (sourceB880 + difference 2 0) sourceC880) = raw14581 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14581; decide +kernel
    rw [ha]
    exact (canonical14581 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA880 + difference 0 3) (sourceB880 + difference 3 0) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA880 + difference 0 3) (sourceB880 + difference 3 0) sourceC880) = raw14582 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14582; decide +kernel
    rw [ha]
    exact (canonical14582 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA880 + difference 0 4) (sourceB880 + difference 4 0) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA880 + difference 0 4) (sourceB880 + difference 4 0) sourceC880) = raw14583 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14583; decide +kernel
    rw [ha]
    exact (canonical14583 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA880 + difference 0 5) (sourceB880 + difference 5 0) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5478) := by
    have ha : (tripleCharges (sourceA880 + difference 0 5) (sourceB880 + difference 5 0) sourceC880) = raw14584 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14584; decide +kernel
    rw [ha]
    exact (canonical14584 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA880 + difference 1 0) (sourceB880 + difference 0 1) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA880 + difference 1 0) (sourceB880 + difference 0 1) sourceC880) = raw14585 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14585; decide +kernel
    rw [ha]
    exact (canonical14585 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA880 + difference 1 2) (sourceB880 + difference 2 1) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA880 + difference 1 2) (sourceB880 + difference 2 1) sourceC880) = raw14586 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14586; decide +kernel
    rw [ha]
    exact (canonical14586 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA880 + difference 1 3) (sourceB880 + difference 3 1) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA880 + difference 1 3) (sourceB880 + difference 3 1) sourceC880) = raw14587 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14587; decide +kernel
    rw [ha]
    exact (canonical14587 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA880 + difference 1 4) (sourceB880 + difference 4 1) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5437) := by
    have ha : (tripleCharges (sourceA880 + difference 1 4) (sourceB880 + difference 4 1) sourceC880) = raw14588 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14588; decide +kernel
    rw [ha]
    exact (canonical14588 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA880 + difference 1 5) (sourceB880 + difference 5 1) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5422) := by
    have ha : (tripleCharges (sourceA880 + difference 1 5) (sourceB880 + difference 5 1) sourceC880) = raw14589 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14589; decide +kernel
    rw [ha]
    exact (canonical14589 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA880 + difference 2 0) (sourceB880 + difference 0 2) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA880 + difference 2 0) (sourceB880 + difference 0 2) sourceC880) = raw14590 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14590; decide +kernel
    rw [ha]
    exact (canonical14590 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA880 + difference 2 1) (sourceB880 + difference 1 2) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5353) := by
    have ha : (tripleCharges (sourceA880 + difference 2 1) (sourceB880 + difference 1 2) sourceC880) = raw14591 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14591; decide +kernel
    rw [ha]
    exact (canonical14591 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA880 + difference 2 3) (sourceB880 + difference 3 2) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA880 + difference 2 3) (sourceB880 + difference 3 2) sourceC880) = raw14592 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14592; decide +kernel
    rw [ha]
    exact (canonical14592 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA880 + difference 2 4) (sourceB880 + difference 4 2) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA880 + difference 2 4) (sourceB880 + difference 4 2) sourceC880) = raw14593 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14593; decide +kernel
    rw [ha]
    exact (canonical14593 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA880 + difference 2 5) (sourceB880 + difference 5 2) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA880 + difference 2 5) (sourceB880 + difference 5 2) sourceC880) = raw14594 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14594; decide +kernel
    rw [ha]
    exact (canonical14594 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA880 + difference 3 0) (sourceB880 + difference 0 3) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4785) := by
    have ha : (tripleCharges (sourceA880 + difference 3 0) (sourceB880 + difference 0 3) sourceC880) = raw14595 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14595; decide +kernel
    rw [ha]
    exact (canonical14595 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA880 + difference 3 1) (sourceB880 + difference 1 3) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5347) := by
    have ha : (tripleCharges (sourceA880 + difference 3 1) (sourceB880 + difference 1 3) sourceC880) = raw14596 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14596; decide +kernel
    rw [ha]
    exact (canonical14596 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA880 + difference 3 2) (sourceB880 + difference 2 3) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5343) := by
    have ha : (tripleCharges (sourceA880 + difference 3 2) (sourceB880 + difference 2 3) sourceC880) = raw14597 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14597; decide +kernel
    rw [ha]
    exact (canonical14597 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA880 + difference 3 4) (sourceB880 + difference 4 3) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA880 + difference 3 4) (sourceB880 + difference 4 3) sourceC880) = raw14598 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14598; decide +kernel
    rw [ha]
    exact (canonical14598 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA880 + difference 3 5) (sourceB880 + difference 5 3) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5419) := by
    have ha : (tripleCharges (sourceA880 + difference 3 5) (sourceB880 + difference 5 3) sourceC880) = raw14599 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14599; decide +kernel
    rw [ha]
    exact (canonical14599 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA880 + difference 4 0) (sourceB880 + difference 0 4) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4781) := by
    have ha : (tripleCharges (sourceA880 + difference 4 0) (sourceB880 + difference 0 4) sourceC880) = raw14600 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14600; decide +kernel
    rw [ha]
    exact (canonical14600 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA880 + difference 4 1) (sourceB880 + difference 1 4) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5122) := by
    have ha : (tripleCharges (sourceA880 + difference 4 1) (sourceB880 + difference 1 4) sourceC880) = raw14601 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14601; decide +kernel
    rw [ha]
    exact (canonical14601 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA880 + difference 4 2) (sourceB880 + difference 2 4) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5121) := by
    have ha : (tripleCharges (sourceA880 + difference 4 2) (sourceB880 + difference 2 4) sourceC880) = raw14602 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14602; decide +kernel
    rw [ha]
    exact (canonical14602 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA880 + difference 4 3) (sourceB880 + difference 3 4) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5219) := by
    have ha : (tripleCharges (sourceA880 + difference 4 3) (sourceB880 + difference 3 4) sourceC880) = raw14603 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14603; decide +kernel
    rw [ha]
    exact (canonical14603 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA880 + difference 4 5) (sourceB880 + difference 5 4) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5144) := by
    have ha : (tripleCharges (sourceA880 + difference 4 5) (sourceB880 + difference 5 4) sourceC880) = raw14604 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14604; decide +kernel
    rw [ha]
    exact (canonical14604 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA880 + difference 5 0) (sourceB880 + difference 0 5) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4780) := by
    have ha : (tripleCharges (sourceA880 + difference 5 0) (sourceB880 + difference 0 5) sourceC880) = raw14605 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14605; decide +kernel
    rw [ha]
    exact (canonical14605 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA880 + difference 5 1) (sourceB880 + difference 1 5) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5182) := by
    have ha : (tripleCharges (sourceA880 + difference 5 1) (sourceB880 + difference 1 5) sourceC880) = raw14606 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14606; decide +kernel
    rw [ha]
    exact (canonical14606 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA880 + difference 5 2) (sourceB880 + difference 2 5) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5191) := by
    have ha : (tripleCharges (sourceA880 + difference 5 2) (sourceB880 + difference 2 5) sourceC880) = raw14607 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14607; decide +kernel
    rw [ha]
    exact (canonical14607 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA880 + difference 5 3) (sourceB880 + difference 3 5) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5187) := by
    have ha : (tripleCharges (sourceA880 + difference 5 3) (sourceB880 + difference 3 5) sourceC880) = raw14608 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14608; decide +kernel
    rw [ha]
    exact (canonical14608 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA880 + difference 5 4) (sourceB880 + difference 4 5) sourceC880) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA880 + difference 5 4) (sourceB880 + difference 4 5) sourceC880) = raw14609 := by
      apply Matrix.ext; unfold tripleCharges sourceA880 sourceB880 sourceC880 difference raw14609; decide +kernel
    rw [ha]
    exact (canonical14609 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA880 sourceB880 sourceC880
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm880, Integer.Sparse.eval]
  linarith only [hs]

def sourceA881 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB881 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC881 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceForm881 : Integer.Sparse Master := [(Sum.inr 1988, 1), (Sum.inr 1989, 1), (Sum.inr 2002, 1), (Sum.inr 2021, 1), (Sum.inr 2192, 1), (Sum.inr 2850, 1), (Sum.inr 2852, 1), (Sum.inr 2861, 1), (Sum.inr 3064, 1), (Sum.inr 3367, 1), (Sum.inr 3369, 1), (Sum.inr 3375, 1), (Sum.inr 3557, 1), (Sum.inr 3684, 1), (Sum.inr 3691, 1), (Sum.inr 3747, 1), (Sum.inr 3759, 1), (Sum.inr 3822, 1), (Sum.inr 3839, 2), (Sum.inr 3842, 1), (Sum.inr 3847, 1), (Sum.inr 3848, 1), (Sum.inr 3899, 1), (Sum.inr 3900, 1), (Sum.inr 3972, 1), (Sum.inr 3974, 1), (Sum.inr 4024, 1), (Sum.inr 4026, 1), (Sum.inr 4033, 1)]

theorem sourceEq881 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm881 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA881 + difference 0 1) (sourceB881 + difference 1 0) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA881 + difference 0 1) (sourceB881 + difference 1 0) sourceC881) = raw14610 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14610; decide +kernel
    rw [ha]
    exact (canonical14610 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA881 + difference 0 2) (sourceB881 + difference 2 0) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA881 + difference 0 2) (sourceB881 + difference 2 0) sourceC881) = raw14611 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14611; decide +kernel
    rw [ha]
    exact (canonical14611 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA881 + difference 0 3) (sourceB881 + difference 3 0) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4026) := by
    have ha : (tripleCharges (sourceA881 + difference 0 3) (sourceB881 + difference 3 0) sourceC881) = raw14612 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14612; decide +kernel
    rw [ha]
    exact (canonical14612 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA881 + difference 0 4) (sourceB881 + difference 4 0) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA881 + difference 0 4) (sourceB881 + difference 4 0) sourceC881) = raw14613 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14613; decide +kernel
    rw [ha]
    exact (canonical14613 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA881 + difference 0 5) (sourceB881 + difference 5 0) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA881 + difference 0 5) (sourceB881 + difference 5 0) sourceC881) = raw14614 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14614; decide +kernel
    rw [ha]
    exact (canonical14614 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA881 + difference 1 0) (sourceB881 + difference 0 1) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA881 + difference 1 0) (sourceB881 + difference 0 1) sourceC881) = raw14615 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14615; decide +kernel
    rw [ha]
    exact (canonical14615 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA881 + difference 1 2) (sourceB881 + difference 2 1) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3759) := by
    have ha : (tripleCharges (sourceA881 + difference 1 2) (sourceB881 + difference 2 1) sourceC881) = raw14616 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14616; decide +kernel
    rw [ha]
    exact (canonical14616 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA881 + difference 1 3) (sourceB881 + difference 3 1) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA881 + difference 1 3) (sourceB881 + difference 3 1) sourceC881) = raw14617 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14617; decide +kernel
    rw [ha]
    exact (canonical14617 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA881 + difference 1 4) (sourceB881 + difference 4 1) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3899) := by
    have ha : (tripleCharges (sourceA881 + difference 1 4) (sourceB881 + difference 4 1) sourceC881) = raw14618 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14618; decide +kernel
    rw [ha]
    exact (canonical14618 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA881 + difference 1 5) (sourceB881 + difference 5 1) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3900) := by
    have ha : (tripleCharges (sourceA881 + difference 1 5) (sourceB881 + difference 5 1) sourceC881) = raw14619 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14619; decide +kernel
    rw [ha]
    exact (canonical14619 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA881 + difference 2 0) (sourceB881 + difference 0 2) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA881 + difference 2 0) (sourceB881 + difference 0 2) sourceC881) = raw14620 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14620; decide +kernel
    rw [ha]
    exact (canonical14620 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA881 + difference 2 1) (sourceB881 + difference 1 2) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3691) := by
    have ha : (tripleCharges (sourceA881 + difference 2 1) (sourceB881 + difference 1 2) sourceC881) = raw14621 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14621; decide +kernel
    rw [ha]
    exact (canonical14621 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA881 + difference 2 3) (sourceB881 + difference 3 2) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3822) := by
    have ha : (tripleCharges (sourceA881 + difference 2 3) (sourceB881 + difference 3 2) sourceC881) = raw14622 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14622; decide +kernel
    rw [ha]
    exact (canonical14622 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA881 + difference 2 4) (sourceB881 + difference 4 2) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA881 + difference 2 4) (sourceB881 + difference 4 2) sourceC881) = raw14623 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14623; decide +kernel
    rw [ha]
    exact (canonical14623 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA881 + difference 2 5) (sourceB881 + difference 5 2) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA881 + difference 2 5) (sourceB881 + difference 5 2) sourceC881) = raw14624 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14624; decide +kernel
    rw [ha]
    exact (canonical14624 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA881 + difference 3 0) (sourceB881 + difference 0 3) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2002) := by
    have ha : (tripleCharges (sourceA881 + difference 3 0) (sourceB881 + difference 0 3) sourceC881) = raw14625 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14625; decide +kernel
    rw [ha]
    exact (canonical14625 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA881 + difference 3 1) (sourceB881 + difference 1 3) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3684) := by
    have ha : (tripleCharges (sourceA881 + difference 3 1) (sourceB881 + difference 1 3) sourceC881) = raw14626 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14626; decide +kernel
    rw [ha]
    exact (canonical14626 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA881 + difference 3 2) (sourceB881 + difference 2 3) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3747) := by
    have ha : (tripleCharges (sourceA881 + difference 3 2) (sourceB881 + difference 2 3) sourceC881) = raw14627 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14627; decide +kernel
    rw [ha]
    exact (canonical14627 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA881 + difference 3 4) (sourceB881 + difference 4 3) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA881 + difference 3 4) (sourceB881 + difference 4 3) sourceC881) = raw14628 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14628; decide +kernel
    rw [ha]
    exact (canonical14628 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA881 + difference 3 5) (sourceB881 + difference 5 3) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3842) := by
    have ha : (tripleCharges (sourceA881 + difference 3 5) (sourceB881 + difference 5 3) sourceC881) = raw14629 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14629; decide +kernel
    rw [ha]
    exact (canonical14629 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA881 + difference 4 0) (sourceB881 + difference 0 4) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1989) := by
    have ha : (tripleCharges (sourceA881 + difference 4 0) (sourceB881 + difference 0 4) sourceC881) = raw14630 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14630; decide +kernel
    rw [ha]
    exact (canonical14630 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA881 + difference 4 1) (sourceB881 + difference 1 4) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3367) := by
    have ha : (tripleCharges (sourceA881 + difference 4 1) (sourceB881 + difference 1 4) sourceC881) = raw14631 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14631; decide +kernel
    rw [ha]
    exact (canonical14631 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA881 + difference 4 2) (sourceB881 + difference 2 4) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3369) := by
    have ha : (tripleCharges (sourceA881 + difference 4 2) (sourceB881 + difference 2 4) sourceC881) = raw14632 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14632; decide +kernel
    rw [ha]
    exact (canonical14632 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA881 + difference 4 3) (sourceB881 + difference 3 4) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3375) := by
    have ha : (tripleCharges (sourceA881 + difference 4 3) (sourceB881 + difference 3 4) sourceC881) = raw14633 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14633; decide +kernel
    rw [ha]
    exact (canonical14633 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA881 + difference 4 5) (sourceB881 + difference 5 4) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3557) := by
    have ha : (tripleCharges (sourceA881 + difference 4 5) (sourceB881 + difference 5 4) sourceC881) = raw14634 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14634; decide +kernel
    rw [ha]
    exact (canonical14634 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA881 + difference 5 0) (sourceB881 + difference 0 5) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1988) := by
    have ha : (tripleCharges (sourceA881 + difference 5 0) (sourceB881 + difference 0 5) sourceC881) = raw14635 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14635; decide +kernel
    rw [ha]
    exact (canonical14635 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA881 + difference 5 1) (sourceB881 + difference 1 5) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2850) := by
    have ha : (tripleCharges (sourceA881 + difference 5 1) (sourceB881 + difference 1 5) sourceC881) = raw14636 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14636; decide +kernel
    rw [ha]
    exact (canonical14636 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA881 + difference 5 2) (sourceB881 + difference 2 5) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2852) := by
    have ha : (tripleCharges (sourceA881 + difference 5 2) (sourceB881 + difference 2 5) sourceC881) = raw14637 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14637; decide +kernel
    rw [ha]
    exact (canonical14637 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA881 + difference 5 3) (sourceB881 + difference 3 5) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2861) := by
    have ha : (tripleCharges (sourceA881 + difference 5 3) (sourceB881 + difference 3 5) sourceC881) = raw14638 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14638; decide +kernel
    rw [ha]
    exact (canonical14638 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA881 + difference 5 4) (sourceB881 + difference 4 5) sourceC881) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA881 + difference 5 4) (sourceB881 + difference 4 5) sourceC881) = raw14639 := by
      apply Matrix.ext; unfold tripleCharges sourceA881 sourceB881 sourceC881 difference raw14639; decide +kernel
    rw [ha]
    exact (canonical14639 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA881 sourceB881 sourceC881
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm881, Integer.Sparse.eval]
  linarith only [hs]

def sourceA882 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB882 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC882 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceForm882 : Integer.Sparse Master := [(Sum.inr 1991, 1), (Sum.inr 1994, 1), (Sum.inr 1998, 1), (Sum.inr 2033, 1), (Sum.inr 2195, 1), (Sum.inr 2533, 1), (Sum.inr 2535, 1), (Sum.inr 2566, 1), (Sum.inr 2661, 1), (Sum.inr 3536, 1), (Sum.inr 3537, 1), (Sum.inr 3539, 1), (Sum.inr 3574, 1), (Sum.inr 3680, 1), (Sum.inr 3697, 1), (Sum.inr 3743, 1), (Sum.inr 3761, 1), (Sum.inr 3810, 1), (Sum.inr 3812, 1), (Sum.inr 3825, 1), (Sum.inr 3829, 1), (Sum.inr 3840, 2), (Sum.inr 3848, 1), (Sum.inr 3849, 1), (Sum.inr 3851, 1), (Sum.inr 3855, 1), (Sum.inr 3871, 1), (Sum.inr 3880, 1), (Sum.inr 3994, 1)]

theorem sourceEq882 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm882 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA882 + difference 0 1) (sourceB882 + difference 1 0) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA882 + difference 0 1) (sourceB882 + difference 1 0) sourceC882) = raw14640 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14640; decide +kernel
    rw [ha]
    exact (canonical14640 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA882 + difference 0 2) (sourceB882 + difference 2 0) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA882 + difference 0 2) (sourceB882 + difference 2 0) sourceC882) = raw14641 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14641; decide +kernel
    rw [ha]
    exact (canonical14641 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA882 + difference 0 3) (sourceB882 + difference 3 0) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA882 + difference 0 3) (sourceB882 + difference 3 0) sourceC882) = raw14642 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14642; decide +kernel
    rw [ha]
    exact (canonical14642 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA882 + difference 0 4) (sourceB882 + difference 4 0) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3851) := by
    have ha : (tripleCharges (sourceA882 + difference 0 4) (sourceB882 + difference 4 0) sourceC882) = raw14643 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14643; decide +kernel
    rw [ha]
    exact (canonical14643 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA882 + difference 0 5) (sourceB882 + difference 5 0) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3994) := by
    have ha : (tripleCharges (sourceA882 + difference 0 5) (sourceB882 + difference 5 0) sourceC882) = raw14644 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14644; decide +kernel
    rw [ha]
    exact (canonical14644 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA882 + difference 1 0) (sourceB882 + difference 0 1) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2033) := by
    have ha : (tripleCharges (sourceA882 + difference 1 0) (sourceB882 + difference 0 1) sourceC882) = raw14645 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14645; decide +kernel
    rw [ha]
    exact (canonical14645 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA882 + difference 1 2) (sourceB882 + difference 2 1) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3697) := by
    have ha : (tripleCharges (sourceA882 + difference 1 2) (sourceB882 + difference 2 1) sourceC882) = raw14646 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14646; decide +kernel
    rw [ha]
    exact (canonical14646 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA882 + difference 1 3) (sourceB882 + difference 3 1) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA882 + difference 1 3) (sourceB882 + difference 3 1) sourceC882) = raw14647 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14647; decide +kernel
    rw [ha]
    exact (canonical14647 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA882 + difference 1 4) (sourceB882 + difference 4 1) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3855) := by
    have ha : (tripleCharges (sourceA882 + difference 1 4) (sourceB882 + difference 4 1) sourceC882) = raw14648 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14648; decide +kernel
    rw [ha]
    exact (canonical14648 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA882 + difference 1 5) (sourceB882 + difference 5 1) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3829) := by
    have ha : (tripleCharges (sourceA882 + difference 1 5) (sourceB882 + difference 5 1) sourceC882) = raw14649 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14649; decide +kernel
    rw [ha]
    exact (canonical14649 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA882 + difference 2 0) (sourceB882 + difference 0 2) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA882 + difference 2 0) (sourceB882 + difference 0 2) sourceC882) = raw14650 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14650; decide +kernel
    rw [ha]
    exact (canonical14650 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA882 + difference 2 1) (sourceB882 + difference 1 2) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3761) := by
    have ha : (tripleCharges (sourceA882 + difference 2 1) (sourceB882 + difference 1 2) sourceC882) = raw14651 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14651; decide +kernel
    rw [ha]
    exact (canonical14651 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA882 + difference 2 3) (sourceB882 + difference 3 2) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3810) := by
    have ha : (tripleCharges (sourceA882 + difference 2 3) (sourceB882 + difference 3 2) sourceC882) = raw14652 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14652; decide +kernel
    rw [ha]
    exact (canonical14652 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA882 + difference 2 4) (sourceB882 + difference 4 2) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA882 + difference 2 4) (sourceB882 + difference 4 2) sourceC882) = raw14653 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14653; decide +kernel
    rw [ha]
    exact (canonical14653 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA882 + difference 2 5) (sourceB882 + difference 5 2) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA882 + difference 2 5) (sourceB882 + difference 5 2) sourceC882) = raw14654 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14654; decide +kernel
    rw [ha]
    exact (canonical14654 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA882 + difference 3 0) (sourceB882 + difference 0 3) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1994) := by
    have ha : (tripleCharges (sourceA882 + difference 3 0) (sourceB882 + difference 0 3) sourceC882) = raw14655 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14655; decide +kernel
    rw [ha]
    exact (canonical14655 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA882 + difference 3 1) (sourceB882 + difference 1 3) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3743) := by
    have ha : (tripleCharges (sourceA882 + difference 3 1) (sourceB882 + difference 1 3) sourceC882) = raw14656 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14656; decide +kernel
    rw [ha]
    exact (canonical14656 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA882 + difference 3 2) (sourceB882 + difference 2 3) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3680) := by
    have ha : (tripleCharges (sourceA882 + difference 3 2) (sourceB882 + difference 2 3) sourceC882) = raw14657 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14657; decide +kernel
    rw [ha]
    exact (canonical14657 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA882 + difference 3 4) (sourceB882 + difference 4 3) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA882 + difference 3 4) (sourceB882 + difference 4 3) sourceC882) = raw14658 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14658; decide +kernel
    rw [ha]
    exact (canonical14658 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA882 + difference 3 5) (sourceB882 + difference 5 3) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3825) := by
    have ha : (tripleCharges (sourceA882 + difference 3 5) (sourceB882 + difference 5 3) sourceC882) = raw14659 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14659; decide +kernel
    rw [ha]
    exact (canonical14659 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA882 + difference 4 0) (sourceB882 + difference 0 4) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1991) := by
    have ha : (tripleCharges (sourceA882 + difference 4 0) (sourceB882 + difference 0 4) sourceC882) = raw14660 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14660; decide +kernel
    rw [ha]
    exact (canonical14660 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA882 + difference 4 1) (sourceB882 + difference 1 4) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2535) := by
    have ha : (tripleCharges (sourceA882 + difference 4 1) (sourceB882 + difference 1 4) sourceC882) = raw14661 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14661; decide +kernel
    rw [ha]
    exact (canonical14661 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA882 + difference 4 2) (sourceB882 + difference 2 4) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2533) := by
    have ha : (tripleCharges (sourceA882 + difference 4 2) (sourceB882 + difference 2 4) sourceC882) = raw14662 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14662; decide +kernel
    rw [ha]
    exact (canonical14662 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA882 + difference 4 3) (sourceB882 + difference 3 4) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2661) := by
    have ha : (tripleCharges (sourceA882 + difference 4 3) (sourceB882 + difference 3 4) sourceC882) = raw14663 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14663; decide +kernel
    rw [ha]
    exact (canonical14663 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA882 + difference 4 5) (sourceB882 + difference 5 4) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2566) := by
    have ha : (tripleCharges (sourceA882 + difference 4 5) (sourceB882 + difference 5 4) sourceC882) = raw14664 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14664; decide +kernel
    rw [ha]
    exact (canonical14664 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA882 + difference 5 0) (sourceB882 + difference 0 5) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1998) := by
    have ha : (tripleCharges (sourceA882 + difference 5 0) (sourceB882 + difference 0 5) sourceC882) = raw14665 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14665; decide +kernel
    rw [ha]
    exact (canonical14665 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA882 + difference 5 1) (sourceB882 + difference 1 5) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3536) := by
    have ha : (tripleCharges (sourceA882 + difference 5 1) (sourceB882 + difference 1 5) sourceC882) = raw14666 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14666; decide +kernel
    rw [ha]
    exact (canonical14666 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA882 + difference 5 2) (sourceB882 + difference 2 5) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3574) := by
    have ha : (tripleCharges (sourceA882 + difference 5 2) (sourceB882 + difference 2 5) sourceC882) = raw14667 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14667; decide +kernel
    rw [ha]
    exact (canonical14667 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA882 + difference 5 3) (sourceB882 + difference 3 5) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3537) := by
    have ha : (tripleCharges (sourceA882 + difference 5 3) (sourceB882 + difference 3 5) sourceC882) = raw14668 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14668; decide +kernel
    rw [ha]
    exact (canonical14668 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA882 + difference 5 4) (sourceB882 + difference 4 5) sourceC882) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA882 + difference 5 4) (sourceB882 + difference 4 5) sourceC882) = raw14669 := by
      apply Matrix.ext; unfold tripleCharges sourceA882 sourceB882 sourceC882 difference raw14669; decide +kernel
    rw [ha]
    exact (canonical14669 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA882 sourceB882 sourceC882
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm882, Integer.Sparse.eval]
  linarith only [hs]

def sourceA883 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB883 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC883 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceForm883 : Integer.Sparse Master := [(Sum.inr 3871, 1), (Sum.inr 3872, 1), (Sum.inr 3875, 1), (Sum.inr 3880, 1), (Sum.inr 3901, 1), (Sum.inr 3974, 1), (Sum.inr 4091, -1)]

theorem sourceEq883 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm883 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA883 + difference 0 0) (sourceB883 + difference 0 0) sourceC883) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA883 + difference 0 0) (sourceB883 + difference 0 0) sourceC883) = raw14670 := by
      apply Matrix.ext; unfold tripleCharges sourceA883 sourceB883 sourceC883 difference raw14670; decide +kernel
    rw [ha]
    exact (canonical14670 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA883 + difference 0 1) (sourceB883 + difference 1 0) sourceC883) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA883 + difference 0 1) (sourceB883 + difference 1 0) sourceC883) = raw14671 := by
      apply Matrix.ext; unfold tripleCharges sourceA883 sourceB883 sourceC883 difference raw14671; decide +kernel
    rw [ha]
    exact (canonical14671 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA883 + difference 0 2) (sourceB883 + difference 2 0) sourceC883) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA883 + difference 0 2) (sourceB883 + difference 2 0) sourceC883) = raw14672 := by
      apply Matrix.ext; unfold tripleCharges sourceA883 sourceB883 sourceC883 difference raw14672; decide +kernel
    rw [ha]
    exact (canonical14672 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA883 + difference 0 3) (sourceB883 + difference 3 0) sourceC883) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA883 + difference 0 3) (sourceB883 + difference 3 0) sourceC883) = raw14673 := by
      apply Matrix.ext; unfold tripleCharges sourceA883 sourceB883 sourceC883 difference raw14673; decide +kernel
    rw [ha]
    exact (canonical14673 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA883 + difference 0 4) (sourceB883 + difference 4 0) sourceC883) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3901) := by
    have ha : (tripleCharges (sourceA883 + difference 0 4) (sourceB883 + difference 4 0) sourceC883) = raw14674 := by
      apply Matrix.ext; unfold tripleCharges sourceA883 sourceB883 sourceC883 difference raw14674; decide +kernel
    rw [ha]
    exact (canonical14674 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA883 + difference 0 5) (sourceB883 + difference 5 0) sourceC883) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA883 + difference 0 5) (sourceB883 + difference 5 0) sourceC883) = raw14675 := by
      apply Matrix.ext; unfold tripleCharges sourceA883 sourceB883 sourceC883 difference raw14675; decide +kernel
    rw [ha]
    exact (canonical14675 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA883 + sourceB883) sourceC883) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA883 + sourceB883) sourceC883) = raw14676 := by
      apply Matrix.ext; unfold doubleCharges sourceA883 sourceB883 sourceC883 raw14676; decide +kernel
    rw [ha]
    exact (canonical14676 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA883 sourceB883 sourceC883
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm883, Integer.Sparse.eval]
  linarith only [hs]

def sourceA884 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB884 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC884 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceForm884 : Integer.Sparse Master := [(Sum.inr 2611, 1), (Sum.inr 2919, 1), (Sum.inr 3195, 1), (Sum.inr 3197, 1), (Sum.inr 3202, 1), (Sum.inr 3872, 1), (Sum.inr 4091, -1)]

theorem sourceEq884 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm884 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA884 + difference 0 0) (sourceB884 + difference 0 0) sourceC884) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA884 + difference 0 0) (sourceB884 + difference 0 0) sourceC884) = raw14670 := by
      apply Matrix.ext; unfold tripleCharges sourceA884 sourceB884 sourceC884 difference raw14670; decide +kernel
    rw [ha]
    exact (canonical14670 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA884 + difference 1 0) (sourceB884 + difference 0 1) sourceC884) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA884 + difference 1 0) (sourceB884 + difference 0 1) sourceC884) = raw14677 := by
      apply Matrix.ext; unfold tripleCharges sourceA884 sourceB884 sourceC884 difference raw14677; decide +kernel
    rw [ha]
    exact (canonical14677 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA884 + difference 2 0) (sourceB884 + difference 0 2) sourceC884) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA884 + difference 2 0) (sourceB884 + difference 0 2) sourceC884) = raw14678 := by
      apply Matrix.ext; unfold tripleCharges sourceA884 sourceB884 sourceC884 difference raw14678; decide +kernel
    rw [ha]
    exact (canonical14678 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA884 + difference 3 0) (sourceB884 + difference 0 3) sourceC884) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3195) := by
    have ha : (tripleCharges (sourceA884 + difference 3 0) (sourceB884 + difference 0 3) sourceC884) = raw14679 := by
      apply Matrix.ext; unfold tripleCharges sourceA884 sourceB884 sourceC884 difference raw14679; decide +kernel
    rw [ha]
    exact (canonical14679 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA884 + difference 4 0) (sourceB884 + difference 0 4) sourceC884) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2919) := by
    have ha : (tripleCharges (sourceA884 + difference 4 0) (sourceB884 + difference 0 4) sourceC884) = raw14680 := by
      apply Matrix.ext; unfold tripleCharges sourceA884 sourceB884 sourceC884 difference raw14680; decide +kernel
    rw [ha]
    exact (canonical14680 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA884 + difference 5 0) (sourceB884 + difference 0 5) sourceC884) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2611) := by
    have ha : (tripleCharges (sourceA884 + difference 5 0) (sourceB884 + difference 0 5) sourceC884) = raw14681 := by
      apply Matrix.ext; unfold tripleCharges sourceA884 sourceB884 sourceC884 difference raw14681; decide +kernel
    rw [ha]
    exact (canonical14681 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA884 + sourceB884) sourceC884) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA884 + sourceB884) sourceC884) = raw14676 := by
      apply Matrix.ext; unfold doubleCharges sourceA884 sourceB884 sourceC884 raw14676; decide +kernel
    rw [ha]
    exact (canonical14676 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA884 sourceB884 sourceC884
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm884, Integer.Sparse.eval]
  linarith only [hs]

def sourceA885 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB885 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC885 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceForm885 : Integer.Sparse Master := [(Sum.inr 3197, 1), (Sum.inr 3872, 2), (Sum.inr 3878, 1), (Sum.inr 3899, 1), (Sum.inr 3964, 1), (Sum.inr 4091, -1)]

theorem sourceEq885 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm885 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA885 + difference 1 0) (sourceB885 + difference 0 1) sourceC885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA885 + difference 1 0) (sourceB885 + difference 0 1) sourceC885) = raw14677 := by
      apply Matrix.ext; unfold tripleCharges sourceA885 sourceB885 sourceC885 difference raw14677; decide +kernel
    rw [ha]
    exact (canonical14677 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA885 + difference 1 1) (sourceB885 + difference 1 1) sourceC885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA885 + difference 1 1) (sourceB885 + difference 1 1) sourceC885) = raw14670 := by
      apply Matrix.ext; unfold tripleCharges sourceA885 sourceB885 sourceC885 difference raw14670; decide +kernel
    rw [ha]
    exact (canonical14670 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA885 + difference 1 2) (sourceB885 + difference 2 1) sourceC885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3878) := by
    have ha : (tripleCharges (sourceA885 + difference 1 2) (sourceB885 + difference 2 1) sourceC885) = raw14682 := by
      apply Matrix.ext; unfold tripleCharges sourceA885 sourceB885 sourceC885 difference raw14682; decide +kernel
    rw [ha]
    exact (canonical14682 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA885 + difference 1 3) (sourceB885 + difference 3 1) sourceC885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA885 + difference 1 3) (sourceB885 + difference 3 1) sourceC885) = raw14683 := by
      apply Matrix.ext; unfold tripleCharges sourceA885 sourceB885 sourceC885 difference raw14683; decide +kernel
    rw [ha]
    exact (canonical14683 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA885 + difference 1 4) (sourceB885 + difference 4 1) sourceC885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3899) := by
    have ha : (tripleCharges (sourceA885 + difference 1 4) (sourceB885 + difference 4 1) sourceC885) = raw14684 := by
      apply Matrix.ext; unfold tripleCharges sourceA885 sourceB885 sourceC885 difference raw14684; decide +kernel
    rw [ha]
    exact (canonical14684 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA885 + difference 1 5) (sourceB885 + difference 5 1) sourceC885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3964) := by
    have ha : (tripleCharges (sourceA885 + difference 1 5) (sourceB885 + difference 5 1) sourceC885) = raw14685 := by
      apply Matrix.ext; unfold tripleCharges sourceA885 sourceB885 sourceC885 difference raw14685; decide +kernel
    rw [ha]
    exact (canonical14685 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA885 + sourceB885) sourceC885) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA885 + sourceB885) sourceC885) = raw14676 := by
      apply Matrix.ext; unfold doubleCharges sourceA885 sourceB885 sourceC885 raw14676; decide +kernel
    rw [ha]
    exact (canonical14676 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA885 sourceB885 sourceC885
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm885, Integer.Sparse.eval]
  linarith only [hs]

def sourceA886 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB886 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC886 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceForm886 : Integer.Sparse Master := [(Sum.inr 2612, 1), (Sum.inr 2945, 1), (Sum.inr 3783, 1), (Sum.inr 3863, 1), (Sum.inr 3871, 1), (Sum.inr 3872, 1), (Sum.inr 4091, -1)]

theorem sourceEq886 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm886 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA886 + difference 0 1) (sourceB886 + difference 1 0) sourceC886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA886 + difference 0 1) (sourceB886 + difference 1 0) sourceC886) = raw14671 := by
      apply Matrix.ext; unfold tripleCharges sourceA886 sourceB886 sourceC886 difference raw14671; decide +kernel
    rw [ha]
    exact (canonical14671 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA886 + difference 1 1) (sourceB886 + difference 1 1) sourceC886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA886 + difference 1 1) (sourceB886 + difference 1 1) sourceC886) = raw14670 := by
      apply Matrix.ext; unfold tripleCharges sourceA886 sourceB886 sourceC886 difference raw14670; decide +kernel
    rw [ha]
    exact (canonical14670 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA886 + difference 2 1) (sourceB886 + difference 1 2) sourceC886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3783) := by
    have ha : (tripleCharges (sourceA886 + difference 2 1) (sourceB886 + difference 1 2) sourceC886) = raw14686 := by
      apply Matrix.ext; unfold tripleCharges sourceA886 sourceB886 sourceC886 difference raw14686; decide +kernel
    rw [ha]
    exact (canonical14686 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA886 + difference 3 1) (sourceB886 + difference 1 3) sourceC886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3863) := by
    have ha : (tripleCharges (sourceA886 + difference 3 1) (sourceB886 + difference 1 3) sourceC886) = raw14687 := by
      apply Matrix.ext; unfold tripleCharges sourceA886 sourceB886 sourceC886 difference raw14687; decide +kernel
    rw [ha]
    exact (canonical14687 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA886 + difference 4 1) (sourceB886 + difference 1 4) sourceC886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2945) := by
    have ha : (tripleCharges (sourceA886 + difference 4 1) (sourceB886 + difference 1 4) sourceC886) = raw14688 := by
      apply Matrix.ext; unfold tripleCharges sourceA886 sourceB886 sourceC886 difference raw14688; decide +kernel
    rw [ha]
    exact (canonical14688 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA886 + difference 5 1) (sourceB886 + difference 1 5) sourceC886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2612) := by
    have ha : (tripleCharges (sourceA886 + difference 5 1) (sourceB886 + difference 1 5) sourceC886) = raw14689 := by
      apply Matrix.ext; unfold tripleCharges sourceA886 sourceB886 sourceC886 difference raw14689; decide +kernel
    rw [ha]
    exact (canonical14689 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA886 + sourceB886) sourceC886) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA886 + sourceB886) sourceC886) = raw14676 := by
      apply Matrix.ext; unfold doubleCharges sourceA886 sourceB886 sourceC886 raw14676; decide +kernel
    rw [ha]
    exact (canonical14676 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA886 sourceB886 sourceC886
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm886, Integer.Sparse.eval]
  linarith only [hs]

def sourceA887 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB887 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC887 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceForm887 : Integer.Sparse Master := [(Sum.inr 3202, 1), (Sum.inr 3783, 1), (Sum.inr 3789, 1), (Sum.inr 3801, 1), (Sum.inr 3872, 1), (Sum.inr 3972, 1), (Sum.inr 4091, -1)]

theorem sourceEq887 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm887 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA887 + difference 2 0) (sourceB887 + difference 0 2) sourceC887) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA887 + difference 2 0) (sourceB887 + difference 0 2) sourceC887) = raw14678 := by
      apply Matrix.ext; unfold tripleCharges sourceA887 sourceB887 sourceC887 difference raw14678; decide +kernel
    rw [ha]
    exact (canonical14678 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA887 + difference 2 1) (sourceB887 + difference 1 2) sourceC887) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3783) := by
    have ha : (tripleCharges (sourceA887 + difference 2 1) (sourceB887 + difference 1 2) sourceC887) = raw14686 := by
      apply Matrix.ext; unfold tripleCharges sourceA887 sourceB887 sourceC887 difference raw14686; decide +kernel
    rw [ha]
    exact (canonical14686 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA887 + difference 2 2) (sourceB887 + difference 2 2) sourceC887) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA887 + difference 2 2) (sourceB887 + difference 2 2) sourceC887) = raw14670 := by
      apply Matrix.ext; unfold tripleCharges sourceA887 sourceB887 sourceC887 difference raw14670; decide +kernel
    rw [ha]
    exact (canonical14670 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA887 + difference 2 3) (sourceB887 + difference 3 2) sourceC887) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3789) := by
    have ha : (tripleCharges (sourceA887 + difference 2 3) (sourceB887 + difference 3 2) sourceC887) = raw14690 := by
      apply Matrix.ext; unfold tripleCharges sourceA887 sourceB887 sourceC887 difference raw14690; decide +kernel
    rw [ha]
    exact (canonical14690 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA887 + difference 2 4) (sourceB887 + difference 4 2) sourceC887) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA887 + difference 2 4) (sourceB887 + difference 4 2) sourceC887) = raw14691 := by
      apply Matrix.ext; unfold tripleCharges sourceA887 sourceB887 sourceC887 difference raw14691; decide +kernel
    rw [ha]
    exact (canonical14691 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA887 + difference 2 5) (sourceB887 + difference 5 2) sourceC887) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA887 + difference 2 5) (sourceB887 + difference 5 2) sourceC887) = raw14692 := by
      apply Matrix.ext; unfold tripleCharges sourceA887 sourceB887 sourceC887 difference raw14692; decide +kernel
    rw [ha]
    exact (canonical14692 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA887 + sourceB887) sourceC887) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA887 + sourceB887) sourceC887) = raw14676 := by
      apply Matrix.ext; unfold doubleCharges sourceA887 sourceB887 sourceC887 raw14676; decide +kernel
    rw [ha]
    exact (canonical14676 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA887 sourceB887 sourceC887
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm887, Integer.Sparse.eval]
  linarith only [hs]

def sourceA888 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB888 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC888 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceForm888 : Integer.Sparse Master := [(Sum.inr 2623, 1), (Sum.inr 2920, 1), (Sum.inr 3865, 1), (Sum.inr 3872, 1), (Sum.inr 3878, 1), (Sum.inr 3880, 1), (Sum.inr 4091, -1)]

theorem sourceEq888 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm888 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA888 + difference 0 2) (sourceB888 + difference 2 0) sourceC888) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA888 + difference 0 2) (sourceB888 + difference 2 0) sourceC888) = raw14672 := by
      apply Matrix.ext; unfold tripleCharges sourceA888 sourceB888 sourceC888 difference raw14672; decide +kernel
    rw [ha]
    exact (canonical14672 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA888 + difference 1 2) (sourceB888 + difference 2 1) sourceC888) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3878) := by
    have ha : (tripleCharges (sourceA888 + difference 1 2) (sourceB888 + difference 2 1) sourceC888) = raw14682 := by
      apply Matrix.ext; unfold tripleCharges sourceA888 sourceB888 sourceC888 difference raw14682; decide +kernel
    rw [ha]
    exact (canonical14682 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA888 + difference 2 2) (sourceB888 + difference 2 2) sourceC888) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA888 + difference 2 2) (sourceB888 + difference 2 2) sourceC888) = raw14670 := by
      apply Matrix.ext; unfold tripleCharges sourceA888 sourceB888 sourceC888 difference raw14670; decide +kernel
    rw [ha]
    exact (canonical14670 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA888 + difference 3 2) (sourceB888 + difference 2 3) sourceC888) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3865) := by
    have ha : (tripleCharges (sourceA888 + difference 3 2) (sourceB888 + difference 2 3) sourceC888) = raw14693 := by
      apply Matrix.ext; unfold tripleCharges sourceA888 sourceB888 sourceC888 difference raw14693; decide +kernel
    rw [ha]
    exact (canonical14693 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA888 + difference 4 2) (sourceB888 + difference 2 4) sourceC888) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2920) := by
    have ha : (tripleCharges (sourceA888 + difference 4 2) (sourceB888 + difference 2 4) sourceC888) = raw14694 := by
      apply Matrix.ext; unfold tripleCharges sourceA888 sourceB888 sourceC888 difference raw14694; decide +kernel
    rw [ha]
    exact (canonical14694 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA888 + difference 5 2) (sourceB888 + difference 2 5) sourceC888) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2623) := by
    have ha : (tripleCharges (sourceA888 + difference 5 2) (sourceB888 + difference 2 5) sourceC888) = raw14695 := by
      apply Matrix.ext; unfold tripleCharges sourceA888 sourceB888 sourceC888 difference raw14695; decide +kernel
    rw [ha]
    exact (canonical14695 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA888 + sourceB888) sourceC888) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA888 + sourceB888) sourceC888) = raw14676 := by
      apply Matrix.ext; unfold doubleCharges sourceA888 sourceB888 sourceC888 raw14676; decide +kernel
    rw [ha]
    exact (canonical14676 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA888 sourceB888 sourceC888
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm888, Integer.Sparse.eval]
  linarith only [hs]

def sourceA889 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB889 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC889 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceForm889 : Integer.Sparse Master := [(Sum.inr 3195, 1), (Sum.inr 3863, 1), (Sum.inr 3865, 1), (Sum.inr 3872, 2), (Sum.inr 3922, 1), (Sum.inr 4091, -1)]

theorem sourceEq889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm889 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA889 + difference 3 0) (sourceB889 + difference 0 3) sourceC889) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3195) := by
    have ha : (tripleCharges (sourceA889 + difference 3 0) (sourceB889 + difference 0 3) sourceC889) = raw14679 := by
      apply Matrix.ext; unfold tripleCharges sourceA889 sourceB889 sourceC889 difference raw14679; decide +kernel
    rw [ha]
    exact (canonical14679 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA889 + difference 3 1) (sourceB889 + difference 1 3) sourceC889) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3863) := by
    have ha : (tripleCharges (sourceA889 + difference 3 1) (sourceB889 + difference 1 3) sourceC889) = raw14687 := by
      apply Matrix.ext; unfold tripleCharges sourceA889 sourceB889 sourceC889 difference raw14687; decide +kernel
    rw [ha]
    exact (canonical14687 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA889 + difference 3 2) (sourceB889 + difference 2 3) sourceC889) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3865) := by
    have ha : (tripleCharges (sourceA889 + difference 3 2) (sourceB889 + difference 2 3) sourceC889) = raw14693 := by
      apply Matrix.ext; unfold tripleCharges sourceA889 sourceB889 sourceC889 difference raw14693; decide +kernel
    rw [ha]
    exact (canonical14693 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA889 + difference 3 3) (sourceB889 + difference 3 3) sourceC889) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA889 + difference 3 3) (sourceB889 + difference 3 3) sourceC889) = raw14670 := by
      apply Matrix.ext; unfold tripleCharges sourceA889 sourceB889 sourceC889 difference raw14670; decide +kernel
    rw [ha]
    exact (canonical14670 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA889 + difference 3 4) (sourceB889 + difference 4 3) sourceC889) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA889 + difference 3 4) (sourceB889 + difference 4 3) sourceC889) = raw14696 := by
      apply Matrix.ext; unfold tripleCharges sourceA889 sourceB889 sourceC889 difference raw14696; decide +kernel
    rw [ha]
    exact (canonical14696 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA889 + difference 3 5) (sourceB889 + difference 5 3) sourceC889) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3922) := by
    have ha : (tripleCharges (sourceA889 + difference 3 5) (sourceB889 + difference 5 3) sourceC889) = raw14697 := by
      apply Matrix.ext; unfold tripleCharges sourceA889 sourceB889 sourceC889 difference raw14697; decide +kernel
    rw [ha]
    exact (canonical14697 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA889 + sourceB889) sourceC889) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA889 + sourceB889) sourceC889) = raw14676 := by
      apply Matrix.ext; unfold doubleCharges sourceA889 sourceB889 sourceC889 raw14676; decide +kernel
    rw [ha]
    exact (canonical14676 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA889 sourceB889 sourceC889
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm889, Integer.Sparse.eval]
  linarith only [hs]

def sourceA890 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB890 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC890 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceForm890 : Integer.Sparse Master := [(Sum.inr 2617, 1), (Sum.inr 3069, 1), (Sum.inr 3789, 1), (Sum.inr 3872, 2), (Sum.inr 3875, 1), (Sum.inr 4091, -1)]

theorem sourceEq890 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm890 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA890 + difference 0 3) (sourceB890 + difference 3 0) sourceC890) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA890 + difference 0 3) (sourceB890 + difference 3 0) sourceC890) = raw14673 := by
      apply Matrix.ext; unfold tripleCharges sourceA890 sourceB890 sourceC890 difference raw14673; decide +kernel
    rw [ha]
    exact (canonical14673 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA890 + difference 1 3) (sourceB890 + difference 3 1) sourceC890) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA890 + difference 1 3) (sourceB890 + difference 3 1) sourceC890) = raw14683 := by
      apply Matrix.ext; unfold tripleCharges sourceA890 sourceB890 sourceC890 difference raw14683; decide +kernel
    rw [ha]
    exact (canonical14683 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA890 + difference 2 3) (sourceB890 + difference 3 2) sourceC890) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3789) := by
    have ha : (tripleCharges (sourceA890 + difference 2 3) (sourceB890 + difference 3 2) sourceC890) = raw14690 := by
      apply Matrix.ext; unfold tripleCharges sourceA890 sourceB890 sourceC890 difference raw14690; decide +kernel
    rw [ha]
    exact (canonical14690 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA890 + difference 3 3) (sourceB890 + difference 3 3) sourceC890) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA890 + difference 3 3) (sourceB890 + difference 3 3) sourceC890) = raw14670 := by
      apply Matrix.ext; unfold tripleCharges sourceA890 sourceB890 sourceC890 difference raw14670; decide +kernel
    rw [ha]
    exact (canonical14670 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA890 + difference 4 3) (sourceB890 + difference 3 4) sourceC890) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3069) := by
    have ha : (tripleCharges (sourceA890 + difference 4 3) (sourceB890 + difference 3 4) sourceC890) = raw14698 := by
      apply Matrix.ext; unfold tripleCharges sourceA890 sourceB890 sourceC890 difference raw14698; decide +kernel
    rw [ha]
    exact (canonical14698 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA890 + difference 5 3) (sourceB890 + difference 3 5) sourceC890) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2617) := by
    have ha : (tripleCharges (sourceA890 + difference 5 3) (sourceB890 + difference 3 5) sourceC890) = raw14699 := by
      apply Matrix.ext; unfold tripleCharges sourceA890 sourceB890 sourceC890 difference raw14699; decide +kernel
    rw [ha]
    exact (canonical14699 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA890 + sourceB890) sourceC890) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA890 + sourceB890) sourceC890) = raw14676 := by
      apply Matrix.ext; unfold doubleCharges sourceA890 sourceB890 sourceC890 raw14676; decide +kernel
    rw [ha]
    exact (canonical14676 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA890 sourceB890 sourceC890
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm890, Integer.Sparse.eval]
  linarith only [hs]

def sourceA891 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB891 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC891 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceForm891 : Integer.Sparse Master := [(Sum.inr 2919, 1), (Sum.inr 2920, 1), (Sum.inr 2928, 1), (Sum.inr 2945, 1), (Sum.inr 3069, 1), (Sum.inr 3872, 1), (Sum.inr 4091, -1)]

theorem sourceEq891 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm891 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA891 + difference 4 0) (sourceB891 + difference 0 4) sourceC891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2919) := by
    have ha : (tripleCharges (sourceA891 + difference 4 0) (sourceB891 + difference 0 4) sourceC891) = raw14680 := by
      apply Matrix.ext; unfold tripleCharges sourceA891 sourceB891 sourceC891 difference raw14680; decide +kernel
    rw [ha]
    exact (canonical14680 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA891 + difference 4 1) (sourceB891 + difference 1 4) sourceC891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2945) := by
    have ha : (tripleCharges (sourceA891 + difference 4 1) (sourceB891 + difference 1 4) sourceC891) = raw14688 := by
      apply Matrix.ext; unfold tripleCharges sourceA891 sourceB891 sourceC891 difference raw14688; decide +kernel
    rw [ha]
    exact (canonical14688 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA891 + difference 4 2) (sourceB891 + difference 2 4) sourceC891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2920) := by
    have ha : (tripleCharges (sourceA891 + difference 4 2) (sourceB891 + difference 2 4) sourceC891) = raw14694 := by
      apply Matrix.ext; unfold tripleCharges sourceA891 sourceB891 sourceC891 difference raw14694; decide +kernel
    rw [ha]
    exact (canonical14694 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA891 + difference 4 3) (sourceB891 + difference 3 4) sourceC891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3069) := by
    have ha : (tripleCharges (sourceA891 + difference 4 3) (sourceB891 + difference 3 4) sourceC891) = raw14698 := by
      apply Matrix.ext; unfold tripleCharges sourceA891 sourceB891 sourceC891 difference raw14698; decide +kernel
    rw [ha]
    exact (canonical14698 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA891 + difference 4 4) (sourceB891 + difference 4 4) sourceC891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA891 + difference 4 4) (sourceB891 + difference 4 4) sourceC891) = raw14670 := by
      apply Matrix.ext; unfold tripleCharges sourceA891 sourceB891 sourceC891 difference raw14670; decide +kernel
    rw [ha]
    exact (canonical14670 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA891 + difference 4 5) (sourceB891 + difference 5 4) sourceC891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2928) := by
    have ha : (tripleCharges (sourceA891 + difference 4 5) (sourceB891 + difference 5 4) sourceC891) = raw14700 := by
      apply Matrix.ext; unfold tripleCharges sourceA891 sourceB891 sourceC891 difference raw14700; decide +kernel
    rw [ha]
    exact (canonical14700 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA891 + sourceB891) sourceC891) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA891 + sourceB891) sourceC891) = raw14676 := by
      apply Matrix.ext; unfold doubleCharges sourceA891 sourceB891 sourceC891 raw14676; decide +kernel
    rw [ha]
    exact (canonical14676 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA891 sourceB891 sourceC891
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm891, Integer.Sparse.eval]
  linarith only [hs]

def sourceA892 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB892 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC892 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm892 : Integer.Sparse Master := [(Sum.inr 5052, 1), (Sum.inr 5053, 1), (Sum.inr 5060, 1), (Sum.inr 5086, 1), (Sum.inr 5131, 1), (Sum.inr 5135, 1), (Sum.inr 5153, 2), (Sum.inr 5154, 1), (Sum.inr 5160, 1), (Sum.inr 5266, 1), (Sum.inr 5267, 1), (Sum.inr 5299, 1), (Sum.inr 5342, 1), (Sum.inr 5360, 1), (Sum.inr 5375, 1), (Sum.inr 5379, 1), (Sum.inr 5382, 1), (Sum.inr 5395, 1), (Sum.inr 5411, 1), (Sum.inr 5424, 2), (Sum.inr 5425, 1), (Sum.inr 5426, 1), (Sum.inr 5428, 1), (Sum.inr 5430, 1), (Sum.inr 5435, 1), (Sum.inr 5436, 1), (Sum.inr 5438, 1), (Sum.inr 5443, 1)]

theorem sourceEq892 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm892 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA892 + difference 0 1) (sourceB892 + difference 1 0) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA892 + difference 0 1) (sourceB892 + difference 1 0) sourceC892) = raw14701 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14701; decide +kernel
    rw [ha]
    exact (canonical14701 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA892 + difference 0 2) (sourceB892 + difference 2 0) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5382) := by
    have ha : (tripleCharges (sourceA892 + difference 0 2) (sourceB892 + difference 2 0) sourceC892) = raw14702 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14702; decide +kernel
    rw [ha]
    exact (canonical14702 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA892 + difference 0 3) (sourceB892 + difference 3 0) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA892 + difference 0 3) (sourceB892 + difference 3 0) sourceC892) = raw14703 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14703; decide +kernel
    rw [ha]
    exact (canonical14703 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA892 + difference 0 4) (sourceB892 + difference 4 0) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA892 + difference 0 4) (sourceB892 + difference 4 0) sourceC892) = raw14704 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14704; decide +kernel
    rw [ha]
    exact (canonical14704 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA892 + difference 0 5) (sourceB892 + difference 5 0) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA892 + difference 0 5) (sourceB892 + difference 5 0) sourceC892) = raw14705 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14705; decide +kernel
    rw [ha]
    exact (canonical14705 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA892 + difference 1 0) (sourceB892 + difference 0 1) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5153) := by
    have ha : (tripleCharges (sourceA892 + difference 1 0) (sourceB892 + difference 0 1) sourceC892) = raw14706 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14706; decide +kernel
    rw [ha]
    exact (canonical14706 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA892 + difference 1 2) (sourceB892 + difference 2 1) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5375) := by
    have ha : (tripleCharges (sourceA892 + difference 1 2) (sourceB892 + difference 2 1) sourceC892) = raw14707 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14707; decide +kernel
    rw [ha]
    exact (canonical14707 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA892 + difference 1 3) (sourceB892 + difference 3 1) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA892 + difference 1 3) (sourceB892 + difference 3 1) sourceC892) = raw14708 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14708; decide +kernel
    rw [ha]
    exact (canonical14708 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA892 + difference 1 4) (sourceB892 + difference 4 1) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA892 + difference 1 4) (sourceB892 + difference 4 1) sourceC892) = raw14709 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14709; decide +kernel
    rw [ha]
    exact (canonical14709 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA892 + difference 1 5) (sourceB892 + difference 5 1) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5153) := by
    have ha : (tripleCharges (sourceA892 + difference 1 5) (sourceB892 + difference 5 1) sourceC892) = raw14710 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14710; decide +kernel
    rw [ha]
    exact (canonical14710 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA892 + difference 2 0) (sourceB892 + difference 0 2) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA892 + difference 2 0) (sourceB892 + difference 0 2) sourceC892) = raw14711 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14711; decide +kernel
    rw [ha]
    exact (canonical14711 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA892 + difference 2 1) (sourceB892 + difference 1 2) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA892 + difference 2 1) (sourceB892 + difference 1 2) sourceC892) = raw14712 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14712; decide +kernel
    rw [ha]
    exact (canonical14712 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA892 + difference 2 3) (sourceB892 + difference 3 2) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA892 + difference 2 3) (sourceB892 + difference 3 2) sourceC892) = raw14713 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14713; decide +kernel
    rw [ha]
    exact (canonical14713 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA892 + difference 2 4) (sourceB892 + difference 4 2) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA892 + difference 2 4) (sourceB892 + difference 4 2) sourceC892) = raw14714 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14714; decide +kernel
    rw [ha]
    exact (canonical14714 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA892 + difference 2 5) (sourceB892 + difference 5 2) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA892 + difference 2 5) (sourceB892 + difference 5 2) sourceC892) = raw14715 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14715; decide +kernel
    rw [ha]
    exact (canonical14715 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA892 + difference 3 0) (sourceB892 + difference 0 3) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5131) := by
    have ha : (tripleCharges (sourceA892 + difference 3 0) (sourceB892 + difference 0 3) sourceC892) = raw14716 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14716; decide +kernel
    rw [ha]
    exact (canonical14716 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA892 + difference 3 1) (sourceB892 + difference 1 3) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA892 + difference 3 1) (sourceB892 + difference 1 3) sourceC892) = raw14717 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14717; decide +kernel
    rw [ha]
    exact (canonical14717 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA892 + difference 3 2) (sourceB892 + difference 2 3) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5342) := by
    have ha : (tripleCharges (sourceA892 + difference 3 2) (sourceB892 + difference 2 3) sourceC892) = raw14718 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14718; decide +kernel
    rw [ha]
    exact (canonical14718 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA892 + difference 3 4) (sourceB892 + difference 4 3) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5426) := by
    have ha : (tripleCharges (sourceA892 + difference 3 4) (sourceB892 + difference 4 3) sourceC892) = raw14719 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14719; decide +kernel
    rw [ha]
    exact (canonical14719 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA892 + difference 3 5) (sourceB892 + difference 5 3) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5154) := by
    have ha : (tripleCharges (sourceA892 + difference 3 5) (sourceB892 + difference 5 3) sourceC892) = raw14720 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14720; decide +kernel
    rw [ha]
    exact (canonical14720 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA892 + difference 4 0) (sourceB892 + difference 0 4) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5052) := by
    have ha : (tripleCharges (sourceA892 + difference 4 0) (sourceB892 + difference 0 4) sourceC892) = raw14721 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14721; decide +kernel
    rw [ha]
    exact (canonical14721 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA892 + difference 4 1) (sourceB892 + difference 1 4) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA892 + difference 4 1) (sourceB892 + difference 1 4) sourceC892) = raw14722 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14722; decide +kernel
    rw [ha]
    exact (canonical14722 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA892 + difference 4 2) (sourceB892 + difference 2 4) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5053) := by
    have ha : (tripleCharges (sourceA892 + difference 4 2) (sourceB892 + difference 2 4) sourceC892) = raw14723 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14723; decide +kernel
    rw [ha]
    exact (canonical14723 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA892 + difference 4 3) (sourceB892 + difference 3 4) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA892 + difference 4 3) (sourceB892 + difference 3 4) sourceC892) = raw14724 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14724; decide +kernel
    rw [ha]
    exact (canonical14724 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA892 + difference 4 5) (sourceB892 + difference 5 4) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5060) := by
    have ha : (tripleCharges (sourceA892 + difference 4 5) (sourceB892 + difference 5 4) sourceC892) = raw14725 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14725; decide +kernel
    rw [ha]
    exact (canonical14725 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA892 + difference 5 0) (sourceB892 + difference 0 5) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5135) := by
    have ha : (tripleCharges (sourceA892 + difference 5 0) (sourceB892 + difference 0 5) sourceC892) = raw14726 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14726; decide +kernel
    rw [ha]
    exact (canonical14726 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA892 + difference 5 1) (sourceB892 + difference 1 5) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5395) := by
    have ha : (tripleCharges (sourceA892 + difference 5 1) (sourceB892 + difference 1 5) sourceC892) = raw14727 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14727; decide +kernel
    rw [ha]
    exact (canonical14727 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA892 + difference 5 2) (sourceB892 + difference 2 5) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA892 + difference 5 2) (sourceB892 + difference 2 5) sourceC892) = raw14728 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14728; decide +kernel
    rw [ha]
    exact (canonical14728 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA892 + difference 5 3) (sourceB892 + difference 3 5) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5428) := by
    have ha : (tripleCharges (sourceA892 + difference 5 3) (sourceB892 + difference 3 5) sourceC892) = raw14729 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14729; decide +kernel
    rw [ha]
    exact (canonical14729 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA892 + difference 5 4) (sourceB892 + difference 4 5) sourceC892) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA892 + difference 5 4) (sourceB892 + difference 4 5) sourceC892) = raw14730 := by
      apply Matrix.ext; unfold tripleCharges sourceA892 sourceB892 sourceC892 difference raw14730; decide +kernel
    rw [ha]
    exact (canonical14730 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA892 sourceB892 sourceC892
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm892, Integer.Sparse.eval]
  linarith only [hs]

def sourceA893 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB893 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC893 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm893 : Integer.Sparse Master := [(Sum.inr 2906, 1), (Sum.inr 2907, 1), (Sum.inr 2909, 1), (Sum.inr 2951, 1), (Sum.inr 3051, 1), (Sum.inr 3430, 1), (Sum.inr 3437, 1), (Sum.inr 3464, 1), (Sum.inr 3515, 1), (Sum.inr 3518, 1), (Sum.inr 3535, 1), (Sum.inr 3541, 1), (Sum.inr 3559, 1), (Sum.inr 3712, 1), (Sum.inr 3714, 1), (Sum.inr 3730, 1), (Sum.inr 3762, 1), (Sum.inr 3794, 1), (Sum.inr 3809, 1), (Sum.inr 3832, 1), (Sum.inr 3838, 1), (Sum.inr 3841, 1), (Sum.inr 3845, 1), (Sum.inr 3853, 1), (Sum.inr 3862, 1), (Sum.inr 3872, 1), (Sum.inr 3877, 1), (Sum.inr 3972, 1), (Sum.inr 3990, 1), (Sum.inr 3993, 1)]

theorem sourceEq893 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm893 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA893 + difference 0 1) (sourceB893 + difference 1 0) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA893 + difference 0 1) (sourceB893 + difference 1 0) sourceC893) = raw14731 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14731; decide +kernel
    rw [ha]
    exact (canonical14731 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA893 + difference 0 2) (sourceB893 + difference 2 0) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3730) := by
    have ha : (tripleCharges (sourceA893 + difference 0 2) (sourceB893 + difference 2 0) sourceC893) = raw14732 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14732; decide +kernel
    rw [ha]
    exact (canonical14732 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA893 + difference 0 3) (sourceB893 + difference 3 0) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA893 + difference 0 3) (sourceB893 + difference 3 0) sourceC893) = raw14733 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14733; decide +kernel
    rw [ha]
    exact (canonical14733 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA893 + difference 0 4) (sourceB893 + difference 4 0) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA893 + difference 0 4) (sourceB893 + difference 4 0) sourceC893) = raw14734 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14734; decide +kernel
    rw [ha]
    exact (canonical14734 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA893 + difference 0 5) (sourceB893 + difference 5 0) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2951) := by
    have ha : (tripleCharges (sourceA893 + difference 0 5) (sourceB893 + difference 5 0) sourceC893) = raw14735 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14735; decide +kernel
    rw [ha]
    exact (canonical14735 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA893 + difference 1 0) (sourceB893 + difference 0 1) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3559) := by
    have ha : (tripleCharges (sourceA893 + difference 1 0) (sourceB893 + difference 0 1) sourceC893) = raw14736 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14736; decide +kernel
    rw [ha]
    exact (canonical14736 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA893 + difference 1 2) (sourceB893 + difference 2 1) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3714) := by
    have ha : (tripleCharges (sourceA893 + difference 1 2) (sourceB893 + difference 2 1) sourceC893) = raw14737 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14737; decide +kernel
    rw [ha]
    exact (canonical14737 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA893 + difference 1 3) (sourceB893 + difference 3 1) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA893 + difference 1 3) (sourceB893 + difference 3 1) sourceC893) = raw14738 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14738; decide +kernel
    rw [ha]
    exact (canonical14738 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA893 + difference 1 4) (sourceB893 + difference 4 1) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA893 + difference 1 4) (sourceB893 + difference 4 1) sourceC893) = raw14739 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14739; decide +kernel
    rw [ha]
    exact (canonical14739 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA893 + difference 1 5) (sourceB893 + difference 5 1) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2909) := by
    have ha : (tripleCharges (sourceA893 + difference 1 5) (sourceB893 + difference 5 1) sourceC893) = raw14740 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14740; decide +kernel
    rw [ha]
    exact (canonical14740 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA893 + difference 2 0) (sourceB893 + difference 0 2) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA893 + difference 2 0) (sourceB893 + difference 0 2) sourceC893) = raw14741 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14741; decide +kernel
    rw [ha]
    exact (canonical14741 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA893 + difference 2 1) (sourceB893 + difference 1 2) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA893 + difference 2 1) (sourceB893 + difference 1 2) sourceC893) = raw14742 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14742; decide +kernel
    rw [ha]
    exact (canonical14742 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA893 + difference 2 3) (sourceB893 + difference 3 2) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA893 + difference 2 3) (sourceB893 + difference 3 2) sourceC893) = raw14743 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14743; decide +kernel
    rw [ha]
    exact (canonical14743 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA893 + difference 2 4) (sourceB893 + difference 4 2) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA893 + difference 2 4) (sourceB893 + difference 4 2) sourceC893) = raw14744 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14744; decide +kernel
    rw [ha]
    exact (canonical14744 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA893 + difference 2 5) (sourceB893 + difference 5 2) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA893 + difference 2 5) (sourceB893 + difference 5 2) sourceC893) = raw14745 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14745; decide +kernel
    rw [ha]
    exact (canonical14745 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA893 + difference 3 0) (sourceB893 + difference 0 3) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3518) := by
    have ha : (tripleCharges (sourceA893 + difference 3 0) (sourceB893 + difference 0 3) sourceC893) = raw14746 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14746; decide +kernel
    rw [ha]
    exact (canonical14746 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA893 + difference 3 1) (sourceB893 + difference 1 3) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA893 + difference 3 1) (sourceB893 + difference 1 3) sourceC893) = raw14747 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14747; decide +kernel
    rw [ha]
    exact (canonical14747 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA893 + difference 3 2) (sourceB893 + difference 2 3) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3712) := by
    have ha : (tripleCharges (sourceA893 + difference 3 2) (sourceB893 + difference 2 3) sourceC893) = raw14748 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14748; decide +kernel
    rw [ha]
    exact (canonical14748 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA893 + difference 3 4) (sourceB893 + difference 4 3) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3841) := by
    have ha : (tripleCharges (sourceA893 + difference 3 4) (sourceB893 + difference 4 3) sourceC893) = raw14749 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14749; decide +kernel
    rw [ha]
    exact (canonical14749 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA893 + difference 3 5) (sourceB893 + difference 5 3) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2907) := by
    have ha : (tripleCharges (sourceA893 + difference 3 5) (sourceB893 + difference 5 3) sourceC893) = raw14750 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14750; decide +kernel
    rw [ha]
    exact (canonical14750 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA893 + difference 4 0) (sourceB893 + difference 0 4) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3437) := by
    have ha : (tripleCharges (sourceA893 + difference 4 0) (sourceB893 + difference 0 4) sourceC893) = raw14751 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14751; decide +kernel
    rw [ha]
    exact (canonical14751 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA893 + difference 4 1) (sourceB893 + difference 1 4) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA893 + difference 4 1) (sourceB893 + difference 1 4) sourceC893) = raw14752 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14752; decide +kernel
    rw [ha]
    exact (canonical14752 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA893 + difference 4 2) (sourceB893 + difference 2 4) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3430) := by
    have ha : (tripleCharges (sourceA893 + difference 4 2) (sourceB893 + difference 2 4) sourceC893) = raw14753 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14753; decide +kernel
    rw [ha]
    exact (canonical14753 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA893 + difference 4 3) (sourceB893 + difference 3 4) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA893 + difference 4 3) (sourceB893 + difference 3 4) sourceC893) = raw14754 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14754; decide +kernel
    rw [ha]
    exact (canonical14754 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA893 + difference 4 5) (sourceB893 + difference 5 4) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2906) := by
    have ha : (tripleCharges (sourceA893 + difference 4 5) (sourceB893 + difference 5 4) sourceC893) = raw14755 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14755; decide +kernel
    rw [ha]
    exact (canonical14755 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA893 + difference 5 0) (sourceB893 + difference 0 5) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3515) := by
    have ha : (tripleCharges (sourceA893 + difference 5 0) (sourceB893 + difference 0 5) sourceC893) = raw14756 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14756; decide +kernel
    rw [ha]
    exact (canonical14756 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA893 + difference 5 1) (sourceB893 + difference 1 5) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3794) := by
    have ha : (tripleCharges (sourceA893 + difference 5 1) (sourceB893 + difference 1 5) sourceC893) = raw14757 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14757; decide +kernel
    rw [ha]
    exact (canonical14757 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA893 + difference 5 2) (sourceB893 + difference 2 5) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA893 + difference 5 2) (sourceB893 + difference 2 5) sourceC893) = raw14758 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14758; decide +kernel
    rw [ha]
    exact (canonical14758 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA893 + difference 5 3) (sourceB893 + difference 3 5) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA893 + difference 5 3) (sourceB893 + difference 3 5) sourceC893) = raw14759 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14759; decide +kernel
    rw [ha]
    exact (canonical14759 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA893 + difference 5 4) (sourceB893 + difference 4 5) sourceC893) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA893 + difference 5 4) (sourceB893 + difference 4 5) sourceC893) = raw14760 := by
      apply Matrix.ext; unfold tripleCharges sourceA893 sourceB893 sourceC893 difference raw14760; decide +kernel
    rw [ha]
    exact (canonical14760 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA893 sourceB893 sourceC893
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm893, Integer.Sparse.eval]
  linarith only [hs]

def sourceA894 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB894 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC894 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm894 : Integer.Sparse Master := [(Sum.inr 2454, 1), (Sum.inr 2455, 1), (Sum.inr 2463, 1), (Sum.inr 2494, 1), (Sum.inr 2732, 1), (Sum.inr 2905, 1), (Sum.inr 2909, 1), (Sum.inr 2934, 1), (Sum.inr 3039, 1), (Sum.inr 3558, 1), (Sum.inr 3559, 1), (Sum.inr 3561, 1), (Sum.inr 3573, 1), (Sum.inr 3679, 1), (Sum.inr 3698, 1), (Sum.inr 3714, 1), (Sum.inr 3724, 1), (Sum.inr 3838, 1), (Sum.inr 3839, 1), (Sum.inr 3841, 1), (Sum.inr 3853, 1), (Sum.inr 3866, 1), (Sum.inr 3871, 1), (Sum.inr 3876, 1), (Sum.inr 3877, 1), (Sum.inr 3883, 1), (Sum.inr 3889, 1), (Sum.inr 3970, 1), (Sum.inr 3990, 1), (Sum.inr 4003, 1)]

theorem sourceEq894 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm894 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA894 + difference 0 1) (sourceB894 + difference 1 0) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA894 + difference 0 1) (sourceB894 + difference 1 0) sourceC894) = raw14761 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14761; decide +kernel
    rw [ha]
    exact (canonical14761 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA894 + difference 0 2) (sourceB894 + difference 2 0) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3866) := by
    have ha : (tripleCharges (sourceA894 + difference 0 2) (sourceB894 + difference 2 0) sourceC894) = raw14762 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14762; decide +kernel
    rw [ha]
    exact (canonical14762 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA894 + difference 0 3) (sourceB894 + difference 3 0) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA894 + difference 0 3) (sourceB894 + difference 3 0) sourceC894) = raw14763 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14763; decide +kernel
    rw [ha]
    exact (canonical14763 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA894 + difference 0 4) (sourceB894 + difference 4 0) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA894 + difference 0 4) (sourceB894 + difference 4 0) sourceC894) = raw14764 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14764; decide +kernel
    rw [ha]
    exact (canonical14764 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA894 + difference 0 5) (sourceB894 + difference 5 0) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA894 + difference 0 5) (sourceB894 + difference 5 0) sourceC894) = raw14765 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14765; decide +kernel
    rw [ha]
    exact (canonical14765 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA894 + difference 1 0) (sourceB894 + difference 0 1) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2909) := by
    have ha : (tripleCharges (sourceA894 + difference 1 0) (sourceB894 + difference 0 1) sourceC894) = raw14766 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14766; decide +kernel
    rw [ha]
    exact (canonical14766 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA894 + difference 1 2) (sourceB894 + difference 2 1) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3714) := by
    have ha : (tripleCharges (sourceA894 + difference 1 2) (sourceB894 + difference 2 1) sourceC894) = raw14767 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14767; decide +kernel
    rw [ha]
    exact (canonical14767 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA894 + difference 1 3) (sourceB894 + difference 3 1) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA894 + difference 1 3) (sourceB894 + difference 3 1) sourceC894) = raw14768 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14768; decide +kernel
    rw [ha]
    exact (canonical14768 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA894 + difference 1 4) (sourceB894 + difference 4 1) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA894 + difference 1 4) (sourceB894 + difference 4 1) sourceC894) = raw14769 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14769; decide +kernel
    rw [ha]
    exact (canonical14769 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA894 + difference 1 5) (sourceB894 + difference 5 1) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3559) := by
    have ha : (tripleCharges (sourceA894 + difference 1 5) (sourceB894 + difference 5 1) sourceC894) = raw14770 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14770; decide +kernel
    rw [ha]
    exact (canonical14770 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA894 + difference 2 0) (sourceB894 + difference 0 2) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA894 + difference 2 0) (sourceB894 + difference 0 2) sourceC894) = raw14771 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14771; decide +kernel
    rw [ha]
    exact (canonical14771 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA894 + difference 2 1) (sourceB894 + difference 1 2) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA894 + difference 2 1) (sourceB894 + difference 1 2) sourceC894) = raw14772 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14772; decide +kernel
    rw [ha]
    exact (canonical14772 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA894 + difference 2 3) (sourceB894 + difference 3 2) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA894 + difference 2 3) (sourceB894 + difference 3 2) sourceC894) = raw14773 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14773; decide +kernel
    rw [ha]
    exact (canonical14773 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA894 + difference 2 4) (sourceB894 + difference 4 2) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA894 + difference 2 4) (sourceB894 + difference 4 2) sourceC894) = raw14774 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14774; decide +kernel
    rw [ha]
    exact (canonical14774 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA894 + difference 2 5) (sourceB894 + difference 5 2) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA894 + difference 2 5) (sourceB894 + difference 5 2) sourceC894) = raw14775 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14775; decide +kernel
    rw [ha]
    exact (canonical14775 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA894 + difference 3 0) (sourceB894 + difference 0 3) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2905) := by
    have ha : (tripleCharges (sourceA894 + difference 3 0) (sourceB894 + difference 0 3) sourceC894) = raw14776 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14776; decide +kernel
    rw [ha]
    exact (canonical14776 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA894 + difference 3 1) (sourceB894 + difference 1 3) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3698) := by
    have ha : (tripleCharges (sourceA894 + difference 3 1) (sourceB894 + difference 1 3) sourceC894) = raw14777 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14777; decide +kernel
    rw [ha]
    exact (canonical14777 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA894 + difference 3 2) (sourceB894 + difference 2 3) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3679) := by
    have ha : (tripleCharges (sourceA894 + difference 3 2) (sourceB894 + difference 2 3) sourceC894) = raw14778 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14778; decide +kernel
    rw [ha]
    exact (canonical14778 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA894 + difference 3 4) (sourceB894 + difference 4 3) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3841) := by
    have ha : (tripleCharges (sourceA894 + difference 3 4) (sourceB894 + difference 4 3) sourceC894) = raw14779 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14779; decide +kernel
    rw [ha]
    exact (canonical14779 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA894 + difference 3 5) (sourceB894 + difference 5 3) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3561) := by
    have ha : (tripleCharges (sourceA894 + difference 3 5) (sourceB894 + difference 5 3) sourceC894) = raw14780 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14780; decide +kernel
    rw [ha]
    exact (canonical14780 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA894 + difference 4 0) (sourceB894 + difference 0 4) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2454) := by
    have ha : (tripleCharges (sourceA894 + difference 4 0) (sourceB894 + difference 0 4) sourceC894) = raw14781 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14781; decide +kernel
    rw [ha]
    exact (canonical14781 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA894 + difference 4 1) (sourceB894 + difference 1 4) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA894 + difference 4 1) (sourceB894 + difference 1 4) sourceC894) = raw14782 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14782; decide +kernel
    rw [ha]
    exact (canonical14782 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA894 + difference 4 2) (sourceB894 + difference 2 4) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2455) := by
    have ha : (tripleCharges (sourceA894 + difference 4 2) (sourceB894 + difference 2 4) sourceC894) = raw14783 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14783; decide +kernel
    rw [ha]
    exact (canonical14783 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA894 + difference 4 3) (sourceB894 + difference 3 4) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA894 + difference 4 3) (sourceB894 + difference 3 4) sourceC894) = raw14784 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14784; decide +kernel
    rw [ha]
    exact (canonical14784 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA894 + difference 4 5) (sourceB894 + difference 5 4) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2463) := by
    have ha : (tripleCharges (sourceA894 + difference 4 5) (sourceB894 + difference 5 4) sourceC894) = raw14785 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14785; decide +kernel
    rw [ha]
    exact (canonical14785 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA894 + difference 5 0) (sourceB894 + difference 0 5) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2934) := by
    have ha : (tripleCharges (sourceA894 + difference 5 0) (sourceB894 + difference 0 5) sourceC894) = raw14786 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14786; decide +kernel
    rw [ha]
    exact (canonical14786 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA894 + difference 5 1) (sourceB894 + difference 1 5) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3970) := by
    have ha : (tripleCharges (sourceA894 + difference 5 1) (sourceB894 + difference 1 5) sourceC894) = raw14787 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14787; decide +kernel
    rw [ha]
    exact (canonical14787 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA894 + difference 5 2) (sourceB894 + difference 2 5) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3724) := by
    have ha : (tripleCharges (sourceA894 + difference 5 2) (sourceB894 + difference 2 5) sourceC894) = raw14788 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14788; decide +kernel
    rw [ha]
    exact (canonical14788 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA894 + difference 5 3) (sourceB894 + difference 3 5) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4003) := by
    have ha : (tripleCharges (sourceA894 + difference 5 3) (sourceB894 + difference 3 5) sourceC894) = raw14789 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14789; decide +kernel
    rw [ha]
    exact (canonical14789 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA894 + difference 5 4) (sourceB894 + difference 4 5) sourceC894) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA894 + difference 5 4) (sourceB894 + difference 4 5) sourceC894) = raw14790 := by
      apply Matrix.ext; unfold tripleCharges sourceA894 sourceB894 sourceC894 difference raw14790; decide +kernel
    rw [ha]
    exact (canonical14790 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA894 sourceB894 sourceC894
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm894, Integer.Sparse.eval]
  linarith only [hs]

def sourceA895 : Charge := ![0, 1, -1, 1, 1, -2]
def sourceB895 : Charge := ![2, 0, 1, -1, -2, 0]
def sourceC895 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm895 : Integer.Sparse Master := [(Sum.inr 2587, 1), (Sum.inr 3730, 1), (Sum.inr 3840, 1), (Sum.inr 3843, 1), (Sum.inr 3848, 1), (Sum.inr 3857, 1), (Sum.inr 4092, -1)]

theorem sourceEq895 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm895 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA895 + difference 0 0) (sourceB895 + difference 0 0) sourceC895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA895 + difference 0 0) (sourceB895 + difference 0 0) sourceC895) = raw14791 := by
      apply Matrix.ext; unfold tripleCharges sourceA895 sourceB895 sourceC895 difference raw14791; decide +kernel
    rw [ha]
    exact (canonical14791 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA895 + difference 0 1) (sourceB895 + difference 1 0) sourceC895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA895 + difference 0 1) (sourceB895 + difference 1 0) sourceC895) = raw14792 := by
      apply Matrix.ext; unfold tripleCharges sourceA895 sourceB895 sourceC895 difference raw14792; decide +kernel
    rw [ha]
    exact (canonical14792 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA895 + difference 0 2) (sourceB895 + difference 2 0) sourceC895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3730) := by
    have ha : (tripleCharges (sourceA895 + difference 0 2) (sourceB895 + difference 2 0) sourceC895) = raw14793 := by
      apply Matrix.ext; unfold tripleCharges sourceA895 sourceB895 sourceC895 difference raw14793; decide +kernel
    rw [ha]
    exact (canonical14793 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA895 + difference 0 3) (sourceB895 + difference 3 0) sourceC895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA895 + difference 0 3) (sourceB895 + difference 3 0) sourceC895) = raw14794 := by
      apply Matrix.ext; unfold tripleCharges sourceA895 sourceB895 sourceC895 difference raw14794; decide +kernel
    rw [ha]
    exact (canonical14794 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA895 + difference 0 4) (sourceB895 + difference 4 0) sourceC895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA895 + difference 0 4) (sourceB895 + difference 4 0) sourceC895) = raw14795 := by
      apply Matrix.ext; unfold tripleCharges sourceA895 sourceB895 sourceC895 difference raw14795; decide +kernel
    rw [ha]
    exact (canonical14795 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA895 + difference 0 5) (sourceB895 + difference 5 0) sourceC895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2587) := by
    have ha : (tripleCharges (sourceA895 + difference 0 5) (sourceB895 + difference 5 0) sourceC895) = raw14796 := by
      apply Matrix.ext; unfold tripleCharges sourceA895 sourceB895 sourceC895 difference raw14796; decide +kernel
    rw [ha]
    exact (canonical14796 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA895 + sourceB895) sourceC895) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA895 + sourceB895) sourceC895) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA895 sourceB895 sourceC895 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA895 sourceB895 sourceC895
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm895, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
