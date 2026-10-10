import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical53

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA288 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB288 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC288 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm288 : Integer.Sparse Master := [(Sum.inr 3533, 1), (Sum.inr 3539, 1), (Sum.inr 3540, 1), (Sum.inr 3541, 1), (Sum.inr 3544, 1), (Sum.inr 3632, 1), (Sum.inr 4084, -1)]

theorem sourceEq288 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm288 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA288 + difference 0 4) (sourceB288 + difference 4 0) sourceC288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA288 + difference 0 4) (sourceB288 + difference 4 0) sourceC288) = raw6437 := by
      apply Matrix.ext; unfold tripleCharges sourceA288 sourceB288 sourceC288 difference raw6437; decide +kernel
    rw [ha]
    exact (canonical6437 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA288 + difference 1 4) (sourceB288 + difference 4 1) sourceC288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3632) := by
    have ha : (tripleCharges (sourceA288 + difference 1 4) (sourceB288 + difference 4 1) sourceC288) = raw6445 := by
      apply Matrix.ext; unfold tripleCharges sourceA288 sourceB288 sourceC288 difference raw6445; decide +kernel
    rw [ha]
    exact (canonical6445 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA288 + difference 2 4) (sourceB288 + difference 4 2) sourceC288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA288 + difference 2 4) (sourceB288 + difference 4 2) sourceC288) = raw6450 := by
      apply Matrix.ext; unfold tripleCharges sourceA288 sourceB288 sourceC288 difference raw6450; decide +kernel
    rw [ha]
    exact (canonical6450 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA288 + difference 3 4) (sourceB288 + difference 4 3) sourceC288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA288 + difference 3 4) (sourceB288 + difference 4 3) sourceC288) = raw6454 := by
      apply Matrix.ext; unfold tripleCharges sourceA288 sourceB288 sourceC288 difference raw6454; decide +kernel
    rw [ha]
    exact (canonical6454 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA288 + difference 4 4) (sourceB288 + difference 4 4) sourceC288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA288 + difference 4 4) (sourceB288 + difference 4 4) sourceC288) = raw6122 := by
      apply Matrix.ext; unfold tripleCharges sourceA288 sourceB288 sourceC288 difference raw6122; decide +kernel
    rw [ha]
    exact (canonical6122 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA288 + difference 5 4) (sourceB288 + difference 4 5) sourceC288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA288 + difference 5 4) (sourceB288 + difference 4 5) sourceC288) = raw6456 := by
      apply Matrix.ext; unfold tripleCharges sourceA288 sourceB288 sourceC288 difference raw6456; decide +kernel
    rw [ha]
    exact (canonical6456 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA288 + sourceB288) sourceC288) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA288 + sourceB288) sourceC288) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA288 sourceB288 sourceC288 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA288 sourceB288 sourceC288
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm288, Integer.Sparse.eval]
  linarith only [hs]

def sourceA289 : Charge := ![1, -1, 0, 1, 1, -2]
def sourceB289 : Charge := ![2, 1, 0, -1, -2, 0]
def sourceC289 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm289 : Integer.Sparse Master := [(Sum.inr 2054, 1), (Sum.inr 3392, 1), (Sum.inr 3494, 1), (Sum.inr 3540, 1), (Sum.inr 3544, 1), (Sum.inr 3548, 1), (Sum.inr 4084, -1)]

theorem sourceEq289 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm289 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA289 + difference 5 0) (sourceB289 + difference 0 5) sourceC289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA289 + difference 5 0) (sourceB289 + difference 0 5) sourceC289) = raw6443 := by
      apply Matrix.ext; unfold tripleCharges sourceA289 sourceB289 sourceC289 difference raw6443; decide +kernel
    rw [ha]
    exact (canonical6443 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA289 + difference 5 1) (sourceB289 + difference 1 5) sourceC289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3392) := by
    have ha : (tripleCharges (sourceA289 + difference 5 1) (sourceB289 + difference 1 5) sourceC289) = raw6449 := by
      apply Matrix.ext; unfold tripleCharges sourceA289 sourceB289 sourceC289 difference raw6449; decide +kernel
    rw [ha]
    exact (canonical6449 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA289 + difference 5 2) (sourceB289 + difference 2 5) sourceC289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3494) := by
    have ha : (tripleCharges (sourceA289 + difference 5 2) (sourceB289 + difference 2 5) sourceC289) = raw6453 := by
      apply Matrix.ext; unfold tripleCharges sourceA289 sourceB289 sourceC289 difference raw6453; decide +kernel
    rw [ha]
    exact (canonical6453 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA289 + difference 5 3) (sourceB289 + difference 3 5) sourceC289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA289 + difference 5 3) (sourceB289 + difference 3 5) sourceC289) = raw6123 := by
      apply Matrix.ext; unfold tripleCharges sourceA289 sourceB289 sourceC289 difference raw6123; decide +kernel
    rw [ha]
    exact (canonical6123 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA289 + difference 5 4) (sourceB289 + difference 4 5) sourceC289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA289 + difference 5 4) (sourceB289 + difference 4 5) sourceC289) = raw6456 := by
      apply Matrix.ext; unfold tripleCharges sourceA289 sourceB289 sourceC289 difference raw6456; decide +kernel
    rw [ha]
    exact (canonical6456 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA289 + difference 5 5) (sourceB289 + difference 5 5) sourceC289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA289 + difference 5 5) (sourceB289 + difference 5 5) sourceC289) = raw6122 := by
      apply Matrix.ext; unfold tripleCharges sourceA289 sourceB289 sourceC289 difference raw6122; decide +kernel
    rw [ha]
    exact (canonical6122 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA289 + sourceB289) sourceC289) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA289 + sourceB289) sourceC289) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA289 sourceB289 sourceC289 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA289 sourceB289 sourceC289
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm289, Integer.Sparse.eval]
  linarith only [hs]

def sourceA290 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB290 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC290 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceForm290 : Integer.Sparse Master := [(Sum.inr 4563, 1), (Sum.inr 4564, 1), (Sum.inr 4565, 1), (Sum.inr 4571, 1), (Sum.inr 4603, 1), (Sum.inr 5052, 1), (Sum.inr 5062, 1), (Sum.inr 5085, 1), (Sum.inr 5087, 1), (Sum.inr 5090, 1), (Sum.inr 5102, 1), (Sum.inr 5131, 1), (Sum.inr 5135, 1), (Sum.inr 5153, 1), (Sum.inr 5208, 1), (Sum.inr 5210, 1), (Sum.inr 5211, 1), (Sum.inr 5265, 1), (Sum.inr 5266, 1), (Sum.inr 5267, 1), (Sum.inr 5268, 1), (Sum.inr 5271, 1), (Sum.inr 5275, 1), (Sum.inr 5299, 2), (Sum.inr 5300, 1), (Sum.inr 5411, 1), (Sum.inr 5425, 1), (Sum.inr 5435, 1), (Sum.inr 5443, 1)]

theorem sourceEq290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm290 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA290 + difference 0 1) (sourceB290 + difference 1 0) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA290 + difference 0 1) (sourceB290 + difference 1 0) sourceC290) = raw6457 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6457; decide +kernel
    rw [ha]
    exact (canonical6457 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA290 + difference 0 2) (sourceB290 + difference 2 0) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA290 + difference 0 2) (sourceB290 + difference 2 0) sourceC290) = raw6458 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6458; decide +kernel
    rw [ha]
    exact (canonical6458 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA290 + difference 0 3) (sourceB290 + difference 3 0) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA290 + difference 0 3) (sourceB290 + difference 3 0) sourceC290) = raw6459 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6459; decide +kernel
    rw [ha]
    exact (canonical6459 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA290 + difference 0 4) (sourceB290 + difference 4 0) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA290 + difference 0 4) (sourceB290 + difference 4 0) sourceC290) = raw6460 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6460; decide +kernel
    rw [ha]
    exact (canonical6460 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA290 + difference 0 5) (sourceB290 + difference 5 0) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA290 + difference 0 5) (sourceB290 + difference 5 0) sourceC290) = raw6461 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6461; decide +kernel
    rw [ha]
    exact (canonical6461 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA290 + difference 1 0) (sourceB290 + difference 0 1) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4571) := by
    have ha : (tripleCharges (sourceA290 + difference 1 0) (sourceB290 + difference 0 1) sourceC290) = raw6462 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6462; decide +kernel
    rw [ha]
    exact (canonical6462 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA290 + difference 1 2) (sourceB290 + difference 2 1) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5153) := by
    have ha : (tripleCharges (sourceA290 + difference 1 2) (sourceB290 + difference 2 1) sourceC290) = raw6463 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6463; decide +kernel
    rw [ha]
    exact (canonical6463 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA290 + difference 1 3) (sourceB290 + difference 3 1) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5211) := by
    have ha : (tripleCharges (sourceA290 + difference 1 3) (sourceB290 + difference 3 1) sourceC290) = raw6464 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6464; decide +kernel
    rw [ha]
    exact (canonical6464 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA290 + difference 1 4) (sourceB290 + difference 4 1) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA290 + difference 1 4) (sourceB290 + difference 4 1) sourceC290) = raw6465 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6465; decide +kernel
    rw [ha]
    exact (canonical6465 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA290 + difference 1 5) (sourceB290 + difference 5 1) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA290 + difference 1 5) (sourceB290 + difference 5 1) sourceC290) = raw6466 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6466; decide +kernel
    rw [ha]
    exact (canonical6466 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA290 + difference 2 0) (sourceB290 + difference 0 2) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4563) := by
    have ha : (tripleCharges (sourceA290 + difference 2 0) (sourceB290 + difference 0 2) sourceC290) = raw6467 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6467; decide +kernel
    rw [ha]
    exact (canonical6467 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA290 + difference 2 1) (sourceB290 + difference 1 2) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA290 + difference 2 1) (sourceB290 + difference 1 2) sourceC290) = raw6468 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6468; decide +kernel
    rw [ha]
    exact (canonical6468 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA290 + difference 2 3) (sourceB290 + difference 3 2) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5208) := by
    have ha : (tripleCharges (sourceA290 + difference 2 3) (sourceB290 + difference 3 2) sourceC290) = raw6469 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6469; decide +kernel
    rw [ha]
    exact (canonical6469 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA290 + difference 2 4) (sourceB290 + difference 4 2) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA290 + difference 2 4) (sourceB290 + difference 4 2) sourceC290) = raw6470 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6470; decide +kernel
    rw [ha]
    exact (canonical6470 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA290 + difference 2 5) (sourceB290 + difference 5 2) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA290 + difference 2 5) (sourceB290 + difference 5 2) sourceC290) = raw6471 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6471; decide +kernel
    rw [ha]
    exact (canonical6471 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA290 + difference 3 0) (sourceB290 + difference 0 3) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4603) := by
    have ha : (tripleCharges (sourceA290 + difference 3 0) (sourceB290 + difference 0 3) sourceC290) = raw6472 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6472; decide +kernel
    rw [ha]
    exact (canonical6472 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA290 + difference 3 1) (sourceB290 + difference 1 3) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5102) := by
    have ha : (tripleCharges (sourceA290 + difference 3 1) (sourceB290 + difference 1 3) sourceC290) = raw6473 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6473; decide +kernel
    rw [ha]
    exact (canonical6473 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA290 + difference 3 2) (sourceB290 + difference 2 3) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5135) := by
    have ha : (tripleCharges (sourceA290 + difference 3 2) (sourceB290 + difference 2 3) sourceC290) = raw6474 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6474; decide +kernel
    rw [ha]
    exact (canonical6474 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA290 + difference 3 4) (sourceB290 + difference 4 3) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5275) := by
    have ha : (tripleCharges (sourceA290 + difference 3 4) (sourceB290 + difference 4 3) sourceC290) = raw6475 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6475; decide +kernel
    rw [ha]
    exact (canonical6475 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA290 + difference 3 5) (sourceB290 + difference 5 3) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA290 + difference 3 5) (sourceB290 + difference 5 3) sourceC290) = raw6476 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6476; decide +kernel
    rw [ha]
    exact (canonical6476 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA290 + difference 4 0) (sourceB290 + difference 0 4) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4565) := by
    have ha : (tripleCharges (sourceA290 + difference 4 0) (sourceB290 + difference 0 4) sourceC290) = raw6477 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6477; decide +kernel
    rw [ha]
    exact (canonical6477 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA290 + difference 4 1) (sourceB290 + difference 1 4) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA290 + difference 4 1) (sourceB290 + difference 1 4) sourceC290) = raw6478 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6478; decide +kernel
    rw [ha]
    exact (canonical6478 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA290 + difference 4 2) (sourceB290 + difference 2 4) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5131) := by
    have ha : (tripleCharges (sourceA290 + difference 4 2) (sourceB290 + difference 2 4) sourceC290) = raw6479 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6479; decide +kernel
    rw [ha]
    exact (canonical6479 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA290 + difference 4 3) (sourceB290 + difference 3 4) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5210) := by
    have ha : (tripleCharges (sourceA290 + difference 4 3) (sourceB290 + difference 3 4) sourceC290) = raw6480 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6480; decide +kernel
    rw [ha]
    exact (canonical6480 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA290 + difference 4 5) (sourceB290 + difference 5 4) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA290 + difference 4 5) (sourceB290 + difference 5 4) sourceC290) = raw6481 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6481; decide +kernel
    rw [ha]
    exact (canonical6481 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA290 + difference 5 0) (sourceB290 + difference 0 5) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4564) := by
    have ha : (tripleCharges (sourceA290 + difference 5 0) (sourceB290 + difference 0 5) sourceC290) = raw6482 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6482; decide +kernel
    rw [ha]
    exact (canonical6482 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA290 + difference 5 1) (sourceB290 + difference 1 5) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5087) := by
    have ha : (tripleCharges (sourceA290 + difference 5 1) (sourceB290 + difference 1 5) sourceC290) = raw6483 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6483; decide +kernel
    rw [ha]
    exact (canonical6483 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA290 + difference 5 2) (sourceB290 + difference 2 5) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5052) := by
    have ha : (tripleCharges (sourceA290 + difference 5 2) (sourceB290 + difference 2 5) sourceC290) = raw6484 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6484; decide +kernel
    rw [ha]
    exact (canonical6484 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA290 + difference 5 3) (sourceB290 + difference 3 5) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5062) := by
    have ha : (tripleCharges (sourceA290 + difference 5 3) (sourceB290 + difference 3 5) sourceC290) = raw6485 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6485; decide +kernel
    rw [ha]
    exact (canonical6485 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA290 + difference 5 4) (sourceB290 + difference 4 5) sourceC290) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5268) := by
    have ha : (tripleCharges (sourceA290 + difference 5 4) (sourceB290 + difference 4 5) sourceC290) = raw6486 := by
      apply Matrix.ext; unfold tripleCharges sourceA290 sourceB290 sourceC290 difference raw6486; decide +kernel
    rw [ha]
    exact (canonical6486 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA290 sourceB290 sourceC290
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm290, Integer.Sparse.eval]
  linarith only [hs]

def sourceA291 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB291 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC291 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceForm291 : Integer.Sparse Master := [(Sum.inr 1180, 1), (Sum.inr 1181, 1), (Sum.inr 1182, 1), (Sum.inr 1189, 1), (Sum.inr 1262, 1), (Sum.inr 2454, 1), (Sum.inr 2465, 1), (Sum.inr 2495, 1), (Sum.inr 2734, 1), (Sum.inr 2834, 1), (Sum.inr 2835, 1), (Sum.inr 2841, 1), (Sum.inr 2905, 1), (Sum.inr 2909, 1), (Sum.inr 2934, 1), (Sum.inr 2976, 1), (Sum.inr 2979, 1), (Sum.inr 2998, 1), (Sum.inr 3037, 1), (Sum.inr 3038, 1), (Sum.inr 3039, 1), (Sum.inr 3051, 1), (Sum.inr 3055, 1), (Sum.inr 3109, 1), (Sum.inr 3110, 1), (Sum.inr 3573, 1), (Sum.inr 3853, 1), (Sum.inr 3872, 1), (Sum.inr 3883, 1), (Sum.inr 3889, 1)]

theorem sourceEq291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm291 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA291 + difference 0 1) (sourceB291 + difference 1 0) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA291 + difference 0 1) (sourceB291 + difference 1 0) sourceC291) = raw6487 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6487; decide +kernel
    rw [ha]
    exact (canonical6487 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA291 + difference 0 2) (sourceB291 + difference 2 0) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA291 + difference 0 2) (sourceB291 + difference 2 0) sourceC291) = raw6488 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6488; decide +kernel
    rw [ha]
    exact (canonical6488 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA291 + difference 0 3) (sourceB291 + difference 3 0) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA291 + difference 0 3) (sourceB291 + difference 3 0) sourceC291) = raw6489 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6489; decide +kernel
    rw [ha]
    exact (canonical6489 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA291 + difference 0 4) (sourceB291 + difference 4 0) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA291 + difference 0 4) (sourceB291 + difference 4 0) sourceC291) = raw6490 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6490; decide +kernel
    rw [ha]
    exact (canonical6490 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA291 + difference 0 5) (sourceB291 + difference 5 0) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA291 + difference 0 5) (sourceB291 + difference 5 0) sourceC291) = raw6491 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6491; decide +kernel
    rw [ha]
    exact (canonical6491 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA291 + difference 1 0) (sourceB291 + difference 0 1) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1189) := by
    have ha : (tripleCharges (sourceA291 + difference 1 0) (sourceB291 + difference 0 1) sourceC291) = raw6492 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6492; decide +kernel
    rw [ha]
    exact (canonical6492 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA291 + difference 1 2) (sourceB291 + difference 2 1) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2909) := by
    have ha : (tripleCharges (sourceA291 + difference 1 2) (sourceB291 + difference 2 1) sourceC291) = raw6493 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6493; decide +kernel
    rw [ha]
    exact (canonical6493 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA291 + difference 1 3) (sourceB291 + difference 3 1) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2841) := by
    have ha : (tripleCharges (sourceA291 + difference 1 3) (sourceB291 + difference 3 1) sourceC291) = raw6494 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6494; decide +kernel
    rw [ha]
    exact (canonical6494 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA291 + difference 1 4) (sourceB291 + difference 4 1) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA291 + difference 1 4) (sourceB291 + difference 4 1) sourceC291) = raw6495 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6495; decide +kernel
    rw [ha]
    exact (canonical6495 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA291 + difference 1 5) (sourceB291 + difference 5 1) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA291 + difference 1 5) (sourceB291 + difference 5 1) sourceC291) = raw6496 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6496; decide +kernel
    rw [ha]
    exact (canonical6496 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA291 + difference 2 0) (sourceB291 + difference 0 2) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1180) := by
    have ha : (tripleCharges (sourceA291 + difference 2 0) (sourceB291 + difference 0 2) sourceC291) = raw6497 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6497; decide +kernel
    rw [ha]
    exact (canonical6497 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA291 + difference 2 1) (sourceB291 + difference 1 2) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2976) := by
    have ha : (tripleCharges (sourceA291 + difference 2 1) (sourceB291 + difference 1 2) sourceC291) = raw6498 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6498; decide +kernel
    rw [ha]
    exact (canonical6498 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA291 + difference 2 3) (sourceB291 + difference 3 2) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2834) := by
    have ha : (tripleCharges (sourceA291 + difference 2 3) (sourceB291 + difference 3 2) sourceC291) = raw6499 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6499; decide +kernel
    rw [ha]
    exact (canonical6499 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA291 + difference 2 4) (sourceB291 + difference 4 2) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA291 + difference 2 4) (sourceB291 + difference 4 2) sourceC291) = raw6500 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6500; decide +kernel
    rw [ha]
    exact (canonical6500 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA291 + difference 2 5) (sourceB291 + difference 5 2) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA291 + difference 2 5) (sourceB291 + difference 5 2) sourceC291) = raw6501 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6501; decide +kernel
    rw [ha]
    exact (canonical6501 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA291 + difference 3 0) (sourceB291 + difference 0 3) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA291 + difference 3 0) (sourceB291 + difference 0 3) sourceC291) = raw6502 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6502; decide +kernel
    rw [ha]
    exact (canonical6502 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA291 + difference 3 1) (sourceB291 + difference 1 3) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2998) := by
    have ha : (tripleCharges (sourceA291 + difference 3 1) (sourceB291 + difference 1 3) sourceC291) = raw6503 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6503; decide +kernel
    rw [ha]
    exact (canonical6503 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA291 + difference 3 2) (sourceB291 + difference 2 3) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2934) := by
    have ha : (tripleCharges (sourceA291 + difference 3 2) (sourceB291 + difference 2 3) sourceC291) = raw6504 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6504; decide +kernel
    rw [ha]
    exact (canonical6504 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA291 + difference 3 4) (sourceB291 + difference 4 3) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3110) := by
    have ha : (tripleCharges (sourceA291 + difference 3 4) (sourceB291 + difference 4 3) sourceC291) = raw6505 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6505; decide +kernel
    rw [ha]
    exact (canonical6505 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA291 + difference 3 5) (sourceB291 + difference 5 3) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA291 + difference 3 5) (sourceB291 + difference 5 3) sourceC291) = raw6506 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6506; decide +kernel
    rw [ha]
    exact (canonical6506 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA291 + difference 4 0) (sourceB291 + difference 0 4) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1182) := by
    have ha : (tripleCharges (sourceA291 + difference 4 0) (sourceB291 + difference 0 4) sourceC291) = raw6507 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6507; decide +kernel
    rw [ha]
    exact (canonical6507 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA291 + difference 4 1) (sourceB291 + difference 1 4) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2979) := by
    have ha : (tripleCharges (sourceA291 + difference 4 1) (sourceB291 + difference 1 4) sourceC291) = raw6508 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6508; decide +kernel
    rw [ha]
    exact (canonical6508 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA291 + difference 4 2) (sourceB291 + difference 2 4) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2905) := by
    have ha : (tripleCharges (sourceA291 + difference 4 2) (sourceB291 + difference 2 4) sourceC291) = raw6509 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6509; decide +kernel
    rw [ha]
    exact (canonical6509 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA291 + difference 4 3) (sourceB291 + difference 3 4) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2835) := by
    have ha : (tripleCharges (sourceA291 + difference 4 3) (sourceB291 + difference 3 4) sourceC291) = raw6510 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6510; decide +kernel
    rw [ha]
    exact (canonical6510 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA291 + difference 4 5) (sourceB291 + difference 5 4) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA291 + difference 4 5) (sourceB291 + difference 5 4) sourceC291) = raw6511 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6511; decide +kernel
    rw [ha]
    exact (canonical6511 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA291 + difference 5 0) (sourceB291 + difference 0 5) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1181) := by
    have ha : (tripleCharges (sourceA291 + difference 5 0) (sourceB291 + difference 0 5) sourceC291) = raw6512 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6512; decide +kernel
    rw [ha]
    exact (canonical6512 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA291 + difference 5 1) (sourceB291 + difference 1 5) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2495) := by
    have ha : (tripleCharges (sourceA291 + difference 5 1) (sourceB291 + difference 1 5) sourceC291) = raw6513 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6513; decide +kernel
    rw [ha]
    exact (canonical6513 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA291 + difference 5 2) (sourceB291 + difference 2 5) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2454) := by
    have ha : (tripleCharges (sourceA291 + difference 5 2) (sourceB291 + difference 2 5) sourceC291) = raw6514 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6514; decide +kernel
    rw [ha]
    exact (canonical6514 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA291 + difference 5 3) (sourceB291 + difference 3 5) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2465) := by
    have ha : (tripleCharges (sourceA291 + difference 5 3) (sourceB291 + difference 3 5) sourceC291) = raw6515 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6515; decide +kernel
    rw [ha]
    exact (canonical6515 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA291 + difference 5 4) (sourceB291 + difference 4 5) sourceC291) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA291 + difference 5 4) (sourceB291 + difference 4 5) sourceC291) = raw6516 := by
      apply Matrix.ext; unfold tripleCharges sourceA291 sourceB291 sourceC291 difference raw6516; decide +kernel
    rw [ha]
    exact (canonical6516 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA291 sourceB291 sourceC291
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm291, Integer.Sparse.eval]
  linarith only [hs]

def sourceA292 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB292 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC292 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceForm292 : Integer.Sparse Master := [(Sum.inr 2836, 1), (Sum.inr 2837, 1), (Sum.inr 2838, 1), (Sum.inr 2841, 1), (Sum.inr 3051, 1), (Sum.inr 3241, 1), (Sum.inr 3242, 1), (Sum.inr 3243, 1), (Sum.inr 3246, 1), (Sum.inr 3294, 1), (Sum.inr 3437, 1), (Sum.inr 3461, 1), (Sum.inr 3471, 1), (Sum.inr 3472, 1), (Sum.inr 3480, 1), (Sum.inr 3515, 1), (Sum.inr 3518, 1), (Sum.inr 3526, 1), (Sum.inr 3534, 1), (Sum.inr 3535, 1), (Sum.inr 3541, 1), (Sum.inr 3548, 1), (Sum.inr 3549, 1), (Sum.inr 3559, 1), (Sum.inr 3573, 1), (Sum.inr 3584, 1), (Sum.inr 3809, 1), (Sum.inr 3839, 1), (Sum.inr 3853, 1), (Sum.inr 3862, 1)]

theorem sourceEq292 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm292 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA292 + difference 0 1) (sourceB292 + difference 1 0) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA292 + difference 0 1) (sourceB292 + difference 1 0) sourceC292) = raw6517 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6517; decide +kernel
    rw [ha]
    exact (canonical6517 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA292 + difference 0 2) (sourceB292 + difference 2 0) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA292 + difference 0 2) (sourceB292 + difference 2 0) sourceC292) = raw6518 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6518; decide +kernel
    rw [ha]
    exact (canonical6518 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA292 + difference 0 3) (sourceB292 + difference 3 0) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA292 + difference 0 3) (sourceB292 + difference 3 0) sourceC292) = raw6519 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6519; decide +kernel
    rw [ha]
    exact (canonical6519 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA292 + difference 0 4) (sourceB292 + difference 4 0) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA292 + difference 0 4) (sourceB292 + difference 4 0) sourceC292) = raw6520 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6520; decide +kernel
    rw [ha]
    exact (canonical6520 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA292 + difference 0 5) (sourceB292 + difference 5 0) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA292 + difference 0 5) (sourceB292 + difference 5 0) sourceC292) = raw6521 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6521; decide +kernel
    rw [ha]
    exact (canonical6521 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA292 + difference 1 0) (sourceB292 + difference 0 1) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3246) := by
    have ha : (tripleCharges (sourceA292 + difference 1 0) (sourceB292 + difference 0 1) sourceC292) = raw6522 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6522; decide +kernel
    rw [ha]
    exact (canonical6522 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA292 + difference 1 2) (sourceB292 + difference 2 1) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3559) := by
    have ha : (tripleCharges (sourceA292 + difference 1 2) (sourceB292 + difference 2 1) sourceC292) = raw6523 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6523; decide +kernel
    rw [ha]
    exact (canonical6523 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA292 + difference 1 3) (sourceB292 + difference 3 1) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2841) := by
    have ha : (tripleCharges (sourceA292 + difference 1 3) (sourceB292 + difference 3 1) sourceC292) = raw6524 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6524; decide +kernel
    rw [ha]
    exact (canonical6524 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA292 + difference 1 4) (sourceB292 + difference 4 1) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA292 + difference 1 4) (sourceB292 + difference 4 1) sourceC292) = raw6525 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6525; decide +kernel
    rw [ha]
    exact (canonical6525 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA292 + difference 1 5) (sourceB292 + difference 5 1) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA292 + difference 1 5) (sourceB292 + difference 5 1) sourceC292) = raw6526 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6526; decide +kernel
    rw [ha]
    exact (canonical6526 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA292 + difference 2 0) (sourceB292 + difference 0 2) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3241) := by
    have ha : (tripleCharges (sourceA292 + difference 2 0) (sourceB292 + difference 0 2) sourceC292) = raw6527 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6527; decide +kernel
    rw [ha]
    exact (canonical6527 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA292 + difference 2 1) (sourceB292 + difference 1 2) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3461) := by
    have ha : (tripleCharges (sourceA292 + difference 2 1) (sourceB292 + difference 1 2) sourceC292) = raw6528 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6528; decide +kernel
    rw [ha]
    exact (canonical6528 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA292 + difference 2 3) (sourceB292 + difference 3 2) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2836) := by
    have ha : (tripleCharges (sourceA292 + difference 2 3) (sourceB292 + difference 3 2) sourceC292) = raw6529 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6529; decide +kernel
    rw [ha]
    exact (canonical6529 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA292 + difference 2 4) (sourceB292 + difference 4 2) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA292 + difference 2 4) (sourceB292 + difference 4 2) sourceC292) = raw6530 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6530; decide +kernel
    rw [ha]
    exact (canonical6530 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA292 + difference 2 5) (sourceB292 + difference 5 2) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA292 + difference 2 5) (sourceB292 + difference 5 2) sourceC292) = raw6531 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6531; decide +kernel
    rw [ha]
    exact (canonical6531 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA292 + difference 3 0) (sourceB292 + difference 0 3) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA292 + difference 3 0) (sourceB292 + difference 0 3) sourceC292) = raw6532 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6532; decide +kernel
    rw [ha]
    exact (canonical6532 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA292 + difference 3 1) (sourceB292 + difference 1 3) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3471) := by
    have ha : (tripleCharges (sourceA292 + difference 3 1) (sourceB292 + difference 1 3) sourceC292) = raw6533 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6533; decide +kernel
    rw [ha]
    exact (canonical6533 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA292 + difference 3 2) (sourceB292 + difference 2 3) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3515) := by
    have ha : (tripleCharges (sourceA292 + difference 3 2) (sourceB292 + difference 2 3) sourceC292) = raw6534 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6534; decide +kernel
    rw [ha]
    exact (canonical6534 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA292 + difference 3 4) (sourceB292 + difference 4 3) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA292 + difference 3 4) (sourceB292 + difference 4 3) sourceC292) = raw6535 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6535; decide +kernel
    rw [ha]
    exact (canonical6535 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA292 + difference 3 5) (sourceB292 + difference 5 3) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA292 + difference 3 5) (sourceB292 + difference 5 3) sourceC292) = raw6536 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6536; decide +kernel
    rw [ha]
    exact (canonical6536 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA292 + difference 4 0) (sourceB292 + difference 0 4) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3243) := by
    have ha : (tripleCharges (sourceA292 + difference 4 0) (sourceB292 + difference 0 4) sourceC292) = raw6537 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6537; decide +kernel
    rw [ha]
    exact (canonical6537 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA292 + difference 4 1) (sourceB292 + difference 1 4) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA292 + difference 4 1) (sourceB292 + difference 1 4) sourceC292) = raw6538 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6538; decide +kernel
    rw [ha]
    exact (canonical6538 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA292 + difference 4 2) (sourceB292 + difference 2 4) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3518) := by
    have ha : (tripleCharges (sourceA292 + difference 4 2) (sourceB292 + difference 2 4) sourceC292) = raw6539 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6539; decide +kernel
    rw [ha]
    exact (canonical6539 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA292 + difference 4 3) (sourceB292 + difference 3 4) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2838) := by
    have ha : (tripleCharges (sourceA292 + difference 4 3) (sourceB292 + difference 3 4) sourceC292) = raw6540 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6540; decide +kernel
    rw [ha]
    exact (canonical6540 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA292 + difference 4 5) (sourceB292 + difference 5 4) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA292 + difference 4 5) (sourceB292 + difference 5 4) sourceC292) = raw6541 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6541; decide +kernel
    rw [ha]
    exact (canonical6541 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA292 + difference 5 0) (sourceB292 + difference 0 5) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3242) := by
    have ha : (tripleCharges (sourceA292 + difference 5 0) (sourceB292 + difference 0 5) sourceC292) = raw6542 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6542; decide +kernel
    rw [ha]
    exact (canonical6542 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA292 + difference 5 1) (sourceB292 + difference 1 5) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3472) := by
    have ha : (tripleCharges (sourceA292 + difference 5 1) (sourceB292 + difference 1 5) sourceC292) = raw6543 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6543; decide +kernel
    rw [ha]
    exact (canonical6543 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA292 + difference 5 2) (sourceB292 + difference 2 5) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3437) := by
    have ha : (tripleCharges (sourceA292 + difference 5 2) (sourceB292 + difference 2 5) sourceC292) = raw6544 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6544; decide +kernel
    rw [ha]
    exact (canonical6544 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA292 + difference 5 3) (sourceB292 + difference 3 5) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2837) := by
    have ha : (tripleCharges (sourceA292 + difference 5 3) (sourceB292 + difference 3 5) sourceC292) = raw6545 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6545; decide +kernel
    rw [ha]
    exact (canonical6545 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA292 + difference 5 4) (sourceB292 + difference 4 5) sourceC292) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA292 + difference 5 4) (sourceB292 + difference 4 5) sourceC292) = raw6546 := by
      apply Matrix.ext; unfold tripleCharges sourceA292 sourceB292 sourceC292 difference raw6546; decide +kernel
    rw [ha]
    exact (canonical6546 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA292 sourceB292 sourceC292
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm292, Integer.Sparse.eval]
  linarith only [hs]

def sourceA293 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB293 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC293 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceForm293 : Integer.Sparse Master := [(Sum.inr 2731, 1), (Sum.inr 2773, 1), (Sum.inr 3813, 1), (Sum.inr 3840, 1), (Sum.inr 3906, 1), (Sum.inr 3907, 1), (Sum.inr 4092, -1)]

theorem sourceEq293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm293 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA293 + difference 0 0) (sourceB293 + difference 0 0) sourceC293) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA293 + difference 0 0) (sourceB293 + difference 0 0) sourceC293) = raw6547 := by
      apply Matrix.ext; unfold tripleCharges sourceA293 sourceB293 sourceC293 difference raw6547; decide +kernel
    rw [ha]
    exact (canonical6547 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA293 + difference 0 1) (sourceB293 + difference 1 0) sourceC293) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA293 + difference 0 1) (sourceB293 + difference 1 0) sourceC293) = raw6548 := by
      apply Matrix.ext; unfold tripleCharges sourceA293 sourceB293 sourceC293 difference raw6548; decide +kernel
    rw [ha]
    exact (canonical6548 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA293 + difference 0 2) (sourceB293 + difference 2 0) sourceC293) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA293 + difference 0 2) (sourceB293 + difference 2 0) sourceC293) = raw6549 := by
      apply Matrix.ext; unfold tripleCharges sourceA293 sourceB293 sourceC293 difference raw6549; decide +kernel
    rw [ha]
    exact (canonical6549 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA293 + difference 0 3) (sourceB293 + difference 3 0) sourceC293) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA293 + difference 0 3) (sourceB293 + difference 3 0) sourceC293) = raw6550 := by
      apply Matrix.ext; unfold tripleCharges sourceA293 sourceB293 sourceC293 difference raw6550; decide +kernel
    rw [ha]
    exact (canonical6550 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA293 + difference 0 4) (sourceB293 + difference 4 0) sourceC293) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA293 + difference 0 4) (sourceB293 + difference 4 0) sourceC293) = raw6551 := by
      apply Matrix.ext; unfold tripleCharges sourceA293 sourceB293 sourceC293 difference raw6551; decide +kernel
    rw [ha]
    exact (canonical6551 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA293 + difference 0 5) (sourceB293 + difference 5 0) sourceC293) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3906) := by
    have ha : (tripleCharges (sourceA293 + difference 0 5) (sourceB293 + difference 5 0) sourceC293) = raw6552 := by
      apply Matrix.ext; unfold tripleCharges sourceA293 sourceB293 sourceC293 difference raw6552; decide +kernel
    rw [ha]
    exact (canonical6552 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA293 + sourceB293) sourceC293) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA293 + sourceB293) sourceC293) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA293 sourceB293 sourceC293 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA293 sourceB293 sourceC293
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm293, Integer.Sparse.eval]
  linarith only [hs]

def sourceA294 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB294 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC294 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceForm294 : Integer.Sparse Master := [(Sum.inr 1222, 1), (Sum.inr 1224, 1), (Sum.inr 1226, 1), (Sum.inr 1237, 1), (Sum.inr 1277, 1), (Sum.inr 2731, 1), (Sum.inr 4092, -1)]

theorem sourceEq294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm294 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA294 + difference 0 0) (sourceB294 + difference 0 0) sourceC294) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA294 + difference 0 0) (sourceB294 + difference 0 0) sourceC294) = raw6547 := by
      apply Matrix.ext; unfold tripleCharges sourceA294 sourceB294 sourceC294 difference raw6547; decide +kernel
    rw [ha]
    exact (canonical6547 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA294 + difference 1 0) (sourceB294 + difference 0 1) sourceC294) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1277) := by
    have ha : (tripleCharges (sourceA294 + difference 1 0) (sourceB294 + difference 0 1) sourceC294) = raw6554 := by
      apply Matrix.ext; unfold tripleCharges sourceA294 sourceB294 sourceC294 difference raw6554; decide +kernel
    rw [ha]
    exact (canonical6554 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA294 + difference 2 0) (sourceB294 + difference 0 2) sourceC294) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1222) := by
    have ha : (tripleCharges (sourceA294 + difference 2 0) (sourceB294 + difference 0 2) sourceC294) = raw6555 := by
      apply Matrix.ext; unfold tripleCharges sourceA294 sourceB294 sourceC294 difference raw6555; decide +kernel
    rw [ha]
    exact (canonical6555 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA294 + difference 3 0) (sourceB294 + difference 0 3) sourceC294) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA294 + difference 3 0) (sourceB294 + difference 0 3) sourceC294) = raw6556 := by
      apply Matrix.ext; unfold tripleCharges sourceA294 sourceB294 sourceC294 difference raw6556; decide +kernel
    rw [ha]
    exact (canonical6556 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA294 + difference 4 0) (sourceB294 + difference 0 4) sourceC294) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1226) := by
    have ha : (tripleCharges (sourceA294 + difference 4 0) (sourceB294 + difference 0 4) sourceC294) = raw6557 := by
      apply Matrix.ext; unfold tripleCharges sourceA294 sourceB294 sourceC294 difference raw6557; decide +kernel
    rw [ha]
    exact (canonical6557 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA294 + difference 5 0) (sourceB294 + difference 0 5) sourceC294) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1224) := by
    have ha : (tripleCharges (sourceA294 + difference 5 0) (sourceB294 + difference 0 5) sourceC294) = raw6558 := by
      apply Matrix.ext; unfold tripleCharges sourceA294 sourceB294 sourceC294 difference raw6558; decide +kernel
    rw [ha]
    exact (canonical6558 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA294 + sourceB294) sourceC294) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA294 + sourceB294) sourceC294) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA294 sourceB294 sourceC294 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA294 sourceB294 sourceC294
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm294, Integer.Sparse.eval]
  linarith only [hs]

def sourceA295 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB295 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC295 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceForm295 : Integer.Sparse Master := [(Sum.inr 1277, 1), (Sum.inr 2577, 1), (Sum.inr 2650, 1), (Sum.inr 2731, 1), (Sum.inr 2773, 1), (Sum.inr 2774, 1), (Sum.inr 4092, -1)]

theorem sourceEq295 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm295 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA295 + difference 1 0) (sourceB295 + difference 0 1) sourceC295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1277) := by
    have ha : (tripleCharges (sourceA295 + difference 1 0) (sourceB295 + difference 0 1) sourceC295) = raw6554 := by
      apply Matrix.ext; unfold tripleCharges sourceA295 sourceB295 sourceC295 difference raw6554; decide +kernel
    rw [ha]
    exact (canonical6554 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA295 + difference 1 1) (sourceB295 + difference 1 1) sourceC295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA295 + difference 1 1) (sourceB295 + difference 1 1) sourceC295) = raw6547 := by
      apply Matrix.ext; unfold tripleCharges sourceA295 sourceB295 sourceC295 difference raw6547; decide +kernel
    rw [ha]
    exact (canonical6547 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA295 + difference 1 2) (sourceB295 + difference 2 1) sourceC295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2577) := by
    have ha : (tripleCharges (sourceA295 + difference 1 2) (sourceB295 + difference 2 1) sourceC295) = raw6559 := by
      apply Matrix.ext; unfold tripleCharges sourceA295 sourceB295 sourceC295 difference raw6559; decide +kernel
    rw [ha]
    exact (canonical6559 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA295 + difference 1 3) (sourceB295 + difference 3 1) sourceC295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2650) := by
    have ha : (tripleCharges (sourceA295 + difference 1 3) (sourceB295 + difference 3 1) sourceC295) = raw6560 := by
      apply Matrix.ext; unfold tripleCharges sourceA295 sourceB295 sourceC295 difference raw6560; decide +kernel
    rw [ha]
    exact (canonical6560 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA295 + difference 1 4) (sourceB295 + difference 4 1) sourceC295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA295 + difference 1 4) (sourceB295 + difference 4 1) sourceC295) = raw6561 := by
      apply Matrix.ext; unfold tripleCharges sourceA295 sourceB295 sourceC295 difference raw6561; decide +kernel
    rw [ha]
    exact (canonical6561 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA295 + difference 1 5) (sourceB295 + difference 5 1) sourceC295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA295 + difference 1 5) (sourceB295 + difference 5 1) sourceC295) = raw6562 := by
      apply Matrix.ext; unfold tripleCharges sourceA295 sourceB295 sourceC295 difference raw6562; decide +kernel
    rw [ha]
    exact (canonical6562 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA295 + sourceB295) sourceC295) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA295 + sourceB295) sourceC295) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA295 sourceB295 sourceC295 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA295 sourceB295 sourceC295
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm295, Integer.Sparse.eval]
  linarith only [hs]

def sourceA296 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB296 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC296 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceForm296 : Integer.Sparse Master := [(Sum.inr 2493, 1), (Sum.inr 2495, 1), (Sum.inr 2499, 1), (Sum.inr 2512, 1), (Sum.inr 2731, 1), (Sum.inr 3813, 1), (Sum.inr 4092, -1)]

theorem sourceEq296 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm296 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA296 + difference 0 1) (sourceB296 + difference 1 0) sourceC296) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA296 + difference 0 1) (sourceB296 + difference 1 0) sourceC296) = raw6548 := by
      apply Matrix.ext; unfold tripleCharges sourceA296 sourceB296 sourceC296 difference raw6548; decide +kernel
    rw [ha]
    exact (canonical6548 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA296 + difference 1 1) (sourceB296 + difference 1 1) sourceC296) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA296 + difference 1 1) (sourceB296 + difference 1 1) sourceC296) = raw6547 := by
      apply Matrix.ext; unfold tripleCharges sourceA296 sourceB296 sourceC296 difference raw6547; decide +kernel
    rw [ha]
    exact (canonical6547 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA296 + difference 2 1) (sourceB296 + difference 1 2) sourceC296) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2493) := by
    have ha : (tripleCharges (sourceA296 + difference 2 1) (sourceB296 + difference 1 2) sourceC296) = raw6563 := by
      apply Matrix.ext; unfold tripleCharges sourceA296 sourceB296 sourceC296 difference raw6563; decide +kernel
    rw [ha]
    exact (canonical6563 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA296 + difference 3 1) (sourceB296 + difference 1 3) sourceC296) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA296 + difference 3 1) (sourceB296 + difference 1 3) sourceC296) = raw6564 := by
      apply Matrix.ext; unfold tripleCharges sourceA296 sourceB296 sourceC296 difference raw6564; decide +kernel
    rw [ha]
    exact (canonical6564 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA296 + difference 4 1) (sourceB296 + difference 1 4) sourceC296) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2499) := by
    have ha : (tripleCharges (sourceA296 + difference 4 1) (sourceB296 + difference 1 4) sourceC296) = raw6565 := by
      apply Matrix.ext; unfold tripleCharges sourceA296 sourceB296 sourceC296 difference raw6565; decide +kernel
    rw [ha]
    exact (canonical6565 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA296 + difference 5 1) (sourceB296 + difference 1 5) sourceC296) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2495) := by
    have ha : (tripleCharges (sourceA296 + difference 5 1) (sourceB296 + difference 1 5) sourceC296) = raw6566 := by
      apply Matrix.ext; unfold tripleCharges sourceA296 sourceB296 sourceC296 difference raw6566; decide +kernel
    rw [ha]
    exact (canonical6566 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA296 + sourceB296) sourceC296) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA296 + sourceB296) sourceC296) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA296 sourceB296 sourceC296 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA296 sourceB296 sourceC296
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm296, Integer.Sparse.eval]
  linarith only [hs]

def sourceA297 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB297 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC297 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceForm297 : Integer.Sparse Master := [(Sum.inr 1222, 1), (Sum.inr 2493, 1), (Sum.inr 2645, 1), (Sum.inr 2730, 1), (Sum.inr 2731, 2), (Sum.inr 4092, -1)]

theorem sourceEq297 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm297 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA297 + difference 2 0) (sourceB297 + difference 0 2) sourceC297) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1222) := by
    have ha : (tripleCharges (sourceA297 + difference 2 0) (sourceB297 + difference 0 2) sourceC297) = raw6555 := by
      apply Matrix.ext; unfold tripleCharges sourceA297 sourceB297 sourceC297 difference raw6555; decide +kernel
    rw [ha]
    exact (canonical6555 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA297 + difference 2 1) (sourceB297 + difference 1 2) sourceC297) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2493) := by
    have ha : (tripleCharges (sourceA297 + difference 2 1) (sourceB297 + difference 1 2) sourceC297) = raw6563 := by
      apply Matrix.ext; unfold tripleCharges sourceA297 sourceB297 sourceC297 difference raw6563; decide +kernel
    rw [ha]
    exact (canonical6563 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA297 + difference 2 2) (sourceB297 + difference 2 2) sourceC297) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA297 + difference 2 2) (sourceB297 + difference 2 2) sourceC297) = raw6547 := by
      apply Matrix.ext; unfold tripleCharges sourceA297 sourceB297 sourceC297 difference raw6547; decide +kernel
    rw [ha]
    exact (canonical6547 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA297 + difference 2 3) (sourceB297 + difference 3 2) sourceC297) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2645) := by
    have ha : (tripleCharges (sourceA297 + difference 2 3) (sourceB297 + difference 3 2) sourceC297) = raw6567 := by
      apply Matrix.ext; unfold tripleCharges sourceA297 sourceB297 sourceC297 difference raw6567; decide +kernel
    rw [ha]
    exact (canonical6567 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA297 + difference 2 4) (sourceB297 + difference 4 2) sourceC297) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA297 + difference 2 4) (sourceB297 + difference 4 2) sourceC297) = raw6568 := by
      apply Matrix.ext; unfold tripleCharges sourceA297 sourceB297 sourceC297 difference raw6568; decide +kernel
    rw [ha]
    exact (canonical6568 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA297 + difference 2 5) (sourceB297 + difference 5 2) sourceC297) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA297 + difference 2 5) (sourceB297 + difference 5 2) sourceC297) = raw6569 := by
      apply Matrix.ext; unfold tripleCharges sourceA297 sourceB297 sourceC297 difference raw6569; decide +kernel
    rw [ha]
    exact (canonical6569 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA297 + sourceB297) sourceC297) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA297 + sourceB297) sourceC297) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA297 sourceB297 sourceC297 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA297 sourceB297 sourceC297
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm297, Integer.Sparse.eval]
  linarith only [hs]

def sourceA298 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB298 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC298 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceForm298 : Integer.Sparse Master := [(Sum.inr 2547, 1), (Sum.inr 2549, 1), (Sum.inr 2554, 1), (Sum.inr 2577, 1), (Sum.inr 2731, 1), (Sum.inr 3840, 1), (Sum.inr 4092, -1)]

theorem sourceEq298 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm298 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA298 + difference 0 2) (sourceB298 + difference 2 0) sourceC298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA298 + difference 0 2) (sourceB298 + difference 2 0) sourceC298) = raw6549 := by
      apply Matrix.ext; unfold tripleCharges sourceA298 sourceB298 sourceC298 difference raw6549; decide +kernel
    rw [ha]
    exact (canonical6549 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA298 + difference 1 2) (sourceB298 + difference 2 1) sourceC298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2577) := by
    have ha : (tripleCharges (sourceA298 + difference 1 2) (sourceB298 + difference 2 1) sourceC298) = raw6559 := by
      apply Matrix.ext; unfold tripleCharges sourceA298 sourceB298 sourceC298 difference raw6559; decide +kernel
    rw [ha]
    exact (canonical6559 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA298 + difference 2 2) (sourceB298 + difference 2 2) sourceC298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA298 + difference 2 2) (sourceB298 + difference 2 2) sourceC298) = raw6547 := by
      apply Matrix.ext; unfold tripleCharges sourceA298 sourceB298 sourceC298 difference raw6547; decide +kernel
    rw [ha]
    exact (canonical6547 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA298 + difference 3 2) (sourceB298 + difference 2 3) sourceC298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2554) := by
    have ha : (tripleCharges (sourceA298 + difference 3 2) (sourceB298 + difference 2 3) sourceC298) = raw6570 := by
      apply Matrix.ext; unfold tripleCharges sourceA298 sourceB298 sourceC298 difference raw6570; decide +kernel
    rw [ha]
    exact (canonical6570 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA298 + difference 4 2) (sourceB298 + difference 2 4) sourceC298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2549) := by
    have ha : (tripleCharges (sourceA298 + difference 4 2) (sourceB298 + difference 2 4) sourceC298) = raw6571 := by
      apply Matrix.ext; unfold tripleCharges sourceA298 sourceB298 sourceC298 difference raw6571; decide +kernel
    rw [ha]
    exact (canonical6571 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA298 + difference 5 2) (sourceB298 + difference 2 5) sourceC298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2547) := by
    have ha : (tripleCharges (sourceA298 + difference 5 2) (sourceB298 + difference 2 5) sourceC298) = raw6572 := by
      apply Matrix.ext; unfold tripleCharges sourceA298 sourceB298 sourceC298 difference raw6572; decide +kernel
    rw [ha]
    exact (canonical6572 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA298 + sourceB298) sourceC298) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA298 + sourceB298) sourceC298) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA298 sourceB298 sourceC298 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA298 sourceB298 sourceC298
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm298, Integer.Sparse.eval]
  linarith only [hs]

def sourceA299 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB299 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC299 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceForm299 : Integer.Sparse Master := [(Sum.inr 1237, 1), (Sum.inr 2512, 1), (Sum.inr 2554, 1), (Sum.inr 2731, 1), (Sum.inr 2739, 1), (Sum.inr 2743, 1), (Sum.inr 4092, -1)]

theorem sourceEq299 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm299 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA299 + difference 3 0) (sourceB299 + difference 0 3) sourceC299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA299 + difference 3 0) (sourceB299 + difference 0 3) sourceC299) = raw6556 := by
      apply Matrix.ext; unfold tripleCharges sourceA299 sourceB299 sourceC299 difference raw6556; decide +kernel
    rw [ha]
    exact (canonical6556 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA299 + difference 3 1) (sourceB299 + difference 1 3) sourceC299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA299 + difference 3 1) (sourceB299 + difference 1 3) sourceC299) = raw6564 := by
      apply Matrix.ext; unfold tripleCharges sourceA299 sourceB299 sourceC299 difference raw6564; decide +kernel
    rw [ha]
    exact (canonical6564 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA299 + difference 3 2) (sourceB299 + difference 2 3) sourceC299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2554) := by
    have ha : (tripleCharges (sourceA299 + difference 3 2) (sourceB299 + difference 2 3) sourceC299) = raw6570 := by
      apply Matrix.ext; unfold tripleCharges sourceA299 sourceB299 sourceC299 difference raw6570; decide +kernel
    rw [ha]
    exact (canonical6570 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA299 + difference 3 3) (sourceB299 + difference 3 3) sourceC299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA299 + difference 3 3) (sourceB299 + difference 3 3) sourceC299) = raw6547 := by
      apply Matrix.ext; unfold tripleCharges sourceA299 sourceB299 sourceC299 difference raw6547; decide +kernel
    rw [ha]
    exact (canonical6547 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA299 + difference 3 4) (sourceB299 + difference 4 3) sourceC299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA299 + difference 3 4) (sourceB299 + difference 4 3) sourceC299) = raw6573 := by
      apply Matrix.ext; unfold tripleCharges sourceA299 sourceB299 sourceC299 difference raw6573; decide +kernel
    rw [ha]
    exact (canonical6573 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA299 + difference 3 5) (sourceB299 + difference 5 3) sourceC299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA299 + difference 3 5) (sourceB299 + difference 5 3) sourceC299) = raw6574 := by
      apply Matrix.ext; unfold tripleCharges sourceA299 sourceB299 sourceC299 difference raw6574; decide +kernel
    rw [ha]
    exact (canonical6574 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA299 + sourceB299) sourceC299) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA299 + sourceB299) sourceC299) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA299 sourceB299 sourceC299 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA299 sourceB299 sourceC299
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm299, Integer.Sparse.eval]
  linarith only [hs]

def sourceA300 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB300 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC300 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceForm300 : Integer.Sparse Master := [(Sum.inr 2645, 1), (Sum.inr 2647, 1), (Sum.inr 2649, 1), (Sum.inr 2650, 1), (Sum.inr 2731, 1), (Sum.inr 2773, 1), (Sum.inr 4092, -1)]

theorem sourceEq300 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm300 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA300 + difference 0 3) (sourceB300 + difference 3 0) sourceC300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA300 + difference 0 3) (sourceB300 + difference 3 0) sourceC300) = raw6550 := by
      apply Matrix.ext; unfold tripleCharges sourceA300 sourceB300 sourceC300 difference raw6550; decide +kernel
    rw [ha]
    exact (canonical6550 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA300 + difference 1 3) (sourceB300 + difference 3 1) sourceC300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2650) := by
    have ha : (tripleCharges (sourceA300 + difference 1 3) (sourceB300 + difference 3 1) sourceC300) = raw6560 := by
      apply Matrix.ext; unfold tripleCharges sourceA300 sourceB300 sourceC300 difference raw6560; decide +kernel
    rw [ha]
    exact (canonical6560 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA300 + difference 2 3) (sourceB300 + difference 3 2) sourceC300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2645) := by
    have ha : (tripleCharges (sourceA300 + difference 2 3) (sourceB300 + difference 3 2) sourceC300) = raw6567 := by
      apply Matrix.ext; unfold tripleCharges sourceA300 sourceB300 sourceC300 difference raw6567; decide +kernel
    rw [ha]
    exact (canonical6567 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA300 + difference 3 3) (sourceB300 + difference 3 3) sourceC300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA300 + difference 3 3) (sourceB300 + difference 3 3) sourceC300) = raw6547 := by
      apply Matrix.ext; unfold tripleCharges sourceA300 sourceB300 sourceC300 difference raw6547; decide +kernel
    rw [ha]
    exact (canonical6547 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA300 + difference 4 3) (sourceB300 + difference 3 4) sourceC300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2649) := by
    have ha : (tripleCharges (sourceA300 + difference 4 3) (sourceB300 + difference 3 4) sourceC300) = raw6575 := by
      apply Matrix.ext; unfold tripleCharges sourceA300 sourceB300 sourceC300 difference raw6575; decide +kernel
    rw [ha]
    exact (canonical6575 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA300 + difference 5 3) (sourceB300 + difference 3 5) sourceC300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2647) := by
    have ha : (tripleCharges (sourceA300 + difference 5 3) (sourceB300 + difference 3 5) sourceC300) = raw6576 := by
      apply Matrix.ext; unfold tripleCharges sourceA300 sourceB300 sourceC300 difference raw6576; decide +kernel
    rw [ha]
    exact (canonical6576 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA300 + sourceB300) sourceC300) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA300 + sourceB300) sourceC300) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA300 sourceB300 sourceC300 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA300 sourceB300 sourceC300
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm300, Integer.Sparse.eval]
  linarith only [hs]

def sourceA301 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB301 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceC301 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceForm301 : Integer.Sparse Master := [(Sum.inr 1226, 1), (Sum.inr 2499, 1), (Sum.inr 2549, 1), (Sum.inr 2649, 1), (Sum.inr 2731, 1), (Sum.inr 2732, 1), (Sum.inr 4092, -1)]

theorem sourceEq301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm301 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA301 + difference 4 0) (sourceB301 + difference 0 4) sourceC301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1226) := by
    have ha : (tripleCharges (sourceA301 + difference 4 0) (sourceB301 + difference 0 4) sourceC301) = raw6557 := by
      apply Matrix.ext; unfold tripleCharges sourceA301 sourceB301 sourceC301 difference raw6557; decide +kernel
    rw [ha]
    exact (canonical6557 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA301 + difference 4 1) (sourceB301 + difference 1 4) sourceC301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2499) := by
    have ha : (tripleCharges (sourceA301 + difference 4 1) (sourceB301 + difference 1 4) sourceC301) = raw6565 := by
      apply Matrix.ext; unfold tripleCharges sourceA301 sourceB301 sourceC301 difference raw6565; decide +kernel
    rw [ha]
    exact (canonical6565 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA301 + difference 4 2) (sourceB301 + difference 2 4) sourceC301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2549) := by
    have ha : (tripleCharges (sourceA301 + difference 4 2) (sourceB301 + difference 2 4) sourceC301) = raw6571 := by
      apply Matrix.ext; unfold tripleCharges sourceA301 sourceB301 sourceC301 difference raw6571; decide +kernel
    rw [ha]
    exact (canonical6571 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA301 + difference 4 3) (sourceB301 + difference 3 4) sourceC301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2649) := by
    have ha : (tripleCharges (sourceA301 + difference 4 3) (sourceB301 + difference 3 4) sourceC301) = raw6575 := by
      apply Matrix.ext; unfold tripleCharges sourceA301 sourceB301 sourceC301 difference raw6575; decide +kernel
    rw [ha]
    exact (canonical6575 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA301 + difference 4 4) (sourceB301 + difference 4 4) sourceC301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA301 + difference 4 4) (sourceB301 + difference 4 4) sourceC301) = raw6547 := by
      apply Matrix.ext; unfold tripleCharges sourceA301 sourceB301 sourceC301 difference raw6547; decide +kernel
    rw [ha]
    exact (canonical6547 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA301 + difference 4 5) (sourceB301 + difference 5 4) sourceC301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA301 + difference 4 5) (sourceB301 + difference 5 4) sourceC301) = raw6577 := by
      apply Matrix.ext; unfold tripleCharges sourceA301 sourceB301 sourceC301 difference raw6577; decide +kernel
    rw [ha]
    exact (canonical6577 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA301 + sourceB301) sourceC301) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA301 + sourceB301) sourceC301) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA301 sourceB301 sourceC301 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA301 sourceB301 sourceC301
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm301, Integer.Sparse.eval]
  linarith only [hs]

def sourceA302 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB302 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC302 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceForm302 : Integer.Sparse Master := [(Sum.inr 4407, 1), (Sum.inr 4408, 1), (Sum.inr 4412, 1), (Sum.inr 4420, 1), (Sum.inr 4474, 1), (Sum.inr 5005, 1), (Sum.inr 5006, 1), (Sum.inr 5010, 1), (Sum.inr 5016, 1), (Sum.inr 5051, 1), (Sum.inr 5054, 1), (Sum.inr 5057, 1), (Sum.inr 5085, 1), (Sum.inr 5147, 1), (Sum.inr 5185, 1), (Sum.inr 5189, 1), (Sum.inr 5203, 1), (Sum.inr 5205, 1), (Sum.inr 5222, 1), (Sum.inr 5244, 1), (Sum.inr 5265, 1), (Sum.inr 5266, 2), (Sum.inr 5270, 1), (Sum.inr 5301, 1), (Sum.inr 5445, 1), (Sum.inr 5446, 1), (Sum.inr 5448, 1), (Sum.inr 5450, 1), (Sum.inr 5473, 1)]

theorem sourceEq302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm302 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA302 + difference 0 1) (sourceB302 + difference 1 0) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA302 + difference 0 1) (sourceB302 + difference 1 0) sourceC302) = raw6578 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6578; decide +kernel
    rw [ha]
    exact (canonical6578 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA302 + difference 0 2) (sourceB302 + difference 2 0) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5445) := by
    have ha : (tripleCharges (sourceA302 + difference 0 2) (sourceB302 + difference 2 0) sourceC302) = raw6579 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6579; decide +kernel
    rw [ha]
    exact (canonical6579 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA302 + difference 0 3) (sourceB302 + difference 3 0) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA302 + difference 0 3) (sourceB302 + difference 3 0) sourceC302) = raw6580 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6580; decide +kernel
    rw [ha]
    exact (canonical6580 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA302 + difference 0 4) (sourceB302 + difference 4 0) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5448) := by
    have ha : (tripleCharges (sourceA302 + difference 0 4) (sourceB302 + difference 4 0) sourceC302) = raw6581 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6581; decide +kernel
    rw [ha]
    exact (canonical6581 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA302 + difference 0 5) (sourceB302 + difference 5 0) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA302 + difference 0 5) (sourceB302 + difference 5 0) sourceC302) = raw6582 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6582; decide +kernel
    rw [ha]
    exact (canonical6582 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA302 + difference 1 0) (sourceB302 + difference 0 1) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4474) := by
    have ha : (tripleCharges (sourceA302 + difference 1 0) (sourceB302 + difference 0 1) sourceC302) = raw6583 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6583; decide +kernel
    rw [ha]
    exact (canonical6583 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA302 + difference 1 2) (sourceB302 + difference 2 1) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5085) := by
    have ha : (tripleCharges (sourceA302 + difference 1 2) (sourceB302 + difference 2 1) sourceC302) = raw6584 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6584; decide +kernel
    rw [ha]
    exact (canonical6584 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA302 + difference 1 3) (sourceB302 + difference 3 1) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA302 + difference 1 3) (sourceB302 + difference 3 1) sourceC302) = raw6585 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6585; decide +kernel
    rw [ha]
    exact (canonical6585 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA302 + difference 1 4) (sourceB302 + difference 4 1) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA302 + difference 1 4) (sourceB302 + difference 4 1) sourceC302) = raw6586 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6586; decide +kernel
    rw [ha]
    exact (canonical6586 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA302 + difference 1 5) (sourceB302 + difference 5 1) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA302 + difference 1 5) (sourceB302 + difference 5 1) sourceC302) = raw6587 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6587; decide +kernel
    rw [ha]
    exact (canonical6587 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA302 + difference 2 0) (sourceB302 + difference 0 2) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4407) := by
    have ha : (tripleCharges (sourceA302 + difference 2 0) (sourceB302 + difference 0 2) sourceC302) = raw6588 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6588; decide +kernel
    rw [ha]
    exact (canonical6588 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA302 + difference 2 1) (sourceB302 + difference 1 2) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5005) := by
    have ha : (tripleCharges (sourceA302 + difference 2 1) (sourceB302 + difference 1 2) sourceC302) = raw6589 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6589; decide +kernel
    rw [ha]
    exact (canonical6589 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA302 + difference 2 3) (sourceB302 + difference 3 2) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5185) := by
    have ha : (tripleCharges (sourceA302 + difference 2 3) (sourceB302 + difference 3 2) sourceC302) = raw6590 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6590; decide +kernel
    rw [ha]
    exact (canonical6590 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA302 + difference 2 4) (sourceB302 + difference 4 2) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5244) := by
    have ha : (tripleCharges (sourceA302 + difference 2 4) (sourceB302 + difference 4 2) sourceC302) = raw6591 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6591; decide +kernel
    rw [ha]
    exact (canonical6591 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA302 + difference 2 5) (sourceB302 + difference 5 2) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA302 + difference 2 5) (sourceB302 + difference 5 2) sourceC302) = raw6592 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6592; decide +kernel
    rw [ha]
    exact (canonical6592 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA302 + difference 3 0) (sourceB302 + difference 0 3) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4420) := by
    have ha : (tripleCharges (sourceA302 + difference 3 0) (sourceB302 + difference 0 3) sourceC302) = raw6593 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6593; decide +kernel
    rw [ha]
    exact (canonical6593 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA302 + difference 3 1) (sourceB302 + difference 1 3) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5016) := by
    have ha : (tripleCharges (sourceA302 + difference 3 1) (sourceB302 + difference 1 3) sourceC302) = raw6594 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6594; decide +kernel
    rw [ha]
    exact (canonical6594 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA302 + difference 3 2) (sourceB302 + difference 2 3) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5057) := by
    have ha : (tripleCharges (sourceA302 + difference 3 2) (sourceB302 + difference 2 3) sourceC302) = raw6595 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6595; decide +kernel
    rw [ha]
    exact (canonical6595 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA302 + difference 3 4) (sourceB302 + difference 4 3) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5205) := by
    have ha : (tripleCharges (sourceA302 + difference 3 4) (sourceB302 + difference 4 3) sourceC302) = raw6596 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6596; decide +kernel
    rw [ha]
    exact (canonical6596 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA302 + difference 3 5) (sourceB302 + difference 5 3) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA302 + difference 3 5) (sourceB302 + difference 5 3) sourceC302) = raw6597 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6597; decide +kernel
    rw [ha]
    exact (canonical6597 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA302 + difference 4 0) (sourceB302 + difference 0 4) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4412) := by
    have ha : (tripleCharges (sourceA302 + difference 4 0) (sourceB302 + difference 0 4) sourceC302) = raw6598 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6598; decide +kernel
    rw [ha]
    exact (canonical6598 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA302 + difference 4 1) (sourceB302 + difference 1 4) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5010) := by
    have ha : (tripleCharges (sourceA302 + difference 4 1) (sourceB302 + difference 1 4) sourceC302) = raw6599 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6599; decide +kernel
    rw [ha]
    exact (canonical6599 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA302 + difference 4 2) (sourceB302 + difference 2 4) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5054) := by
    have ha : (tripleCharges (sourceA302 + difference 4 2) (sourceB302 + difference 2 4) sourceC302) = raw6600 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6600; decide +kernel
    rw [ha]
    exact (canonical6600 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA302 + difference 4 3) (sourceB302 + difference 3 4) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5189) := by
    have ha : (tripleCharges (sourceA302 + difference 4 3) (sourceB302 + difference 3 4) sourceC302) = raw6601 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6601; decide +kernel
    rw [ha]
    exact (canonical6601 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA302 + difference 4 5) (sourceB302 + difference 5 4) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA302 + difference 4 5) (sourceB302 + difference 5 4) sourceC302) = raw6602 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6602; decide +kernel
    rw [ha]
    exact (canonical6602 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA302 + difference 5 0) (sourceB302 + difference 0 5) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4408) := by
    have ha : (tripleCharges (sourceA302 + difference 5 0) (sourceB302 + difference 0 5) sourceC302) = raw6603 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6603; decide +kernel
    rw [ha]
    exact (canonical6603 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA302 + difference 5 1) (sourceB302 + difference 1 5) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5006) := by
    have ha : (tripleCharges (sourceA302 + difference 5 1) (sourceB302 + difference 1 5) sourceC302) = raw6604 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6604; decide +kernel
    rw [ha]
    exact (canonical6604 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA302 + difference 5 2) (sourceB302 + difference 2 5) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5051) := by
    have ha : (tripleCharges (sourceA302 + difference 5 2) (sourceB302 + difference 2 5) sourceC302) = raw6605 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6605; decide +kernel
    rw [ha]
    exact (canonical6605 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA302 + difference 5 3) (sourceB302 + difference 3 5) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA302 + difference 5 3) (sourceB302 + difference 3 5) sourceC302) = raw6606 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6606; decide +kernel
    rw [ha]
    exact (canonical6606 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA302 + difference 5 4) (sourceB302 + difference 4 5) sourceC302) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5222) := by
    have ha : (tripleCharges (sourceA302 + difference 5 4) (sourceB302 + difference 4 5) sourceC302) = raw6607 := by
      apply Matrix.ext; unfold tripleCharges sourceA302 sourceB302 sourceC302 difference raw6607; decide +kernel
    rw [ha]
    exact (canonical6607 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA302 sourceB302 sourceC302
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm302, Integer.Sparse.eval]
  linarith only [hs]

def sourceA303 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB303 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC303 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceForm303 : Integer.Sparse Master := [(Sum.inr 988, 1), (Sum.inr 989, 1), (Sum.inr 993, 1), (Sum.inr 1001, 1), (Sum.inr 1057, 1), (Sum.inr 2390, 1), (Sum.inr 2391, 1), (Sum.inr 2395, 1), (Sum.inr 2401, 1), (Sum.inr 2453, 1), (Sum.inr 2456, 1), (Sum.inr 2460, 1), (Sum.inr 2493, 1), (Sum.inr 2569, 1), (Sum.inr 2615, 1), (Sum.inr 2621, 1), (Sum.inr 2637, 1), (Sum.inr 2664, 1), (Sum.inr 2698, 1), (Sum.inr 2706, 1), (Sum.inr 2730, 1), (Sum.inr 2731, 2), (Sum.inr 2738, 1), (Sum.inr 2775, 1), (Sum.inr 3880, 1), (Sum.inr 3884, 1), (Sum.inr 3885, 1), (Sum.inr 3887, 1), (Sum.inr 3995, 1)]

theorem sourceEq303 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm303 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA303 + difference 0 1) (sourceB303 + difference 1 0) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA303 + difference 0 1) (sourceB303 + difference 1 0) sourceC303) = raw6608 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6608; decide +kernel
    rw [ha]
    exact (canonical6608 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA303 + difference 0 2) (sourceB303 + difference 2 0) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA303 + difference 0 2) (sourceB303 + difference 2 0) sourceC303) = raw6609 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6609; decide +kernel
    rw [ha]
    exact (canonical6609 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA303 + difference 0 3) (sourceB303 + difference 3 0) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA303 + difference 0 3) (sourceB303 + difference 3 0) sourceC303) = raw6610 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6610; decide +kernel
    rw [ha]
    exact (canonical6610 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA303 + difference 0 4) (sourceB303 + difference 4 0) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA303 + difference 0 4) (sourceB303 + difference 4 0) sourceC303) = raw6611 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6611; decide +kernel
    rw [ha]
    exact (canonical6611 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA303 + difference 0 5) (sourceB303 + difference 5 0) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3887) := by
    have ha : (tripleCharges (sourceA303 + difference 0 5) (sourceB303 + difference 5 0) sourceC303) = raw6612 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6612; decide +kernel
    rw [ha]
    exact (canonical6612 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA303 + difference 1 0) (sourceB303 + difference 0 1) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1057) := by
    have ha : (tripleCharges (sourceA303 + difference 1 0) (sourceB303 + difference 0 1) sourceC303) = raw6613 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6613; decide +kernel
    rw [ha]
    exact (canonical6613 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA303 + difference 1 2) (sourceB303 + difference 2 1) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2493) := by
    have ha : (tripleCharges (sourceA303 + difference 1 2) (sourceB303 + difference 2 1) sourceC303) = raw6614 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6614; decide +kernel
    rw [ha]
    exact (canonical6614 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA303 + difference 1 3) (sourceB303 + difference 3 1) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2637) := by
    have ha : (tripleCharges (sourceA303 + difference 1 3) (sourceB303 + difference 3 1) sourceC303) = raw6615 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6615; decide +kernel
    rw [ha]
    exact (canonical6615 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA303 + difference 1 4) (sourceB303 + difference 4 1) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA303 + difference 1 4) (sourceB303 + difference 4 1) sourceC303) = raw6616 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6616; decide +kernel
    rw [ha]
    exact (canonical6616 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA303 + difference 1 5) (sourceB303 + difference 5 1) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2775) := by
    have ha : (tripleCharges (sourceA303 + difference 1 5) (sourceB303 + difference 5 1) sourceC303) = raw6617 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6617; decide +kernel
    rw [ha]
    exact (canonical6617 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA303 + difference 2 0) (sourceB303 + difference 0 2) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 988) := by
    have ha : (tripleCharges (sourceA303 + difference 2 0) (sourceB303 + difference 0 2) sourceC303) = raw6618 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6618; decide +kernel
    rw [ha]
    exact (canonical6618 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA303 + difference 2 1) (sourceB303 + difference 1 2) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2390) := by
    have ha : (tripleCharges (sourceA303 + difference 2 1) (sourceB303 + difference 1 2) sourceC303) = raw6619 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6619; decide +kernel
    rw [ha]
    exact (canonical6619 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA303 + difference 2 3) (sourceB303 + difference 3 2) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2615) := by
    have ha : (tripleCharges (sourceA303 + difference 2 3) (sourceB303 + difference 3 2) sourceC303) = raw6620 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6620; decide +kernel
    rw [ha]
    exact (canonical6620 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA303 + difference 2 4) (sourceB303 + difference 4 2) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2698) := by
    have ha : (tripleCharges (sourceA303 + difference 2 4) (sourceB303 + difference 4 2) sourceC303) = raw6621 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6621; decide +kernel
    rw [ha]
    exact (canonical6621 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA303 + difference 2 5) (sourceB303 + difference 5 2) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA303 + difference 2 5) (sourceB303 + difference 5 2) sourceC303) = raw6622 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6622; decide +kernel
    rw [ha]
    exact (canonical6622 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA303 + difference 3 0) (sourceB303 + difference 0 3) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1001) := by
    have ha : (tripleCharges (sourceA303 + difference 3 0) (sourceB303 + difference 0 3) sourceC303) = raw6623 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6623; decide +kernel
    rw [ha]
    exact (canonical6623 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA303 + difference 3 1) (sourceB303 + difference 1 3) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2401) := by
    have ha : (tripleCharges (sourceA303 + difference 3 1) (sourceB303 + difference 1 3) sourceC303) = raw6624 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6624; decide +kernel
    rw [ha]
    exact (canonical6624 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA303 + difference 3 2) (sourceB303 + difference 2 3) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2460) := by
    have ha : (tripleCharges (sourceA303 + difference 3 2) (sourceB303 + difference 2 3) sourceC303) = raw6625 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6625; decide +kernel
    rw [ha]
    exact (canonical6625 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA303 + difference 3 4) (sourceB303 + difference 4 3) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2706) := by
    have ha : (tripleCharges (sourceA303 + difference 3 4) (sourceB303 + difference 4 3) sourceC303) = raw6626 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6626; decide +kernel
    rw [ha]
    exact (canonical6626 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA303 + difference 3 5) (sourceB303 + difference 5 3) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2738) := by
    have ha : (tripleCharges (sourceA303 + difference 3 5) (sourceB303 + difference 5 3) sourceC303) = raw6627 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6627; decide +kernel
    rw [ha]
    exact (canonical6627 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA303 + difference 4 0) (sourceB303 + difference 0 4) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 993) := by
    have ha : (tripleCharges (sourceA303 + difference 4 0) (sourceB303 + difference 0 4) sourceC303) = raw6628 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6628; decide +kernel
    rw [ha]
    exact (canonical6628 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA303 + difference 4 1) (sourceB303 + difference 1 4) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2395) := by
    have ha : (tripleCharges (sourceA303 + difference 4 1) (sourceB303 + difference 1 4) sourceC303) = raw6629 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6629; decide +kernel
    rw [ha]
    exact (canonical6629 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA303 + difference 4 2) (sourceB303 + difference 2 4) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2456) := by
    have ha : (tripleCharges (sourceA303 + difference 4 2) (sourceB303 + difference 2 4) sourceC303) = raw6630 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6630; decide +kernel
    rw [ha]
    exact (canonical6630 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA303 + difference 4 3) (sourceB303 + difference 3 4) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2621) := by
    have ha : (tripleCharges (sourceA303 + difference 4 3) (sourceB303 + difference 3 4) sourceC303) = raw6631 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6631; decide +kernel
    rw [ha]
    exact (canonical6631 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA303 + difference 4 5) (sourceB303 + difference 5 4) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA303 + difference 4 5) (sourceB303 + difference 5 4) sourceC303) = raw6632 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6632; decide +kernel
    rw [ha]
    exact (canonical6632 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA303 + difference 5 0) (sourceB303 + difference 0 5) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 989) := by
    have ha : (tripleCharges (sourceA303 + difference 5 0) (sourceB303 + difference 0 5) sourceC303) = raw6633 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6633; decide +kernel
    rw [ha]
    exact (canonical6633 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA303 + difference 5 1) (sourceB303 + difference 1 5) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2391) := by
    have ha : (tripleCharges (sourceA303 + difference 5 1) (sourceB303 + difference 1 5) sourceC303) = raw6634 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6634; decide +kernel
    rw [ha]
    exact (canonical6634 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA303 + difference 5 2) (sourceB303 + difference 2 5) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2453) := by
    have ha : (tripleCharges (sourceA303 + difference 5 2) (sourceB303 + difference 2 5) sourceC303) = raw6635 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6635; decide +kernel
    rw [ha]
    exact (canonical6635 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA303 + difference 5 3) (sourceB303 + difference 3 5) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2569) := by
    have ha : (tripleCharges (sourceA303 + difference 5 3) (sourceB303 + difference 3 5) sourceC303) = raw6636 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6636; decide +kernel
    rw [ha]
    exact (canonical6636 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA303 + difference 5 4) (sourceB303 + difference 4 5) sourceC303) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2664) := by
    have ha : (tripleCharges (sourceA303 + difference 5 4) (sourceB303 + difference 4 5) sourceC303) = raw6637 := by
      apply Matrix.ext; unfold tripleCharges sourceA303 sourceB303 sourceC303 difference raw6637; decide +kernel
    rw [ha]
    exact (canonical6637 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA303 sourceB303 sourceC303
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm303, Integer.Sparse.eval]
  linarith only [hs]

def sourceA304 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB304 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC304 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceForm304 : Integer.Sparse Master := [(Sum.inr 1601, 1), (Sum.inr 1603, 1), (Sum.inr 1604, 1), (Sum.inr 1626, 1), (Sum.inr 1709, 1), (Sum.inr 2851, 1), (Sum.inr 2855, 1), (Sum.inr 2879, 1), (Sum.inr 3075, 1), (Sum.inr 3342, 1), (Sum.inr 3343, 1), (Sum.inr 3359, 1), (Sum.inr 3368, 1), (Sum.inr 3389, 1), (Sum.inr 3438, 1), (Sum.inr 3461, 1), (Sum.inr 3497, 1), (Sum.inr 3526, 1), (Sum.inr 3529, 1), (Sum.inr 3530, 1), (Sum.inr 3535, 2), (Sum.inr 3542, 1), (Sum.inr 3619, 1), (Sum.inr 3621, 1), (Sum.inr 3959, 1), (Sum.inr 3961, 1), (Sum.inr 4024, 1), (Sum.inr 4028, 1), (Sum.inr 4029, 1)]

theorem sourceEq304 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm304 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA304 + difference 0 1) (sourceB304 + difference 1 0) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA304 + difference 0 1) (sourceB304 + difference 1 0) sourceC304) = raw6638 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6638; decide +kernel
    rw [ha]
    exact (canonical6638 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA304 + difference 0 2) (sourceB304 + difference 2 0) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4024) := by
    have ha : (tripleCharges (sourceA304 + difference 0 2) (sourceB304 + difference 2 0) sourceC304) = raw6639 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6639; decide +kernel
    rw [ha]
    exact (canonical6639 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA304 + difference 0 3) (sourceB304 + difference 3 0) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA304 + difference 0 3) (sourceB304 + difference 3 0) sourceC304) = raw6640 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6640; decide +kernel
    rw [ha]
    exact (canonical6640 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA304 + difference 0 4) (sourceB304 + difference 4 0) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4028) := by
    have ha : (tripleCharges (sourceA304 + difference 0 4) (sourceB304 + difference 4 0) sourceC304) = raw6641 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6641; decide +kernel
    rw [ha]
    exact (canonical6641 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA304 + difference 0 5) (sourceB304 + difference 5 0) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA304 + difference 0 5) (sourceB304 + difference 5 0) sourceC304) = raw6642 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6642; decide +kernel
    rw [ha]
    exact (canonical6642 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA304 + difference 1 0) (sourceB304 + difference 0 1) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA304 + difference 1 0) (sourceB304 + difference 0 1) sourceC304) = raw6643 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6643; decide +kernel
    rw [ha]
    exact (canonical6643 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA304 + difference 1 2) (sourceB304 + difference 2 1) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3461) := by
    have ha : (tripleCharges (sourceA304 + difference 1 2) (sourceB304 + difference 2 1) sourceC304) = raw6644 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6644; decide +kernel
    rw [ha]
    exact (canonical6644 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA304 + difference 1 3) (sourceB304 + difference 3 1) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3621) := by
    have ha : (tripleCharges (sourceA304 + difference 1 3) (sourceB304 + difference 3 1) sourceC304) = raw6645 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6645; decide +kernel
    rw [ha]
    exact (canonical6645 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA304 + difference 1 4) (sourceB304 + difference 4 1) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA304 + difference 1 4) (sourceB304 + difference 4 1) sourceC304) = raw6646 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6646; decide +kernel
    rw [ha]
    exact (canonical6646 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA304 + difference 1 5) (sourceB304 + difference 5 1) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3619) := by
    have ha : (tripleCharges (sourceA304 + difference 1 5) (sourceB304 + difference 5 1) sourceC304) = raw6647 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6647; decide +kernel
    rw [ha]
    exact (canonical6647 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA304 + difference 2 0) (sourceB304 + difference 0 2) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1601) := by
    have ha : (tripleCharges (sourceA304 + difference 2 0) (sourceB304 + difference 0 2) sourceC304) = raw6648 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6648; decide +kernel
    rw [ha]
    exact (canonical6648 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA304 + difference 2 1) (sourceB304 + difference 1 2) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3342) := by
    have ha : (tripleCharges (sourceA304 + difference 2 1) (sourceB304 + difference 1 2) sourceC304) = raw6649 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6649; decide +kernel
    rw [ha]
    exact (canonical6649 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA304 + difference 2 3) (sourceB304 + difference 3 2) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3529) := by
    have ha : (tripleCharges (sourceA304 + difference 2 3) (sourceB304 + difference 3 2) sourceC304) = raw6650 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6650; decide +kernel
    rw [ha]
    exact (canonical6650 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA304 + difference 2 4) (sourceB304 + difference 4 2) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3497) := by
    have ha : (tripleCharges (sourceA304 + difference 2 4) (sourceB304 + difference 4 2) sourceC304) = raw6651 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6651; decide +kernel
    rw [ha]
    exact (canonical6651 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA304 + difference 2 5) (sourceB304 + difference 5 2) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA304 + difference 2 5) (sourceB304 + difference 5 2) sourceC304) = raw6652 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6652; decide +kernel
    rw [ha]
    exact (canonical6652 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA304 + difference 3 0) (sourceB304 + difference 0 3) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1603) := by
    have ha : (tripleCharges (sourceA304 + difference 3 0) (sourceB304 + difference 0 3) sourceC304) = raw6653 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6653; decide +kernel
    rw [ha]
    exact (canonical6653 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA304 + difference 3 1) (sourceB304 + difference 1 3) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2855) := by
    have ha : (tripleCharges (sourceA304 + difference 3 1) (sourceB304 + difference 1 3) sourceC304) = raw6654 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6654; decide +kernel
    rw [ha]
    exact (canonical6654 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA304 + difference 3 2) (sourceB304 + difference 2 3) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2851) := by
    have ha : (tripleCharges (sourceA304 + difference 3 2) (sourceB304 + difference 2 3) sourceC304) = raw6655 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6655; decide +kernel
    rw [ha]
    exact (canonical6655 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA304 + difference 3 4) (sourceB304 + difference 4 3) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2879) := by
    have ha : (tripleCharges (sourceA304 + difference 3 4) (sourceB304 + difference 4 3) sourceC304) = raw6656 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6656; decide +kernel
    rw [ha]
    exact (canonical6656 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA304 + difference 3 5) (sourceB304 + difference 5 3) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA304 + difference 3 5) (sourceB304 + difference 5 3) sourceC304) = raw6657 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6657; decide +kernel
    rw [ha]
    exact (canonical6657 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA304 + difference 4 0) (sourceB304 + difference 0 4) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1626) := by
    have ha : (tripleCharges (sourceA304 + difference 4 0) (sourceB304 + difference 0 4) sourceC304) = raw6658 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6658; decide +kernel
    rw [ha]
    exact (canonical6658 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA304 + difference 4 1) (sourceB304 + difference 1 4) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3359) := by
    have ha : (tripleCharges (sourceA304 + difference 4 1) (sourceB304 + difference 1 4) sourceC304) = raw6659 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6659; decide +kernel
    rw [ha]
    exact (canonical6659 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA304 + difference 4 2) (sourceB304 + difference 2 4) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3438) := by
    have ha : (tripleCharges (sourceA304 + difference 4 2) (sourceB304 + difference 2 4) sourceC304) = raw6660 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6660; decide +kernel
    rw [ha]
    exact (canonical6660 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA304 + difference 4 3) (sourceB304 + difference 3 4) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3542) := by
    have ha : (tripleCharges (sourceA304 + difference 4 3) (sourceB304 + difference 3 4) sourceC304) = raw6661 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6661; decide +kernel
    rw [ha]
    exact (canonical6661 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA304 + difference 4 5) (sourceB304 + difference 5 4) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA304 + difference 4 5) (sourceB304 + difference 5 4) sourceC304) = raw6662 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6662; decide +kernel
    rw [ha]
    exact (canonical6662 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA304 + difference 5 0) (sourceB304 + difference 0 5) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1604) := by
    have ha : (tripleCharges (sourceA304 + difference 5 0) (sourceB304 + difference 0 5) sourceC304) = raw6663 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6663; decide +kernel
    rw [ha]
    exact (canonical6663 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA304 + difference 5 1) (sourceB304 + difference 1 5) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3343) := by
    have ha : (tripleCharges (sourceA304 + difference 5 1) (sourceB304 + difference 1 5) sourceC304) = raw6664 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6664; decide +kernel
    rw [ha]
    exact (canonical6664 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA304 + difference 5 2) (sourceB304 + difference 2 5) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3368) := by
    have ha : (tripleCharges (sourceA304 + difference 5 2) (sourceB304 + difference 2 5) sourceC304) = raw6665 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6665; decide +kernel
    rw [ha]
    exact (canonical6665 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA304 + difference 5 3) (sourceB304 + difference 3 5) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA304 + difference 5 3) (sourceB304 + difference 3 5) sourceC304) = raw6666 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6666; decide +kernel
    rw [ha]
    exact (canonical6666 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA304 + difference 5 4) (sourceB304 + difference 4 5) sourceC304) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3389) := by
    have ha : (tripleCharges (sourceA304 + difference 5 4) (sourceB304 + difference 4 5) sourceC304) = raw6667 := by
      apply Matrix.ext; unfold tripleCharges sourceA304 sourceB304 sourceC304 difference raw6667; decide +kernel
    rw [ha]
    exact (canonical6667 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA304 sourceB304 sourceC304
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm304, Integer.Sparse.eval]
  linarith only [hs]

def sourceA305 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB305 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC305 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceForm305 : Integer.Sparse Master := [(Sum.inr 3039, 1), (Sum.inr 3880, 1), (Sum.inr 3881, 1), (Sum.inr 3885, 1), (Sum.inr 3910, 1), (Sum.inr 3958, 1), (Sum.inr 4091, -1)]

theorem sourceEq305 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm305 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA305 + difference 0 0) (sourceB305 + difference 0 0) sourceC305) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA305 + difference 0 0) (sourceB305 + difference 0 0) sourceC305) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA305 sourceB305 sourceC305 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA305 + difference 0 1) (sourceB305 + difference 1 0) sourceC305) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA305 + difference 0 1) (sourceB305 + difference 1 0) sourceC305) = raw6669 := by
      apply Matrix.ext; unfold tripleCharges sourceA305 sourceB305 sourceC305 difference raw6669; decide +kernel
    rw [ha]
    exact (canonical6669 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA305 + difference 0 2) (sourceB305 + difference 2 0) sourceC305) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA305 + difference 0 2) (sourceB305 + difference 2 0) sourceC305) = raw6670 := by
      apply Matrix.ext; unfold tripleCharges sourceA305 sourceB305 sourceC305 difference raw6670; decide +kernel
    rw [ha]
    exact (canonical6670 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA305 + difference 0 3) (sourceB305 + difference 3 0) sourceC305) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA305 + difference 0 3) (sourceB305 + difference 3 0) sourceC305) = raw6671 := by
      apply Matrix.ext; unfold tripleCharges sourceA305 sourceB305 sourceC305 difference raw6671; decide +kernel
    rw [ha]
    exact (canonical6671 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA305 + difference 0 4) (sourceB305 + difference 4 0) sourceC305) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA305 + difference 0 4) (sourceB305 + difference 4 0) sourceC305) = raw6672 := by
      apply Matrix.ext; unfold tripleCharges sourceA305 sourceB305 sourceC305 difference raw6672; decide +kernel
    rw [ha]
    exact (canonical6672 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA305 + difference 0 5) (sourceB305 + difference 5 0) sourceC305) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3910) := by
    have ha : (tripleCharges (sourceA305 + difference 0 5) (sourceB305 + difference 5 0) sourceC305) = raw6673 := by
      apply Matrix.ext; unfold tripleCharges sourceA305 sourceB305 sourceC305 difference raw6673; decide +kernel
    rw [ha]
    exact (canonical6673 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA305 + sourceB305) sourceC305) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA305 + sourceB305) sourceC305) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA305 sourceB305 sourceC305 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA305 sourceB305 sourceC305
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm305, Integer.Sparse.eval]
  linarith only [hs]

def sourceA306 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB306 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC306 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceForm306 : Integer.Sparse Master := [(Sum.inr 1358, 1), (Sum.inr 1361, 1), (Sum.inr 1363, 1), (Sum.inr 1370, 1), (Sum.inr 1423, 1), (Sum.inr 3039, 1), (Sum.inr 4091, -1)]

theorem sourceEq306 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm306 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA306 + difference 0 0) (sourceB306 + difference 0 0) sourceC306) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA306 + difference 0 0) (sourceB306 + difference 0 0) sourceC306) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA306 sourceB306 sourceC306 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA306 + difference 1 0) (sourceB306 + difference 0 1) sourceC306) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1370) := by
    have ha : (tripleCharges (sourceA306 + difference 1 0) (sourceB306 + difference 0 1) sourceC306) = raw6675 := by
      apply Matrix.ext; unfold tripleCharges sourceA306 sourceB306 sourceC306 difference raw6675; decide +kernel
    rw [ha]
    exact (canonical6675 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA306 + difference 2 0) (sourceB306 + difference 0 2) sourceC306) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1358) := by
    have ha : (tripleCharges (sourceA306 + difference 2 0) (sourceB306 + difference 0 2) sourceC306) = raw6676 := by
      apply Matrix.ext; unfold tripleCharges sourceA306 sourceB306 sourceC306 difference raw6676; decide +kernel
    rw [ha]
    exact (canonical6676 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA306 + difference 3 0) (sourceB306 + difference 0 3) sourceC306) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1423) := by
    have ha : (tripleCharges (sourceA306 + difference 3 0) (sourceB306 + difference 0 3) sourceC306) = raw6677 := by
      apply Matrix.ext; unfold tripleCharges sourceA306 sourceB306 sourceC306 difference raw6677; decide +kernel
    rw [ha]
    exact (canonical6677 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA306 + difference 4 0) (sourceB306 + difference 0 4) sourceC306) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1363) := by
    have ha : (tripleCharges (sourceA306 + difference 4 0) (sourceB306 + difference 0 4) sourceC306) = raw6678 := by
      apply Matrix.ext; unfold tripleCharges sourceA306 sourceB306 sourceC306 difference raw6678; decide +kernel
    rw [ha]
    exact (canonical6678 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA306 + difference 5 0) (sourceB306 + difference 0 5) sourceC306) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1361) := by
    have ha : (tripleCharges (sourceA306 + difference 5 0) (sourceB306 + difference 0 5) sourceC306) = raw6679 := by
      apply Matrix.ext; unfold tripleCharges sourceA306 sourceB306 sourceC306 difference raw6679; decide +kernel
    rw [ha]
    exact (canonical6679 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA306 + sourceB306) sourceC306) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA306 + sourceB306) sourceC306) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA306 sourceB306 sourceC306 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA306 sourceB306 sourceC306
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm306, Integer.Sparse.eval]
  linarith only [hs]

def sourceA307 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB307 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC307 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceForm307 : Integer.Sparse Master := [(Sum.inr 1370, 1), (Sum.inr 2884, 1), (Sum.inr 2976, 1), (Sum.inr 3039, 2), (Sum.inr 3053, 1), (Sum.inr 4091, -1)]

theorem sourceEq307 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm307 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA307 + difference 1 0) (sourceB307 + difference 0 1) sourceC307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1370) := by
    have ha : (tripleCharges (sourceA307 + difference 1 0) (sourceB307 + difference 0 1) sourceC307) = raw6675 := by
      apply Matrix.ext; unfold tripleCharges sourceA307 sourceB307 sourceC307 difference raw6675; decide +kernel
    rw [ha]
    exact (canonical6675 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA307 + difference 1 1) (sourceB307 + difference 1 1) sourceC307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA307 + difference 1 1) (sourceB307 + difference 1 1) sourceC307) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA307 sourceB307 sourceC307 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA307 + difference 1 2) (sourceB307 + difference 2 1) sourceC307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2976) := by
    have ha : (tripleCharges (sourceA307 + difference 1 2) (sourceB307 + difference 2 1) sourceC307) = raw6680 := by
      apply Matrix.ext; unfold tripleCharges sourceA307 sourceB307 sourceC307 difference raw6680; decide +kernel
    rw [ha]
    exact (canonical6680 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA307 + difference 1 3) (sourceB307 + difference 3 1) sourceC307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA307 + difference 1 3) (sourceB307 + difference 3 1) sourceC307) = raw6681 := by
      apply Matrix.ext; unfold tripleCharges sourceA307 sourceB307 sourceC307 difference raw6681; decide +kernel
    rw [ha]
    exact (canonical6681 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA307 + difference 1 4) (sourceB307 + difference 4 1) sourceC307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA307 + difference 1 4) (sourceB307 + difference 4 1) sourceC307) = raw6682 := by
      apply Matrix.ext; unfold tripleCharges sourceA307 sourceB307 sourceC307 difference raw6682; decide +kernel
    rw [ha]
    exact (canonical6682 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA307 + difference 1 5) (sourceB307 + difference 5 1) sourceC307) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA307 + difference 1 5) (sourceB307 + difference 5 1) sourceC307) = raw6683 := by
      apply Matrix.ext; unfold tripleCharges sourceA307 sourceB307 sourceC307 difference raw6683; decide +kernel
    rw [ha]
    exact (canonical6683 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA307 + sourceB307) sourceC307) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA307 + sourceB307) sourceC307) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA307 sourceB307 sourceC307 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA307 sourceB307 sourceC307
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm307, Integer.Sparse.eval]
  linarith only [hs]

def sourceA308 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB308 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC308 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceForm308 : Integer.Sparse Master := [(Sum.inr 2627, 1), (Sum.inr 2946, 1), (Sum.inr 3008, 1), (Sum.inr 3011, 1), (Sum.inr 3039, 1), (Sum.inr 3881, 1), (Sum.inr 4091, -1)]

theorem sourceEq308 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm308 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA308 + difference 0 1) (sourceB308 + difference 1 0) sourceC308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA308 + difference 0 1) (sourceB308 + difference 1 0) sourceC308) = raw6669 := by
      apply Matrix.ext; unfold tripleCharges sourceA308 sourceB308 sourceC308 difference raw6669; decide +kernel
    rw [ha]
    exact (canonical6669 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA308 + difference 1 1) (sourceB308 + difference 1 1) sourceC308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA308 + difference 1 1) (sourceB308 + difference 1 1) sourceC308) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA308 sourceB308 sourceC308 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA308 + difference 2 1) (sourceB308 + difference 1 2) sourceC308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3008) := by
    have ha : (tripleCharges (sourceA308 + difference 2 1) (sourceB308 + difference 1 2) sourceC308) = raw6684 := by
      apply Matrix.ext; unfold tripleCharges sourceA308 sourceB308 sourceC308 difference raw6684; decide +kernel
    rw [ha]
    exact (canonical6684 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA308 + difference 3 1) (sourceB308 + difference 1 3) sourceC308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2627) := by
    have ha : (tripleCharges (sourceA308 + difference 3 1) (sourceB308 + difference 1 3) sourceC308) = raw6685 := by
      apply Matrix.ext; unfold tripleCharges sourceA308 sourceB308 sourceC308 difference raw6685; decide +kernel
    rw [ha]
    exact (canonical6685 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA308 + difference 4 1) (sourceB308 + difference 1 4) sourceC308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3011) := by
    have ha : (tripleCharges (sourceA308 + difference 4 1) (sourceB308 + difference 1 4) sourceC308) = raw6686 := by
      apply Matrix.ext; unfold tripleCharges sourceA308 sourceB308 sourceC308 difference raw6686; decide +kernel
    rw [ha]
    exact (canonical6686 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA308 + difference 5 1) (sourceB308 + difference 1 5) sourceC308) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2946) := by
    have ha : (tripleCharges (sourceA308 + difference 5 1) (sourceB308 + difference 1 5) sourceC308) = raw6687 := by
      apply Matrix.ext; unfold tripleCharges sourceA308 sourceB308 sourceC308 difference raw6687; decide +kernel
    rw [ha]
    exact (canonical6687 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA308 + sourceB308) sourceC308) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA308 + sourceB308) sourceC308) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA308 sourceB308 sourceC308 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA308 sourceB308 sourceC308
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm308, Integer.Sparse.eval]
  linarith only [hs]

def sourceA309 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB309 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC309 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceForm309 : Integer.Sparse Master := [(Sum.inr 1358, 1), (Sum.inr 2862, 1), (Sum.inr 3008, 1), (Sum.inr 3029, 1), (Sum.inr 3037, 1), (Sum.inr 3039, 1), (Sum.inr 4091, -1)]

theorem sourceEq309 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm309 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA309 + difference 2 0) (sourceB309 + difference 0 2) sourceC309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1358) := by
    have ha : (tripleCharges (sourceA309 + difference 2 0) (sourceB309 + difference 0 2) sourceC309) = raw6676 := by
      apply Matrix.ext; unfold tripleCharges sourceA309 sourceB309 sourceC309 difference raw6676; decide +kernel
    rw [ha]
    exact (canonical6676 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA309 + difference 2 1) (sourceB309 + difference 1 2) sourceC309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3008) := by
    have ha : (tripleCharges (sourceA309 + difference 2 1) (sourceB309 + difference 1 2) sourceC309) = raw6684 := by
      apply Matrix.ext; unfold tripleCharges sourceA309 sourceB309 sourceC309 difference raw6684; decide +kernel
    rw [ha]
    exact (canonical6684 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA309 + difference 2 2) (sourceB309 + difference 2 2) sourceC309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA309 + difference 2 2) (sourceB309 + difference 2 2) sourceC309) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA309 sourceB309 sourceC309 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA309 + difference 2 3) (sourceB309 + difference 3 2) sourceC309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2862) := by
    have ha : (tripleCharges (sourceA309 + difference 2 3) (sourceB309 + difference 3 2) sourceC309) = raw6688 := by
      apply Matrix.ext; unfold tripleCharges sourceA309 sourceB309 sourceC309 difference raw6688; decide +kernel
    rw [ha]
    exact (canonical6688 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA309 + difference 2 4) (sourceB309 + difference 4 2) sourceC309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3029) := by
    have ha : (tripleCharges (sourceA309 + difference 2 4) (sourceB309 + difference 4 2) sourceC309) = raw6689 := by
      apply Matrix.ext; unfold tripleCharges sourceA309 sourceB309 sourceC309 difference raw6689; decide +kernel
    rw [ha]
    exact (canonical6689 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA309 + difference 2 5) (sourceB309 + difference 5 2) sourceC309) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA309 + difference 2 5) (sourceB309 + difference 5 2) sourceC309) = raw6690 := by
      apply Matrix.ext; unfold tripleCharges sourceA309 sourceB309 sourceC309 difference raw6690; decide +kernel
    rw [ha]
    exact (canonical6690 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA309 + sourceB309) sourceC309) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA309 + sourceB309) sourceC309) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA309 sourceB309 sourceC309 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA309 sourceB309 sourceC309
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm309, Integer.Sparse.eval]
  linarith only [hs]

def sourceA310 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB310 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC310 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceForm310 : Integer.Sparse Master := [(Sum.inr 2625, 1), (Sum.inr 2918, 1), (Sum.inr 2972, 1), (Sum.inr 2976, 1), (Sum.inr 3039, 1), (Sum.inr 3880, 1), (Sum.inr 4091, -1)]

theorem sourceEq310 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm310 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA310 + difference 0 2) (sourceB310 + difference 2 0) sourceC310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA310 + difference 0 2) (sourceB310 + difference 2 0) sourceC310) = raw6670 := by
      apply Matrix.ext; unfold tripleCharges sourceA310 sourceB310 sourceC310 difference raw6670; decide +kernel
    rw [ha]
    exact (canonical6670 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA310 + difference 1 2) (sourceB310 + difference 2 1) sourceC310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2976) := by
    have ha : (tripleCharges (sourceA310 + difference 1 2) (sourceB310 + difference 2 1) sourceC310) = raw6680 := by
      apply Matrix.ext; unfold tripleCharges sourceA310 sourceB310 sourceC310 difference raw6680; decide +kernel
    rw [ha]
    exact (canonical6680 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA310 + difference 2 2) (sourceB310 + difference 2 2) sourceC310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA310 + difference 2 2) (sourceB310 + difference 2 2) sourceC310) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA310 sourceB310 sourceC310 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA310 + difference 3 2) (sourceB310 + difference 2 3) sourceC310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2625) := by
    have ha : (tripleCharges (sourceA310 + difference 3 2) (sourceB310 + difference 2 3) sourceC310) = raw6691 := by
      apply Matrix.ext; unfold tripleCharges sourceA310 sourceB310 sourceC310 difference raw6691; decide +kernel
    rw [ha]
    exact (canonical6691 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA310 + difference 4 2) (sourceB310 + difference 2 4) sourceC310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2972) := by
    have ha : (tripleCharges (sourceA310 + difference 4 2) (sourceB310 + difference 2 4) sourceC310) = raw6692 := by
      apply Matrix.ext; unfold tripleCharges sourceA310 sourceB310 sourceC310 difference raw6692; decide +kernel
    rw [ha]
    exact (canonical6692 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA310 + difference 5 2) (sourceB310 + difference 2 5) sourceC310) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2918) := by
    have ha : (tripleCharges (sourceA310 + difference 5 2) (sourceB310 + difference 2 5) sourceC310) = raw6693 := by
      apply Matrix.ext; unfold tripleCharges sourceA310 sourceB310 sourceC310 difference raw6693; decide +kernel
    rw [ha]
    exact (canonical6693 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA310 + sourceB310) sourceC310) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA310 + sourceB310) sourceC310) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA310 sourceB310 sourceC310 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA310 sourceB310 sourceC310
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm310, Integer.Sparse.eval]
  linarith only [hs]

def sourceA311 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB311 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC311 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceForm311 : Integer.Sparse Master := [(Sum.inr 1423, 1), (Sum.inr 2625, 1), (Sum.inr 2627, 1), (Sum.inr 2641, 1), (Sum.inr 2754, 1), (Sum.inr 3039, 1), (Sum.inr 4091, -1)]

theorem sourceEq311 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm311 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA311 + difference 3 0) (sourceB311 + difference 0 3) sourceC311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1423) := by
    have ha : (tripleCharges (sourceA311 + difference 3 0) (sourceB311 + difference 0 3) sourceC311) = raw6677 := by
      apply Matrix.ext; unfold tripleCharges sourceA311 sourceB311 sourceC311 difference raw6677; decide +kernel
    rw [ha]
    exact (canonical6677 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA311 + difference 3 1) (sourceB311 + difference 1 3) sourceC311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2627) := by
    have ha : (tripleCharges (sourceA311 + difference 3 1) (sourceB311 + difference 1 3) sourceC311) = raw6685 := by
      apply Matrix.ext; unfold tripleCharges sourceA311 sourceB311 sourceC311 difference raw6685; decide +kernel
    rw [ha]
    exact (canonical6685 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA311 + difference 3 2) (sourceB311 + difference 2 3) sourceC311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2625) := by
    have ha : (tripleCharges (sourceA311 + difference 3 2) (sourceB311 + difference 2 3) sourceC311) = raw6691 := by
      apply Matrix.ext; unfold tripleCharges sourceA311 sourceB311 sourceC311 difference raw6691; decide +kernel
    rw [ha]
    exact (canonical6691 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA311 + difference 3 3) (sourceB311 + difference 3 3) sourceC311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA311 + difference 3 3) (sourceB311 + difference 3 3) sourceC311) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA311 sourceB311 sourceC311 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA311 + difference 3 4) (sourceB311 + difference 4 3) sourceC311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2641) := by
    have ha : (tripleCharges (sourceA311 + difference 3 4) (sourceB311 + difference 4 3) sourceC311) = raw6694 := by
      apply Matrix.ext; unfold tripleCharges sourceA311 sourceB311 sourceC311 difference raw6694; decide +kernel
    rw [ha]
    exact (canonical6694 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA311 + difference 3 5) (sourceB311 + difference 5 3) sourceC311) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA311 + difference 3 5) (sourceB311 + difference 5 3) sourceC311) = raw6695 := by
      apply Matrix.ext; unfold tripleCharges sourceA311 sourceB311 sourceC311 difference raw6695; decide +kernel
    rw [ha]
    exact (canonical6695 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA311 + sourceB311) sourceC311) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA311 + sourceB311) sourceC311) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA311 sourceB311 sourceC311 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA311 sourceB311 sourceC311
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm311, Integer.Sparse.eval]
  linarith only [hs]

def sourceA312 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB312 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC312 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceForm312 : Integer.Sparse Master := [(Sum.inr 2862, 1), (Sum.inr 2865, 1), (Sum.inr 2868, 1), (Sum.inr 2884, 1), (Sum.inr 3039, 1), (Sum.inr 3958, 1), (Sum.inr 4091, -1)]

theorem sourceEq312 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm312 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA312 + difference 0 3) (sourceB312 + difference 3 0) sourceC312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA312 + difference 0 3) (sourceB312 + difference 3 0) sourceC312) = raw6671 := by
      apply Matrix.ext; unfold tripleCharges sourceA312 sourceB312 sourceC312 difference raw6671; decide +kernel
    rw [ha]
    exact (canonical6671 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA312 + difference 1 3) (sourceB312 + difference 3 1) sourceC312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA312 + difference 1 3) (sourceB312 + difference 3 1) sourceC312) = raw6681 := by
      apply Matrix.ext; unfold tripleCharges sourceA312 sourceB312 sourceC312 difference raw6681; decide +kernel
    rw [ha]
    exact (canonical6681 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA312 + difference 2 3) (sourceB312 + difference 3 2) sourceC312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2862) := by
    have ha : (tripleCharges (sourceA312 + difference 2 3) (sourceB312 + difference 3 2) sourceC312) = raw6688 := by
      apply Matrix.ext; unfold tripleCharges sourceA312 sourceB312 sourceC312 difference raw6688; decide +kernel
    rw [ha]
    exact (canonical6688 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA312 + difference 3 3) (sourceB312 + difference 3 3) sourceC312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA312 + difference 3 3) (sourceB312 + difference 3 3) sourceC312) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA312 sourceB312 sourceC312 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA312 + difference 4 3) (sourceB312 + difference 3 4) sourceC312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2868) := by
    have ha : (tripleCharges (sourceA312 + difference 4 3) (sourceB312 + difference 3 4) sourceC312) = raw6696 := by
      apply Matrix.ext; unfold tripleCharges sourceA312 sourceB312 sourceC312 difference raw6696; decide +kernel
    rw [ha]
    exact (canonical6696 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA312 + difference 5 3) (sourceB312 + difference 3 5) sourceC312) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA312 + difference 5 3) (sourceB312 + difference 3 5) sourceC312) = raw6697 := by
      apply Matrix.ext; unfold tripleCharges sourceA312 sourceB312 sourceC312 difference raw6697; decide +kernel
    rw [ha]
    exact (canonical6697 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA312 + sourceB312) sourceC312) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA312 + sourceB312) sourceC312) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA312 sourceB312 sourceC312 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA312 sourceB312 sourceC312
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm312, Integer.Sparse.eval]
  linarith only [hs]

def sourceA313 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB313 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC313 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceForm313 : Integer.Sparse Master := [(Sum.inr 1363, 1), (Sum.inr 2868, 1), (Sum.inr 2972, 1), (Sum.inr 3011, 1), (Sum.inr 3039, 2), (Sum.inr 4091, -1)]

theorem sourceEq313 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm313 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA313 + difference 4 0) (sourceB313 + difference 0 4) sourceC313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1363) := by
    have ha : (tripleCharges (sourceA313 + difference 4 0) (sourceB313 + difference 0 4) sourceC313) = raw6678 := by
      apply Matrix.ext; unfold tripleCharges sourceA313 sourceB313 sourceC313 difference raw6678; decide +kernel
    rw [ha]
    exact (canonical6678 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA313 + difference 4 1) (sourceB313 + difference 1 4) sourceC313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3011) := by
    have ha : (tripleCharges (sourceA313 + difference 4 1) (sourceB313 + difference 1 4) sourceC313) = raw6686 := by
      apply Matrix.ext; unfold tripleCharges sourceA313 sourceB313 sourceC313 difference raw6686; decide +kernel
    rw [ha]
    exact (canonical6686 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA313 + difference 4 2) (sourceB313 + difference 2 4) sourceC313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2972) := by
    have ha : (tripleCharges (sourceA313 + difference 4 2) (sourceB313 + difference 2 4) sourceC313) = raw6692 := by
      apply Matrix.ext; unfold tripleCharges sourceA313 sourceB313 sourceC313 difference raw6692; decide +kernel
    rw [ha]
    exact (canonical6692 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA313 + difference 4 3) (sourceB313 + difference 3 4) sourceC313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2868) := by
    have ha : (tripleCharges (sourceA313 + difference 4 3) (sourceB313 + difference 3 4) sourceC313) = raw6696 := by
      apply Matrix.ext; unfold tripleCharges sourceA313 sourceB313 sourceC313 difference raw6696; decide +kernel
    rw [ha]
    exact (canonical6696 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA313 + difference 4 4) (sourceB313 + difference 4 4) sourceC313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA313 + difference 4 4) (sourceB313 + difference 4 4) sourceC313) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA313 sourceB313 sourceC313 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA313 + difference 4 5) (sourceB313 + difference 5 4) sourceC313) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA313 + difference 4 5) (sourceB313 + difference 5 4) sourceC313) = raw6698 := by
      apply Matrix.ext; unfold tripleCharges sourceA313 sourceB313 sourceC313 difference raw6698; decide +kernel
    rw [ha]
    exact (canonical6698 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA313 + sourceB313) sourceC313) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA313 + sourceB313) sourceC313) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA313 sourceB313 sourceC313 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA313 sourceB313 sourceC313
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm313, Integer.Sparse.eval]
  linarith only [hs]

def sourceA314 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB314 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC314 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceForm314 : Integer.Sparse Master := [(Sum.inr 2641, 1), (Sum.inr 3029, 1), (Sum.inr 3031, 1), (Sum.inr 3039, 2), (Sum.inr 3885, 1), (Sum.inr 4091, -1)]

theorem sourceEq314 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm314 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA314 + difference 0 4) (sourceB314 + difference 4 0) sourceC314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA314 + difference 0 4) (sourceB314 + difference 4 0) sourceC314) = raw6672 := by
      apply Matrix.ext; unfold tripleCharges sourceA314 sourceB314 sourceC314 difference raw6672; decide +kernel
    rw [ha]
    exact (canonical6672 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA314 + difference 1 4) (sourceB314 + difference 4 1) sourceC314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA314 + difference 1 4) (sourceB314 + difference 4 1) sourceC314) = raw6682 := by
      apply Matrix.ext; unfold tripleCharges sourceA314 sourceB314 sourceC314 difference raw6682; decide +kernel
    rw [ha]
    exact (canonical6682 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA314 + difference 2 4) (sourceB314 + difference 4 2) sourceC314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3029) := by
    have ha : (tripleCharges (sourceA314 + difference 2 4) (sourceB314 + difference 4 2) sourceC314) = raw6689 := by
      apply Matrix.ext; unfold tripleCharges sourceA314 sourceB314 sourceC314 difference raw6689; decide +kernel
    rw [ha]
    exact (canonical6689 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA314 + difference 3 4) (sourceB314 + difference 4 3) sourceC314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2641) := by
    have ha : (tripleCharges (sourceA314 + difference 3 4) (sourceB314 + difference 4 3) sourceC314) = raw6694 := by
      apply Matrix.ext; unfold tripleCharges sourceA314 sourceB314 sourceC314 difference raw6694; decide +kernel
    rw [ha]
    exact (canonical6694 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA314 + difference 4 4) (sourceB314 + difference 4 4) sourceC314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA314 + difference 4 4) (sourceB314 + difference 4 4) sourceC314) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA314 sourceB314 sourceC314 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA314 + difference 5 4) (sourceB314 + difference 4 5) sourceC314) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3031) := by
    have ha : (tripleCharges (sourceA314 + difference 5 4) (sourceB314 + difference 4 5) sourceC314) = raw6699 := by
      apply Matrix.ext; unfold tripleCharges sourceA314 sourceB314 sourceC314 difference raw6699; decide +kernel
    rw [ha]
    exact (canonical6699 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA314 + sourceB314) sourceC314) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA314 + sourceB314) sourceC314) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA314 sourceB314 sourceC314 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA314 sourceB314 sourceC314
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm314, Integer.Sparse.eval]
  linarith only [hs]

def sourceA315 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB315 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC315 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceForm315 : Integer.Sparse Master := [(Sum.inr 1361, 1), (Sum.inr 2865, 1), (Sum.inr 2918, 1), (Sum.inr 2946, 1), (Sum.inr 3031, 1), (Sum.inr 3039, 1), (Sum.inr 4091, -1)]

theorem sourceEq315 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm315 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA315 + difference 5 0) (sourceB315 + difference 0 5) sourceC315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1361) := by
    have ha : (tripleCharges (sourceA315 + difference 5 0) (sourceB315 + difference 0 5) sourceC315) = raw6679 := by
      apply Matrix.ext; unfold tripleCharges sourceA315 sourceB315 sourceC315 difference raw6679; decide +kernel
    rw [ha]
    exact (canonical6679 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA315 + difference 5 1) (sourceB315 + difference 1 5) sourceC315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2946) := by
    have ha : (tripleCharges (sourceA315 + difference 5 1) (sourceB315 + difference 1 5) sourceC315) = raw6687 := by
      apply Matrix.ext; unfold tripleCharges sourceA315 sourceB315 sourceC315 difference raw6687; decide +kernel
    rw [ha]
    exact (canonical6687 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA315 + difference 5 2) (sourceB315 + difference 2 5) sourceC315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2918) := by
    have ha : (tripleCharges (sourceA315 + difference 5 2) (sourceB315 + difference 2 5) sourceC315) = raw6693 := by
      apply Matrix.ext; unfold tripleCharges sourceA315 sourceB315 sourceC315 difference raw6693; decide +kernel
    rw [ha]
    exact (canonical6693 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA315 + difference 5 3) (sourceB315 + difference 3 5) sourceC315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA315 + difference 5 3) (sourceB315 + difference 3 5) sourceC315) = raw6697 := by
      apply Matrix.ext; unfold tripleCharges sourceA315 sourceB315 sourceC315 difference raw6697; decide +kernel
    rw [ha]
    exact (canonical6697 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA315 + difference 5 4) (sourceB315 + difference 4 5) sourceC315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3031) := by
    have ha : (tripleCharges (sourceA315 + difference 5 4) (sourceB315 + difference 4 5) sourceC315) = raw6699 := by
      apply Matrix.ext; unfold tripleCharges sourceA315 sourceB315 sourceC315 difference raw6699; decide +kernel
    rw [ha]
    exact (canonical6699 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA315 + difference 5 5) (sourceB315 + difference 5 5) sourceC315) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA315 + difference 5 5) (sourceB315 + difference 5 5) sourceC315) = raw6668 := by
      apply Matrix.ext; unfold tripleCharges sourceA315 sourceB315 sourceC315 difference raw6668; decide +kernel
    rw [ha]
    exact (canonical6668 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA315 + sourceB315) sourceC315) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA315 + sourceB315) sourceC315) = raw6674 := by
      apply Matrix.ext; unfold doubleCharges sourceA315 sourceB315 sourceC315 raw6674; decide +kernel
    rw [ha]
    exact (canonical6674 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA315 sourceB315 sourceC315
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm315, Integer.Sparse.eval]
  linarith only [hs]

def sourceA316 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB316 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC316 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm316 : Integer.Sparse Master := [(Sum.inr 4803, 1), (Sum.inr 4808, 1), (Sum.inr 4810, 1), (Sum.inr 4839, 1), (Sum.inr 4854, 1), (Sum.inr 4855, 1), (Sum.inr 4870, 1), (Sum.inr 4880, 1), (Sum.inr 4896, 1), (Sum.inr 5220, 1), (Sum.inr 5223, 1), (Sum.inr 5228, 1), (Sum.inr 5229, 1), (Sum.inr 5232, 1), (Sum.inr 5233, 2), (Sum.inr 5243, 1), (Sum.inr 5244, 1), (Sum.inr 5250, 1), (Sum.inr 5253, 1), (Sum.inr 5254, 1), (Sum.inr 5258, 1), (Sum.inr 5259, 2), (Sum.inr 5264, 1), (Sum.inr 5266, 1), (Sum.inr 5267, 1), (Sum.inr 5293, 1), (Sum.inr 5300, 1), (Sum.inr 5302, 1)]

theorem sourceEq316 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm316 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA316 + difference 0 1) (sourceB316 + difference 1 0) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA316 + difference 0 1) (sourceB316 + difference 1 0) sourceC316) = raw6700 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6700; decide +kernel
    rw [ha]
    exact (canonical6700 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA316 + difference 0 2) (sourceB316 + difference 2 0) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5220) := by
    have ha : (tripleCharges (sourceA316 + difference 0 2) (sourceB316 + difference 2 0) sourceC316) = raw6701 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6701; decide +kernel
    rw [ha]
    exact (canonical6701 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA316 + difference 0 3) (sourceB316 + difference 3 0) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA316 + difference 0 3) (sourceB316 + difference 3 0) sourceC316) = raw6702 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6702; decide +kernel
    rw [ha]
    exact (canonical6702 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA316 + difference 0 4) (sourceB316 + difference 4 0) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA316 + difference 0 4) (sourceB316 + difference 4 0) sourceC316) = raw6703 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6703; decide +kernel
    rw [ha]
    exact (canonical6703 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA316 + difference 0 5) (sourceB316 + difference 5 0) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5228) := by
    have ha : (tripleCharges (sourceA316 + difference 0 5) (sourceB316 + difference 5 0) sourceC316) = raw6704 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6704; decide +kernel
    rw [ha]
    exact (canonical6704 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA316 + difference 1 0) (sourceB316 + difference 0 1) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4896) := by
    have ha : (tripleCharges (sourceA316 + difference 1 0) (sourceB316 + difference 0 1) sourceC316) = raw6705 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6705; decide +kernel
    rw [ha]
    exact (canonical6705 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA316 + difference 1 2) (sourceB316 + difference 2 1) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA316 + difference 1 2) (sourceB316 + difference 2 1) sourceC316) = raw6706 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6706; decide +kernel
    rw [ha]
    exact (canonical6706 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA316 + difference 1 3) (sourceB316 + difference 3 1) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA316 + difference 1 3) (sourceB316 + difference 3 1) sourceC316) = raw6707 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6707; decide +kernel
    rw [ha]
    exact (canonical6707 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA316 + difference 1 4) (sourceB316 + difference 4 1) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA316 + difference 1 4) (sourceB316 + difference 4 1) sourceC316) = raw6708 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6708; decide +kernel
    rw [ha]
    exact (canonical6708 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA316 + difference 1 5) (sourceB316 + difference 5 1) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA316 + difference 1 5) (sourceB316 + difference 5 1) sourceC316) = raw6709 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6709; decide +kernel
    rw [ha]
    exact (canonical6709 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA316 + difference 2 0) (sourceB316 + difference 0 2) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA316 + difference 2 0) (sourceB316 + difference 0 2) sourceC316) = raw6710 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6710; decide +kernel
    rw [ha]
    exact (canonical6710 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA316 + difference 2 1) (sourceB316 + difference 1 2) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5223) := by
    have ha : (tripleCharges (sourceA316 + difference 2 1) (sourceB316 + difference 1 2) sourceC316) = raw6711 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6711; decide +kernel
    rw [ha]
    exact (canonical6711 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA316 + difference 2 3) (sourceB316 + difference 3 2) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5250) := by
    have ha : (tripleCharges (sourceA316 + difference 2 3) (sourceB316 + difference 3 2) sourceC316) = raw6712 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6712; decide +kernel
    rw [ha]
    exact (canonical6712 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA316 + difference 2 4) (sourceB316 + difference 4 2) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5253) := by
    have ha : (tripleCharges (sourceA316 + difference 2 4) (sourceB316 + difference 4 2) sourceC316) = raw6713 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6713; decide +kernel
    rw [ha]
    exact (canonical6713 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA316 + difference 2 5) (sourceB316 + difference 5 2) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA316 + difference 2 5) (sourceB316 + difference 5 2) sourceC316) = raw6714 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6714; decide +kernel
    rw [ha]
    exact (canonical6714 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA316 + difference 3 0) (sourceB316 + difference 0 3) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4808) := by
    have ha : (tripleCharges (sourceA316 + difference 3 0) (sourceB316 + difference 0 3) sourceC316) = raw6715 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6715; decide +kernel
    rw [ha]
    exact (canonical6715 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA316 + difference 3 1) (sourceB316 + difference 1 3) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4855) := by
    have ha : (tripleCharges (sourceA316 + difference 3 1) (sourceB316 + difference 1 3) sourceC316) = raw6716 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6716; decide +kernel
    rw [ha]
    exact (canonical6716 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA316 + difference 3 2) (sourceB316 + difference 2 3) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4854) := by
    have ha : (tripleCharges (sourceA316 + difference 3 2) (sourceB316 + difference 2 3) sourceC316) = raw6717 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6717; decide +kernel
    rw [ha]
    exact (canonical6717 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA316 + difference 3 4) (sourceB316 + difference 4 3) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4870) := by
    have ha : (tripleCharges (sourceA316 + difference 3 4) (sourceB316 + difference 4 3) sourceC316) = raw6718 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6718; decide +kernel
    rw [ha]
    exact (canonical6718 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA316 + difference 3 5) (sourceB316 + difference 5 3) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA316 + difference 3 5) (sourceB316 + difference 5 3) sourceC316) = raw6719 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6719; decide +kernel
    rw [ha]
    exact (canonical6719 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA316 + difference 4 0) (sourceB316 + difference 0 4) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4839) := by
    have ha : (tripleCharges (sourceA316 + difference 4 0) (sourceB316 + difference 0 4) sourceC316) = raw6720 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6720; decide +kernel
    rw [ha]
    exact (canonical6720 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA316 + difference 4 1) (sourceB316 + difference 1 4) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5233) := by
    have ha : (tripleCharges (sourceA316 + difference 4 1) (sourceB316 + difference 1 4) sourceC316) = raw6721 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6721; decide +kernel
    rw [ha]
    exact (canonical6721 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA316 + difference 4 2) (sourceB316 + difference 2 4) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5244) := by
    have ha : (tripleCharges (sourceA316 + difference 4 2) (sourceB316 + difference 2 4) sourceC316) = raw6722 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6722; decide +kernel
    rw [ha]
    exact (canonical6722 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA316 + difference 4 3) (sourceB316 + difference 3 4) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA316 + difference 4 3) (sourceB316 + difference 3 4) sourceC316) = raw6390 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6390; decide +kernel
    rw [ha]
    exact (canonical6390 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA316 + difference 4 5) (sourceB316 + difference 5 4) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA316 + difference 4 5) (sourceB316 + difference 5 4) sourceC316) = raw6384 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6384; decide +kernel
    rw [ha]
    exact (canonical6384 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA316 + difference 5 0) (sourceB316 + difference 0 5) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4810) := by
    have ha : (tripleCharges (sourceA316 + difference 5 0) (sourceB316 + difference 0 5) sourceC316) = raw6723 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6723; decide +kernel
    rw [ha]
    exact (canonical6723 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA316 + difference 5 1) (sourceB316 + difference 1 5) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5232) := by
    have ha : (tripleCharges (sourceA316 + difference 5 1) (sourceB316 + difference 1 5) sourceC316) = raw6724 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6724; decide +kernel
    rw [ha]
    exact (canonical6724 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA316 + difference 5 2) (sourceB316 + difference 2 5) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5243) := by
    have ha : (tripleCharges (sourceA316 + difference 5 2) (sourceB316 + difference 2 5) sourceC316) = raw6725 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6725; decide +kernel
    rw [ha]
    exact (canonical6725 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA316 + difference 5 3) (sourceB316 + difference 3 5) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA316 + difference 5 3) (sourceB316 + difference 3 5) sourceC316) = raw6726 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6726; decide +kernel
    rw [ha]
    exact (canonical6726 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA316 + difference 5 4) (sourceB316 + difference 4 5) sourceC316) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5264) := by
    have ha : (tripleCharges (sourceA316 + difference 5 4) (sourceB316 + difference 4 5) sourceC316) = raw6727 := by
      apply Matrix.ext; unfold tripleCharges sourceA316 sourceB316 sourceC316 difference raw6727; decide +kernel
    rw [ha]
    exact (canonical6727 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA316 sourceB316 sourceC316
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm316, Integer.Sparse.eval]
  linarith only [hs]

def sourceA317 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB317 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC317 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm317 : Integer.Sparse Master := [(Sum.inr 2127, 1), (Sum.inr 2128, 1), (Sum.inr 2129, 1), (Sum.inr 2133, 1), (Sum.inr 2195, 1), (Sum.inr 2215, 1), (Sum.inr 2216, 1), (Sum.inr 2220, 1), (Sum.inr 2278, 1), (Sum.inr 2665, 1), (Sum.inr 2677, 1), (Sum.inr 2678, 1), (Sum.inr 2697, 1), (Sum.inr 2698, 1), (Sum.inr 2709, 1), (Sum.inr 2713, 1), (Sum.inr 2714, 1), (Sum.inr 2722, 1), (Sum.inr 2723, 1), (Sum.inr 2729, 1), (Sum.inr 2731, 1), (Sum.inr 2732, 1), (Sum.inr 2767, 1), (Sum.inr 2774, 1), (Sum.inr 2776, 1), (Sum.inr 3044, 1), (Sum.inr 3068, 1), (Sum.inr 3088, 1), (Sum.inr 3092, 1), (Sum.inr 3094, 1)]

theorem sourceEq317 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm317 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA317 + difference 0 1) (sourceB317 + difference 1 0) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3044) := by
    have ha : (tripleCharges (sourceA317 + difference 0 1) (sourceB317 + difference 1 0) sourceC317) = raw6728 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6728; decide +kernel
    rw [ha]
    exact (canonical6728 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA317 + difference 0 2) (sourceB317 + difference 2 0) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3068) := by
    have ha : (tripleCharges (sourceA317 + difference 0 2) (sourceB317 + difference 2 0) sourceC317) = raw6729 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6729; decide +kernel
    rw [ha]
    exact (canonical6729 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA317 + difference 0 3) (sourceB317 + difference 3 0) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA317 + difference 0 3) (sourceB317 + difference 3 0) sourceC317) = raw6730 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6730; decide +kernel
    rw [ha]
    exact (canonical6730 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA317 + difference 0 4) (sourceB317 + difference 4 0) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA317 + difference 0 4) (sourceB317 + difference 4 0) sourceC317) = raw6731 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6731; decide +kernel
    rw [ha]
    exact (canonical6731 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA317 + difference 0 5) (sourceB317 + difference 5 0) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3094) := by
    have ha : (tripleCharges (sourceA317 + difference 0 5) (sourceB317 + difference 5 0) sourceC317) = raw6732 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6732; decide +kernel
    rw [ha]
    exact (canonical6732 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA317 + difference 1 0) (sourceB317 + difference 0 1) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA317 + difference 1 0) (sourceB317 + difference 0 1) sourceC317) = raw6733 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6733; decide +kernel
    rw [ha]
    exact (canonical6733 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA317 + difference 1 2) (sourceB317 + difference 2 1) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA317 + difference 1 2) (sourceB317 + difference 2 1) sourceC317) = raw6734 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6734; decide +kernel
    rw [ha]
    exact (canonical6734 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA317 + difference 1 3) (sourceB317 + difference 3 1) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA317 + difference 1 3) (sourceB317 + difference 3 1) sourceC317) = raw6735 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6735; decide +kernel
    rw [ha]
    exact (canonical6735 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA317 + difference 1 4) (sourceB317 + difference 4 1) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA317 + difference 1 4) (sourceB317 + difference 4 1) sourceC317) = raw6736 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6736; decide +kernel
    rw [ha]
    exact (canonical6736 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA317 + difference 1 5) (sourceB317 + difference 5 1) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA317 + difference 1 5) (sourceB317 + difference 5 1) sourceC317) = raw6737 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6737; decide +kernel
    rw [ha]
    exact (canonical6737 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA317 + difference 2 0) (sourceB317 + difference 0 2) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA317 + difference 2 0) (sourceB317 + difference 0 2) sourceC317) = raw6738 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6738; decide +kernel
    rw [ha]
    exact (canonical6738 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA317 + difference 2 1) (sourceB317 + difference 1 2) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2665) := by
    have ha : (tripleCharges (sourceA317 + difference 2 1) (sourceB317 + difference 1 2) sourceC317) = raw6739 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6739; decide +kernel
    rw [ha]
    exact (canonical6739 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA317 + difference 2 3) (sourceB317 + difference 3 2) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA317 + difference 2 3) (sourceB317 + difference 3 2) sourceC317) = raw6740 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6740; decide +kernel
    rw [ha]
    exact (canonical6740 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA317 + difference 2 4) (sourceB317 + difference 4 2) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2713) := by
    have ha : (tripleCharges (sourceA317 + difference 2 4) (sourceB317 + difference 4 2) sourceC317) = raw6741 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6741; decide +kernel
    rw [ha]
    exact (canonical6741 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA317 + difference 2 5) (sourceB317 + difference 5 2) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA317 + difference 2 5) (sourceB317 + difference 5 2) sourceC317) = raw6742 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6742; decide +kernel
    rw [ha]
    exact (canonical6742 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA317 + difference 3 0) (sourceB317 + difference 0 3) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2220) := by
    have ha : (tripleCharges (sourceA317 + difference 3 0) (sourceB317 + difference 0 3) sourceC317) = raw6743 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6743; decide +kernel
    rw [ha]
    exact (canonical6743 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA317 + difference 3 1) (sourceB317 + difference 1 3) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2128) := by
    have ha : (tripleCharges (sourceA317 + difference 3 1) (sourceB317 + difference 1 3) sourceC317) = raw6744 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6744; decide +kernel
    rw [ha]
    exact (canonical6744 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA317 + difference 3 2) (sourceB317 + difference 2 3) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2127) := by
    have ha : (tripleCharges (sourceA317 + difference 3 2) (sourceB317 + difference 2 3) sourceC317) = raw6745 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6745; decide +kernel
    rw [ha]
    exact (canonical6745 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA317 + difference 3 4) (sourceB317 + difference 4 3) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2129) := by
    have ha : (tripleCharges (sourceA317 + difference 3 4) (sourceB317 + difference 4 3) sourceC317) = raw6746 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6746; decide +kernel
    rw [ha]
    exact (canonical6746 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA317 + difference 3 5) (sourceB317 + difference 5 3) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2133) := by
    have ha : (tripleCharges (sourceA317 + difference 3 5) (sourceB317 + difference 5 3) sourceC317) = raw6747 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6747; decide +kernel
    rw [ha]
    exact (canonical6747 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA317 + difference 4 0) (sourceB317 + difference 0 4) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA317 + difference 4 0) (sourceB317 + difference 0 4) sourceC317) = raw6748 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6748; decide +kernel
    rw [ha]
    exact (canonical6748 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA317 + difference 4 1) (sourceB317 + difference 1 4) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA317 + difference 4 1) (sourceB317 + difference 1 4) sourceC317) = raw6749 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6749; decide +kernel
    rw [ha]
    exact (canonical6749 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA317 + difference 4 2) (sourceB317 + difference 2 4) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2698) := by
    have ha : (tripleCharges (sourceA317 + difference 4 2) (sourceB317 + difference 2 4) sourceC317) = raw6750 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6750; decide +kernel
    rw [ha]
    exact (canonical6750 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA317 + difference 4 3) (sourceB317 + difference 3 4) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA317 + difference 4 3) (sourceB317 + difference 3 4) sourceC317) = raw6412 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6412; decide +kernel
    rw [ha]
    exact (canonical6412 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA317 + difference 4 5) (sourceB317 + difference 5 4) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA317 + difference 4 5) (sourceB317 + difference 5 4) sourceC317) = raw6406 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6406; decide +kernel
    rw [ha]
    exact (canonical6406 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA317 + difference 5 0) (sourceB317 + difference 0 5) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2215) := by
    have ha : (tripleCharges (sourceA317 + difference 5 0) (sourceB317 + difference 0 5) sourceC317) = raw6751 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6751; decide +kernel
    rw [ha]
    exact (canonical6751 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA317 + difference 5 1) (sourceB317 + difference 1 5) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2677) := by
    have ha : (tripleCharges (sourceA317 + difference 5 1) (sourceB317 + difference 1 5) sourceC317) = raw6752 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6752; decide +kernel
    rw [ha]
    exact (canonical6752 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA317 + difference 5 2) (sourceB317 + difference 2 5) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA317 + difference 5 2) (sourceB317 + difference 2 5) sourceC317) = raw6753 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6753; decide +kernel
    rw [ha]
    exact (canonical6753 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA317 + difference 5 3) (sourceB317 + difference 3 5) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA317 + difference 5 3) (sourceB317 + difference 3 5) sourceC317) = raw6754 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6754; decide +kernel
    rw [ha]
    exact (canonical6754 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA317 + difference 5 4) (sourceB317 + difference 4 5) sourceC317) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2729) := by
    have ha : (tripleCharges (sourceA317 + difference 5 4) (sourceB317 + difference 4 5) sourceC317) = raw6755 := by
      apply Matrix.ext; unfold tripleCharges sourceA317 sourceB317 sourceC317 difference raw6755; decide +kernel
    rw [ha]
    exact (canonical6755 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA317 sourceB317 sourceC317
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm317, Integer.Sparse.eval]
  linarith only [hs]

def sourceA318 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB318 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC318 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm318 : Integer.Sparse Master := [(Sum.inr 2091, 1), (Sum.inr 2092, 1), (Sum.inr 2093, 1), (Sum.inr 2111, 1), (Sum.inr 2254, 1), (Sum.inr 2662, 1), (Sum.inr 2672, 1), (Sum.inr 2673, 1), (Sum.inr 2678, 1), (Sum.inr 2723, 1), (Sum.inr 3016, 1), (Sum.inr 3017, 1), (Sum.inr 3019, 1), (Sum.inr 3029, 1), (Sum.inr 3030, 1), (Sum.inr 3038, 1), (Sum.inr 3039, 1), (Sum.inr 3040, 1), (Sum.inr 3044, 1), (Sum.inr 3045, 1), (Sum.inr 3054, 1), (Sum.inr 3055, 1), (Sum.inr 3065, 1), (Sum.inr 3088, 1), (Sum.inr 3089, 1), (Sum.inr 3102, 1), (Sum.inr 3202, 1), (Sum.inr 3206, 1), (Sum.inr 3210, 1), (Sum.inr 3225, 1)]

theorem sourceEq318 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm318 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA318 + difference 0 1) (sourceB318 + difference 1 0) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2678) := by
    have ha : (tripleCharges (sourceA318 + difference 0 1) (sourceB318 + difference 1 0) sourceC318) = raw6756 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6756; decide +kernel
    rw [ha]
    exact (canonical6756 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA318 + difference 0 2) (sourceB318 + difference 2 0) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2662) := by
    have ha : (tripleCharges (sourceA318 + difference 0 2) (sourceB318 + difference 2 0) sourceC318) = raw6757 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6757; decide +kernel
    rw [ha]
    exact (canonical6757 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA318 + difference 0 3) (sourceB318 + difference 3 0) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA318 + difference 0 3) (sourceB318 + difference 3 0) sourceC318) = raw6758 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6758; decide +kernel
    rw [ha]
    exact (canonical6758 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA318 + difference 0 4) (sourceB318 + difference 4 0) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA318 + difference 0 4) (sourceB318 + difference 4 0) sourceC318) = raw6759 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6759; decide +kernel
    rw [ha]
    exact (canonical6759 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA318 + difference 0 5) (sourceB318 + difference 5 0) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA318 + difference 0 5) (sourceB318 + difference 5 0) sourceC318) = raw6760 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6760; decide +kernel
    rw [ha]
    exact (canonical6760 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA318 + difference 1 0) (sourceB318 + difference 0 1) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3225) := by
    have ha : (tripleCharges (sourceA318 + difference 1 0) (sourceB318 + difference 0 1) sourceC318) = raw6761 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6761; decide +kernel
    rw [ha]
    exact (canonical6761 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA318 + difference 1 2) (sourceB318 + difference 2 1) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA318 + difference 1 2) (sourceB318 + difference 2 1) sourceC318) = raw6762 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6762; decide +kernel
    rw [ha]
    exact (canonical6762 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA318 + difference 1 3) (sourceB318 + difference 3 1) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA318 + difference 1 3) (sourceB318 + difference 3 1) sourceC318) = raw6763 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6763; decide +kernel
    rw [ha]
    exact (canonical6763 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA318 + difference 1 4) (sourceB318 + difference 4 1) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA318 + difference 1 4) (sourceB318 + difference 4 1) sourceC318) = raw6764 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6764; decide +kernel
    rw [ha]
    exact (canonical6764 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA318 + difference 1 5) (sourceB318 + difference 5 1) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA318 + difference 1 5) (sourceB318 + difference 5 1) sourceC318) = raw6765 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6765; decide +kernel
    rw [ha]
    exact (canonical6765 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA318 + difference 2 0) (sourceB318 + difference 0 2) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA318 + difference 2 0) (sourceB318 + difference 0 2) sourceC318) = raw6766 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6766; decide +kernel
    rw [ha]
    exact (canonical6766 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA318 + difference 2 1) (sourceB318 + difference 1 2) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3019) := by
    have ha : (tripleCharges (sourceA318 + difference 2 1) (sourceB318 + difference 1 2) sourceC318) = raw6767 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6767; decide +kernel
    rw [ha]
    exact (canonical6767 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA318 + difference 2 3) (sourceB318 + difference 3 2) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3065) := by
    have ha : (tripleCharges (sourceA318 + difference 2 3) (sourceB318 + difference 3 2) sourceC318) = raw6768 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6768; decide +kernel
    rw [ha]
    exact (canonical6768 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA318 + difference 2 4) (sourceB318 + difference 4 2) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3017) := by
    have ha : (tripleCharges (sourceA318 + difference 2 4) (sourceB318 + difference 4 2) sourceC318) = raw6769 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6769; decide +kernel
    rw [ha]
    exact (canonical6769 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA318 + difference 2 5) (sourceB318 + difference 5 2) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA318 + difference 2 5) (sourceB318 + difference 5 2) sourceC318) = raw6770 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6770; decide +kernel
    rw [ha]
    exact (canonical6770 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA318 + difference 3 0) (sourceB318 + difference 0 3) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2092) := by
    have ha : (tripleCharges (sourceA318 + difference 3 0) (sourceB318 + difference 0 3) sourceC318) = raw6771 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6771; decide +kernel
    rw [ha]
    exact (canonical6771 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA318 + difference 3 1) (sourceB318 + difference 1 3) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2093) := by
    have ha : (tripleCharges (sourceA318 + difference 3 1) (sourceB318 + difference 1 3) sourceC318) = raw6772 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6772; decide +kernel
    rw [ha]
    exact (canonical6772 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA318 + difference 3 2) (sourceB318 + difference 2 3) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2091) := by
    have ha : (tripleCharges (sourceA318 + difference 3 2) (sourceB318 + difference 2 3) sourceC318) = raw6773 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6773; decide +kernel
    rw [ha]
    exact (canonical6773 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA318 + difference 3 4) (sourceB318 + difference 4 3) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2111) := by
    have ha : (tripleCharges (sourceA318 + difference 3 4) (sourceB318 + difference 4 3) sourceC318) = raw6774 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6774; decide +kernel
    rw [ha]
    exact (canonical6774 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA318 + difference 3 5) (sourceB318 + difference 5 3) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA318 + difference 3 5) (sourceB318 + difference 5 3) sourceC318) = raw6775 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6775; decide +kernel
    rw [ha]
    exact (canonical6775 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA318 + difference 4 0) (sourceB318 + difference 0 4) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3210) := by
    have ha : (tripleCharges (sourceA318 + difference 4 0) (sourceB318 + difference 0 4) sourceC318) = raw6776 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6776; decide +kernel
    rw [ha]
    exact (canonical6776 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA318 + difference 4 1) (sourceB318 + difference 1 4) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3044) := by
    have ha : (tripleCharges (sourceA318 + difference 4 1) (sourceB318 + difference 1 4) sourceC318) = raw6777 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6777; decide +kernel
    rw [ha]
    exact (canonical6777 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA318 + difference 4 2) (sourceB318 + difference 2 4) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3029) := by
    have ha : (tripleCharges (sourceA318 + difference 4 2) (sourceB318 + difference 2 4) sourceC318) = raw6778 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6778; decide +kernel
    rw [ha]
    exact (canonical6778 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA318 + difference 4 3) (sourceB318 + difference 3 4) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3088) := by
    have ha : (tripleCharges (sourceA318 + difference 4 3) (sourceB318 + difference 3 4) sourceC318) = raw6434 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6434; decide +kernel
    rw [ha]
    exact (canonical6434 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA318 + difference 4 5) (sourceB318 + difference 5 4) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA318 + difference 4 5) (sourceB318 + difference 5 4) sourceC318) = raw6428 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6428; decide +kernel
    rw [ha]
    exact (canonical6428 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA318 + difference 5 0) (sourceB318 + difference 0 5) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3206) := by
    have ha : (tripleCharges (sourceA318 + difference 5 0) (sourceB318 + difference 0 5) sourceC318) = raw6779 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6779; decide +kernel
    rw [ha]
    exact (canonical6779 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA318 + difference 5 1) (sourceB318 + difference 1 5) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3045) := by
    have ha : (tripleCharges (sourceA318 + difference 5 1) (sourceB318 + difference 1 5) sourceC318) = raw6780 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6780; decide +kernel
    rw [ha]
    exact (canonical6780 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA318 + difference 5 2) (sourceB318 + difference 2 5) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3030) := by
    have ha : (tripleCharges (sourceA318 + difference 5 2) (sourceB318 + difference 2 5) sourceC318) = raw6781 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6781; decide +kernel
    rw [ha]
    exact (canonical6781 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA318 + difference 5 3) (sourceB318 + difference 3 5) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3089) := by
    have ha : (tripleCharges (sourceA318 + difference 5 3) (sourceB318 + difference 3 5) sourceC318) = raw6782 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6782; decide +kernel
    rw [ha]
    exact (canonical6782 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA318 + difference 5 4) (sourceB318 + difference 4 5) sourceC318) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3040) := by
    have ha : (tripleCharges (sourceA318 + difference 5 4) (sourceB318 + difference 4 5) sourceC318) = raw6783 := by
      apply Matrix.ext; unfold tripleCharges sourceA318 sourceB318 sourceC318 difference raw6783; decide +kernel
    rw [ha]
    exact (canonical6783 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA318 sourceB318 sourceC318
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm318, Integer.Sparse.eval]
  linarith only [hs]

def sourceA319 : Charge := ![1, -1, 0, 2, -1, -1]
def sourceB319 : Charge := ![2, 1, 0, -2, 0, -1]
def sourceC319 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm319 : Integer.Sparse Master := [(Sum.inr 3388, 1), (Sum.inr 3391, 1), (Sum.inr 3392, 1), (Sum.inr 3395, 1), (Sum.inr 3535, 1), (Sum.inr 3544, 1), (Sum.inr 4084, -1)]

theorem sourceEq319 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm319 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA319 + difference 0 0) (sourceB319 + difference 0 0) sourceC319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA319 + difference 0 0) (sourceB319 + difference 0 0) sourceC319) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA319 sourceB319 sourceC319 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA319 + difference 0 1) (sourceB319 + difference 1 0) sourceC319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3395) := by
    have ha : (tripleCharges (sourceA319 + difference 0 1) (sourceB319 + difference 1 0) sourceC319) = raw6785 := by
      apply Matrix.ext; unfold tripleCharges sourceA319 sourceB319 sourceC319 difference raw6785; decide +kernel
    rw [ha]
    exact (canonical6785 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA319 + difference 0 2) (sourceB319 + difference 2 0) sourceC319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3388) := by
    have ha : (tripleCharges (sourceA319 + difference 0 2) (sourceB319 + difference 2 0) sourceC319) = raw6786 := by
      apply Matrix.ext; unfold tripleCharges sourceA319 sourceB319 sourceC319 difference raw6786; decide +kernel
    rw [ha]
    exact (canonical6786 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA319 + difference 0 3) (sourceB319 + difference 3 0) sourceC319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA319 + difference 0 3) (sourceB319 + difference 3 0) sourceC319) = raw6787 := by
      apply Matrix.ext; unfold tripleCharges sourceA319 sourceB319 sourceC319 difference raw6787; decide +kernel
    rw [ha]
    exact (canonical6787 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA319 + difference 0 4) (sourceB319 + difference 4 0) sourceC319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3392) := by
    have ha : (tripleCharges (sourceA319 + difference 0 4) (sourceB319 + difference 4 0) sourceC319) = raw6788 := by
      apply Matrix.ext; unfold tripleCharges sourceA319 sourceB319 sourceC319 difference raw6788; decide +kernel
    rw [ha]
    exact (canonical6788 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA319 + difference 0 5) (sourceB319 + difference 5 0) sourceC319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3391) := by
    have ha : (tripleCharges (sourceA319 + difference 0 5) (sourceB319 + difference 5 0) sourceC319) = raw6789 := by
      apply Matrix.ext; unfold tripleCharges sourceA319 sourceB319 sourceC319 difference raw6789; decide +kernel
    rw [ha]
    exact (canonical6789 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA319 + sourceB319) sourceC319) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA319 + sourceB319) sourceC319) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA319 sourceB319 sourceC319 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA319 sourceB319 sourceC319
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm319, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
