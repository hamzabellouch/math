import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical45

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA192 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB192 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC192 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceForm192 : Integer.Sparse Master := [(Sum.inr 2497, 1), (Sum.inr 2716, 1), (Sum.inr 3196, 1), (Sum.inr 3198, 1), (Sum.inr 3222, 1), (Sum.inr 3814, 1), (Sum.inr 4092, -1)]

theorem sourceEq192 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm192 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA192 + difference 0 2) (sourceB192 + difference 2 0) sourceC192) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA192 + difference 0 2) (sourceB192 + difference 2 0) sourceC192) = raw5401 := by
      apply Matrix.ext; unfold tripleCharges sourceA192 sourceB192 sourceC192 difference raw5401; decide +kernel
    rw [ha]
    exact (canonical5401 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA192 + difference 1 2) (sourceB192 + difference 2 1) sourceC192) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3196) := by
    have ha : (tripleCharges (sourceA192 + difference 1 2) (sourceB192 + difference 2 1) sourceC192) = raw5411 := by
      apply Matrix.ext; unfold tripleCharges sourceA192 sourceB192 sourceC192 difference raw5411; decide +kernel
    rw [ha]
    exact (canonical5411 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA192 + difference 2 2) (sourceB192 + difference 2 2) sourceC192) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA192 + difference 2 2) (sourceB192 + difference 2 2) sourceC192) = raw5399 := by
      apply Matrix.ext; unfold tripleCharges sourceA192 sourceB192 sourceC192 difference raw5399; decide +kernel
    rw [ha]
    exact (canonical5399 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA192 + difference 3 2) (sourceB192 + difference 2 3) sourceC192) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA192 + difference 3 2) (sourceB192 + difference 2 3) sourceC192) = raw5422 := by
      apply Matrix.ext; unfold tripleCharges sourceA192 sourceB192 sourceC192 difference raw5422; decide +kernel
    rw [ha]
    exact (canonical5422 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA192 + difference 4 2) (sourceB192 + difference 2 4) sourceC192) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3198) := by
    have ha : (tripleCharges (sourceA192 + difference 4 2) (sourceB192 + difference 2 4) sourceC192) = raw5423 := by
      apply Matrix.ext; unfold tripleCharges sourceA192 sourceB192 sourceC192 difference raw5423; decide +kernel
    rw [ha]
    exact (canonical5423 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA192 + difference 5 2) (sourceB192 + difference 2 5) sourceC192) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA192 + difference 5 2) (sourceB192 + difference 2 5) sourceC192) = raw5424 := by
      apply Matrix.ext; unfold tripleCharges sourceA192 sourceB192 sourceC192 difference raw5424; decide +kernel
    rw [ha]
    exact (canonical5424 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA192 + sourceB192) sourceC192) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA192 + sourceB192) sourceC192) = raw5405 := by
      apply Matrix.ext; unfold doubleCharges sourceA192 sourceB192 sourceC192 raw5405; decide +kernel
    rw [ha]
    exact (canonical5405 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA192 sourceB192 sourceC192
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm192, Integer.Sparse.eval]
  linarith only [hs]

def sourceA193 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB193 : Charge := ![3, 0, -1, -2, 0, 0]
def sourceC193 : Charge := ![0, 0, 1, 2, -1, -2]
def sourceForm193 : Integer.Sparse Master := [(Sum.inr 1465, 1), (Sum.inr 2474, 1), (Sum.inr 2486, 1), (Sum.inr 2497, 1), (Sum.inr 2716, 1), (Sum.inr 3222, 1), (Sum.inr 4092, -1)]

theorem sourceEq193 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm193 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA193 + difference 3 0) (sourceB193 + difference 0 3) sourceC193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1465) := by
    have ha : (tripleCharges (sourceA193 + difference 3 0) (sourceB193 + difference 0 3) sourceC193) = raw5408 := by
      apply Matrix.ext; unfold tripleCharges sourceA193 sourceB193 sourceC193 difference raw5408; decide +kernel
    rw [ha]
    exact (canonical5408 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA193 + difference 3 1) (sourceB193 + difference 1 3) sourceC193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2474) := by
    have ha : (tripleCharges (sourceA193 + difference 3 1) (sourceB193 + difference 1 3) sourceC193) = raw5416 := by
      apply Matrix.ext; unfold tripleCharges sourceA193 sourceB193 sourceC193 difference raw5416; decide +kernel
    rw [ha]
    exact (canonical5416 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA193 + difference 3 2) (sourceB193 + difference 2 3) sourceC193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA193 + difference 3 2) (sourceB193 + difference 2 3) sourceC193) = raw5422 := by
      apply Matrix.ext; unfold tripleCharges sourceA193 sourceB193 sourceC193 difference raw5422; decide +kernel
    rw [ha]
    exact (canonical5422 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA193 + difference 3 3) (sourceB193 + difference 3 3) sourceC193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA193 + difference 3 3) (sourceB193 + difference 3 3) sourceC193) = raw5399 := by
      apply Matrix.ext; unfold tripleCharges sourceA193 sourceB193 sourceC193 difference raw5399; decide +kernel
    rw [ha]
    exact (canonical5399 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA193 + difference 3 4) (sourceB193 + difference 4 3) sourceC193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA193 + difference 3 4) (sourceB193 + difference 4 3) sourceC193) = raw5425 := by
      apply Matrix.ext; unfold tripleCharges sourceA193 sourceB193 sourceC193 difference raw5425; decide +kernel
    rw [ha]
    exact (canonical5425 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA193 + difference 3 5) (sourceB193 + difference 5 3) sourceC193) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA193 + difference 3 5) (sourceB193 + difference 5 3) sourceC193) = raw5426 := by
      apply Matrix.ext; unfold tripleCharges sourceA193 sourceB193 sourceC193 difference raw5426; decide +kernel
    rw [ha]
    exact (canonical5426 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA193 + sourceB193) sourceC193) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA193 + sourceB193) sourceC193) = raw5405 := by
      apply Matrix.ext; unfold doubleCharges sourceA193 sourceB193 sourceC193 raw5405; decide +kernel
    rw [ha]
    exact (canonical5405 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA193 sourceB193 sourceC193
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm193, Integer.Sparse.eval]
  linarith only [hs]

def sourceA194 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB194 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC194 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceForm194 : Integer.Sparse Master := [(Sum.inr 4433, 1), (Sum.inr 4434, 1), (Sum.inr 4439, 3), (Sum.inr 4730, 3), (Sum.inr 4847, 3), (Sum.inr 4852, 6), (Sum.inr 4885, 1), (Sum.inr 4886, 1), (Sum.inr 4887, 3), (Sum.inr 4889, 3), (Sum.inr 5283, 1), (Sum.inr 5286, 3), (Sum.inr 5301, 1)]

theorem sourceEq194 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm194 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA194 + difference 0 1) (sourceB194 + difference 1 0) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA194 + difference 0 1) (sourceB194 + difference 1 0) sourceC194) = raw5427 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5427; decide +kernel
    rw [ha]
    exact (canonical5427 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA194 + difference 0 2) (sourceB194 + difference 2 0) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA194 + difference 0 2) (sourceB194 + difference 2 0) sourceC194) = raw5428 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5428; decide +kernel
    rw [ha]
    exact (canonical5428 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA194 + difference 0 3) (sourceB194 + difference 3 0) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA194 + difference 0 3) (sourceB194 + difference 3 0) sourceC194) = raw5429 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5429; decide +kernel
    rw [ha]
    exact (canonical5429 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA194 + difference 0 4) (sourceB194 + difference 4 0) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA194 + difference 0 4) (sourceB194 + difference 4 0) sourceC194) = raw5430 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5430; decide +kernel
    rw [ha]
    exact (canonical5430 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA194 + difference 0 5) (sourceB194 + difference 5 0) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5283) := by
    have ha : (tripleCharges (sourceA194 + difference 0 5) (sourceB194 + difference 5 0) sourceC194) = raw5431 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5431; decide +kernel
    rw [ha]
    exact (canonical5431 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA194 + difference 1 0) (sourceB194 + difference 0 1) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA194 + difference 1 0) (sourceB194 + difference 0 1) sourceC194) = raw5432 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5432; decide +kernel
    rw [ha]
    exact (canonical5432 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA194 + difference 1 2) (sourceB194 + difference 2 1) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA194 + difference 1 2) (sourceB194 + difference 2 1) sourceC194) = raw5433 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5433; decide +kernel
    rw [ha]
    exact (canonical5433 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA194 + difference 1 3) (sourceB194 + difference 3 1) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA194 + difference 1 3) (sourceB194 + difference 3 1) sourceC194) = raw5434 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5434; decide +kernel
    rw [ha]
    exact (canonical5434 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA194 + difference 1 4) (sourceB194 + difference 4 1) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA194 + difference 1 4) (sourceB194 + difference 4 1) sourceC194) = raw5435 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5435; decide +kernel
    rw [ha]
    exact (canonical5435 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA194 + difference 1 5) (sourceB194 + difference 5 1) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA194 + difference 1 5) (sourceB194 + difference 5 1) sourceC194) = raw5436 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5436; decide +kernel
    rw [ha]
    exact (canonical5436 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA194 + difference 2 0) (sourceB194 + difference 0 2) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA194 + difference 2 0) (sourceB194 + difference 0 2) sourceC194) = raw5437 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5437; decide +kernel
    rw [ha]
    exact (canonical5437 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA194 + difference 2 1) (sourceB194 + difference 1 2) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA194 + difference 2 1) (sourceB194 + difference 1 2) sourceC194) = raw5438 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5438; decide +kernel
    rw [ha]
    exact (canonical5438 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA194 + difference 2 3) (sourceB194 + difference 3 2) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA194 + difference 2 3) (sourceB194 + difference 3 2) sourceC194) = raw5439 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5439; decide +kernel
    rw [ha]
    exact (canonical5439 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA194 + difference 2 4) (sourceB194 + difference 4 2) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA194 + difference 2 4) (sourceB194 + difference 4 2) sourceC194) = raw5440 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5440; decide +kernel
    rw [ha]
    exact (canonical5440 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA194 + difference 2 5) (sourceB194 + difference 5 2) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA194 + difference 2 5) (sourceB194 + difference 5 2) sourceC194) = raw5441 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5441; decide +kernel
    rw [ha]
    exact (canonical5441 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA194 + difference 3 0) (sourceB194 + difference 0 3) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4439) := by
    have ha : (tripleCharges (sourceA194 + difference 3 0) (sourceB194 + difference 0 3) sourceC194) = raw5442 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5442; decide +kernel
    rw [ha]
    exact (canonical5442 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA194 + difference 3 1) (sourceB194 + difference 1 3) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA194 + difference 3 1) (sourceB194 + difference 1 3) sourceC194) = raw5443 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5443; decide +kernel
    rw [ha]
    exact (canonical5443 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA194 + difference 3 2) (sourceB194 + difference 2 3) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4852) := by
    have ha : (tripleCharges (sourceA194 + difference 3 2) (sourceB194 + difference 2 3) sourceC194) = raw5444 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5444; decide +kernel
    rw [ha]
    exact (canonical5444 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA194 + difference 3 4) (sourceB194 + difference 4 3) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA194 + difference 3 4) (sourceB194 + difference 4 3) sourceC194) = raw5445 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5445; decide +kernel
    rw [ha]
    exact (canonical5445 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA194 + difference 3 5) (sourceB194 + difference 5 3) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA194 + difference 3 5) (sourceB194 + difference 5 3) sourceC194) = raw5446 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5446; decide +kernel
    rw [ha]
    exact (canonical5446 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA194 + difference 4 0) (sourceB194 + difference 0 4) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4434) := by
    have ha : (tripleCharges (sourceA194 + difference 4 0) (sourceB194 + difference 0 4) sourceC194) = raw5447 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5447; decide +kernel
    rw [ha]
    exact (canonical5447 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA194 + difference 4 1) (sourceB194 + difference 1 4) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4847) := by
    have ha : (tripleCharges (sourceA194 + difference 4 1) (sourceB194 + difference 1 4) sourceC194) = raw5448 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5448; decide +kernel
    rw [ha]
    exact (canonical5448 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA194 + difference 4 2) (sourceB194 + difference 2 4) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4847) := by
    have ha : (tripleCharges (sourceA194 + difference 4 2) (sourceB194 + difference 2 4) sourceC194) = raw5449 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5449; decide +kernel
    rw [ha]
    exact (canonical5449 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA194 + difference 4 3) (sourceB194 + difference 3 4) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4847) := by
    have ha : (tripleCharges (sourceA194 + difference 4 3) (sourceB194 + difference 3 4) sourceC194) = raw5450 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5450; decide +kernel
    rw [ha]
    exact (canonical5450 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA194 + difference 4 5) (sourceB194 + difference 5 4) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4885) := by
    have ha : (tripleCharges (sourceA194 + difference 4 5) (sourceB194 + difference 5 4) sourceC194) = raw5451 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5451; decide +kernel
    rw [ha]
    exact (canonical5451 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA194 + difference 5 0) (sourceB194 + difference 0 5) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4433) := by
    have ha : (tripleCharges (sourceA194 + difference 5 0) (sourceB194 + difference 0 5) sourceC194) = raw5452 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5452; decide +kernel
    rw [ha]
    exact (canonical5452 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA194 + difference 5 1) (sourceB194 + difference 1 5) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4730) := by
    have ha : (tripleCharges (sourceA194 + difference 5 1) (sourceB194 + difference 1 5) sourceC194) = raw5453 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5453; decide +kernel
    rw [ha]
    exact (canonical5453 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA194 + difference 5 2) (sourceB194 + difference 2 5) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4730) := by
    have ha : (tripleCharges (sourceA194 + difference 5 2) (sourceB194 + difference 2 5) sourceC194) = raw5454 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5454; decide +kernel
    rw [ha]
    exact (canonical5454 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA194 + difference 5 3) (sourceB194 + difference 3 5) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4730) := by
    have ha : (tripleCharges (sourceA194 + difference 5 3) (sourceB194 + difference 3 5) sourceC194) = raw5455 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5455; decide +kernel
    rw [ha]
    exact (canonical5455 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA194 + difference 5 4) (sourceB194 + difference 4 5) sourceC194) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4886) := by
    have ha : (tripleCharges (sourceA194 + difference 5 4) (sourceB194 + difference 4 5) sourceC194) = raw5456 := by
      apply Matrix.ext; unfold tripleCharges sourceA194 sourceB194 sourceC194 difference raw5456; decide +kernel
    rw [ha]
    exact (canonical5456 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA194 sourceB194 sourceC194
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm194, Integer.Sparse.eval]
  linarith only [hs]

def sourceA195 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB195 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC195 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceForm195 : Integer.Sparse Master := [(Sum.inr 1376, 1), (Sum.inr 1377, 1), (Sum.inr 1383, 3), (Sum.inr 1899, 3), (Sum.inr 2235, 1), (Sum.inr 3023, 3), (Sum.inr 3053, 1), (Sum.inr 3076, 1), (Sum.inr 3167, 3), (Sum.inr 3170, 6), (Sum.inr 3221, 1), (Sum.inr 3223, 3), (Sum.inr 3226, 3)]

theorem sourceEq195 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm195 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA195 + difference 0 1) (sourceB195 + difference 1 0) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA195 + difference 0 1) (sourceB195 + difference 1 0) sourceC195) = raw5457 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5457; decide +kernel
    rw [ha]
    exact (canonical5457 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA195 + difference 0 2) (sourceB195 + difference 2 0) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA195 + difference 0 2) (sourceB195 + difference 2 0) sourceC195) = raw5458 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5458; decide +kernel
    rw [ha]
    exact (canonical5458 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA195 + difference 0 3) (sourceB195 + difference 3 0) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA195 + difference 0 3) (sourceB195 + difference 3 0) sourceC195) = raw5459 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5459; decide +kernel
    rw [ha]
    exact (canonical5459 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA195 + difference 0 4) (sourceB195 + difference 4 0) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3053) := by
    have ha : (tripleCharges (sourceA195 + difference 0 4) (sourceB195 + difference 4 0) sourceC195) = raw5460 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5460; decide +kernel
    rw [ha]
    exact (canonical5460 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA195 + difference 0 5) (sourceB195 + difference 5 0) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3076) := by
    have ha : (tripleCharges (sourceA195 + difference 0 5) (sourceB195 + difference 5 0) sourceC195) = raw5461 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5461; decide +kernel
    rw [ha]
    exact (canonical5461 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA195 + difference 1 0) (sourceB195 + difference 0 1) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1383) := by
    have ha : (tripleCharges (sourceA195 + difference 1 0) (sourceB195 + difference 0 1) sourceC195) = raw5462 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5462; decide +kernel
    rw [ha]
    exact (canonical5462 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA195 + difference 1 2) (sourceB195 + difference 2 1) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA195 + difference 1 2) (sourceB195 + difference 2 1) sourceC195) = raw5463 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5463; decide +kernel
    rw [ha]
    exact (canonical5463 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA195 + difference 1 3) (sourceB195 + difference 3 1) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA195 + difference 1 3) (sourceB195 + difference 3 1) sourceC195) = raw5464 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5464; decide +kernel
    rw [ha]
    exact (canonical5464 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA195 + difference 1 4) (sourceB195 + difference 4 1) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA195 + difference 1 4) (sourceB195 + difference 4 1) sourceC195) = raw5465 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5465; decide +kernel
    rw [ha]
    exact (canonical5465 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA195 + difference 1 5) (sourceB195 + difference 5 1) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3226) := by
    have ha : (tripleCharges (sourceA195 + difference 1 5) (sourceB195 + difference 5 1) sourceC195) = raw5466 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5466; decide +kernel
    rw [ha]
    exact (canonical5466 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA195 + difference 2 0) (sourceB195 + difference 0 2) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1383) := by
    have ha : (tripleCharges (sourceA195 + difference 2 0) (sourceB195 + difference 0 2) sourceC195) = raw5467 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5467; decide +kernel
    rw [ha]
    exact (canonical5467 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA195 + difference 2 1) (sourceB195 + difference 1 2) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA195 + difference 2 1) (sourceB195 + difference 1 2) sourceC195) = raw5468 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5468; decide +kernel
    rw [ha]
    exact (canonical5468 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA195 + difference 2 3) (sourceB195 + difference 3 2) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA195 + difference 2 3) (sourceB195 + difference 3 2) sourceC195) = raw5469 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5469; decide +kernel
    rw [ha]
    exact (canonical5469 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA195 + difference 2 4) (sourceB195 + difference 4 2) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA195 + difference 2 4) (sourceB195 + difference 4 2) sourceC195) = raw5470 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5470; decide +kernel
    rw [ha]
    exact (canonical5470 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA195 + difference 2 5) (sourceB195 + difference 5 2) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3226) := by
    have ha : (tripleCharges (sourceA195 + difference 2 5) (sourceB195 + difference 5 2) sourceC195) = raw5471 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5471; decide +kernel
    rw [ha]
    exact (canonical5471 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA195 + difference 3 0) (sourceB195 + difference 0 3) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1383) := by
    have ha : (tripleCharges (sourceA195 + difference 3 0) (sourceB195 + difference 0 3) sourceC195) = raw5472 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5472; decide +kernel
    rw [ha]
    exact (canonical5472 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA195 + difference 3 1) (sourceB195 + difference 1 3) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA195 + difference 3 1) (sourceB195 + difference 1 3) sourceC195) = raw5473 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5473; decide +kernel
    rw [ha]
    exact (canonical5473 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA195 + difference 3 2) (sourceB195 + difference 2 3) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA195 + difference 3 2) (sourceB195 + difference 2 3) sourceC195) = raw5474 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5474; decide +kernel
    rw [ha]
    exact (canonical5474 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA195 + difference 3 4) (sourceB195 + difference 4 3) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA195 + difference 3 4) (sourceB195 + difference 4 3) sourceC195) = raw5475 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5475; decide +kernel
    rw [ha]
    exact (canonical5475 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA195 + difference 3 5) (sourceB195 + difference 5 3) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3226) := by
    have ha : (tripleCharges (sourceA195 + difference 3 5) (sourceB195 + difference 5 3) sourceC195) = raw5476 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5476; decide +kernel
    rw [ha]
    exact (canonical5476 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA195 + difference 4 0) (sourceB195 + difference 0 4) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1377) := by
    have ha : (tripleCharges (sourceA195 + difference 4 0) (sourceB195 + difference 0 4) sourceC195) = raw5477 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5477; decide +kernel
    rw [ha]
    exact (canonical5477 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA195 + difference 4 1) (sourceB195 + difference 1 4) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3167) := by
    have ha : (tripleCharges (sourceA195 + difference 4 1) (sourceB195 + difference 1 4) sourceC195) = raw5478 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5478; decide +kernel
    rw [ha]
    exact (canonical5478 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA195 + difference 4 2) (sourceB195 + difference 2 4) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3167) := by
    have ha : (tripleCharges (sourceA195 + difference 4 2) (sourceB195 + difference 2 4) sourceC195) = raw5479 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5479; decide +kernel
    rw [ha]
    exact (canonical5479 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA195 + difference 4 3) (sourceB195 + difference 3 4) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3167) := by
    have ha : (tripleCharges (sourceA195 + difference 4 3) (sourceB195 + difference 3 4) sourceC195) = raw5480 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5480; decide +kernel
    rw [ha]
    exact (canonical5480 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA195 + difference 4 5) (sourceB195 + difference 5 4) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA195 + difference 4 5) (sourceB195 + difference 5 4) sourceC195) = raw5481 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5481; decide +kernel
    rw [ha]
    exact (canonical5481 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA195 + difference 5 0) (sourceB195 + difference 0 5) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1376) := by
    have ha : (tripleCharges (sourceA195 + difference 5 0) (sourceB195 + difference 0 5) sourceC195) = raw5482 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5482; decide +kernel
    rw [ha]
    exact (canonical5482 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA195 + difference 5 1) (sourceB195 + difference 1 5) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1899) := by
    have ha : (tripleCharges (sourceA195 + difference 5 1) (sourceB195 + difference 1 5) sourceC195) = raw5483 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5483; decide +kernel
    rw [ha]
    exact (canonical5483 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA195 + difference 5 2) (sourceB195 + difference 2 5) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1899) := by
    have ha : (tripleCharges (sourceA195 + difference 5 2) (sourceB195 + difference 2 5) sourceC195) = raw5484 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5484; decide +kernel
    rw [ha]
    exact (canonical5484 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA195 + difference 5 3) (sourceB195 + difference 3 5) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1899) := by
    have ha : (tripleCharges (sourceA195 + difference 5 3) (sourceB195 + difference 3 5) sourceC195) = raw5485 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5485; decide +kernel
    rw [ha]
    exact (canonical5485 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA195 + difference 5 4) (sourceB195 + difference 4 5) sourceC195) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2235) := by
    have ha : (tripleCharges (sourceA195 + difference 5 4) (sourceB195 + difference 4 5) sourceC195) = raw5486 := by
      apply Matrix.ext; unfold tripleCharges sourceA195 sourceB195 sourceC195 difference raw5486; decide +kernel
    rw [ha]
    exact (canonical5486 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA195 sourceB195 sourceC195
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm195, Integer.Sparse.eval]
  linarith only [hs]

def sourceA196 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB196 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC196 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceForm196 : Integer.Sparse Master := [(Sum.inr 1713, 3), (Sum.inr 1717, 1), (Sum.inr 1731, 1), (Sum.inr 1930, 3), (Sum.inr 2243, 3), (Sum.inr 2250, 6), (Sum.inr 2252, 1), (Sum.inr 2269, 3), (Sum.inr 2277, 3), (Sum.inr 2283, 1), (Sum.inr 2752, 1), (Sum.inr 2757, 3), (Sum.inr 2775, 1)]

theorem sourceEq196 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm196 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA196 + difference 0 1) (sourceB196 + difference 1 0) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2757) := by
    have ha : (tripleCharges (sourceA196 + difference 0 1) (sourceB196 + difference 1 0) sourceC196) = raw5487 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5487; decide +kernel
    rw [ha]
    exact (canonical5487 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA196 + difference 0 2) (sourceB196 + difference 2 0) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2757) := by
    have ha : (tripleCharges (sourceA196 + difference 0 2) (sourceB196 + difference 2 0) sourceC196) = raw5488 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5488; decide +kernel
    rw [ha]
    exact (canonical5488 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA196 + difference 0 3) (sourceB196 + difference 3 0) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2757) := by
    have ha : (tripleCharges (sourceA196 + difference 0 3) (sourceB196 + difference 3 0) sourceC196) = raw5489 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5489; decide +kernel
    rw [ha]
    exact (canonical5489 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA196 + difference 0 4) (sourceB196 + difference 4 0) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2775) := by
    have ha : (tripleCharges (sourceA196 + difference 0 4) (sourceB196 + difference 4 0) sourceC196) = raw5490 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5490; decide +kernel
    rw [ha]
    exact (canonical5490 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA196 + difference 0 5) (sourceB196 + difference 5 0) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2752) := by
    have ha : (tripleCharges (sourceA196 + difference 0 5) (sourceB196 + difference 5 0) sourceC196) = raw5491 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5491; decide +kernel
    rw [ha]
    exact (canonical5491 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA196 + difference 1 0) (sourceB196 + difference 0 1) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA196 + difference 1 0) (sourceB196 + difference 0 1) sourceC196) = raw5492 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5492; decide +kernel
    rw [ha]
    exact (canonical5492 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA196 + difference 1 2) (sourceB196 + difference 2 1) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA196 + difference 1 2) (sourceB196 + difference 2 1) sourceC196) = raw5493 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5493; decide +kernel
    rw [ha]
    exact (canonical5493 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA196 + difference 1 3) (sourceB196 + difference 3 1) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA196 + difference 1 3) (sourceB196 + difference 3 1) sourceC196) = raw5494 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5494; decide +kernel
    rw [ha]
    exact (canonical5494 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA196 + difference 1 4) (sourceB196 + difference 4 1) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA196 + difference 1 4) (sourceB196 + difference 4 1) sourceC196) = raw5495 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5495; decide +kernel
    rw [ha]
    exact (canonical5495 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA196 + difference 1 5) (sourceB196 + difference 5 1) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA196 + difference 1 5) (sourceB196 + difference 5 1) sourceC196) = raw5496 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5496; decide +kernel
    rw [ha]
    exact (canonical5496 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA196 + difference 2 0) (sourceB196 + difference 0 2) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA196 + difference 2 0) (sourceB196 + difference 0 2) sourceC196) = raw5497 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5497; decide +kernel
    rw [ha]
    exact (canonical5497 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA196 + difference 2 1) (sourceB196 + difference 1 2) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA196 + difference 2 1) (sourceB196 + difference 1 2) sourceC196) = raw5498 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5498; decide +kernel
    rw [ha]
    exact (canonical5498 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA196 + difference 2 3) (sourceB196 + difference 3 2) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA196 + difference 2 3) (sourceB196 + difference 3 2) sourceC196) = raw5499 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5499; decide +kernel
    rw [ha]
    exact (canonical5499 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA196 + difference 2 4) (sourceB196 + difference 4 2) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA196 + difference 2 4) (sourceB196 + difference 4 2) sourceC196) = raw5500 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5500; decide +kernel
    rw [ha]
    exact (canonical5500 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA196 + difference 2 5) (sourceB196 + difference 5 2) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA196 + difference 2 5) (sourceB196 + difference 5 2) sourceC196) = raw5501 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5501; decide +kernel
    rw [ha]
    exact (canonical5501 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA196 + difference 3 0) (sourceB196 + difference 0 3) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA196 + difference 3 0) (sourceB196 + difference 0 3) sourceC196) = raw5502 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5502; decide +kernel
    rw [ha]
    exact (canonical5502 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA196 + difference 3 1) (sourceB196 + difference 1 3) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA196 + difference 3 1) (sourceB196 + difference 1 3) sourceC196) = raw5503 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5503; decide +kernel
    rw [ha]
    exact (canonical5503 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA196 + difference 3 2) (sourceB196 + difference 2 3) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2250) := by
    have ha : (tripleCharges (sourceA196 + difference 3 2) (sourceB196 + difference 2 3) sourceC196) = raw5504 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5504; decide +kernel
    rw [ha]
    exact (canonical5504 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA196 + difference 3 4) (sourceB196 + difference 4 3) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA196 + difference 3 4) (sourceB196 + difference 4 3) sourceC196) = raw5505 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5505; decide +kernel
    rw [ha]
    exact (canonical5505 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA196 + difference 3 5) (sourceB196 + difference 5 3) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA196 + difference 3 5) (sourceB196 + difference 5 3) sourceC196) = raw5506 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5506; decide +kernel
    rw [ha]
    exact (canonical5506 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA196 + difference 4 0) (sourceB196 + difference 0 4) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1731) := by
    have ha : (tripleCharges (sourceA196 + difference 4 0) (sourceB196 + difference 0 4) sourceC196) = raw5507 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5507; decide +kernel
    rw [ha]
    exact (canonical5507 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA196 + difference 4 1) (sourceB196 + difference 1 4) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2269) := by
    have ha : (tripleCharges (sourceA196 + difference 4 1) (sourceB196 + difference 1 4) sourceC196) = raw5508 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5508; decide +kernel
    rw [ha]
    exact (canonical5508 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA196 + difference 4 2) (sourceB196 + difference 2 4) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2269) := by
    have ha : (tripleCharges (sourceA196 + difference 4 2) (sourceB196 + difference 2 4) sourceC196) = raw5509 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5509; decide +kernel
    rw [ha]
    exact (canonical5509 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA196 + difference 4 3) (sourceB196 + difference 3 4) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2269) := by
    have ha : (tripleCharges (sourceA196 + difference 4 3) (sourceB196 + difference 3 4) sourceC196) = raw5510 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5510; decide +kernel
    rw [ha]
    exact (canonical5510 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA196 + difference 4 5) (sourceB196 + difference 5 4) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2252) := by
    have ha : (tripleCharges (sourceA196 + difference 4 5) (sourceB196 + difference 5 4) sourceC196) = raw5511 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5511; decide +kernel
    rw [ha]
    exact (canonical5511 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA196 + difference 5 0) (sourceB196 + difference 0 5) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1717) := by
    have ha : (tripleCharges (sourceA196 + difference 5 0) (sourceB196 + difference 0 5) sourceC196) = raw5512 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5512; decide +kernel
    rw [ha]
    exact (canonical5512 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA196 + difference 5 1) (sourceB196 + difference 1 5) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1930) := by
    have ha : (tripleCharges (sourceA196 + difference 5 1) (sourceB196 + difference 1 5) sourceC196) = raw5513 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5513; decide +kernel
    rw [ha]
    exact (canonical5513 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA196 + difference 5 2) (sourceB196 + difference 2 5) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1930) := by
    have ha : (tripleCharges (sourceA196 + difference 5 2) (sourceB196 + difference 2 5) sourceC196) = raw5514 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5514; decide +kernel
    rw [ha]
    exact (canonical5514 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA196 + difference 5 3) (sourceB196 + difference 3 5) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1930) := by
    have ha : (tripleCharges (sourceA196 + difference 5 3) (sourceB196 + difference 3 5) sourceC196) = raw5515 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5515; decide +kernel
    rw [ha]
    exact (canonical5515 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA196 + difference 5 4) (sourceB196 + difference 4 5) sourceC196) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2283) := by
    have ha : (tripleCharges (sourceA196 + difference 5 4) (sourceB196 + difference 4 5) sourceC196) = raw5516 := by
      apply Matrix.ext; unfold tripleCharges sourceA196 sourceB196 sourceC196 difference raw5516; decide +kernel
    rw [ha]
    exact (canonical5516 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA196 sourceB196 sourceC196
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm196, Integer.Sparse.eval]
  linarith only [hs]

def sourceA197 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB197 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC197 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceForm197 : Integer.Sparse Master := [(Sum.inr 2233, 1), (Sum.inr 3567, 3), (Sum.inr 3618, 1), (Sum.inr 3619, 1), (Sum.inr 4083, -1)]

theorem sourceEq197 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm197 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA197 + difference 0 0) (sourceB197 + difference 0 0) sourceC197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA197 + difference 0 0) (sourceB197 + difference 0 0) sourceC197) = raw5517 := by
      apply Matrix.ext; unfold tripleCharges sourceA197 sourceB197 sourceC197 difference raw5517; decide +kernel
    rw [ha]
    exact (canonical5517 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA197 + difference 0 1) (sourceB197 + difference 1 0) sourceC197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3567) := by
    have ha : (tripleCharges (sourceA197 + difference 0 1) (sourceB197 + difference 1 0) sourceC197) = raw5518 := by
      apply Matrix.ext; unfold tripleCharges sourceA197 sourceB197 sourceC197 difference raw5518; decide +kernel
    rw [ha]
    exact (canonical5518 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA197 + difference 0 2) (sourceB197 + difference 2 0) sourceC197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3567) := by
    have ha : (tripleCharges (sourceA197 + difference 0 2) (sourceB197 + difference 2 0) sourceC197) = raw5519 := by
      apply Matrix.ext; unfold tripleCharges sourceA197 sourceB197 sourceC197 difference raw5519; decide +kernel
    rw [ha]
    exact (canonical5519 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA197 + difference 0 3) (sourceB197 + difference 3 0) sourceC197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3567) := by
    have ha : (tripleCharges (sourceA197 + difference 0 3) (sourceB197 + difference 3 0) sourceC197) = raw5520 := by
      apply Matrix.ext; unfold tripleCharges sourceA197 sourceB197 sourceC197 difference raw5520; decide +kernel
    rw [ha]
    exact (canonical5520 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA197 + difference 0 4) (sourceB197 + difference 4 0) sourceC197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3619) := by
    have ha : (tripleCharges (sourceA197 + difference 0 4) (sourceB197 + difference 4 0) sourceC197) = raw5521 := by
      apply Matrix.ext; unfold tripleCharges sourceA197 sourceB197 sourceC197 difference raw5521; decide +kernel
    rw [ha]
    exact (canonical5521 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA197 + difference 0 5) (sourceB197 + difference 5 0) sourceC197) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3618) := by
    have ha : (tripleCharges (sourceA197 + difference 0 5) (sourceB197 + difference 5 0) sourceC197) = raw5522 := by
      apply Matrix.ext; unfold tripleCharges sourceA197 sourceB197 sourceC197 difference raw5522; decide +kernel
    rw [ha]
    exact (canonical5522 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA197 + sourceB197) sourceC197) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA197 + sourceB197) sourceC197) = raw5523 := by
      apply Matrix.ext; unfold doubleCharges sourceA197 sourceB197 sourceC197 raw5523; decide +kernel
    rw [ha]
    exact (canonical5523 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA197 sourceB197 sourceC197
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm197, Integer.Sparse.eval]
  linarith only [hs]

def sourceA198 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB198 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC198 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceForm198 : Integer.Sparse Master := [(Sum.inr 1014, 1), (Sum.inr 1015, 1), (Sum.inr 1021, 3), (Sum.inr 2233, 1), (Sum.inr 4083, -1)]

theorem sourceEq198 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm198 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA198 + difference 0 0) (sourceB198 + difference 0 0) sourceC198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA198 + difference 0 0) (sourceB198 + difference 0 0) sourceC198) = raw5517 := by
      apply Matrix.ext; unfold tripleCharges sourceA198 sourceB198 sourceC198 difference raw5517; decide +kernel
    rw [ha]
    exact (canonical5517 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA198 + difference 1 0) (sourceB198 + difference 0 1) sourceC198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA198 + difference 1 0) (sourceB198 + difference 0 1) sourceC198) = raw5524 := by
      apply Matrix.ext; unfold tripleCharges sourceA198 sourceB198 sourceC198 difference raw5524; decide +kernel
    rw [ha]
    exact (canonical5524 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA198 + difference 2 0) (sourceB198 + difference 0 2) sourceC198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA198 + difference 2 0) (sourceB198 + difference 0 2) sourceC198) = raw5525 := by
      apply Matrix.ext; unfold tripleCharges sourceA198 sourceB198 sourceC198 difference raw5525; decide +kernel
    rw [ha]
    exact (canonical5525 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA198 + difference 3 0) (sourceB198 + difference 0 3) sourceC198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA198 + difference 3 0) (sourceB198 + difference 0 3) sourceC198) = raw5526 := by
      apply Matrix.ext; unfold tripleCharges sourceA198 sourceB198 sourceC198 difference raw5526; decide +kernel
    rw [ha]
    exact (canonical5526 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA198 + difference 4 0) (sourceB198 + difference 0 4) sourceC198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1015) := by
    have ha : (tripleCharges (sourceA198 + difference 4 0) (sourceB198 + difference 0 4) sourceC198) = raw5527 := by
      apply Matrix.ext; unfold tripleCharges sourceA198 sourceB198 sourceC198 difference raw5527; decide +kernel
    rw [ha]
    exact (canonical5527 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA198 + difference 5 0) (sourceB198 + difference 0 5) sourceC198) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1014) := by
    have ha : (tripleCharges (sourceA198 + difference 5 0) (sourceB198 + difference 0 5) sourceC198) = raw5528 := by
      apply Matrix.ext; unfold tripleCharges sourceA198 sourceB198 sourceC198 difference raw5528; decide +kernel
    rw [ha]
    exact (canonical5528 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA198 + sourceB198) sourceC198) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA198 + sourceB198) sourceC198) = raw5523 := by
      apply Matrix.ext; unfold doubleCharges sourceA198 sourceB198 sourceC198 raw5523; decide +kernel
    rw [ha]
    exact (canonical5523 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA198 sourceB198 sourceC198
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm198, Integer.Sparse.eval]
  linarith only [hs]

def sourceA199 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB199 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC199 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceForm199 : Integer.Sparse Master := [(Sum.inr 1021, 1), (Sum.inr 2089, 2), (Sum.inr 2233, 1), (Sum.inr 2243, 1), (Sum.inr 2245, 1), (Sum.inr 4083, -1)]

theorem sourceEq199 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm199 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA199 + difference 1 0) (sourceB199 + difference 0 1) sourceC199) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA199 + difference 1 0) (sourceB199 + difference 0 1) sourceC199) = raw5524 := by
      apply Matrix.ext; unfold tripleCharges sourceA199 sourceB199 sourceC199 difference raw5524; decide +kernel
    rw [ha]
    exact (canonical5524 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA199 + difference 1 1) (sourceB199 + difference 1 1) sourceC199) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA199 + difference 1 1) (sourceB199 + difference 1 1) sourceC199) = raw5517 := by
      apply Matrix.ext; unfold tripleCharges sourceA199 sourceB199 sourceC199 difference raw5517; decide +kernel
    rw [ha]
    exact (canonical5517 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA199 + difference 1 2) (sourceB199 + difference 2 1) sourceC199) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA199 + difference 1 2) (sourceB199 + difference 2 1) sourceC199) = raw5529 := by
      apply Matrix.ext; unfold tripleCharges sourceA199 sourceB199 sourceC199 difference raw5529; decide +kernel
    rw [ha]
    exact (canonical5529 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA199 + difference 1 3) (sourceB199 + difference 3 1) sourceC199) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA199 + difference 1 3) (sourceB199 + difference 3 1) sourceC199) = raw5530 := by
      apply Matrix.ext; unfold tripleCharges sourceA199 sourceB199 sourceC199 difference raw5530; decide +kernel
    rw [ha]
    exact (canonical5530 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA199 + difference 1 4) (sourceB199 + difference 4 1) sourceC199) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA199 + difference 1 4) (sourceB199 + difference 4 1) sourceC199) = raw5531 := by
      apply Matrix.ext; unfold tripleCharges sourceA199 sourceB199 sourceC199 difference raw5531; decide +kernel
    rw [ha]
    exact (canonical5531 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA199 + difference 1 5) (sourceB199 + difference 5 1) sourceC199) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA199 + difference 1 5) (sourceB199 + difference 5 1) sourceC199) = raw5532 := by
      apply Matrix.ext; unfold tripleCharges sourceA199 sourceB199 sourceC199 difference raw5532; decide +kernel
    rw [ha]
    exact (canonical5532 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA199 + sourceB199) sourceC199) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA199 + sourceB199) sourceC199) = raw5523 := by
      apply Matrix.ext; unfold doubleCharges sourceA199 sourceB199 sourceC199 raw5523; decide +kernel
    rw [ha]
    exact (canonical5523 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA199 sourceB199 sourceC199
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm199, Integer.Sparse.eval]
  linarith only [hs]

def sourceA200 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB200 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC200 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceForm200 : Integer.Sparse Master := [(Sum.inr 2083, 1), (Sum.inr 2084, 1), (Sum.inr 2089, 2), (Sum.inr 2233, 1), (Sum.inr 3567, 1), (Sum.inr 4083, -1)]

theorem sourceEq200 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm200 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA200 + difference 0 1) (sourceB200 + difference 1 0) sourceC200) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3567) := by
    have ha : (tripleCharges (sourceA200 + difference 0 1) (sourceB200 + difference 1 0) sourceC200) = raw5518 := by
      apply Matrix.ext; unfold tripleCharges sourceA200 sourceB200 sourceC200 difference raw5518; decide +kernel
    rw [ha]
    exact (canonical5518 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA200 + difference 1 1) (sourceB200 + difference 1 1) sourceC200) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA200 + difference 1 1) (sourceB200 + difference 1 1) sourceC200) = raw5517 := by
      apply Matrix.ext; unfold tripleCharges sourceA200 sourceB200 sourceC200 difference raw5517; decide +kernel
    rw [ha]
    exact (canonical5517 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA200 + difference 2 1) (sourceB200 + difference 1 2) sourceC200) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA200 + difference 2 1) (sourceB200 + difference 1 2) sourceC200) = raw5533 := by
      apply Matrix.ext; unfold tripleCharges sourceA200 sourceB200 sourceC200 difference raw5533; decide +kernel
    rw [ha]
    exact (canonical5533 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA200 + difference 3 1) (sourceB200 + difference 1 3) sourceC200) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA200 + difference 3 1) (sourceB200 + difference 1 3) sourceC200) = raw5534 := by
      apply Matrix.ext; unfold tripleCharges sourceA200 sourceB200 sourceC200 difference raw5534; decide +kernel
    rw [ha]
    exact (canonical5534 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA200 + difference 4 1) (sourceB200 + difference 1 4) sourceC200) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2084) := by
    have ha : (tripleCharges (sourceA200 + difference 4 1) (sourceB200 + difference 1 4) sourceC200) = raw5535 := by
      apply Matrix.ext; unfold tripleCharges sourceA200 sourceB200 sourceC200 difference raw5535; decide +kernel
    rw [ha]
    exact (canonical5535 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA200 + difference 5 1) (sourceB200 + difference 1 5) sourceC200) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2083) := by
    have ha : (tripleCharges (sourceA200 + difference 5 1) (sourceB200 + difference 1 5) sourceC200) = raw5536 := by
      apply Matrix.ext; unfold tripleCharges sourceA200 sourceB200 sourceC200 difference raw5536; decide +kernel
    rw [ha]
    exact (canonical5536 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA200 + sourceB200) sourceC200) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA200 + sourceB200) sourceC200) = raw5523 := by
      apply Matrix.ext; unfold doubleCharges sourceA200 sourceB200 sourceC200 raw5523; decide +kernel
    rw [ha]
    exact (canonical5523 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA200 sourceB200 sourceC200
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm200, Integer.Sparse.eval]
  linarith only [hs]

def sourceA201 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB201 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceC201 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceForm201 : Integer.Sparse Master := [(Sum.inr 1015, 1), (Sum.inr 2084, 3), (Sum.inr 2233, 2), (Sum.inr 4083, -1)]

theorem sourceEq201 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm201 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA201 + difference 4 0) (sourceB201 + difference 0 4) sourceC201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1015) := by
    have ha : (tripleCharges (sourceA201 + difference 4 0) (sourceB201 + difference 0 4) sourceC201) = raw5527 := by
      apply Matrix.ext; unfold tripleCharges sourceA201 sourceB201 sourceC201 difference raw5527; decide +kernel
    rw [ha]
    exact (canonical5527 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA201 + difference 4 1) (sourceB201 + difference 1 4) sourceC201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2084) := by
    have ha : (tripleCharges (sourceA201 + difference 4 1) (sourceB201 + difference 1 4) sourceC201) = raw5535 := by
      apply Matrix.ext; unfold tripleCharges sourceA201 sourceB201 sourceC201 difference raw5535; decide +kernel
    rw [ha]
    exact (canonical5535 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA201 + difference 4 2) (sourceB201 + difference 2 4) sourceC201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2084) := by
    have ha : (tripleCharges (sourceA201 + difference 4 2) (sourceB201 + difference 2 4) sourceC201) = raw5537 := by
      apply Matrix.ext; unfold tripleCharges sourceA201 sourceB201 sourceC201 difference raw5537; decide +kernel
    rw [ha]
    exact (canonical5537 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA201 + difference 4 3) (sourceB201 + difference 3 4) sourceC201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2084) := by
    have ha : (tripleCharges (sourceA201 + difference 4 3) (sourceB201 + difference 3 4) sourceC201) = raw5538 := by
      apply Matrix.ext; unfold tripleCharges sourceA201 sourceB201 sourceC201 difference raw5538; decide +kernel
    rw [ha]
    exact (canonical5538 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA201 + difference 4 4) (sourceB201 + difference 4 4) sourceC201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA201 + difference 4 4) (sourceB201 + difference 4 4) sourceC201) = raw5517 := by
      apply Matrix.ext; unfold tripleCharges sourceA201 sourceB201 sourceC201 difference raw5517; decide +kernel
    rw [ha]
    exact (canonical5517 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA201 + difference 4 5) (sourceB201 + difference 5 4) sourceC201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2233) := by
    have ha : (tripleCharges (sourceA201 + difference 4 5) (sourceB201 + difference 5 4) sourceC201) = raw5539 := by
      apply Matrix.ext; unfold tripleCharges sourceA201 sourceB201 sourceC201 difference raw5539; decide +kernel
    rw [ha]
    exact (canonical5539 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA201 + sourceB201) sourceC201) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA201 + sourceB201) sourceC201) = raw5523 := by
      apply Matrix.ext; unfold doubleCharges sourceA201 sourceB201 sourceC201 raw5523; decide +kernel
    rw [ha]
    exact (canonical5523 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA201 sourceB201 sourceC201
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm201, Integer.Sparse.eval]
  linarith only [hs]

def sourceA202 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB202 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC202 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceForm202 : Integer.Sparse Master := [(Sum.inr 4244, 1), (Sum.inr 4246, 1), (Sum.inr 4250, 3), (Sum.inr 4792, 3), (Sum.inr 4795, 3), (Sum.inr 4803, 6), (Sum.inr 4815, 3), (Sum.inr 4830, 1), (Sum.inr 4851, 3), (Sum.inr 4863, 1), (Sum.inr 5406, 3), (Sum.inr 5437, 1), (Sum.inr 5447, 1)]

theorem sourceEq202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm202 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA202 + difference 0 1) (sourceB202 + difference 1 0) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA202 + difference 0 1) (sourceB202 + difference 1 0) sourceC202) = raw5540 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5540; decide +kernel
    rw [ha]
    exact (canonical5540 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA202 + difference 0 2) (sourceB202 + difference 2 0) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA202 + difference 0 2) (sourceB202 + difference 2 0) sourceC202) = raw5541 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5541; decide +kernel
    rw [ha]
    exact (canonical5541 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA202 + difference 0 3) (sourceB202 + difference 3 0) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA202 + difference 0 3) (sourceB202 + difference 3 0) sourceC202) = raw5542 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5542; decide +kernel
    rw [ha]
    exact (canonical5542 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA202 + difference 0 4) (sourceB202 + difference 4 0) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5437) := by
    have ha : (tripleCharges (sourceA202 + difference 0 4) (sourceB202 + difference 4 0) sourceC202) = raw5543 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5543; decide +kernel
    rw [ha]
    exact (canonical5543 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA202 + difference 0 5) (sourceB202 + difference 5 0) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA202 + difference 0 5) (sourceB202 + difference 5 0) sourceC202) = raw5544 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5544; decide +kernel
    rw [ha]
    exact (canonical5544 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA202 + difference 1 0) (sourceB202 + difference 0 1) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4250) := by
    have ha : (tripleCharges (sourceA202 + difference 1 0) (sourceB202 + difference 0 1) sourceC202) = raw5545 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5545; decide +kernel
    rw [ha]
    exact (canonical5545 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA202 + difference 1 2) (sourceB202 + difference 2 1) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA202 + difference 1 2) (sourceB202 + difference 2 1) sourceC202) = raw5546 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5546; decide +kernel
    rw [ha]
    exact (canonical5546 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA202 + difference 1 3) (sourceB202 + difference 3 1) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA202 + difference 1 3) (sourceB202 + difference 3 1) sourceC202) = raw5547 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5547; decide +kernel
    rw [ha]
    exact (canonical5547 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA202 + difference 1 4) (sourceB202 + difference 4 1) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA202 + difference 1 4) (sourceB202 + difference 4 1) sourceC202) = raw5548 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5548; decide +kernel
    rw [ha]
    exact (canonical5548 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA202 + difference 1 5) (sourceB202 + difference 5 1) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA202 + difference 1 5) (sourceB202 + difference 5 1) sourceC202) = raw5549 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5549; decide +kernel
    rw [ha]
    exact (canonical5549 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA202 + difference 2 0) (sourceB202 + difference 0 2) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4250) := by
    have ha : (tripleCharges (sourceA202 + difference 2 0) (sourceB202 + difference 0 2) sourceC202) = raw5550 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5550; decide +kernel
    rw [ha]
    exact (canonical5550 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA202 + difference 2 1) (sourceB202 + difference 1 2) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA202 + difference 2 1) (sourceB202 + difference 1 2) sourceC202) = raw5551 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5551; decide +kernel
    rw [ha]
    exact (canonical5551 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA202 + difference 2 3) (sourceB202 + difference 3 2) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA202 + difference 2 3) (sourceB202 + difference 3 2) sourceC202) = raw5552 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5552; decide +kernel
    rw [ha]
    exact (canonical5552 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA202 + difference 2 4) (sourceB202 + difference 4 2) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA202 + difference 2 4) (sourceB202 + difference 4 2) sourceC202) = raw5553 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5553; decide +kernel
    rw [ha]
    exact (canonical5553 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA202 + difference 2 5) (sourceB202 + difference 5 2) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA202 + difference 2 5) (sourceB202 + difference 5 2) sourceC202) = raw5554 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5554; decide +kernel
    rw [ha]
    exact (canonical5554 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA202 + difference 3 0) (sourceB202 + difference 0 3) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4250) := by
    have ha : (tripleCharges (sourceA202 + difference 3 0) (sourceB202 + difference 0 3) sourceC202) = raw5555 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5555; decide +kernel
    rw [ha]
    exact (canonical5555 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA202 + difference 3 1) (sourceB202 + difference 1 3) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA202 + difference 3 1) (sourceB202 + difference 1 3) sourceC202) = raw5556 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5556; decide +kernel
    rw [ha]
    exact (canonical5556 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA202 + difference 3 2) (sourceB202 + difference 2 3) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4803) := by
    have ha : (tripleCharges (sourceA202 + difference 3 2) (sourceB202 + difference 2 3) sourceC202) = raw5557 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5557; decide +kernel
    rw [ha]
    exact (canonical5557 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA202 + difference 3 4) (sourceB202 + difference 4 3) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4815) := by
    have ha : (tripleCharges (sourceA202 + difference 3 4) (sourceB202 + difference 4 3) sourceC202) = raw5558 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5558; decide +kernel
    rw [ha]
    exact (canonical5558 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA202 + difference 3 5) (sourceB202 + difference 5 3) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA202 + difference 3 5) (sourceB202 + difference 5 3) sourceC202) = raw5559 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5559; decide +kernel
    rw [ha]
    exact (canonical5559 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA202 + difference 4 0) (sourceB202 + difference 0 4) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4246) := by
    have ha : (tripleCharges (sourceA202 + difference 4 0) (sourceB202 + difference 0 4) sourceC202) = raw5560 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5560; decide +kernel
    rw [ha]
    exact (canonical5560 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA202 + difference 4 1) (sourceB202 + difference 1 4) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA202 + difference 4 1) (sourceB202 + difference 1 4) sourceC202) = raw5561 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5561; decide +kernel
    rw [ha]
    exact (canonical5561 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA202 + difference 4 2) (sourceB202 + difference 2 4) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA202 + difference 4 2) (sourceB202 + difference 2 4) sourceC202) = raw5562 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5562; decide +kernel
    rw [ha]
    exact (canonical5562 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA202 + difference 4 3) (sourceB202 + difference 3 4) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA202 + difference 4 3) (sourceB202 + difference 3 4) sourceC202) = raw5563 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5563; decide +kernel
    rw [ha]
    exact (canonical5563 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA202 + difference 4 5) (sourceB202 + difference 5 4) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4863) := by
    have ha : (tripleCharges (sourceA202 + difference 4 5) (sourceB202 + difference 5 4) sourceC202) = raw5564 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5564; decide +kernel
    rw [ha]
    exact (canonical5564 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA202 + difference 5 0) (sourceB202 + difference 0 5) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4244) := by
    have ha : (tripleCharges (sourceA202 + difference 5 0) (sourceB202 + difference 0 5) sourceC202) = raw5565 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5565; decide +kernel
    rw [ha]
    exact (canonical5565 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA202 + difference 5 1) (sourceB202 + difference 1 5) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA202 + difference 5 1) (sourceB202 + difference 1 5) sourceC202) = raw5566 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5566; decide +kernel
    rw [ha]
    exact (canonical5566 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA202 + difference 5 2) (sourceB202 + difference 2 5) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA202 + difference 5 2) (sourceB202 + difference 2 5) sourceC202) = raw5567 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5567; decide +kernel
    rw [ha]
    exact (canonical5567 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA202 + difference 5 3) (sourceB202 + difference 3 5) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA202 + difference 5 3) (sourceB202 + difference 3 5) sourceC202) = raw5568 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5568; decide +kernel
    rw [ha]
    exact (canonical5568 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA202 + difference 5 4) (sourceB202 + difference 4 5) sourceC202) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4830) := by
    have ha : (tripleCharges (sourceA202 + difference 5 4) (sourceB202 + difference 4 5) sourceC202) = raw5569 := by
      apply Matrix.ext; unfold tripleCharges sourceA202 sourceB202 sourceC202 difference raw5569; decide +kernel
    rw [ha]
    exact (canonical5569 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA202 sourceB202 sourceC202
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm202, Integer.Sparse.eval]
  linarith only [hs]

def sourceA203 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB203 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC203 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceForm203 : Integer.Sparse Master := [(Sum.inr 776, 1), (Sum.inr 778, 1), (Sum.inr 784, 3), (Sum.inr 2009, 3), (Sum.inr 2012, 3), (Sum.inr 2021, 6), (Sum.inr 2187, 1), (Sum.inr 2192, 3), (Sum.inr 2232, 1), (Sum.inr 2240, 3), (Sum.inr 3847, 3), (Sum.inr 3899, 1), (Sum.inr 3909, 1)]

theorem sourceEq203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm203 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA203 + difference 0 1) (sourceB203 + difference 1 0) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA203 + difference 0 1) (sourceB203 + difference 1 0) sourceC203) = raw5570 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5570; decide +kernel
    rw [ha]
    exact (canonical5570 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA203 + difference 0 2) (sourceB203 + difference 2 0) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA203 + difference 0 2) (sourceB203 + difference 2 0) sourceC203) = raw5571 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5571; decide +kernel
    rw [ha]
    exact (canonical5571 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA203 + difference 0 3) (sourceB203 + difference 3 0) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA203 + difference 0 3) (sourceB203 + difference 3 0) sourceC203) = raw5572 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5572; decide +kernel
    rw [ha]
    exact (canonical5572 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA203 + difference 0 4) (sourceB203 + difference 4 0) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3899) := by
    have ha : (tripleCharges (sourceA203 + difference 0 4) (sourceB203 + difference 4 0) sourceC203) = raw5573 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5573; decide +kernel
    rw [ha]
    exact (canonical5573 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA203 + difference 0 5) (sourceB203 + difference 5 0) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3909) := by
    have ha : (tripleCharges (sourceA203 + difference 0 5) (sourceB203 + difference 5 0) sourceC203) = raw5574 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5574; decide +kernel
    rw [ha]
    exact (canonical5574 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA203 + difference 1 0) (sourceB203 + difference 0 1) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 784) := by
    have ha : (tripleCharges (sourceA203 + difference 1 0) (sourceB203 + difference 0 1) sourceC203) = raw5575 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5575; decide +kernel
    rw [ha]
    exact (canonical5575 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA203 + difference 1 2) (sourceB203 + difference 2 1) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA203 + difference 1 2) (sourceB203 + difference 2 1) sourceC203) = raw5576 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5576; decide +kernel
    rw [ha]
    exact (canonical5576 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA203 + difference 1 3) (sourceB203 + difference 3 1) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA203 + difference 1 3) (sourceB203 + difference 3 1) sourceC203) = raw5577 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5577; decide +kernel
    rw [ha]
    exact (canonical5577 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA203 + difference 1 4) (sourceB203 + difference 4 1) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA203 + difference 1 4) (sourceB203 + difference 4 1) sourceC203) = raw5578 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5578; decide +kernel
    rw [ha]
    exact (canonical5578 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA203 + difference 1 5) (sourceB203 + difference 5 1) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA203 + difference 1 5) (sourceB203 + difference 5 1) sourceC203) = raw5579 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5579; decide +kernel
    rw [ha]
    exact (canonical5579 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA203 + difference 2 0) (sourceB203 + difference 0 2) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 784) := by
    have ha : (tripleCharges (sourceA203 + difference 2 0) (sourceB203 + difference 0 2) sourceC203) = raw5580 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5580; decide +kernel
    rw [ha]
    exact (canonical5580 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA203 + difference 2 1) (sourceB203 + difference 1 2) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA203 + difference 2 1) (sourceB203 + difference 1 2) sourceC203) = raw5581 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5581; decide +kernel
    rw [ha]
    exact (canonical5581 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA203 + difference 2 3) (sourceB203 + difference 3 2) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA203 + difference 2 3) (sourceB203 + difference 3 2) sourceC203) = raw5582 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5582; decide +kernel
    rw [ha]
    exact (canonical5582 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA203 + difference 2 4) (sourceB203 + difference 4 2) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA203 + difference 2 4) (sourceB203 + difference 4 2) sourceC203) = raw5583 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5583; decide +kernel
    rw [ha]
    exact (canonical5583 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA203 + difference 2 5) (sourceB203 + difference 5 2) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA203 + difference 2 5) (sourceB203 + difference 5 2) sourceC203) = raw5584 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5584; decide +kernel
    rw [ha]
    exact (canonical5584 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA203 + difference 3 0) (sourceB203 + difference 0 3) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 784) := by
    have ha : (tripleCharges (sourceA203 + difference 3 0) (sourceB203 + difference 0 3) sourceC203) = raw5585 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5585; decide +kernel
    rw [ha]
    exact (canonical5585 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA203 + difference 3 1) (sourceB203 + difference 1 3) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA203 + difference 3 1) (sourceB203 + difference 1 3) sourceC203) = raw5586 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5586; decide +kernel
    rw [ha]
    exact (canonical5586 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA203 + difference 3 2) (sourceB203 + difference 2 3) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA203 + difference 3 2) (sourceB203 + difference 2 3) sourceC203) = raw5587 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5587; decide +kernel
    rw [ha]
    exact (canonical5587 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA203 + difference 3 4) (sourceB203 + difference 4 3) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA203 + difference 3 4) (sourceB203 + difference 4 3) sourceC203) = raw5588 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5588; decide +kernel
    rw [ha]
    exact (canonical5588 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA203 + difference 3 5) (sourceB203 + difference 5 3) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA203 + difference 3 5) (sourceB203 + difference 5 3) sourceC203) = raw5589 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5589; decide +kernel
    rw [ha]
    exact (canonical5589 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA203 + difference 4 0) (sourceB203 + difference 0 4) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 778) := by
    have ha : (tripleCharges (sourceA203 + difference 4 0) (sourceB203 + difference 0 4) sourceC203) = raw5590 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5590; decide +kernel
    rw [ha]
    exact (canonical5590 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA203 + difference 4 1) (sourceB203 + difference 1 4) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2012) := by
    have ha : (tripleCharges (sourceA203 + difference 4 1) (sourceB203 + difference 1 4) sourceC203) = raw5591 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5591; decide +kernel
    rw [ha]
    exact (canonical5591 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA203 + difference 4 2) (sourceB203 + difference 2 4) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2012) := by
    have ha : (tripleCharges (sourceA203 + difference 4 2) (sourceB203 + difference 2 4) sourceC203) = raw5592 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5592; decide +kernel
    rw [ha]
    exact (canonical5592 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA203 + difference 4 3) (sourceB203 + difference 3 4) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2012) := by
    have ha : (tripleCharges (sourceA203 + difference 4 3) (sourceB203 + difference 3 4) sourceC203) = raw5593 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5593; decide +kernel
    rw [ha]
    exact (canonical5593 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA203 + difference 4 5) (sourceB203 + difference 5 4) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2232) := by
    have ha : (tripleCharges (sourceA203 + difference 4 5) (sourceB203 + difference 5 4) sourceC203) = raw5594 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5594; decide +kernel
    rw [ha]
    exact (canonical5594 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA203 + difference 5 0) (sourceB203 + difference 0 5) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 776) := by
    have ha : (tripleCharges (sourceA203 + difference 5 0) (sourceB203 + difference 0 5) sourceC203) = raw5595 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5595; decide +kernel
    rw [ha]
    exact (canonical5595 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA203 + difference 5 1) (sourceB203 + difference 1 5) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2009) := by
    have ha : (tripleCharges (sourceA203 + difference 5 1) (sourceB203 + difference 1 5) sourceC203) = raw5596 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5596; decide +kernel
    rw [ha]
    exact (canonical5596 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA203 + difference 5 2) (sourceB203 + difference 2 5) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2009) := by
    have ha : (tripleCharges (sourceA203 + difference 5 2) (sourceB203 + difference 2 5) sourceC203) = raw5597 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5597; decide +kernel
    rw [ha]
    exact (canonical5597 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA203 + difference 5 3) (sourceB203 + difference 3 5) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2009) := by
    have ha : (tripleCharges (sourceA203 + difference 5 3) (sourceB203 + difference 3 5) sourceC203) = raw5598 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5598; decide +kernel
    rw [ha]
    exact (canonical5598 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA203 + difference 5 4) (sourceB203 + difference 4 5) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2187) := by
    have ha : (tripleCharges (sourceA203 + difference 5 4) (sourceB203 + difference 4 5) sourceC203) = raw5599 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5599; decide +kernel
    rw [ha]
    exact (canonical5599 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA203 sourceB203 sourceC203
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm203, Integer.Sparse.eval]
  linarith only [hs]

def sourceA204 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB204 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC204 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceForm204 : Integer.Sparse Master := [(Sum.inr 792, 3), (Sum.inr 802, 1), (Sum.inr 821, 1), (Sum.inr 2033, 3), (Sum.inr 2050, 1), (Sum.inr 2088, 3), (Sum.inr 2104, 1), (Sum.inr 2195, 6), (Sum.inr 2201, 3), (Sum.inr 2213, 3), (Sum.inr 3812, 3), (Sum.inr 3855, 1), (Sum.inr 3882, 1)]

theorem sourceEq204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm204 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA204 + difference 0 1) (sourceB204 + difference 1 0) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA204 + difference 0 1) (sourceB204 + difference 1 0) sourceC204) = raw5600 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5600; decide +kernel
    rw [ha]
    exact (canonical5600 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA204 + difference 0 2) (sourceB204 + difference 2 0) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA204 + difference 0 2) (sourceB204 + difference 2 0) sourceC204) = raw5601 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5601; decide +kernel
    rw [ha]
    exact (canonical5601 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA204 + difference 0 3) (sourceB204 + difference 3 0) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA204 + difference 0 3) (sourceB204 + difference 3 0) sourceC204) = raw5602 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5602; decide +kernel
    rw [ha]
    exact (canonical5602 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA204 + difference 0 4) (sourceB204 + difference 4 0) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3855) := by
    have ha : (tripleCharges (sourceA204 + difference 0 4) (sourceB204 + difference 4 0) sourceC204) = raw5603 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5603; decide +kernel
    rw [ha]
    exact (canonical5603 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA204 + difference 0 5) (sourceB204 + difference 5 0) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3882) := by
    have ha : (tripleCharges (sourceA204 + difference 0 5) (sourceB204 + difference 5 0) sourceC204) = raw5604 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5604; decide +kernel
    rw [ha]
    exact (canonical5604 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA204 + difference 1 0) (sourceB204 + difference 0 1) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 792) := by
    have ha : (tripleCharges (sourceA204 + difference 1 0) (sourceB204 + difference 0 1) sourceC204) = raw5605 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5605; decide +kernel
    rw [ha]
    exact (canonical5605 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA204 + difference 1 2) (sourceB204 + difference 2 1) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA204 + difference 1 2) (sourceB204 + difference 2 1) sourceC204) = raw5606 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5606; decide +kernel
    rw [ha]
    exact (canonical5606 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA204 + difference 1 3) (sourceB204 + difference 3 1) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA204 + difference 1 3) (sourceB204 + difference 3 1) sourceC204) = raw5607 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5607; decide +kernel
    rw [ha]
    exact (canonical5607 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA204 + difference 1 4) (sourceB204 + difference 4 1) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2033) := by
    have ha : (tripleCharges (sourceA204 + difference 1 4) (sourceB204 + difference 4 1) sourceC204) = raw5608 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5608; decide +kernel
    rw [ha]
    exact (canonical5608 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA204 + difference 1 5) (sourceB204 + difference 5 1) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2088) := by
    have ha : (tripleCharges (sourceA204 + difference 1 5) (sourceB204 + difference 5 1) sourceC204) = raw5609 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5609; decide +kernel
    rw [ha]
    exact (canonical5609 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA204 + difference 2 0) (sourceB204 + difference 0 2) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 792) := by
    have ha : (tripleCharges (sourceA204 + difference 2 0) (sourceB204 + difference 0 2) sourceC204) = raw5610 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5610; decide +kernel
    rw [ha]
    exact (canonical5610 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA204 + difference 2 1) (sourceB204 + difference 1 2) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA204 + difference 2 1) (sourceB204 + difference 1 2) sourceC204) = raw5611 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5611; decide +kernel
    rw [ha]
    exact (canonical5611 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA204 + difference 2 3) (sourceB204 + difference 3 2) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA204 + difference 2 3) (sourceB204 + difference 3 2) sourceC204) = raw5612 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5612; decide +kernel
    rw [ha]
    exact (canonical5612 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA204 + difference 2 4) (sourceB204 + difference 4 2) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2033) := by
    have ha : (tripleCharges (sourceA204 + difference 2 4) (sourceB204 + difference 4 2) sourceC204) = raw5613 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5613; decide +kernel
    rw [ha]
    exact (canonical5613 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA204 + difference 2 5) (sourceB204 + difference 5 2) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2088) := by
    have ha : (tripleCharges (sourceA204 + difference 2 5) (sourceB204 + difference 5 2) sourceC204) = raw5614 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5614; decide +kernel
    rw [ha]
    exact (canonical5614 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA204 + difference 3 0) (sourceB204 + difference 0 3) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 792) := by
    have ha : (tripleCharges (sourceA204 + difference 3 0) (sourceB204 + difference 0 3) sourceC204) = raw5615 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5615; decide +kernel
    rw [ha]
    exact (canonical5615 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA204 + difference 3 1) (sourceB204 + difference 1 3) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA204 + difference 3 1) (sourceB204 + difference 1 3) sourceC204) = raw5616 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5616; decide +kernel
    rw [ha]
    exact (canonical5616 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA204 + difference 3 2) (sourceB204 + difference 2 3) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2195) := by
    have ha : (tripleCharges (sourceA204 + difference 3 2) (sourceB204 + difference 2 3) sourceC204) = raw5617 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5617; decide +kernel
    rw [ha]
    exact (canonical5617 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA204 + difference 3 4) (sourceB204 + difference 4 3) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2033) := by
    have ha : (tripleCharges (sourceA204 + difference 3 4) (sourceB204 + difference 4 3) sourceC204) = raw5618 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5618; decide +kernel
    rw [ha]
    exact (canonical5618 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA204 + difference 3 5) (sourceB204 + difference 5 3) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2088) := by
    have ha : (tripleCharges (sourceA204 + difference 3 5) (sourceB204 + difference 5 3) sourceC204) = raw5619 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5619; decide +kernel
    rw [ha]
    exact (canonical5619 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA204 + difference 4 0) (sourceB204 + difference 0 4) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 821) := by
    have ha : (tripleCharges (sourceA204 + difference 4 0) (sourceB204 + difference 0 4) sourceC204) = raw5620 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5620; decide +kernel
    rw [ha]
    exact (canonical5620 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA204 + difference 4 1) (sourceB204 + difference 1 4) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA204 + difference 4 1) (sourceB204 + difference 1 4) sourceC204) = raw5621 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5621; decide +kernel
    rw [ha]
    exact (canonical5621 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA204 + difference 4 2) (sourceB204 + difference 2 4) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA204 + difference 4 2) (sourceB204 + difference 2 4) sourceC204) = raw5622 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5622; decide +kernel
    rw [ha]
    exact (canonical5622 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA204 + difference 4 3) (sourceB204 + difference 3 4) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA204 + difference 4 3) (sourceB204 + difference 3 4) sourceC204) = raw5623 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5623; decide +kernel
    rw [ha]
    exact (canonical5623 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA204 + difference 4 5) (sourceB204 + difference 5 4) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2104) := by
    have ha : (tripleCharges (sourceA204 + difference 4 5) (sourceB204 + difference 5 4) sourceC204) = raw5624 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5624; decide +kernel
    rw [ha]
    exact (canonical5624 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA204 + difference 5 0) (sourceB204 + difference 0 5) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 802) := by
    have ha : (tripleCharges (sourceA204 + difference 5 0) (sourceB204 + difference 0 5) sourceC204) = raw5625 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5625; decide +kernel
    rw [ha]
    exact (canonical5625 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA204 + difference 5 1) (sourceB204 + difference 1 5) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA204 + difference 5 1) (sourceB204 + difference 1 5) sourceC204) = raw5626 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5626; decide +kernel
    rw [ha]
    exact (canonical5626 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA204 + difference 5 2) (sourceB204 + difference 2 5) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA204 + difference 5 2) (sourceB204 + difference 2 5) sourceC204) = raw5627 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5627; decide +kernel
    rw [ha]
    exact (canonical5627 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA204 + difference 5 3) (sourceB204 + difference 3 5) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2201) := by
    have ha : (tripleCharges (sourceA204 + difference 5 3) (sourceB204 + difference 3 5) sourceC204) = raw5628 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5628; decide +kernel
    rw [ha]
    exact (canonical5628 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA204 + difference 5 4) (sourceB204 + difference 4 5) sourceC204) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2050) := by
    have ha : (tripleCharges (sourceA204 + difference 5 4) (sourceB204 + difference 4 5) sourceC204) = raw5629 := by
      apply Matrix.ext; unfold tripleCharges sourceA204 sourceB204 sourceC204 difference raw5629; decide +kernel
    rw [ha]
    exact (canonical5629 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA204 sourceB204 sourceC204
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm204, Integer.Sparse.eval]
  linarith only [hs]

def sourceA205 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB205 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC205 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceForm205 : Integer.Sparse Master := [(Sum.inr 3221, 1), (Sum.inr 3801, 3), (Sum.inr 3899, 1), (Sum.inr 4025, 1), (Sum.inr 4091, -1)]

theorem sourceEq205 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm205 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA205 + difference 0 0) (sourceB205 + difference 0 0) sourceC205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA205 + difference 0 0) (sourceB205 + difference 0 0) sourceC205) = raw5630 := by
      apply Matrix.ext; unfold tripleCharges sourceA205 sourceB205 sourceC205 difference raw5630; decide +kernel
    rw [ha]
    exact (canonical5630 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA205 + difference 0 1) (sourceB205 + difference 1 0) sourceC205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA205 + difference 0 1) (sourceB205 + difference 1 0) sourceC205) = raw5631 := by
      apply Matrix.ext; unfold tripleCharges sourceA205 sourceB205 sourceC205 difference raw5631; decide +kernel
    rw [ha]
    exact (canonical5631 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA205 + difference 0 2) (sourceB205 + difference 2 0) sourceC205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA205 + difference 0 2) (sourceB205 + difference 2 0) sourceC205) = raw5632 := by
      apply Matrix.ext; unfold tripleCharges sourceA205 sourceB205 sourceC205 difference raw5632; decide +kernel
    rw [ha]
    exact (canonical5632 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA205 + difference 0 3) (sourceB205 + difference 3 0) sourceC205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA205 + difference 0 3) (sourceB205 + difference 3 0) sourceC205) = raw5633 := by
      apply Matrix.ext; unfold tripleCharges sourceA205 sourceB205 sourceC205 difference raw5633; decide +kernel
    rw [ha]
    exact (canonical5633 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA205 + difference 0 4) (sourceB205 + difference 4 0) sourceC205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3899) := by
    have ha : (tripleCharges (sourceA205 + difference 0 4) (sourceB205 + difference 4 0) sourceC205) = raw5634 := by
      apply Matrix.ext; unfold tripleCharges sourceA205 sourceB205 sourceC205 difference raw5634; decide +kernel
    rw [ha]
    exact (canonical5634 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA205 + difference 0 5) (sourceB205 + difference 5 0) sourceC205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4025) := by
    have ha : (tripleCharges (sourceA205 + difference 0 5) (sourceB205 + difference 5 0) sourceC205) = raw5635 := by
      apply Matrix.ext; unfold tripleCharges sourceA205 sourceB205 sourceC205 difference raw5635; decide +kernel
    rw [ha]
    exact (canonical5635 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA205 + sourceB205) sourceC205) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA205 + sourceB205) sourceC205) = raw5636 := by
      apply Matrix.ext; unfold doubleCharges sourceA205 sourceB205 sourceC205 raw5636; decide +kernel
    rw [ha]
    exact (canonical5636 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA205 sourceB205 sourceC205
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm205, Integer.Sparse.eval]
  linarith only [hs]

def sourceA206 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB206 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC206 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceForm206 : Integer.Sparse Master := [(Sum.inr 1464, 3), (Sum.inr 1467, 1), (Sum.inr 1474, 1), (Sum.inr 3221, 1), (Sum.inr 4091, -1)]

theorem sourceEq206 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm206 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA206 + difference 0 0) (sourceB206 + difference 0 0) sourceC206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA206 + difference 0 0) (sourceB206 + difference 0 0) sourceC206) = raw5630 := by
      apply Matrix.ext; unfold tripleCharges sourceA206 sourceB206 sourceC206 difference raw5630; decide +kernel
    rw [ha]
    exact (canonical5630 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA206 + difference 1 0) (sourceB206 + difference 0 1) sourceC206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1464) := by
    have ha : (tripleCharges (sourceA206 + difference 1 0) (sourceB206 + difference 0 1) sourceC206) = raw5637 := by
      apply Matrix.ext; unfold tripleCharges sourceA206 sourceB206 sourceC206 difference raw5637; decide +kernel
    rw [ha]
    exact (canonical5637 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA206 + difference 2 0) (sourceB206 + difference 0 2) sourceC206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1464) := by
    have ha : (tripleCharges (sourceA206 + difference 2 0) (sourceB206 + difference 0 2) sourceC206) = raw5638 := by
      apply Matrix.ext; unfold tripleCharges sourceA206 sourceB206 sourceC206 difference raw5638; decide +kernel
    rw [ha]
    exact (canonical5638 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA206 + difference 3 0) (sourceB206 + difference 0 3) sourceC206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1464) := by
    have ha : (tripleCharges (sourceA206 + difference 3 0) (sourceB206 + difference 0 3) sourceC206) = raw5639 := by
      apply Matrix.ext; unfold tripleCharges sourceA206 sourceB206 sourceC206 difference raw5639; decide +kernel
    rw [ha]
    exact (canonical5639 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA206 + difference 4 0) (sourceB206 + difference 0 4) sourceC206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1467) := by
    have ha : (tripleCharges (sourceA206 + difference 4 0) (sourceB206 + difference 0 4) sourceC206) = raw5640 := by
      apply Matrix.ext; unfold tripleCharges sourceA206 sourceB206 sourceC206 difference raw5640; decide +kernel
    rw [ha]
    exact (canonical5640 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA206 + difference 5 0) (sourceB206 + difference 0 5) sourceC206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1474) := by
    have ha : (tripleCharges (sourceA206 + difference 5 0) (sourceB206 + difference 0 5) sourceC206) = raw5641 := by
      apply Matrix.ext; unfold tripleCharges sourceA206 sourceB206 sourceC206 difference raw5641; decide +kernel
    rw [ha]
    exact (canonical5641 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA206 + sourceB206) sourceC206) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA206 + sourceB206) sourceC206) = raw5636 := by
      apply Matrix.ext; unfold doubleCharges sourceA206 sourceB206 sourceC206 raw5636; decide +kernel
    rw [ha]
    exact (canonical5636 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA206 sourceB206 sourceC206
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm206, Integer.Sparse.eval]
  linarith only [hs]

def sourceA207 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB207 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC207 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceForm207 : Integer.Sparse Master := [(Sum.inr 1464, 1), (Sum.inr 3172, 1), (Sum.inr 3197, 1), (Sum.inr 3202, 2), (Sum.inr 3221, 1), (Sum.inr 4091, -1)]

theorem sourceEq207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm207 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA207 + difference 1 0) (sourceB207 + difference 0 1) sourceC207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1464) := by
    have ha : (tripleCharges (sourceA207 + difference 1 0) (sourceB207 + difference 0 1) sourceC207) = raw5637 := by
      apply Matrix.ext; unfold tripleCharges sourceA207 sourceB207 sourceC207 difference raw5637; decide +kernel
    rw [ha]
    exact (canonical5637 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA207 + difference 1 1) (sourceB207 + difference 1 1) sourceC207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA207 + difference 1 1) (sourceB207 + difference 1 1) sourceC207) = raw5630 := by
      apply Matrix.ext; unfold tripleCharges sourceA207 sourceB207 sourceC207 difference raw5630; decide +kernel
    rw [ha]
    exact (canonical5630 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA207 + difference 1 2) (sourceB207 + difference 2 1) sourceC207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA207 + difference 1 2) (sourceB207 + difference 2 1) sourceC207) = raw5642 := by
      apply Matrix.ext; unfold tripleCharges sourceA207 sourceB207 sourceC207 difference raw5642; decide +kernel
    rw [ha]
    exact (canonical5642 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA207 + difference 1 3) (sourceB207 + difference 3 1) sourceC207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA207 + difference 1 3) (sourceB207 + difference 3 1) sourceC207) = raw5643 := by
      apply Matrix.ext; unfold tripleCharges sourceA207 sourceB207 sourceC207 difference raw5643; decide +kernel
    rw [ha]
    exact (canonical5643 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA207 + difference 1 4) (sourceB207 + difference 4 1) sourceC207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA207 + difference 1 4) (sourceB207 + difference 4 1) sourceC207) = raw5644 := by
      apply Matrix.ext; unfold tripleCharges sourceA207 sourceB207 sourceC207 difference raw5644; decide +kernel
    rw [ha]
    exact (canonical5644 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA207 + difference 1 5) (sourceB207 + difference 5 1) sourceC207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3172) := by
    have ha : (tripleCharges (sourceA207 + difference 1 5) (sourceB207 + difference 5 1) sourceC207) = raw5645 := by
      apply Matrix.ext; unfold tripleCharges sourceA207 sourceB207 sourceC207 difference raw5645; decide +kernel
    rw [ha]
    exact (canonical5645 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA207 + sourceB207) sourceC207) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA207 + sourceB207) sourceC207) = raw5636 := by
      apply Matrix.ext; unfold doubleCharges sourceA207 sourceB207 sourceC207 raw5636; decide +kernel
    rw [ha]
    exact (canonical5636 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA207 sourceB207 sourceC207
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm207, Integer.Sparse.eval]
  linarith only [hs]

def sourceA208 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB208 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC208 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceForm208 : Integer.Sparse Master := [(Sum.inr 2471, 1), (Sum.inr 3199, 1), (Sum.inr 3202, 2), (Sum.inr 3221, 1), (Sum.inr 3801, 1), (Sum.inr 4091, -1)]

theorem sourceEq208 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm208 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA208 + difference 0 1) (sourceB208 + difference 1 0) sourceC208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA208 + difference 0 1) (sourceB208 + difference 1 0) sourceC208) = raw5631 := by
      apply Matrix.ext; unfold tripleCharges sourceA208 sourceB208 sourceC208 difference raw5631; decide +kernel
    rw [ha]
    exact (canonical5631 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA208 + difference 1 1) (sourceB208 + difference 1 1) sourceC208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA208 + difference 1 1) (sourceB208 + difference 1 1) sourceC208) = raw5630 := by
      apply Matrix.ext; unfold tripleCharges sourceA208 sourceB208 sourceC208 difference raw5630; decide +kernel
    rw [ha]
    exact (canonical5630 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA208 + difference 2 1) (sourceB208 + difference 1 2) sourceC208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA208 + difference 2 1) (sourceB208 + difference 1 2) sourceC208) = raw5646 := by
      apply Matrix.ext; unfold tripleCharges sourceA208 sourceB208 sourceC208 difference raw5646; decide +kernel
    rw [ha]
    exact (canonical5646 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA208 + difference 3 1) (sourceB208 + difference 1 3) sourceC208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA208 + difference 3 1) (sourceB208 + difference 1 3) sourceC208) = raw5647 := by
      apply Matrix.ext; unfold tripleCharges sourceA208 sourceB208 sourceC208 difference raw5647; decide +kernel
    rw [ha]
    exact (canonical5647 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA208 + difference 4 1) (sourceB208 + difference 1 4) sourceC208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA208 + difference 4 1) (sourceB208 + difference 1 4) sourceC208) = raw5648 := by
      apply Matrix.ext; unfold tripleCharges sourceA208 sourceB208 sourceC208 difference raw5648; decide +kernel
    rw [ha]
    exact (canonical5648 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA208 + difference 5 1) (sourceB208 + difference 1 5) sourceC208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA208 + difference 5 1) (sourceB208 + difference 1 5) sourceC208) = raw5649 := by
      apply Matrix.ext; unfold tripleCharges sourceA208 sourceB208 sourceC208 difference raw5649; decide +kernel
    rw [ha]
    exact (canonical5649 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA208 + sourceB208) sourceC208) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA208 + sourceB208) sourceC208) = raw5636 := by
      apply Matrix.ext; unfold doubleCharges sourceA208 sourceB208 sourceC208 raw5636; decide +kernel
    rw [ha]
    exact (canonical5636 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA208 sourceB208 sourceC208
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm208, Integer.Sparse.eval]
  linarith only [hs]

def sourceA209 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB209 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC209 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceForm209 : Integer.Sparse Master := [(Sum.inr 1467, 1), (Sum.inr 3179, 1), (Sum.inr 3199, 3), (Sum.inr 3221, 1), (Sum.inr 4091, -1)]

theorem sourceEq209 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm209 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA209 + difference 4 0) (sourceB209 + difference 0 4) sourceC209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1467) := by
    have ha : (tripleCharges (sourceA209 + difference 4 0) (sourceB209 + difference 0 4) sourceC209) = raw5640 := by
      apply Matrix.ext; unfold tripleCharges sourceA209 sourceB209 sourceC209 difference raw5640; decide +kernel
    rw [ha]
    exact (canonical5640 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA209 + difference 4 1) (sourceB209 + difference 1 4) sourceC209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA209 + difference 4 1) (sourceB209 + difference 1 4) sourceC209) = raw5648 := by
      apply Matrix.ext; unfold tripleCharges sourceA209 sourceB209 sourceC209 difference raw5648; decide +kernel
    rw [ha]
    exact (canonical5648 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA209 + difference 4 2) (sourceB209 + difference 2 4) sourceC209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA209 + difference 4 2) (sourceB209 + difference 2 4) sourceC209) = raw5650 := by
      apply Matrix.ext; unfold tripleCharges sourceA209 sourceB209 sourceC209 difference raw5650; decide +kernel
    rw [ha]
    exact (canonical5650 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA209 + difference 4 3) (sourceB209 + difference 3 4) sourceC209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA209 + difference 4 3) (sourceB209 + difference 3 4) sourceC209) = raw5651 := by
      apply Matrix.ext; unfold tripleCharges sourceA209 sourceB209 sourceC209 difference raw5651; decide +kernel
    rw [ha]
    exact (canonical5651 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA209 + difference 4 4) (sourceB209 + difference 4 4) sourceC209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA209 + difference 4 4) (sourceB209 + difference 4 4) sourceC209) = raw5630 := by
      apply Matrix.ext; unfold tripleCharges sourceA209 sourceB209 sourceC209 difference raw5630; decide +kernel
    rw [ha]
    exact (canonical5630 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA209 + difference 4 5) (sourceB209 + difference 5 4) sourceC209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3179) := by
    have ha : (tripleCharges (sourceA209 + difference 4 5) (sourceB209 + difference 5 4) sourceC209) = raw5652 := by
      apply Matrix.ext; unfold tripleCharges sourceA209 sourceB209 sourceC209 difference raw5652; decide +kernel
    rw [ha]
    exact (canonical5652 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA209 + sourceB209) sourceC209) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA209 + sourceB209) sourceC209) = raw5636 := by
      apply Matrix.ext; unfold doubleCharges sourceA209 sourceB209 sourceC209 raw5636; decide +kernel
    rw [ha]
    exact (canonical5636 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA209 sourceB209 sourceC209
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm209, Integer.Sparse.eval]
  linarith only [hs]

def sourceA210 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB210 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC210 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceForm210 : Integer.Sparse Master := [(Sum.inr 2707, 1), (Sum.inr 3197, 3), (Sum.inr 3221, 1), (Sum.inr 3899, 1), (Sum.inr 4091, -1)]

theorem sourceEq210 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm210 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA210 + difference 0 4) (sourceB210 + difference 4 0) sourceC210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3899) := by
    have ha : (tripleCharges (sourceA210 + difference 0 4) (sourceB210 + difference 4 0) sourceC210) = raw5634 := by
      apply Matrix.ext; unfold tripleCharges sourceA210 sourceB210 sourceC210 difference raw5634; decide +kernel
    rw [ha]
    exact (canonical5634 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA210 + difference 1 4) (sourceB210 + difference 4 1) sourceC210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA210 + difference 1 4) (sourceB210 + difference 4 1) sourceC210) = raw5644 := by
      apply Matrix.ext; unfold tripleCharges sourceA210 sourceB210 sourceC210 difference raw5644; decide +kernel
    rw [ha]
    exact (canonical5644 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA210 + difference 2 4) (sourceB210 + difference 4 2) sourceC210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA210 + difference 2 4) (sourceB210 + difference 4 2) sourceC210) = raw5653 := by
      apply Matrix.ext; unfold tripleCharges sourceA210 sourceB210 sourceC210 difference raw5653; decide +kernel
    rw [ha]
    exact (canonical5653 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA210 + difference 3 4) (sourceB210 + difference 4 3) sourceC210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA210 + difference 3 4) (sourceB210 + difference 4 3) sourceC210) = raw5654 := by
      apply Matrix.ext; unfold tripleCharges sourceA210 sourceB210 sourceC210 difference raw5654; decide +kernel
    rw [ha]
    exact (canonical5654 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA210 + difference 4 4) (sourceB210 + difference 4 4) sourceC210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA210 + difference 4 4) (sourceB210 + difference 4 4) sourceC210) = raw5630 := by
      apply Matrix.ext; unfold tripleCharges sourceA210 sourceB210 sourceC210 difference raw5630; decide +kernel
    rw [ha]
    exact (canonical5630 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA210 + difference 5 4) (sourceB210 + difference 4 5) sourceC210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2707) := by
    have ha : (tripleCharges (sourceA210 + difference 5 4) (sourceB210 + difference 4 5) sourceC210) = raw5655 := by
      apply Matrix.ext; unfold tripleCharges sourceA210 sourceB210 sourceC210 difference raw5655; decide +kernel
    rw [ha]
    exact (canonical5655 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA210 + sourceB210) sourceC210) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA210 + sourceB210) sourceC210) = raw5636 := by
      apply Matrix.ext; unfold doubleCharges sourceA210 sourceB210 sourceC210 raw5636; decide +kernel
    rw [ha]
    exact (canonical5636 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA210 sourceB210 sourceC210
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm210, Integer.Sparse.eval]
  linarith only [hs]

def sourceA211 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB211 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC211 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceForm211 : Integer.Sparse Master := [(Sum.inr 1474, 1), (Sum.inr 2471, 3), (Sum.inr 2707, 1), (Sum.inr 3221, 1), (Sum.inr 4091, -1)]

theorem sourceEq211 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm211 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA211 + difference 5 0) (sourceB211 + difference 0 5) sourceC211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1474) := by
    have ha : (tripleCharges (sourceA211 + difference 5 0) (sourceB211 + difference 0 5) sourceC211) = raw5641 := by
      apply Matrix.ext; unfold tripleCharges sourceA211 sourceB211 sourceC211 difference raw5641; decide +kernel
    rw [ha]
    exact (canonical5641 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA211 + difference 5 1) (sourceB211 + difference 1 5) sourceC211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA211 + difference 5 1) (sourceB211 + difference 1 5) sourceC211) = raw5649 := by
      apply Matrix.ext; unfold tripleCharges sourceA211 sourceB211 sourceC211 difference raw5649; decide +kernel
    rw [ha]
    exact (canonical5649 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA211 + difference 5 2) (sourceB211 + difference 2 5) sourceC211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA211 + difference 5 2) (sourceB211 + difference 2 5) sourceC211) = raw5656 := by
      apply Matrix.ext; unfold tripleCharges sourceA211 sourceB211 sourceC211 difference raw5656; decide +kernel
    rw [ha]
    exact (canonical5656 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA211 + difference 5 3) (sourceB211 + difference 3 5) sourceC211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA211 + difference 5 3) (sourceB211 + difference 3 5) sourceC211) = raw5657 := by
      apply Matrix.ext; unfold tripleCharges sourceA211 sourceB211 sourceC211 difference raw5657; decide +kernel
    rw [ha]
    exact (canonical5657 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA211 + difference 5 4) (sourceB211 + difference 4 5) sourceC211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2707) := by
    have ha : (tripleCharges (sourceA211 + difference 5 4) (sourceB211 + difference 4 5) sourceC211) = raw5655 := by
      apply Matrix.ext; unfold tripleCharges sourceA211 sourceB211 sourceC211 difference raw5655; decide +kernel
    rw [ha]
    exact (canonical5655 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA211 + difference 5 5) (sourceB211 + difference 5 5) sourceC211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA211 + difference 5 5) (sourceB211 + difference 5 5) sourceC211) = raw5630 := by
      apply Matrix.ext; unfold tripleCharges sourceA211 sourceB211 sourceC211 difference raw5630; decide +kernel
    rw [ha]
    exact (canonical5630 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA211 + sourceB211) sourceC211) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA211 + sourceB211) sourceC211) = raw5636 := by
      apply Matrix.ext; unfold doubleCharges sourceA211 sourceB211 sourceC211 raw5636; decide +kernel
    rw [ha]
    exact (canonical5636 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA211 sourceB211 sourceC211
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm211, Integer.Sparse.eval]
  linarith only [hs]

def sourceA212 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB212 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC212 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm212 : Integer.Sparse Master := [(Sum.inr 4446, 3), (Sum.inr 4455, 1), (Sum.inr 4473, 1), (Sum.inr 4857, 3), (Sum.inr 4863, 1), (Sum.inr 4876, 3), (Sum.inr 4878, 1), (Sum.inr 4888, 3), (Sum.inr 4889, 3), (Sum.inr 4891, 6), (Sum.inr 5097, 1), (Sum.inr 5277, 1), (Sum.inr 5284, 3)]

theorem sourceEq212 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm212 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA212 + difference 0 1) (sourceB212 + difference 1 0) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA212 + difference 0 1) (sourceB212 + difference 1 0) sourceC212) = raw5658 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5658; decide +kernel
    rw [ha]
    exact (canonical5658 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA212 + difference 0 2) (sourceB212 + difference 2 0) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA212 + difference 0 2) (sourceB212 + difference 2 0) sourceC212) = raw5659 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5659; decide +kernel
    rw [ha]
    exact (canonical5659 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA212 + difference 0 3) (sourceB212 + difference 3 0) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA212 + difference 0 3) (sourceB212 + difference 3 0) sourceC212) = raw5660 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5660; decide +kernel
    rw [ha]
    exact (canonical5660 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA212 + difference 0 4) (sourceB212 + difference 4 0) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5277) := by
    have ha : (tripleCharges (sourceA212 + difference 0 4) (sourceB212 + difference 4 0) sourceC212) = raw5661 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5661; decide +kernel
    rw [ha]
    exact (canonical5661 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA212 + difference 0 5) (sourceB212 + difference 5 0) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5097) := by
    have ha : (tripleCharges (sourceA212 + difference 0 5) (sourceB212 + difference 5 0) sourceC212) = raw5662 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5662; decide +kernel
    rw [ha]
    exact (canonical5662 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA212 + difference 1 0) (sourceB212 + difference 0 1) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4446) := by
    have ha : (tripleCharges (sourceA212 + difference 1 0) (sourceB212 + difference 0 1) sourceC212) = raw5663 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5663; decide +kernel
    rw [ha]
    exact (canonical5663 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA212 + difference 1 2) (sourceB212 + difference 2 1) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA212 + difference 1 2) (sourceB212 + difference 2 1) sourceC212) = raw5664 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5664; decide +kernel
    rw [ha]
    exact (canonical5664 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA212 + difference 1 3) (sourceB212 + difference 3 1) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA212 + difference 1 3) (sourceB212 + difference 3 1) sourceC212) = raw5665 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5665; decide +kernel
    rw [ha]
    exact (canonical5665 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA212 + difference 1 4) (sourceB212 + difference 4 1) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4857) := by
    have ha : (tripleCharges (sourceA212 + difference 1 4) (sourceB212 + difference 4 1) sourceC212) = raw5666 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5666; decide +kernel
    rw [ha]
    exact (canonical5666 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA212 + difference 1 5) (sourceB212 + difference 5 1) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4876) := by
    have ha : (tripleCharges (sourceA212 + difference 1 5) (sourceB212 + difference 5 1) sourceC212) = raw5667 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5667; decide +kernel
    rw [ha]
    exact (canonical5667 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA212 + difference 2 0) (sourceB212 + difference 0 2) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4446) := by
    have ha : (tripleCharges (sourceA212 + difference 2 0) (sourceB212 + difference 0 2) sourceC212) = raw5668 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5668; decide +kernel
    rw [ha]
    exact (canonical5668 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA212 + difference 2 1) (sourceB212 + difference 1 2) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA212 + difference 2 1) (sourceB212 + difference 1 2) sourceC212) = raw5669 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5669; decide +kernel
    rw [ha]
    exact (canonical5669 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA212 + difference 2 3) (sourceB212 + difference 3 2) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA212 + difference 2 3) (sourceB212 + difference 3 2) sourceC212) = raw5670 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5670; decide +kernel
    rw [ha]
    exact (canonical5670 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA212 + difference 2 4) (sourceB212 + difference 4 2) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4857) := by
    have ha : (tripleCharges (sourceA212 + difference 2 4) (sourceB212 + difference 4 2) sourceC212) = raw5671 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5671; decide +kernel
    rw [ha]
    exact (canonical5671 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA212 + difference 2 5) (sourceB212 + difference 5 2) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4876) := by
    have ha : (tripleCharges (sourceA212 + difference 2 5) (sourceB212 + difference 5 2) sourceC212) = raw5672 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5672; decide +kernel
    rw [ha]
    exact (canonical5672 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA212 + difference 3 0) (sourceB212 + difference 0 3) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4446) := by
    have ha : (tripleCharges (sourceA212 + difference 3 0) (sourceB212 + difference 0 3) sourceC212) = raw5673 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5673; decide +kernel
    rw [ha]
    exact (canonical5673 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA212 + difference 3 1) (sourceB212 + difference 1 3) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA212 + difference 3 1) (sourceB212 + difference 1 3) sourceC212) = raw5674 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5674; decide +kernel
    rw [ha]
    exact (canonical5674 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA212 + difference 3 2) (sourceB212 + difference 2 3) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA212 + difference 3 2) (sourceB212 + difference 2 3) sourceC212) = raw5675 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5675; decide +kernel
    rw [ha]
    exact (canonical5675 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA212 + difference 3 4) (sourceB212 + difference 4 3) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4857) := by
    have ha : (tripleCharges (sourceA212 + difference 3 4) (sourceB212 + difference 4 3) sourceC212) = raw5676 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5676; decide +kernel
    rw [ha]
    exact (canonical5676 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA212 + difference 3 5) (sourceB212 + difference 5 3) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4876) := by
    have ha : (tripleCharges (sourceA212 + difference 3 5) (sourceB212 + difference 5 3) sourceC212) = raw5677 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5677; decide +kernel
    rw [ha]
    exact (canonical5677 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA212 + difference 4 0) (sourceB212 + difference 0 4) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4473) := by
    have ha : (tripleCharges (sourceA212 + difference 4 0) (sourceB212 + difference 0 4) sourceC212) = raw5678 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5678; decide +kernel
    rw [ha]
    exact (canonical5678 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA212 + difference 4 1) (sourceB212 + difference 1 4) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA212 + difference 4 1) (sourceB212 + difference 1 4) sourceC212) = raw5679 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5679; decide +kernel
    rw [ha]
    exact (canonical5679 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA212 + difference 4 2) (sourceB212 + difference 2 4) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA212 + difference 4 2) (sourceB212 + difference 2 4) sourceC212) = raw5680 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5680; decide +kernel
    rw [ha]
    exact (canonical5680 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA212 + difference 4 3) (sourceB212 + difference 3 4) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA212 + difference 4 3) (sourceB212 + difference 3 4) sourceC212) = raw5681 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5681; decide +kernel
    rw [ha]
    exact (canonical5681 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA212 + difference 4 5) (sourceB212 + difference 5 4) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4878) := by
    have ha : (tripleCharges (sourceA212 + difference 4 5) (sourceB212 + difference 5 4) sourceC212) = raw5682 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5682; decide +kernel
    rw [ha]
    exact (canonical5682 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA212 + difference 5 0) (sourceB212 + difference 0 5) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4455) := by
    have ha : (tripleCharges (sourceA212 + difference 5 0) (sourceB212 + difference 0 5) sourceC212) = raw5683 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5683; decide +kernel
    rw [ha]
    exact (canonical5683 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA212 + difference 5 1) (sourceB212 + difference 1 5) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA212 + difference 5 1) (sourceB212 + difference 1 5) sourceC212) = raw5684 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5684; decide +kernel
    rw [ha]
    exact (canonical5684 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA212 + difference 5 2) (sourceB212 + difference 2 5) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA212 + difference 5 2) (sourceB212 + difference 2 5) sourceC212) = raw5685 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5685; decide +kernel
    rw [ha]
    exact (canonical5685 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA212 + difference 5 3) (sourceB212 + difference 3 5) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA212 + difference 5 3) (sourceB212 + difference 3 5) sourceC212) = raw5686 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5686; decide +kernel
    rw [ha]
    exact (canonical5686 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA212 + difference 5 4) (sourceB212 + difference 4 5) sourceC212) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4863) := by
    have ha : (tripleCharges (sourceA212 + difference 5 4) (sourceB212 + difference 4 5) sourceC212) = raw5687 := by
      apply Matrix.ext; unfold tripleCharges sourceA212 sourceB212 sourceC212 difference raw5687; decide +kernel
    rw [ha]
    exact (canonical5687 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA212 sourceB212 sourceC212
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm212, Integer.Sparse.eval]
  linarith only [hs]

def sourceA213 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB213 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC213 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm213 : Integer.Sparse Master := [(Sum.inr 1698, 1), (Sum.inr 1699, 1), (Sum.inr 1701, 3), (Sum.inr 2232, 1), (Sum.inr 2234, 1), (Sum.inr 2236, 3), (Sum.inr 2237, 3), (Sum.inr 2244, 3), (Sum.inr 2245, 3), (Sum.inr 2253, 6), (Sum.inr 2745, 1), (Sum.inr 2746, 1), (Sum.inr 2753, 3)]

theorem sourceEq213 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm213 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA213 + difference 0 1) (sourceB213 + difference 1 0) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA213 + difference 0 1) (sourceB213 + difference 1 0) sourceC213) = raw5688 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5688; decide +kernel
    rw [ha]
    exact (canonical5688 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA213 + difference 0 2) (sourceB213 + difference 2 0) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA213 + difference 0 2) (sourceB213 + difference 2 0) sourceC213) = raw5689 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5689; decide +kernel
    rw [ha]
    exact (canonical5689 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA213 + difference 0 3) (sourceB213 + difference 3 0) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA213 + difference 0 3) (sourceB213 + difference 3 0) sourceC213) = raw5690 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5690; decide +kernel
    rw [ha]
    exact (canonical5690 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA213 + difference 0 4) (sourceB213 + difference 4 0) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2745) := by
    have ha : (tripleCharges (sourceA213 + difference 0 4) (sourceB213 + difference 4 0) sourceC213) = raw5691 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5691; decide +kernel
    rw [ha]
    exact (canonical5691 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA213 + difference 0 5) (sourceB213 + difference 5 0) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2746) := by
    have ha : (tripleCharges (sourceA213 + difference 0 5) (sourceB213 + difference 5 0) sourceC213) = raw5692 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5692; decide +kernel
    rw [ha]
    exact (canonical5692 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA213 + difference 1 0) (sourceB213 + difference 0 1) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1701) := by
    have ha : (tripleCharges (sourceA213 + difference 1 0) (sourceB213 + difference 0 1) sourceC213) = raw5693 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5693; decide +kernel
    rw [ha]
    exact (canonical5693 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA213 + difference 1 2) (sourceB213 + difference 2 1) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA213 + difference 1 2) (sourceB213 + difference 2 1) sourceC213) = raw5694 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5694; decide +kernel
    rw [ha]
    exact (canonical5694 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA213 + difference 1 3) (sourceB213 + difference 3 1) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA213 + difference 1 3) (sourceB213 + difference 3 1) sourceC213) = raw5695 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5695; decide +kernel
    rw [ha]
    exact (canonical5695 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA213 + difference 1 4) (sourceB213 + difference 4 1) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2236) := by
    have ha : (tripleCharges (sourceA213 + difference 1 4) (sourceB213 + difference 4 1) sourceC213) = raw5696 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5696; decide +kernel
    rw [ha]
    exact (canonical5696 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA213 + difference 1 5) (sourceB213 + difference 5 1) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2237) := by
    have ha : (tripleCharges (sourceA213 + difference 1 5) (sourceB213 + difference 5 1) sourceC213) = raw5697 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5697; decide +kernel
    rw [ha]
    exact (canonical5697 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA213 + difference 2 0) (sourceB213 + difference 0 2) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1701) := by
    have ha : (tripleCharges (sourceA213 + difference 2 0) (sourceB213 + difference 0 2) sourceC213) = raw5698 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5698; decide +kernel
    rw [ha]
    exact (canonical5698 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA213 + difference 2 1) (sourceB213 + difference 1 2) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA213 + difference 2 1) (sourceB213 + difference 1 2) sourceC213) = raw5699 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5699; decide +kernel
    rw [ha]
    exact (canonical5699 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA213 + difference 2 3) (sourceB213 + difference 3 2) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA213 + difference 2 3) (sourceB213 + difference 3 2) sourceC213) = raw5700 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5700; decide +kernel
    rw [ha]
    exact (canonical5700 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA213 + difference 2 4) (sourceB213 + difference 4 2) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2236) := by
    have ha : (tripleCharges (sourceA213 + difference 2 4) (sourceB213 + difference 4 2) sourceC213) = raw5701 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5701; decide +kernel
    rw [ha]
    exact (canonical5701 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA213 + difference 2 5) (sourceB213 + difference 5 2) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2237) := by
    have ha : (tripleCharges (sourceA213 + difference 2 5) (sourceB213 + difference 5 2) sourceC213) = raw5702 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5702; decide +kernel
    rw [ha]
    exact (canonical5702 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA213 + difference 3 0) (sourceB213 + difference 0 3) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1701) := by
    have ha : (tripleCharges (sourceA213 + difference 3 0) (sourceB213 + difference 0 3) sourceC213) = raw5703 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5703; decide +kernel
    rw [ha]
    exact (canonical5703 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA213 + difference 3 1) (sourceB213 + difference 1 3) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA213 + difference 3 1) (sourceB213 + difference 1 3) sourceC213) = raw5704 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5704; decide +kernel
    rw [ha]
    exact (canonical5704 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA213 + difference 3 2) (sourceB213 + difference 2 3) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA213 + difference 3 2) (sourceB213 + difference 2 3) sourceC213) = raw5705 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5705; decide +kernel
    rw [ha]
    exact (canonical5705 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA213 + difference 3 4) (sourceB213 + difference 4 3) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2236) := by
    have ha : (tripleCharges (sourceA213 + difference 3 4) (sourceB213 + difference 4 3) sourceC213) = raw5706 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5706; decide +kernel
    rw [ha]
    exact (canonical5706 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA213 + difference 3 5) (sourceB213 + difference 5 3) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2237) := by
    have ha : (tripleCharges (sourceA213 + difference 3 5) (sourceB213 + difference 5 3) sourceC213) = raw5707 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5707; decide +kernel
    rw [ha]
    exact (canonical5707 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA213 + difference 4 0) (sourceB213 + difference 0 4) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1699) := by
    have ha : (tripleCharges (sourceA213 + difference 4 0) (sourceB213 + difference 0 4) sourceC213) = raw5708 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5708; decide +kernel
    rw [ha]
    exact (canonical5708 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA213 + difference 4 1) (sourceB213 + difference 1 4) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA213 + difference 4 1) (sourceB213 + difference 1 4) sourceC213) = raw5709 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5709; decide +kernel
    rw [ha]
    exact (canonical5709 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA213 + difference 4 2) (sourceB213 + difference 2 4) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA213 + difference 4 2) (sourceB213 + difference 2 4) sourceC213) = raw5710 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5710; decide +kernel
    rw [ha]
    exact (canonical5710 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA213 + difference 4 3) (sourceB213 + difference 3 4) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2245) := by
    have ha : (tripleCharges (sourceA213 + difference 4 3) (sourceB213 + difference 3 4) sourceC213) = raw5711 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5711; decide +kernel
    rw [ha]
    exact (canonical5711 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA213 + difference 4 5) (sourceB213 + difference 5 4) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2234) := by
    have ha : (tripleCharges (sourceA213 + difference 4 5) (sourceB213 + difference 5 4) sourceC213) = raw5712 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5712; decide +kernel
    rw [ha]
    exact (canonical5712 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA213 + difference 5 0) (sourceB213 + difference 0 5) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1698) := by
    have ha : (tripleCharges (sourceA213 + difference 5 0) (sourceB213 + difference 0 5) sourceC213) = raw5713 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5713; decide +kernel
    rw [ha]
    exact (canonical5713 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA213 + difference 5 1) (sourceB213 + difference 1 5) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA213 + difference 5 1) (sourceB213 + difference 1 5) sourceC213) = raw5714 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5714; decide +kernel
    rw [ha]
    exact (canonical5714 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA213 + difference 5 2) (sourceB213 + difference 2 5) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA213 + difference 5 2) (sourceB213 + difference 2 5) sourceC213) = raw5715 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5715; decide +kernel
    rw [ha]
    exact (canonical5715 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA213 + difference 5 3) (sourceB213 + difference 3 5) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2244) := by
    have ha : (tripleCharges (sourceA213 + difference 5 3) (sourceB213 + difference 3 5) sourceC213) = raw5716 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5716; decide +kernel
    rw [ha]
    exact (canonical5716 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA213 + difference 5 4) (sourceB213 + difference 4 5) sourceC213) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2232) := by
    have ha : (tripleCharges (sourceA213 + difference 5 4) (sourceB213 + difference 4 5) sourceC213) = raw5717 := by
      apply Matrix.ext; unfold tripleCharges sourceA213 sourceB213 sourceC213 difference raw5717; decide +kernel
    rw [ha]
    exact (canonical5717 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA213 sourceB213 sourceC213
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm213, Integer.Sparse.eval]
  linarith only [hs]

def sourceA214 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB214 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC214 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm214 : Integer.Sparse Master := [(Sum.inr 1354, 3), (Sum.inr 1366, 1), (Sum.inr 1405, 1), (Sum.inr 3058, 1), (Sum.inr 3059, 1), (Sum.inr 3077, 3), (Sum.inr 3146, 3), (Sum.inr 3155, 1), (Sum.inr 3165, 3), (Sum.inr 3179, 1), (Sum.inr 3222, 6), (Sum.inr 3223, 3), (Sum.inr 3227, 3)]

theorem sourceEq214 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm214 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA214 + difference 0 1) (sourceB214 + difference 1 0) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA214 + difference 0 1) (sourceB214 + difference 1 0) sourceC214) = raw5718 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5718; decide +kernel
    rw [ha]
    exact (canonical5718 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA214 + difference 0 2) (sourceB214 + difference 2 0) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA214 + difference 0 2) (sourceB214 + difference 2 0) sourceC214) = raw5719 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5719; decide +kernel
    rw [ha]
    exact (canonical5719 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA214 + difference 0 3) (sourceB214 + difference 3 0) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA214 + difference 0 3) (sourceB214 + difference 3 0) sourceC214) = raw5720 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5720; decide +kernel
    rw [ha]
    exact (canonical5720 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA214 + difference 0 4) (sourceB214 + difference 4 0) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3059) := by
    have ha : (tripleCharges (sourceA214 + difference 0 4) (sourceB214 + difference 4 0) sourceC214) = raw5721 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5721; decide +kernel
    rw [ha]
    exact (canonical5721 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA214 + difference 0 5) (sourceB214 + difference 5 0) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3058) := by
    have ha : (tripleCharges (sourceA214 + difference 0 5) (sourceB214 + difference 5 0) sourceC214) = raw5722 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5722; decide +kernel
    rw [ha]
    exact (canonical5722 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA214 + difference 1 0) (sourceB214 + difference 0 1) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1354) := by
    have ha : (tripleCharges (sourceA214 + difference 1 0) (sourceB214 + difference 0 1) sourceC214) = raw5723 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5723; decide +kernel
    rw [ha]
    exact (canonical5723 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA214 + difference 1 2) (sourceB214 + difference 2 1) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA214 + difference 1 2) (sourceB214 + difference 2 1) sourceC214) = raw5724 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5724; decide +kernel
    rw [ha]
    exact (canonical5724 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA214 + difference 1 3) (sourceB214 + difference 3 1) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA214 + difference 1 3) (sourceB214 + difference 3 1) sourceC214) = raw5725 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5725; decide +kernel
    rw [ha]
    exact (canonical5725 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA214 + difference 1 4) (sourceB214 + difference 4 1) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3165) := by
    have ha : (tripleCharges (sourceA214 + difference 1 4) (sourceB214 + difference 4 1) sourceC214) = raw5726 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5726; decide +kernel
    rw [ha]
    exact (canonical5726 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA214 + difference 1 5) (sourceB214 + difference 5 1) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3146) := by
    have ha : (tripleCharges (sourceA214 + difference 1 5) (sourceB214 + difference 5 1) sourceC214) = raw5727 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5727; decide +kernel
    rw [ha]
    exact (canonical5727 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA214 + difference 2 0) (sourceB214 + difference 0 2) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1354) := by
    have ha : (tripleCharges (sourceA214 + difference 2 0) (sourceB214 + difference 0 2) sourceC214) = raw5728 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5728; decide +kernel
    rw [ha]
    exact (canonical5728 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA214 + difference 2 1) (sourceB214 + difference 1 2) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA214 + difference 2 1) (sourceB214 + difference 1 2) sourceC214) = raw5729 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5729; decide +kernel
    rw [ha]
    exact (canonical5729 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA214 + difference 2 3) (sourceB214 + difference 3 2) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA214 + difference 2 3) (sourceB214 + difference 3 2) sourceC214) = raw5730 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5730; decide +kernel
    rw [ha]
    exact (canonical5730 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA214 + difference 2 4) (sourceB214 + difference 4 2) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3165) := by
    have ha : (tripleCharges (sourceA214 + difference 2 4) (sourceB214 + difference 4 2) sourceC214) = raw5731 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5731; decide +kernel
    rw [ha]
    exact (canonical5731 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA214 + difference 2 5) (sourceB214 + difference 5 2) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3146) := by
    have ha : (tripleCharges (sourceA214 + difference 2 5) (sourceB214 + difference 5 2) sourceC214) = raw5732 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5732; decide +kernel
    rw [ha]
    exact (canonical5732 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA214 + difference 3 0) (sourceB214 + difference 0 3) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1354) := by
    have ha : (tripleCharges (sourceA214 + difference 3 0) (sourceB214 + difference 0 3) sourceC214) = raw5733 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5733; decide +kernel
    rw [ha]
    exact (canonical5733 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA214 + difference 3 1) (sourceB214 + difference 1 3) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA214 + difference 3 1) (sourceB214 + difference 1 3) sourceC214) = raw5734 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5734; decide +kernel
    rw [ha]
    exact (canonical5734 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA214 + difference 3 2) (sourceB214 + difference 2 3) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3222) := by
    have ha : (tripleCharges (sourceA214 + difference 3 2) (sourceB214 + difference 2 3) sourceC214) = raw5735 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5735; decide +kernel
    rw [ha]
    exact (canonical5735 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA214 + difference 3 4) (sourceB214 + difference 4 3) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3165) := by
    have ha : (tripleCharges (sourceA214 + difference 3 4) (sourceB214 + difference 4 3) sourceC214) = raw5736 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5736; decide +kernel
    rw [ha]
    exact (canonical5736 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA214 + difference 3 5) (sourceB214 + difference 5 3) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3146) := by
    have ha : (tripleCharges (sourceA214 + difference 3 5) (sourceB214 + difference 5 3) sourceC214) = raw5737 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5737; decide +kernel
    rw [ha]
    exact (canonical5737 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA214 + difference 4 0) (sourceB214 + difference 0 4) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1366) := by
    have ha : (tripleCharges (sourceA214 + difference 4 0) (sourceB214 + difference 0 4) sourceC214) = raw5738 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5738; decide +kernel
    rw [ha]
    exact (canonical5738 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA214 + difference 4 1) (sourceB214 + difference 1 4) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA214 + difference 4 1) (sourceB214 + difference 1 4) sourceC214) = raw5739 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5739; decide +kernel
    rw [ha]
    exact (canonical5739 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA214 + difference 4 2) (sourceB214 + difference 2 4) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA214 + difference 4 2) (sourceB214 + difference 2 4) sourceC214) = raw5740 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5740; decide +kernel
    rw [ha]
    exact (canonical5740 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA214 + difference 4 3) (sourceB214 + difference 3 4) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3223) := by
    have ha : (tripleCharges (sourceA214 + difference 4 3) (sourceB214 + difference 3 4) sourceC214) = raw5741 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5741; decide +kernel
    rw [ha]
    exact (canonical5741 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA214 + difference 4 5) (sourceB214 + difference 5 4) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3155) := by
    have ha : (tripleCharges (sourceA214 + difference 4 5) (sourceB214 + difference 5 4) sourceC214) = raw5742 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5742; decide +kernel
    rw [ha]
    exact (canonical5742 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA214 + difference 5 0) (sourceB214 + difference 0 5) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1405) := by
    have ha : (tripleCharges (sourceA214 + difference 5 0) (sourceB214 + difference 0 5) sourceC214) = raw5743 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5743; decide +kernel
    rw [ha]
    exact (canonical5743 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA214 + difference 5 1) (sourceB214 + difference 1 5) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA214 + difference 5 1) (sourceB214 + difference 1 5) sourceC214) = raw5744 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5744; decide +kernel
    rw [ha]
    exact (canonical5744 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA214 + difference 5 2) (sourceB214 + difference 2 5) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA214 + difference 5 2) (sourceB214 + difference 2 5) sourceC214) = raw5745 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5745; decide +kernel
    rw [ha]
    exact (canonical5745 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA214 + difference 5 3) (sourceB214 + difference 3 5) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA214 + difference 5 3) (sourceB214 + difference 3 5) sourceC214) = raw5746 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5746; decide +kernel
    rw [ha]
    exact (canonical5746 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA214 + difference 5 4) (sourceB214 + difference 4 5) sourceC214) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3179) := by
    have ha : (tripleCharges (sourceA214 + difference 5 4) (sourceB214 + difference 4 5) sourceC214) = raw5747 := by
      apply Matrix.ext; unfold tripleCharges sourceA214 sourceB214 sourceC214 difference raw5747; decide +kernel
    rw [ha]
    exact (canonical5747 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA214 sourceB214 sourceC214
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm214, Integer.Sparse.eval]
  linarith only [hs]

def sourceA215 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB215 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC215 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm215 : Integer.Sparse Master := [(Sum.inr 2252, 1), (Sum.inr 2507, 1), (Sum.inr 3576, 1), (Sum.inr 3625, 3), (Sum.inr 4084, -1)]

theorem sourceEq215 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm215 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA215 + difference 0 0) (sourceB215 + difference 0 0) sourceC215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2252) := by
    have ha : (tripleCharges (sourceA215 + difference 0 0) (sourceB215 + difference 0 0) sourceC215) = raw5748 := by
      apply Matrix.ext; unfold tripleCharges sourceA215 sourceB215 sourceC215 difference raw5748; decide +kernel
    rw [ha]
    exact (canonical5748 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA215 + difference 0 1) (sourceB215 + difference 1 0) sourceC215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA215 + difference 0 1) (sourceB215 + difference 1 0) sourceC215) = raw5749 := by
      apply Matrix.ext; unfold tripleCharges sourceA215 sourceB215 sourceC215 difference raw5749; decide +kernel
    rw [ha]
    exact (canonical5749 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA215 + difference 0 2) (sourceB215 + difference 2 0) sourceC215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA215 + difference 0 2) (sourceB215 + difference 2 0) sourceC215) = raw5750 := by
      apply Matrix.ext; unfold tripleCharges sourceA215 sourceB215 sourceC215 difference raw5750; decide +kernel
    rw [ha]
    exact (canonical5750 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA215 + difference 0 3) (sourceB215 + difference 3 0) sourceC215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA215 + difference 0 3) (sourceB215 + difference 3 0) sourceC215) = raw5751 := by
      apply Matrix.ext; unfold tripleCharges sourceA215 sourceB215 sourceC215 difference raw5751; decide +kernel
    rw [ha]
    exact (canonical5751 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA215 + difference 0 4) (sourceB215 + difference 4 0) sourceC215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3576) := by
    have ha : (tripleCharges (sourceA215 + difference 0 4) (sourceB215 + difference 4 0) sourceC215) = raw5752 := by
      apply Matrix.ext; unfold tripleCharges sourceA215 sourceB215 sourceC215 difference raw5752; decide +kernel
    rw [ha]
    exact (canonical5752 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA215 + difference 0 5) (sourceB215 + difference 5 0) sourceC215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2507) := by
    have ha : (tripleCharges (sourceA215 + difference 0 5) (sourceB215 + difference 5 0) sourceC215) = raw5753 := by
      apply Matrix.ext; unfold tripleCharges sourceA215 sourceB215 sourceC215 difference raw5753; decide +kernel
    rw [ha]
    exact (canonical5753 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA215 + sourceB215) sourceC215) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA215 + sourceB215) sourceC215) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA215 sourceB215 sourceC215 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA215 sourceB215 sourceC215
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm215, Integer.Sparse.eval]
  linarith only [hs]

def sourceA216 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB216 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC216 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm216 : Integer.Sparse Master := [(Sum.inr 1028, 3), (Sum.inr 1038, 1), (Sum.inr 1056, 1), (Sum.inr 2252, 1), (Sum.inr 4084, -1)]

theorem sourceEq216 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm216 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA216 + difference 0 0) (sourceB216 + difference 0 0) sourceC216) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2252) := by
    have ha : (tripleCharges (sourceA216 + difference 0 0) (sourceB216 + difference 0 0) sourceC216) = raw5748 := by
      apply Matrix.ext; unfold tripleCharges sourceA216 sourceB216 sourceC216 difference raw5748; decide +kernel
    rw [ha]
    exact (canonical5748 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA216 + difference 1 0) (sourceB216 + difference 0 1) sourceC216) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1028) := by
    have ha : (tripleCharges (sourceA216 + difference 1 0) (sourceB216 + difference 0 1) sourceC216) = raw5755 := by
      apply Matrix.ext; unfold tripleCharges sourceA216 sourceB216 sourceC216 difference raw5755; decide +kernel
    rw [ha]
    exact (canonical5755 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA216 + difference 2 0) (sourceB216 + difference 0 2) sourceC216) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1028) := by
    have ha : (tripleCharges (sourceA216 + difference 2 0) (sourceB216 + difference 0 2) sourceC216) = raw5756 := by
      apply Matrix.ext; unfold tripleCharges sourceA216 sourceB216 sourceC216 difference raw5756; decide +kernel
    rw [ha]
    exact (canonical5756 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA216 + difference 3 0) (sourceB216 + difference 0 3) sourceC216) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1028) := by
    have ha : (tripleCharges (sourceA216 + difference 3 0) (sourceB216 + difference 0 3) sourceC216) = raw5757 := by
      apply Matrix.ext; unfold tripleCharges sourceA216 sourceB216 sourceC216 difference raw5757; decide +kernel
    rw [ha]
    exact (canonical5757 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA216 + difference 4 0) (sourceB216 + difference 0 4) sourceC216) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1056) := by
    have ha : (tripleCharges (sourceA216 + difference 4 0) (sourceB216 + difference 0 4) sourceC216) = raw5758 := by
      apply Matrix.ext; unfold tripleCharges sourceA216 sourceB216 sourceC216 difference raw5758; decide +kernel
    rw [ha]
    exact (canonical5758 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA216 + difference 5 0) (sourceB216 + difference 0 5) sourceC216) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1038) := by
    have ha : (tripleCharges (sourceA216 + difference 5 0) (sourceB216 + difference 0 5) sourceC216) = raw5759 := by
      apply Matrix.ext; unfold tripleCharges sourceA216 sourceB216 sourceC216 difference raw5759; decide +kernel
    rw [ha]
    exact (canonical5759 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA216 + sourceB216) sourceC216) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA216 + sourceB216) sourceC216) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA216 sourceB216 sourceC216 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA216 sourceB216 sourceC216
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm216, Integer.Sparse.eval]
  linarith only [hs]

def sourceA217 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB217 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC217 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm217 : Integer.Sparse Master := [(Sum.inr 1056, 1), (Sum.inr 2131, 1), (Sum.inr 2252, 1), (Sum.inr 2277, 3), (Sum.inr 4084, -1)]

theorem sourceEq217 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm217 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA217 + difference 4 0) (sourceB217 + difference 0 4) sourceC217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1056) := by
    have ha : (tripleCharges (sourceA217 + difference 4 0) (sourceB217 + difference 0 4) sourceC217) = raw5758 := by
      apply Matrix.ext; unfold tripleCharges sourceA217 sourceB217 sourceC217 difference raw5758; decide +kernel
    rw [ha]
    exact (canonical5758 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA217 + difference 4 1) (sourceB217 + difference 1 4) sourceC217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA217 + difference 4 1) (sourceB217 + difference 1 4) sourceC217) = raw5760 := by
      apply Matrix.ext; unfold tripleCharges sourceA217 sourceB217 sourceC217 difference raw5760; decide +kernel
    rw [ha]
    exact (canonical5760 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA217 + difference 4 2) (sourceB217 + difference 2 4) sourceC217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA217 + difference 4 2) (sourceB217 + difference 2 4) sourceC217) = raw5761 := by
      apply Matrix.ext; unfold tripleCharges sourceA217 sourceB217 sourceC217 difference raw5761; decide +kernel
    rw [ha]
    exact (canonical5761 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA217 + difference 4 3) (sourceB217 + difference 3 4) sourceC217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA217 + difference 4 3) (sourceB217 + difference 3 4) sourceC217) = raw5762 := by
      apply Matrix.ext; unfold tripleCharges sourceA217 sourceB217 sourceC217 difference raw5762; decide +kernel
    rw [ha]
    exact (canonical5762 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA217 + difference 4 4) (sourceB217 + difference 4 4) sourceC217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2252) := by
    have ha : (tripleCharges (sourceA217 + difference 4 4) (sourceB217 + difference 4 4) sourceC217) = raw5748 := by
      apply Matrix.ext; unfold tripleCharges sourceA217 sourceB217 sourceC217 difference raw5748; decide +kernel
    rw [ha]
    exact (canonical5748 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA217 + difference 4 5) (sourceB217 + difference 5 4) sourceC217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2131) := by
    have ha : (tripleCharges (sourceA217 + difference 4 5) (sourceB217 + difference 5 4) sourceC217) = raw5763 := by
      apply Matrix.ext; unfold tripleCharges sourceA217 sourceB217 sourceC217 difference raw5763; decide +kernel
    rw [ha]
    exact (canonical5763 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA217 + sourceB217) sourceC217) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA217 + sourceB217) sourceC217) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA217 sourceB217 sourceC217 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA217 sourceB217 sourceC217
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm217, Integer.Sparse.eval]
  linarith only [hs]

def sourceA218 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB218 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC218 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm218 : Integer.Sparse Master := [(Sum.inr 2095, 3), (Sum.inr 2104, 1), (Sum.inr 2252, 1), (Sum.inr 3576, 1), (Sum.inr 4084, -1)]

theorem sourceEq218 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm218 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA218 + difference 0 4) (sourceB218 + difference 4 0) sourceC218) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3576) := by
    have ha : (tripleCharges (sourceA218 + difference 0 4) (sourceB218 + difference 4 0) sourceC218) = raw5752 := by
      apply Matrix.ext; unfold tripleCharges sourceA218 sourceB218 sourceC218 difference raw5752; decide +kernel
    rw [ha]
    exact (canonical5752 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA218 + difference 1 4) (sourceB218 + difference 4 1) sourceC218) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2095) := by
    have ha : (tripleCharges (sourceA218 + difference 1 4) (sourceB218 + difference 4 1) sourceC218) = raw5764 := by
      apply Matrix.ext; unfold tripleCharges sourceA218 sourceB218 sourceC218 difference raw5764; decide +kernel
    rw [ha]
    exact (canonical5764 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA218 + difference 2 4) (sourceB218 + difference 4 2) sourceC218) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2095) := by
    have ha : (tripleCharges (sourceA218 + difference 2 4) (sourceB218 + difference 4 2) sourceC218) = raw5765 := by
      apply Matrix.ext; unfold tripleCharges sourceA218 sourceB218 sourceC218 difference raw5765; decide +kernel
    rw [ha]
    exact (canonical5765 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA218 + difference 3 4) (sourceB218 + difference 4 3) sourceC218) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2095) := by
    have ha : (tripleCharges (sourceA218 + difference 3 4) (sourceB218 + difference 4 3) sourceC218) = raw5766 := by
      apply Matrix.ext; unfold tripleCharges sourceA218 sourceB218 sourceC218 difference raw5766; decide +kernel
    rw [ha]
    exact (canonical5766 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA218 + difference 4 4) (sourceB218 + difference 4 4) sourceC218) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2252) := by
    have ha : (tripleCharges (sourceA218 + difference 4 4) (sourceB218 + difference 4 4) sourceC218) = raw5748 := by
      apply Matrix.ext; unfold tripleCharges sourceA218 sourceB218 sourceC218 difference raw5748; decide +kernel
    rw [ha]
    exact (canonical5748 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA218 + difference 5 4) (sourceB218 + difference 4 5) sourceC218) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2104) := by
    have ha : (tripleCharges (sourceA218 + difference 5 4) (sourceB218 + difference 4 5) sourceC218) = raw5767 := by
      apply Matrix.ext; unfold tripleCharges sourceA218 sourceB218 sourceC218 difference raw5767; decide +kernel
    rw [ha]
    exact (canonical5767 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA218 + sourceB218) sourceC218) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA218 + sourceB218) sourceC218) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA218 sourceB218 sourceC218 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA218 sourceB218 sourceC218
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm218, Integer.Sparse.eval]
  linarith only [hs]

def sourceA219 : Charge := ![0, 1, 1, 1, -1, -2]
def sourceB219 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC219 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceForm219 : Integer.Sparse Master := [(Sum.inr 1038, 1), (Sum.inr 2104, 1), (Sum.inr 2252, 1), (Sum.inr 2262, 3), (Sum.inr 4084, -1)]

theorem sourceEq219 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm219 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA219 + difference 5 0) (sourceB219 + difference 0 5) sourceC219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1038) := by
    have ha : (tripleCharges (sourceA219 + difference 5 0) (sourceB219 + difference 0 5) sourceC219) = raw5759 := by
      apply Matrix.ext; unfold tripleCharges sourceA219 sourceB219 sourceC219 difference raw5759; decide +kernel
    rw [ha]
    exact (canonical5759 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA219 + difference 5 1) (sourceB219 + difference 1 5) sourceC219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA219 + difference 5 1) (sourceB219 + difference 1 5) sourceC219) = raw5768 := by
      apply Matrix.ext; unfold tripleCharges sourceA219 sourceB219 sourceC219 difference raw5768; decide +kernel
    rw [ha]
    exact (canonical5768 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA219 + difference 5 2) (sourceB219 + difference 2 5) sourceC219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA219 + difference 5 2) (sourceB219 + difference 2 5) sourceC219) = raw5769 := by
      apply Matrix.ext; unfold tripleCharges sourceA219 sourceB219 sourceC219 difference raw5769; decide +kernel
    rw [ha]
    exact (canonical5769 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA219 + difference 5 3) (sourceB219 + difference 3 5) sourceC219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA219 + difference 5 3) (sourceB219 + difference 3 5) sourceC219) = raw5770 := by
      apply Matrix.ext; unfold tripleCharges sourceA219 sourceB219 sourceC219 difference raw5770; decide +kernel
    rw [ha]
    exact (canonical5770 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA219 + difference 5 4) (sourceB219 + difference 4 5) sourceC219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2104) := by
    have ha : (tripleCharges (sourceA219 + difference 5 4) (sourceB219 + difference 4 5) sourceC219) = raw5767 := by
      apply Matrix.ext; unfold tripleCharges sourceA219 sourceB219 sourceC219 difference raw5767; decide +kernel
    rw [ha]
    exact (canonical5767 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA219 + difference 5 5) (sourceB219 + difference 5 5) sourceC219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2252) := by
    have ha : (tripleCharges (sourceA219 + difference 5 5) (sourceB219 + difference 5 5) sourceC219) = raw5748 := by
      apply Matrix.ext; unfold tripleCharges sourceA219 sourceB219 sourceC219 difference raw5748; decide +kernel
    rw [ha]
    exact (canonical5748 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA219 + sourceB219) sourceC219) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA219 + sourceB219) sourceC219) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA219 sourceB219 sourceC219 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA219 sourceB219 sourceC219
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm219, Integer.Sparse.eval]
  linarith only [hs]

def sourceA220 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB220 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC220 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceForm220 : Integer.Sparse Master := [(Sum.inr 4604, 2), (Sum.inr 4610, 1), (Sum.inr 4611, 1), (Sum.inr 4615, 1), (Sum.inr 4840, 2), (Sum.inr 4844, 1), (Sum.inr 4880, 2), (Sum.inr 4881, 1), (Sum.inr 4884, 1), (Sum.inr 4898, 1), (Sum.inr 5103, 2), (Sum.inr 5110, 1), (Sum.inr 5136, 2), (Sum.inr 5140, 2), (Sum.inr 5165, 2), (Sum.inr 5267, 2), (Sum.inr 5270, 2), (Sum.inr 5272, 1), (Sum.inr 5294, 1), (Sum.inr 5295, 1), (Sum.inr 5302, 1)]

theorem sourceEq220 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm220 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA220 + difference 0 1) (sourceB220 + difference 1 0) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA220 + difference 0 1) (sourceB220 + difference 1 0) sourceC220) = raw5771 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5771; decide +kernel
    rw [ha]
    exact (canonical5771 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA220 + difference 0 2) (sourceB220 + difference 2 0) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA220 + difference 0 2) (sourceB220 + difference 2 0) sourceC220) = raw5772 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5772; decide +kernel
    rw [ha]
    exact (canonical5772 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA220 + difference 0 3) (sourceB220 + difference 3 0) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA220 + difference 0 3) (sourceB220 + difference 3 0) sourceC220) = raw5773 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5773; decide +kernel
    rw [ha]
    exact (canonical5773 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA220 + difference 0 4) (sourceB220 + difference 4 0) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA220 + difference 0 4) (sourceB220 + difference 4 0) sourceC220) = raw5774 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5774; decide +kernel
    rw [ha]
    exact (canonical5774 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA220 + difference 0 5) (sourceB220 + difference 5 0) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA220 + difference 0 5) (sourceB220 + difference 5 0) sourceC220) = raw5775 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5775; decide +kernel
    rw [ha]
    exact (canonical5775 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA220 + difference 1 0) (sourceB220 + difference 0 1) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4615) := by
    have ha : (tripleCharges (sourceA220 + difference 1 0) (sourceB220 + difference 0 1) sourceC220) = raw5776 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5776; decide +kernel
    rw [ha]
    exact (canonical5776 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA220 + difference 1 2) (sourceB220 + difference 2 1) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5165) := by
    have ha : (tripleCharges (sourceA220 + difference 1 2) (sourceB220 + difference 2 1) sourceC220) = raw5777 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5777; decide +kernel
    rw [ha]
    exact (canonical5777 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA220 + difference 1 3) (sourceB220 + difference 3 1) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5165) := by
    have ha : (tripleCharges (sourceA220 + difference 1 3) (sourceB220 + difference 3 1) sourceC220) = raw5778 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5778; decide +kernel
    rw [ha]
    exact (canonical5778 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA220 + difference 1 4) (sourceB220 + difference 4 1) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4884) := by
    have ha : (tripleCharges (sourceA220 + difference 1 4) (sourceB220 + difference 4 1) sourceC220) = raw5779 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5779; decide +kernel
    rw [ha]
    exact (canonical5779 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA220 + difference 1 5) (sourceB220 + difference 5 1) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA220 + difference 1 5) (sourceB220 + difference 5 1) sourceC220) = raw5780 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5780; decide +kernel
    rw [ha]
    exact (canonical5780 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA220 + difference 2 0) (sourceB220 + difference 0 2) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4604) := by
    have ha : (tripleCharges (sourceA220 + difference 2 0) (sourceB220 + difference 0 2) sourceC220) = raw5781 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5781; decide +kernel
    rw [ha]
    exact (canonical5781 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA220 + difference 2 1) (sourceB220 + difference 1 2) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA220 + difference 2 1) (sourceB220 + difference 1 2) sourceC220) = raw5782 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5782; decide +kernel
    rw [ha]
    exact (canonical5782 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA220 + difference 2 3) (sourceB220 + difference 3 2) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5136) := by
    have ha : (tripleCharges (sourceA220 + difference 2 3) (sourceB220 + difference 3 2) sourceC220) = raw5783 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5783; decide +kernel
    rw [ha]
    exact (canonical5783 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA220 + difference 2 4) (sourceB220 + difference 4 2) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA220 + difference 2 4) (sourceB220 + difference 4 2) sourceC220) = raw5784 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5784; decide +kernel
    rw [ha]
    exact (canonical5784 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA220 + difference 2 5) (sourceB220 + difference 5 2) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA220 + difference 2 5) (sourceB220 + difference 5 2) sourceC220) = raw5785 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5785; decide +kernel
    rw [ha]
    exact (canonical5785 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA220 + difference 3 0) (sourceB220 + difference 0 3) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4604) := by
    have ha : (tripleCharges (sourceA220 + difference 3 0) (sourceB220 + difference 0 3) sourceC220) = raw5786 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5786; decide +kernel
    rw [ha]
    exact (canonical5786 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA220 + difference 3 1) (sourceB220 + difference 1 3) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA220 + difference 3 1) (sourceB220 + difference 1 3) sourceC220) = raw5787 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5787; decide +kernel
    rw [ha]
    exact (canonical5787 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA220 + difference 3 2) (sourceB220 + difference 2 3) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5136) := by
    have ha : (tripleCharges (sourceA220 + difference 3 2) (sourceB220 + difference 2 3) sourceC220) = raw5788 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5788; decide +kernel
    rw [ha]
    exact (canonical5788 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA220 + difference 3 4) (sourceB220 + difference 4 3) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4880) := by
    have ha : (tripleCharges (sourceA220 + difference 3 4) (sourceB220 + difference 4 3) sourceC220) = raw5789 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5789; decide +kernel
    rw [ha]
    exact (canonical5789 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA220 + difference 3 5) (sourceB220 + difference 5 3) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5270) := by
    have ha : (tripleCharges (sourceA220 + difference 3 5) (sourceB220 + difference 5 3) sourceC220) = raw5790 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5790; decide +kernel
    rw [ha]
    exact (canonical5790 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA220 + difference 4 0) (sourceB220 + difference 0 4) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4611) := by
    have ha : (tripleCharges (sourceA220 + difference 4 0) (sourceB220 + difference 0 4) sourceC220) = raw5791 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5791; decide +kernel
    rw [ha]
    exact (canonical5791 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA220 + difference 4 1) (sourceB220 + difference 1 4) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5110) := by
    have ha : (tripleCharges (sourceA220 + difference 4 1) (sourceB220 + difference 1 4) sourceC220) = raw5792 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5792; decide +kernel
    rw [ha]
    exact (canonical5792 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA220 + difference 4 2) (sourceB220 + difference 2 4) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA220 + difference 4 2) (sourceB220 + difference 2 4) sourceC220) = raw5793 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5793; decide +kernel
    rw [ha]
    exact (canonical5793 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA220 + difference 4 3) (sourceB220 + difference 3 4) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA220 + difference 4 3) (sourceB220 + difference 3 4) sourceC220) = raw5794 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5794; decide +kernel
    rw [ha]
    exact (canonical5794 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA220 + difference 4 5) (sourceB220 + difference 5 4) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5272) := by
    have ha : (tripleCharges (sourceA220 + difference 4 5) (sourceB220 + difference 5 4) sourceC220) = raw5795 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5795; decide +kernel
    rw [ha]
    exact (canonical5795 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA220 + difference 5 0) (sourceB220 + difference 0 5) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4610) := by
    have ha : (tripleCharges (sourceA220 + difference 5 0) (sourceB220 + difference 0 5) sourceC220) = raw5796 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5796; decide +kernel
    rw [ha]
    exact (canonical5796 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA220 + difference 5 1) (sourceB220 + difference 1 5) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4881) := by
    have ha : (tripleCharges (sourceA220 + difference 5 1) (sourceB220 + difference 1 5) sourceC220) = raw5797 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5797; decide +kernel
    rw [ha]
    exact (canonical5797 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA220 + difference 5 2) (sourceB220 + difference 2 5) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4840) := by
    have ha : (tripleCharges (sourceA220 + difference 5 2) (sourceB220 + difference 2 5) sourceC220) = raw5798 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5798; decide +kernel
    rw [ha]
    exact (canonical5798 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA220 + difference 5 3) (sourceB220 + difference 3 5) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4840) := by
    have ha : (tripleCharges (sourceA220 + difference 5 3) (sourceB220 + difference 3 5) sourceC220) = raw5799 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5799; decide +kernel
    rw [ha]
    exact (canonical5799 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA220 + difference 5 4) (sourceB220 + difference 4 5) sourceC220) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4844) := by
    have ha : (tripleCharges (sourceA220 + difference 5 4) (sourceB220 + difference 4 5) sourceC220) = raw5800 := by
      apply Matrix.ext; unfold tripleCharges sourceA220 sourceB220 sourceC220 difference raw5800; decide +kernel
    rw [ha]
    exact (canonical5800 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA220 sourceB220 sourceC220
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm220, Integer.Sparse.eval]
  linarith only [hs]

def sourceA221 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB221 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC221 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceForm221 : Integer.Sparse Master := [(Sum.inr 1257, 2), (Sum.inr 1258, 1), (Sum.inr 1273, 1), (Sum.inr 1288, 1), (Sum.inr 2121, 2), (Sum.inr 2134, 1), (Sum.inr 2222, 1), (Sum.inr 2254, 2), (Sum.inr 2279, 1), (Sum.inr 2280, 1), (Sum.inr 2715, 2), (Sum.inr 2732, 2), (Sum.inr 2733, 2), (Sum.inr 2754, 2), (Sum.inr 2759, 2), (Sum.inr 2768, 1), (Sum.inr 2769, 1), (Sum.inr 2776, 1), (Sum.inr 2942, 2), (Sum.inr 3005, 1), (Sum.inr 3113, 1)]

theorem sourceEq221 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm221 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA221 + difference 0 1) (sourceB221 + difference 1 0) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2776) := by
    have ha : (tripleCharges (sourceA221 + difference 0 1) (sourceB221 + difference 1 0) sourceC221) = raw5801 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5801; decide +kernel
    rw [ha]
    exact (canonical5801 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA221 + difference 0 2) (sourceB221 + difference 2 0) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA221 + difference 0 2) (sourceB221 + difference 2 0) sourceC221) = raw5802 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5802; decide +kernel
    rw [ha]
    exact (canonical5802 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA221 + difference 0 3) (sourceB221 + difference 3 0) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA221 + difference 0 3) (sourceB221 + difference 3 0) sourceC221) = raw5803 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5803; decide +kernel
    rw [ha]
    exact (canonical5803 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA221 + difference 0 4) (sourceB221 + difference 4 0) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA221 + difference 0 4) (sourceB221 + difference 4 0) sourceC221) = raw5804 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5804; decide +kernel
    rw [ha]
    exact (canonical5804 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA221 + difference 0 5) (sourceB221 + difference 5 0) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2768) := by
    have ha : (tripleCharges (sourceA221 + difference 0 5) (sourceB221 + difference 5 0) sourceC221) = raw5805 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5805; decide +kernel
    rw [ha]
    exact (canonical5805 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA221 + difference 1 0) (sourceB221 + difference 0 1) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1288) := by
    have ha : (tripleCharges (sourceA221 + difference 1 0) (sourceB221 + difference 0 1) sourceC221) = raw5806 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5806; decide +kernel
    rw [ha]
    exact (canonical5806 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA221 + difference 1 2) (sourceB221 + difference 2 1) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2733) := by
    have ha : (tripleCharges (sourceA221 + difference 1 2) (sourceB221 + difference 2 1) sourceC221) = raw5807 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5807; decide +kernel
    rw [ha]
    exact (canonical5807 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA221 + difference 1 3) (sourceB221 + difference 3 1) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2733) := by
    have ha : (tripleCharges (sourceA221 + difference 1 3) (sourceB221 + difference 3 1) sourceC221) = raw5808 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5808; decide +kernel
    rw [ha]
    exact (canonical5808 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA221 + difference 1 4) (sourceB221 + difference 4 1) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2280) := by
    have ha : (tripleCharges (sourceA221 + difference 1 4) (sourceB221 + difference 4 1) sourceC221) = raw5809 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5809; decide +kernel
    rw [ha]
    exact (canonical5809 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA221 + difference 1 5) (sourceB221 + difference 5 1) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA221 + difference 1 5) (sourceB221 + difference 5 1) sourceC221) = raw5810 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5810; decide +kernel
    rw [ha]
    exact (canonical5810 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA221 + difference 2 0) (sourceB221 + difference 0 2) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1257) := by
    have ha : (tripleCharges (sourceA221 + difference 2 0) (sourceB221 + difference 0 2) sourceC221) = raw5811 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5811; decide +kernel
    rw [ha]
    exact (canonical5811 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA221 + difference 2 1) (sourceB221 + difference 1 2) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2759) := by
    have ha : (tripleCharges (sourceA221 + difference 2 1) (sourceB221 + difference 1 2) sourceC221) = raw5812 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5812; decide +kernel
    rw [ha]
    exact (canonical5812 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA221 + difference 2 3) (sourceB221 + difference 3 2) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2715) := by
    have ha : (tripleCharges (sourceA221 + difference 2 3) (sourceB221 + difference 3 2) sourceC221) = raw5813 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5813; decide +kernel
    rw [ha]
    exact (canonical5813 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA221 + difference 2 4) (sourceB221 + difference 4 2) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA221 + difference 2 4) (sourceB221 + difference 4 2) sourceC221) = raw5814 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5814; decide +kernel
    rw [ha]
    exact (canonical5814 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA221 + difference 2 5) (sourceB221 + difference 5 2) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA221 + difference 2 5) (sourceB221 + difference 5 2) sourceC221) = raw5815 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5815; decide +kernel
    rw [ha]
    exact (canonical5815 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA221 + difference 3 0) (sourceB221 + difference 0 3) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1257) := by
    have ha : (tripleCharges (sourceA221 + difference 3 0) (sourceB221 + difference 0 3) sourceC221) = raw5816 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5816; decide +kernel
    rw [ha]
    exact (canonical5816 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA221 + difference 3 1) (sourceB221 + difference 1 3) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2759) := by
    have ha : (tripleCharges (sourceA221 + difference 3 1) (sourceB221 + difference 1 3) sourceC221) = raw5817 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5817; decide +kernel
    rw [ha]
    exact (canonical5817 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA221 + difference 3 2) (sourceB221 + difference 2 3) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2715) := by
    have ha : (tripleCharges (sourceA221 + difference 3 2) (sourceB221 + difference 2 3) sourceC221) = raw5818 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5818; decide +kernel
    rw [ha]
    exact (canonical5818 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA221 + difference 3 4) (sourceB221 + difference 4 3) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2254) := by
    have ha : (tripleCharges (sourceA221 + difference 3 4) (sourceB221 + difference 4 3) sourceC221) = raw5819 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5819; decide +kernel
    rw [ha]
    exact (canonical5819 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA221 + difference 3 5) (sourceB221 + difference 5 3) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2754) := by
    have ha : (tripleCharges (sourceA221 + difference 3 5) (sourceB221 + difference 5 3) sourceC221) = raw5820 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5820; decide +kernel
    rw [ha]
    exact (canonical5820 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA221 + difference 4 0) (sourceB221 + difference 0 4) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1273) := by
    have ha : (tripleCharges (sourceA221 + difference 4 0) (sourceB221 + difference 0 4) sourceC221) = raw5821 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5821; decide +kernel
    rw [ha]
    exact (canonical5821 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA221 + difference 4 1) (sourceB221 + difference 1 4) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3005) := by
    have ha : (tripleCharges (sourceA221 + difference 4 1) (sourceB221 + difference 1 4) sourceC221) = raw5822 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5822; decide +kernel
    rw [ha]
    exact (canonical5822 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA221 + difference 4 2) (sourceB221 + difference 2 4) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2942) := by
    have ha : (tripleCharges (sourceA221 + difference 4 2) (sourceB221 + difference 2 4) sourceC221) = raw5823 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5823; decide +kernel
    rw [ha]
    exact (canonical5823 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA221 + difference 4 3) (sourceB221 + difference 3 4) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2942) := by
    have ha : (tripleCharges (sourceA221 + difference 4 3) (sourceB221 + difference 3 4) sourceC221) = raw5824 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5824; decide +kernel
    rw [ha]
    exact (canonical5824 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA221 + difference 4 5) (sourceB221 + difference 5 4) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3113) := by
    have ha : (tripleCharges (sourceA221 + difference 4 5) (sourceB221 + difference 5 4) sourceC221) = raw5825 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5825; decide +kernel
    rw [ha]
    exact (canonical5825 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA221 + difference 5 0) (sourceB221 + difference 0 5) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1258) := by
    have ha : (tripleCharges (sourceA221 + difference 5 0) (sourceB221 + difference 0 5) sourceC221) = raw5826 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5826; decide +kernel
    rw [ha]
    exact (canonical5826 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA221 + difference 5 1) (sourceB221 + difference 1 5) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2134) := by
    have ha : (tripleCharges (sourceA221 + difference 5 1) (sourceB221 + difference 1 5) sourceC221) = raw5827 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5827; decide +kernel
    rw [ha]
    exact (canonical5827 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA221 + difference 5 2) (sourceB221 + difference 2 5) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2121) := by
    have ha : (tripleCharges (sourceA221 + difference 5 2) (sourceB221 + difference 2 5) sourceC221) = raw5828 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5828; decide +kernel
    rw [ha]
    exact (canonical5828 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA221 + difference 5 3) (sourceB221 + difference 3 5) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2121) := by
    have ha : (tripleCharges (sourceA221 + difference 5 3) (sourceB221 + difference 3 5) sourceC221) = raw5829 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5829; decide +kernel
    rw [ha]
    exact (canonical5829 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA221 + difference 5 4) (sourceB221 + difference 4 5) sourceC221) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2222) := by
    have ha : (tripleCharges (sourceA221 + difference 5 4) (sourceB221 + difference 4 5) sourceC221) = raw5830 := by
      apply Matrix.ext; unfold tripleCharges sourceA221 sourceB221 sourceC221 difference raw5830; decide +kernel
    rw [ha]
    exact (canonical5830 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA221 sourceB221 sourceC221
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm221, Integer.Sparse.eval]
  linarith only [hs]

def sourceA222 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB222 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC222 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceForm222 : Integer.Sparse Master := [(Sum.inr 2059, 2), (Sum.inr 2063, 1), (Sum.inr 2064, 1), (Sum.inr 2267, 1), (Sum.inr 2670, 2), (Sum.inr 2683, 1), (Sum.inr 2685, 1), (Sum.inr 2740, 1), (Sum.inr 3015, 2), (Sum.inr 3022, 2), (Sum.inr 3024, 2), (Sum.inr 3035, 2), (Sum.inr 3038, 2), (Sum.inr 3049, 1), (Sum.inr 3054, 1), (Sum.inr 3075, 2), (Sum.inr 3098, 1), (Sum.inr 3101, 1), (Sum.inr 3156, 2), (Sum.inr 3161, 1), (Sum.inr 3224, 1)]

theorem sourceEq222 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm222 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA222 + difference 0 1) (sourceB222 + difference 1 0) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA222 + difference 0 1) (sourceB222 + difference 1 0) sourceC222) = raw5831 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5831; decide +kernel
    rw [ha]
    exact (canonical5831 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA222 + difference 0 2) (sourceB222 + difference 2 0) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA222 + difference 0 2) (sourceB222 + difference 2 0) sourceC222) = raw5832 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5832; decide +kernel
    rw [ha]
    exact (canonical5832 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA222 + difference 0 3) (sourceB222 + difference 3 0) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA222 + difference 0 3) (sourceB222 + difference 3 0) sourceC222) = raw5833 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5833; decide +kernel
    rw [ha]
    exact (canonical5833 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA222 + difference 0 4) (sourceB222 + difference 4 0) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3224) := by
    have ha : (tripleCharges (sourceA222 + difference 0 4) (sourceB222 + difference 4 0) sourceC222) = raw5834 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5834; decide +kernel
    rw [ha]
    exact (canonical5834 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA222 + difference 0 5) (sourceB222 + difference 5 0) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA222 + difference 0 5) (sourceB222 + difference 5 0) sourceC222) = raw5835 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5835; decide +kernel
    rw [ha]
    exact (canonical5835 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA222 + difference 1 0) (sourceB222 + difference 0 1) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3049) := by
    have ha : (tripleCharges (sourceA222 + difference 1 0) (sourceB222 + difference 0 1) sourceC222) = raw5836 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5836; decide +kernel
    rw [ha]
    exact (canonical5836 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA222 + difference 1 2) (sourceB222 + difference 2 1) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3035) := by
    have ha : (tripleCharges (sourceA222 + difference 1 2) (sourceB222 + difference 2 1) sourceC222) = raw5837 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5837; decide +kernel
    rw [ha]
    exact (canonical5837 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA222 + difference 1 3) (sourceB222 + difference 3 1) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3035) := by
    have ha : (tripleCharges (sourceA222 + difference 1 3) (sourceB222 + difference 3 1) sourceC222) = raw5838 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5838; decide +kernel
    rw [ha]
    exact (canonical5838 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA222 + difference 1 4) (sourceB222 + difference 4 1) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3161) := by
    have ha : (tripleCharges (sourceA222 + difference 1 4) (sourceB222 + difference 4 1) sourceC222) = raw5839 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5839; decide +kernel
    rw [ha]
    exact (canonical5839 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA222 + difference 1 5) (sourceB222 + difference 5 1) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA222 + difference 1 5) (sourceB222 + difference 5 1) sourceC222) = raw5840 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5840; decide +kernel
    rw [ha]
    exact (canonical5840 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA222 + difference 2 0) (sourceB222 + difference 0 2) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3022) := by
    have ha : (tripleCharges (sourceA222 + difference 2 0) (sourceB222 + difference 0 2) sourceC222) = raw5841 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5841; decide +kernel
    rw [ha]
    exact (canonical5841 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA222 + difference 2 1) (sourceB222 + difference 1 2) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA222 + difference 2 1) (sourceB222 + difference 1 2) sourceC222) = raw5842 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5842; decide +kernel
    rw [ha]
    exact (canonical5842 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA222 + difference 2 3) (sourceB222 + difference 3 2) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3015) := by
    have ha : (tripleCharges (sourceA222 + difference 2 3) (sourceB222 + difference 3 2) sourceC222) = raw5843 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5843; decide +kernel
    rw [ha]
    exact (canonical5843 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA222 + difference 2 4) (sourceB222 + difference 4 2) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3156) := by
    have ha : (tripleCharges (sourceA222 + difference 2 4) (sourceB222 + difference 4 2) sourceC222) = raw5844 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5844; decide +kernel
    rw [ha]
    exact (canonical5844 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA222 + difference 2 5) (sourceB222 + difference 5 2) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA222 + difference 2 5) (sourceB222 + difference 5 2) sourceC222) = raw5845 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5845; decide +kernel
    rw [ha]
    exact (canonical5845 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA222 + difference 3 0) (sourceB222 + difference 0 3) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3022) := by
    have ha : (tripleCharges (sourceA222 + difference 3 0) (sourceB222 + difference 0 3) sourceC222) = raw5846 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5846; decide +kernel
    rw [ha]
    exact (canonical5846 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA222 + difference 3 1) (sourceB222 + difference 1 3) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA222 + difference 3 1) (sourceB222 + difference 1 3) sourceC222) = raw5847 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5847; decide +kernel
    rw [ha]
    exact (canonical5847 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA222 + difference 3 2) (sourceB222 + difference 2 3) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3015) := by
    have ha : (tripleCharges (sourceA222 + difference 3 2) (sourceB222 + difference 2 3) sourceC222) = raw5848 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5848; decide +kernel
    rw [ha]
    exact (canonical5848 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA222 + difference 3 4) (sourceB222 + difference 4 3) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3156) := by
    have ha : (tripleCharges (sourceA222 + difference 3 4) (sourceB222 + difference 4 3) sourceC222) = raw5849 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5849; decide +kernel
    rw [ha]
    exact (canonical5849 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA222 + difference 3 5) (sourceB222 + difference 5 3) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3075) := by
    have ha : (tripleCharges (sourceA222 + difference 3 5) (sourceB222 + difference 5 3) sourceC222) = raw5850 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5850; decide +kernel
    rw [ha]
    exact (canonical5850 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA222 + difference 4 0) (sourceB222 + difference 0 4) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2683) := by
    have ha : (tripleCharges (sourceA222 + difference 4 0) (sourceB222 + difference 0 4) sourceC222) = raw5851 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5851; decide +kernel
    rw [ha]
    exact (canonical5851 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA222 + difference 4 1) (sourceB222 + difference 1 4) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2685) := by
    have ha : (tripleCharges (sourceA222 + difference 4 1) (sourceB222 + difference 1 4) sourceC222) = raw5852 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5852; decide +kernel
    rw [ha]
    exact (canonical5852 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA222 + difference 4 2) (sourceB222 + difference 2 4) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA222 + difference 4 2) (sourceB222 + difference 2 4) sourceC222) = raw5853 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5853; decide +kernel
    rw [ha]
    exact (canonical5853 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA222 + difference 4 3) (sourceB222 + difference 3 4) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA222 + difference 4 3) (sourceB222 + difference 3 4) sourceC222) = raw5854 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5854; decide +kernel
    rw [ha]
    exact (canonical5854 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA222 + difference 4 5) (sourceB222 + difference 5 4) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA222 + difference 4 5) (sourceB222 + difference 5 4) sourceC222) = raw5855 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5855; decide +kernel
    rw [ha]
    exact (canonical5855 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA222 + difference 5 0) (sourceB222 + difference 0 5) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2064) := by
    have ha : (tripleCharges (sourceA222 + difference 5 0) (sourceB222 + difference 0 5) sourceC222) = raw5856 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5856; decide +kernel
    rw [ha]
    exact (canonical5856 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA222 + difference 5 1) (sourceB222 + difference 1 5) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2267) := by
    have ha : (tripleCharges (sourceA222 + difference 5 1) (sourceB222 + difference 1 5) sourceC222) = raw5857 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5857; decide +kernel
    rw [ha]
    exact (canonical5857 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA222 + difference 5 2) (sourceB222 + difference 2 5) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2059) := by
    have ha : (tripleCharges (sourceA222 + difference 5 2) (sourceB222 + difference 2 5) sourceC222) = raw5858 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5858; decide +kernel
    rw [ha]
    exact (canonical5858 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA222 + difference 5 3) (sourceB222 + difference 3 5) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2059) := by
    have ha : (tripleCharges (sourceA222 + difference 5 3) (sourceB222 + difference 3 5) sourceC222) = raw5859 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5859; decide +kernel
    rw [ha]
    exact (canonical5859 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA222 + difference 5 4) (sourceB222 + difference 4 5) sourceC222) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA222 + difference 5 4) (sourceB222 + difference 4 5) sourceC222) = raw5860 := by
      apply Matrix.ext; unfold tripleCharges sourceA222 sourceB222 sourceC222 difference raw5860; decide +kernel
    rw [ha]
    exact (canonical5860 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA222 sourceB222 sourceC222
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm222, Integer.Sparse.eval]
  linarith only [hs]

def sourceA223 : Charge := ![-3, 0, 0, 0, 1, 2]
def sourceB223 : Charge := ![1, -1, 0, 0, 2, -2]
def sourceC223 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceForm223 : Integer.Sparse Master := [(Sum.inr 2279, 1), (Sum.inr 2744, 1), (Sum.inr 3541, 2), (Sum.inr 3626, 1), (Sum.inr 3632, 1), (Sum.inr 4084, -1)]

theorem sourceEq223 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm223 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA223 + difference 0 0) (sourceB223 + difference 0 0) sourceC223) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA223 + difference 0 0) (sourceB223 + difference 0 0) sourceC223) = raw5861 := by
      apply Matrix.ext; unfold tripleCharges sourceA223 sourceB223 sourceC223 difference raw5861; decide +kernel
    rw [ha]
    exact (canonical5861 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA223 + difference 0 1) (sourceB223 + difference 1 0) sourceC223) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA223 + difference 0 1) (sourceB223 + difference 1 0) sourceC223) = raw5862 := by
      apply Matrix.ext; unfold tripleCharges sourceA223 sourceB223 sourceC223 difference raw5862; decide +kernel
    rw [ha]
    exact (canonical5862 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA223 + difference 0 2) (sourceB223 + difference 2 0) sourceC223) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA223 + difference 0 2) (sourceB223 + difference 2 0) sourceC223) = raw5863 := by
      apply Matrix.ext; unfold tripleCharges sourceA223 sourceB223 sourceC223 difference raw5863; decide +kernel
    rw [ha]
    exact (canonical5863 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA223 + difference 0 3) (sourceB223 + difference 3 0) sourceC223) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA223 + difference 0 3) (sourceB223 + difference 3 0) sourceC223) = raw5864 := by
      apply Matrix.ext; unfold tripleCharges sourceA223 sourceB223 sourceC223 difference raw5864; decide +kernel
    rw [ha]
    exact (canonical5864 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA223 + difference 0 4) (sourceB223 + difference 4 0) sourceC223) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA223 + difference 0 4) (sourceB223 + difference 4 0) sourceC223) = raw5865 := by
      apply Matrix.ext; unfold tripleCharges sourceA223 sourceB223 sourceC223 difference raw5865; decide +kernel
    rw [ha]
    exact (canonical5865 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA223 + difference 0 5) (sourceB223 + difference 5 0) sourceC223) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3632) := by
    have ha : (tripleCharges (sourceA223 + difference 0 5) (sourceB223 + difference 5 0) sourceC223) = raw5866 := by
      apply Matrix.ext; unfold tripleCharges sourceA223 sourceB223 sourceC223 difference raw5866; decide +kernel
    rw [ha]
    exact (canonical5866 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA223 + sourceB223) sourceC223) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA223 + sourceB223) sourceC223) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA223 sourceB223 sourceC223 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA223 sourceB223 sourceC223
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm223, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
