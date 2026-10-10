import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical115
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical118
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical119
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical120
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical121
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical122
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical123

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA928 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB928 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC928 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceForm928 : Integer.Sparse Master := [(Sum.inr 2616, 1), (Sum.inr 2870, 1), (Sum.inr 3698, 1), (Sum.inr 3788, 1), (Sum.inr 3874, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

theorem sourceEq928 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm928 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA928 + difference 0 2) (sourceB928 + difference 2 0) sourceC928) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA928 + difference 0 2) (sourceB928 + difference 2 0) sourceC928) = raw15370 := by
      apply Matrix.ext; unfold tripleCharges sourceA928 sourceB928 sourceC928 difference raw15370; decide +kernel
    rw [ha]
    exact (canonical15370 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA928 + difference 1 2) (sourceB928 + difference 2 1) sourceC928) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA928 + difference 1 2) (sourceB928 + difference 2 1) sourceC928) = raw15361 := by
      apply Matrix.ext; unfold tripleCharges sourceA928 sourceB928 sourceC928 difference raw15361; decide +kernel
    rw [ha]
    exact (canonical15361 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA928 + difference 2 2) (sourceB928 + difference 2 2) sourceC928) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA928 + difference 2 2) (sourceB928 + difference 2 2) sourceC928) = raw15354 := by
      apply Matrix.ext; unfold tripleCharges sourceA928 sourceB928 sourceC928 difference raw15354; decide +kernel
    rw [ha]
    exact (canonical15354 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA928 + difference 3 2) (sourceB928 + difference 2 3) sourceC928) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2616) := by
    have ha : (tripleCharges (sourceA928 + difference 3 2) (sourceB928 + difference 2 3) sourceC928) = raw15371 := by
      apply Matrix.ext; unfold tripleCharges sourceA928 sourceB928 sourceC928 difference raw15371; decide +kernel
    rw [ha]
    exact (canonical15371 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA928 + difference 4 2) (sourceB928 + difference 2 4) sourceC928) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3698) := by
    have ha : (tripleCharges (sourceA928 + difference 4 2) (sourceB928 + difference 2 4) sourceC928) = raw15372 := by
      apply Matrix.ext; unfold tripleCharges sourceA928 sourceB928 sourceC928 difference raw15372; decide +kernel
    rw [ha]
    exact (canonical15372 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA928 + difference 5 2) (sourceB928 + difference 2 5) sourceC928) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2870) := by
    have ha : (tripleCharges (sourceA928 + difference 5 2) (sourceB928 + difference 2 5) sourceC928) = raw15373 := by
      apply Matrix.ext; unfold tripleCharges sourceA928 sourceB928 sourceC928 difference raw15373; decide +kernel
    rw [ha]
    exact (canonical15373 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA928 + sourceB928) sourceC928) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA928 + sourceB928) sourceC928) = raw15360 := by
      apply Matrix.ext; unfold doubleCharges sourceA928 sourceB928 sourceC928 raw15360; decide +kernel
    rw [ha]
    exact (canonical15360 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA928 sourceB928 sourceC928
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm928, Integer.Sparse.eval]
  linarith only [hs]

def sourceA929 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB929 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC929 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceForm929 : Integer.Sparse Master := [(Sum.inr 2885, 1), (Sum.inr 3706, 1), (Sum.inr 3877, 1), (Sum.inr 3946, 1), (Sum.inr 3959, 1), (Sum.inr 3961, 1), (Sum.inr 4092, -1)]

theorem sourceEq929 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm929 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA929 + difference 0 3) (sourceB929 + difference 3 0) sourceC929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA929 + difference 0 3) (sourceB929 + difference 3 0) sourceC929) = raw15374 := by
      apply Matrix.ext; unfold tripleCharges sourceA929 sourceB929 sourceC929 difference raw15374; decide +kernel
    rw [ha]
    exact (canonical15374 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA929 + difference 1 3) (sourceB929 + difference 3 1) sourceC929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA929 + difference 1 3) (sourceB929 + difference 3 1) sourceC929) = raw15362 := by
      apply Matrix.ext; unfold tripleCharges sourceA929 sourceB929 sourceC929 difference raw15362; decide +kernel
    rw [ha]
    exact (canonical15362 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA929 + difference 2 3) (sourceB929 + difference 3 2) sourceC929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3946) := by
    have ha : (tripleCharges (sourceA929 + difference 2 3) (sourceB929 + difference 3 2) sourceC929) = raw15375 := by
      apply Matrix.ext; unfold tripleCharges sourceA929 sourceB929 sourceC929 difference raw15375; decide +kernel
    rw [ha]
    exact (canonical15375 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA929 + difference 3 3) (sourceB929 + difference 3 3) sourceC929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA929 + difference 3 3) (sourceB929 + difference 3 3) sourceC929) = raw15354 := by
      apply Matrix.ext; unfold tripleCharges sourceA929 sourceB929 sourceC929 difference raw15354; decide +kernel
    rw [ha]
    exact (canonical15354 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA929 + difference 4 3) (sourceB929 + difference 3 4) sourceC929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA929 + difference 4 3) (sourceB929 + difference 3 4) sourceC929) = raw15376 := by
      apply Matrix.ext; unfold tripleCharges sourceA929 sourceB929 sourceC929 difference raw15376; decide +kernel
    rw [ha]
    exact (canonical15376 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA929 + difference 5 3) (sourceB929 + difference 3 5) sourceC929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2885) := by
    have ha : (tripleCharges (sourceA929 + difference 5 3) (sourceB929 + difference 3 5) sourceC929) = raw15377 := by
      apply Matrix.ext; unfold tripleCharges sourceA929 sourceB929 sourceC929 difference raw15377; decide +kernel
    rw [ha]
    exact (canonical15377 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA929 + sourceB929) sourceC929) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA929 + sourceB929) sourceC929) = raw15360 := by
      apply Matrix.ext; unfold doubleCharges sourceA929 sourceB929 sourceC929 raw15360; decide +kernel
    rw [ha]
    exact (canonical15360 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA929 sourceB929 sourceC929
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm929, Integer.Sparse.eval]
  linarith only [hs]

def sourceA930 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB930 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC930 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceForm930 : Integer.Sparse Master := [(Sum.inr 3198, 1), (Sum.inr 3698, 1), (Sum.inr 3699, 1), (Sum.inr 3706, 1), (Sum.inr 3814, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

theorem sourceEq930 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm930 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA930 + difference 4 0) (sourceB930 + difference 0 4) sourceC930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3198) := by
    have ha : (tripleCharges (sourceA930 + difference 4 0) (sourceB930 + difference 0 4) sourceC930) = raw15358 := by
      apply Matrix.ext; unfold tripleCharges sourceA930 sourceB930 sourceC930 difference raw15358; decide +kernel
    rw [ha]
    exact (canonical15358 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA930 + difference 4 1) (sourceB930 + difference 1 4) sourceC930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3699) := by
    have ha : (tripleCharges (sourceA930 + difference 4 1) (sourceB930 + difference 1 4) sourceC930) = raw15368 := by
      apply Matrix.ext; unfold tripleCharges sourceA930 sourceB930 sourceC930 difference raw15368; decide +kernel
    rw [ha]
    exact (canonical15368 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA930 + difference 4 2) (sourceB930 + difference 2 4) sourceC930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3698) := by
    have ha : (tripleCharges (sourceA930 + difference 4 2) (sourceB930 + difference 2 4) sourceC930) = raw15372 := by
      apply Matrix.ext; unfold tripleCharges sourceA930 sourceB930 sourceC930 difference raw15372; decide +kernel
    rw [ha]
    exact (canonical15372 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA930 + difference 4 3) (sourceB930 + difference 3 4) sourceC930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3706) := by
    have ha : (tripleCharges (sourceA930 + difference 4 3) (sourceB930 + difference 3 4) sourceC930) = raw15376 := by
      apply Matrix.ext; unfold tripleCharges sourceA930 sourceB930 sourceC930 difference raw15376; decide +kernel
    rw [ha]
    exact (canonical15376 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA930 + difference 4 4) (sourceB930 + difference 4 4) sourceC930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA930 + difference 4 4) (sourceB930 + difference 4 4) sourceC930) = raw15354 := by
      apply Matrix.ext; unfold tripleCharges sourceA930 sourceB930 sourceC930 difference raw15354; decide +kernel
    rw [ha]
    exact (canonical15354 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA930 + difference 4 5) (sourceB930 + difference 5 4) sourceC930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA930 + difference 4 5) (sourceB930 + difference 5 4) sourceC930) = raw15378 := by
      apply Matrix.ext; unfold tripleCharges sourceA930 sourceB930 sourceC930 difference raw15378; decide +kernel
    rw [ha]
    exact (canonical15378 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA930 + sourceB930) sourceC930) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA930 + sourceB930) sourceC930) = raw15360 := by
      apply Matrix.ext; unfold doubleCharges sourceA930 sourceB930 sourceC930 raw15360; decide +kernel
    rw [ha]
    exact (canonical15360 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA930 sourceB930 sourceC930
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm930, Integer.Sparse.eval]
  linarith only [hs]

def sourceA931 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB931 : Charge := ![2, 0, 0, -2, 1, -1]
def sourceC931 : Charge := ![0, 1, 0, 2, -2, -1]
def sourceForm931 : Integer.Sparse Master := [(Sum.inr 2620, 1), (Sum.inr 3045, 1), (Sum.inr 3723, 1), (Sum.inr 3732, 1), (Sum.inr 3850, 1), (Sum.inr 3877, 1), (Sum.inr 4092, -1)]

theorem sourceEq931 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm931 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA931 + difference 0 4) (sourceB931 + difference 4 0) sourceC931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA931 + difference 0 4) (sourceB931 + difference 4 0) sourceC931) = raw15379 := by
      apply Matrix.ext; unfold tripleCharges sourceA931 sourceB931 sourceC931 difference raw15379; decide +kernel
    rw [ha]
    exact (canonical15379 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA931 + difference 1 4) (sourceB931 + difference 4 1) sourceC931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA931 + difference 1 4) (sourceB931 + difference 4 1) sourceC931) = raw15363 := by
      apply Matrix.ext; unfold tripleCharges sourceA931 sourceB931 sourceC931 difference raw15363; decide +kernel
    rw [ha]
    exact (canonical15363 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA931 + difference 2 4) (sourceB931 + difference 4 2) sourceC931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3723) := by
    have ha : (tripleCharges (sourceA931 + difference 2 4) (sourceB931 + difference 4 2) sourceC931) = raw15380 := by
      apply Matrix.ext; unfold tripleCharges sourceA931 sourceB931 sourceC931 difference raw15380; decide +kernel
    rw [ha]
    exact (canonical15380 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA931 + difference 3 4) (sourceB931 + difference 4 3) sourceC931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2620) := by
    have ha : (tripleCharges (sourceA931 + difference 3 4) (sourceB931 + difference 4 3) sourceC931) = raw15381 := by
      apply Matrix.ext; unfold tripleCharges sourceA931 sourceB931 sourceC931 difference raw15381; decide +kernel
    rw [ha]
    exact (canonical15381 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA931 + difference 4 4) (sourceB931 + difference 4 4) sourceC931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA931 + difference 4 4) (sourceB931 + difference 4 4) sourceC931) = raw15354 := by
      apply Matrix.ext; unfold tripleCharges sourceA931 sourceB931 sourceC931 difference raw15354; decide +kernel
    rw [ha]
    exact (canonical15354 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA931 + difference 5 4) (sourceB931 + difference 4 5) sourceC931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3045) := by
    have ha : (tripleCharges (sourceA931 + difference 5 4) (sourceB931 + difference 4 5) sourceC931) = raw15382 := by
      apply Matrix.ext; unfold tripleCharges sourceA931 sourceB931 sourceC931 difference raw15382; decide +kernel
    rw [ha]
    exact (canonical15382 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA931 + sourceB931) sourceC931) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA931 + sourceB931) sourceC931) = raw15360 := by
      apply Matrix.ext; unfold doubleCharges sourceA931 sourceB931 sourceC931 raw15360; decide +kernel
    rw [ha]
    exact (canonical15360 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA931 sourceB931 sourceC931
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm931, Integer.Sparse.eval]
  linarith only [hs]

def sourceA932 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB932 : Charge := ![0, 1, 0, 2, -1, -2]
def sourceC932 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceForm932 : Integer.Sparse Master := [(Sum.inr 4746, 1), (Sum.inr 4747, 2), (Sum.inr 4749, 1), (Sum.inr 4898, 1), (Sum.inr 5155, 2), (Sum.inr 5156, 2), (Sum.inr 5170, 2), (Sum.inr 5302, 2), (Sum.inr 5328, 1), (Sum.inr 5329, 1), (Sum.inr 5374, 1), (Sum.inr 5384, 2), (Sum.inr 5403, 2), (Sum.inr 5412, 3), (Sum.inr 5437, 1), (Sum.inr 5439, 2), (Sum.inr 5443, 2), (Sum.inr 5453, 1), (Sum.inr 5456, 1)]

theorem sourceEq932 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm932 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA932 + difference 0 1) (sourceB932 + difference 1 0) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA932 + difference 0 1) (sourceB932 + difference 1 0) sourceC932) = raw15383 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15383; decide +kernel
    rw [ha]
    exact (canonical15383 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA932 + difference 0 2) (sourceB932 + difference 2 0) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA932 + difference 0 2) (sourceB932 + difference 2 0) sourceC932) = raw15384 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15384; decide +kernel
    rw [ha]
    exact (canonical15384 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA932 + difference 0 3) (sourceB932 + difference 3 0) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA932 + difference 0 3) (sourceB932 + difference 3 0) sourceC932) = raw15385 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15385; decide +kernel
    rw [ha]
    exact (canonical15385 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA932 + difference 0 4) (sourceB932 + difference 4 0) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA932 + difference 0 4) (sourceB932 + difference 4 0) sourceC932) = raw15386 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15386; decide +kernel
    rw [ha]
    exact (canonical15386 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA932 + difference 0 5) (sourceB932 + difference 5 0) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA932 + difference 0 5) (sourceB932 + difference 5 0) sourceC932) = raw15387 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15387; decide +kernel
    rw [ha]
    exact (canonical15387 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA932 + difference 1 0) (sourceB932 + difference 0 1) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA932 + difference 1 0) (sourceB932 + difference 0 1) sourceC932) = raw15388 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15388; decide +kernel
    rw [ha]
    exact (canonical15388 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA932 + difference 1 2) (sourceB932 + difference 2 1) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA932 + difference 1 2) (sourceB932 + difference 2 1) sourceC932) = raw8621 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw8621; decide +kernel
    rw [ha]
    exact (canonical8621 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA932 + difference 1 3) (sourceB932 + difference 3 1) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5302) := by
    have ha : (tripleCharges (sourceA932 + difference 1 3) (sourceB932 + difference 3 1) sourceC932) = raw8622 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw8622; decide +kernel
    rw [ha]
    exact (canonical8622 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA932 + difference 1 4) (sourceB932 + difference 4 1) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5456) := by
    have ha : (tripleCharges (sourceA932 + difference 1 4) (sourceB932 + difference 4 1) sourceC932) = raw8623 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw8623; decide +kernel
    rw [ha]
    exact (canonical8623 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA932 + difference 1 5) (sourceB932 + difference 5 1) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5453) := by
    have ha : (tripleCharges (sourceA932 + difference 1 5) (sourceB932 + difference 5 1) sourceC932) = raw8624 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw8624; decide +kernel
    rw [ha]
    exact (canonical8624 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA932 + difference 2 0) (sourceB932 + difference 0 2) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA932 + difference 2 0) (sourceB932 + difference 0 2) sourceC932) = raw8631 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw8631; decide +kernel
    rw [ha]
    exact (canonical8631 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA932 + difference 2 1) (sourceB932 + difference 1 2) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5374) := by
    have ha : (tripleCharges (sourceA932 + difference 2 1) (sourceB932 + difference 1 2) sourceC932) = raw15389 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15389; decide +kernel
    rw [ha]
    exact (canonical15389 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA932 + difference 2 3) (sourceB932 + difference 3 2) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5155) := by
    have ha : (tripleCharges (sourceA932 + difference 2 3) (sourceB932 + difference 3 2) sourceC932) = raw15390 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15390; decide +kernel
    rw [ha]
    exact (canonical15390 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA932 + difference 2 4) (sourceB932 + difference 4 2) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA932 + difference 2 4) (sourceB932 + difference 4 2) sourceC932) = raw15391 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15391; decide +kernel
    rw [ha]
    exact (canonical15391 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA932 + difference 2 5) (sourceB932 + difference 5 2) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5437) := by
    have ha : (tripleCharges (sourceA932 + difference 2 5) (sourceB932 + difference 5 2) sourceC932) = raw15392 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15392; decide +kernel
    rw [ha]
    exact (canonical15392 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA932 + difference 3 0) (sourceB932 + difference 0 3) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA932 + difference 3 0) (sourceB932 + difference 0 3) sourceC932) = raw8636 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw8636; decide +kernel
    rw [ha]
    exact (canonical8636 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA932 + difference 3 1) (sourceB932 + difference 1 3) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5384) := by
    have ha : (tripleCharges (sourceA932 + difference 3 1) (sourceB932 + difference 1 3) sourceC932) = raw15393 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15393; decide +kernel
    rw [ha]
    exact (canonical15393 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA932 + difference 3 2) (sourceB932 + difference 2 3) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5403) := by
    have ha : (tripleCharges (sourceA932 + difference 3 2) (sourceB932 + difference 2 3) sourceC932) = raw15394 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15394; decide +kernel
    rw [ha]
    exact (canonical15394 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA932 + difference 3 4) (sourceB932 + difference 4 3) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA932 + difference 3 4) (sourceB932 + difference 4 3) sourceC932) = raw15395 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15395; decide +kernel
    rw [ha]
    exact (canonical15395 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA932 + difference 3 5) (sourceB932 + difference 5 3) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA932 + difference 3 5) (sourceB932 + difference 5 3) sourceC932) = raw15396 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15396; decide +kernel
    rw [ha]
    exact (canonical15396 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA932 + difference 4 0) (sourceB932 + difference 0 4) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5156) := by
    have ha : (tripleCharges (sourceA932 + difference 4 0) (sourceB932 + difference 0 4) sourceC932) = raw8641 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw8641; decide +kernel
    rw [ha]
    exact (canonical8641 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA932 + difference 4 1) (sourceB932 + difference 1 4) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5329) := by
    have ha : (tripleCharges (sourceA932 + difference 4 1) (sourceB932 + difference 1 4) sourceC932) = raw15397 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15397; decide +kernel
    rw [ha]
    exact (canonical15397 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA932 + difference 4 2) (sourceB932 + difference 2 4) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5328) := by
    have ha : (tripleCharges (sourceA932 + difference 4 2) (sourceB932 + difference 2 4) sourceC932) = raw15398 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15398; decide +kernel
    rw [ha]
    exact (canonical15398 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA932 + difference 4 3) (sourceB932 + difference 3 4) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5156) := by
    have ha : (tripleCharges (sourceA932 + difference 4 3) (sourceB932 + difference 3 4) sourceC932) = raw15399 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15399; decide +kernel
    rw [ha]
    exact (canonical15399 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA932 + difference 4 5) (sourceB932 + difference 5 4) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA932 + difference 4 5) (sourceB932 + difference 5 4) sourceC932) = raw15400 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15400; decide +kernel
    rw [ha]
    exact (canonical15400 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA932 + difference 5 0) (sourceB932 + difference 0 5) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA932 + difference 5 0) (sourceB932 + difference 0 5) sourceC932) = raw8646 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw8646; decide +kernel
    rw [ha]
    exact (canonical8646 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA932 + difference 5 1) (sourceB932 + difference 1 5) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4749) := by
    have ha : (tripleCharges (sourceA932 + difference 5 1) (sourceB932 + difference 1 5) sourceC932) = raw15401 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15401; decide +kernel
    rw [ha]
    exact (canonical15401 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA932 + difference 5 2) (sourceB932 + difference 2 5) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4746) := by
    have ha : (tripleCharges (sourceA932 + difference 5 2) (sourceB932 + difference 2 5) sourceC932) = raw15402 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15402; decide +kernel
    rw [ha]
    exact (canonical15402 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA932 + difference 5 3) (sourceB932 + difference 3 5) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA932 + difference 5 3) (sourceB932 + difference 3 5) sourceC932) = raw15403 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15403; decide +kernel
    rw [ha]
    exact (canonical15403 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA932 + difference 5 4) (sourceB932 + difference 4 5) sourceC932) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4898) := by
    have ha : (tripleCharges (sourceA932 + difference 5 4) (sourceB932 + difference 4 5) sourceC932) = raw15404 := by
      apply Matrix.ext; unfold tripleCharges sourceA932 sourceB932 sourceC932 difference raw15404; decide +kernel
    rw [ha]
    exact (canonical15404 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA932 sourceB932 sourceC932
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm932, Integer.Sparse.eval]
  linarith only [hs]

def sourceA933 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB933 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC933 : Charge := ![0, 1, 0, 2, -1, -2]
def sourceForm933 : Integer.Sparse Master := [(Sum.inr 4816, 1), (Sum.inr 4817, 1), (Sum.inr 4821, 1), (Sum.inr 4836, 1), (Sum.inr 4891, 1), (Sum.inr 5086, 1), (Sum.inr 5090, 1), (Sum.inr 5105, 1), (Sum.inr 5254, 1), (Sum.inr 5260, 1), (Sum.inr 5267, 2), (Sum.inr 5287, 1), (Sum.inr 5360, 2), (Sum.inr 5361, 1), (Sum.inr 5370, 1), (Sum.inr 5397, 1), (Sum.inr 5406, 1), (Sum.inr 5407, 1), (Sum.inr 5410, 1), (Sum.inr 5411, 3), (Sum.inr 5412, 1), (Sum.inr 5425, 1), (Sum.inr 5426, 1), (Sum.inr 5434, 1), (Sum.inr 5435, 1), (Sum.inr 5436, 1)]

theorem sourceEq933 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm933 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA933 + difference 0 1) (sourceB933 + difference 1 0) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA933 + difference 0 1) (sourceB933 + difference 1 0) sourceC933) = raw15405 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15405; decide +kernel
    rw [ha]
    exact (canonical15405 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA933 + difference 0 2) (sourceB933 + difference 2 0) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA933 + difference 0 2) (sourceB933 + difference 2 0) sourceC933) = raw15406 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15406; decide +kernel
    rw [ha]
    exact (canonical15406 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA933 + difference 0 3) (sourceB933 + difference 3 0) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5410) := by
    have ha : (tripleCharges (sourceA933 + difference 0 3) (sourceB933 + difference 3 0) sourceC933) = raw15407 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15407; decide +kernel
    rw [ha]
    exact (canonical15407 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA933 + difference 0 4) (sourceB933 + difference 4 0) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA933 + difference 0 4) (sourceB933 + difference 4 0) sourceC933) = raw15408 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15408; decide +kernel
    rw [ha]
    exact (canonical15408 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA933 + difference 0 5) (sourceB933 + difference 5 0) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA933 + difference 0 5) (sourceB933 + difference 5 0) sourceC933) = raw15409 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15409; decide +kernel
    rw [ha]
    exact (canonical15409 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA933 + difference 1 0) (sourceB933 + difference 0 1) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4891) := by
    have ha : (tripleCharges (sourceA933 + difference 1 0) (sourceB933 + difference 0 1) sourceC933) = raw15410 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15410; decide +kernel
    rw [ha]
    exact (canonical15410 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA933 + difference 1 2) (sourceB933 + difference 2 1) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5407) := by
    have ha : (tripleCharges (sourceA933 + difference 1 2) (sourceB933 + difference 2 1) sourceC933) = raw15411 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15411; decide +kernel
    rw [ha]
    exact (canonical15411 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA933 + difference 1 3) (sourceB933 + difference 3 1) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA933 + difference 1 3) (sourceB933 + difference 3 1) sourceC933) = raw15412 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15412; decide +kernel
    rw [ha]
    exact (canonical15412 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA933 + difference 1 4) (sourceB933 + difference 4 1) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5412) := by
    have ha : (tripleCharges (sourceA933 + difference 1 4) (sourceB933 + difference 4 1) sourceC933) = raw15413 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15413; decide +kernel
    rw [ha]
    exact (canonical15413 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA933 + difference 1 5) (sourceB933 + difference 5 1) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA933 + difference 1 5) (sourceB933 + difference 5 1) sourceC933) = raw15414 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15414; decide +kernel
    rw [ha]
    exact (canonical15414 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA933 + difference 2 0) (sourceB933 + difference 0 2) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4816) := by
    have ha : (tripleCharges (sourceA933 + difference 2 0) (sourceB933 + difference 0 2) sourceC933) = raw15415 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15415; decide +kernel
    rw [ha]
    exact (canonical15415 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA933 + difference 2 1) (sourceB933 + difference 1 2) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA933 + difference 2 1) (sourceB933 + difference 1 2) sourceC933) = raw15416 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15416; decide +kernel
    rw [ha]
    exact (canonical15416 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA933 + difference 2 3) (sourceB933 + difference 3 2) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5397) := by
    have ha : (tripleCharges (sourceA933 + difference 2 3) (sourceB933 + difference 3 2) sourceC933) = raw15417 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15417; decide +kernel
    rw [ha]
    exact (canonical15417 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA933 + difference 2 4) (sourceB933 + difference 4 2) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5426) := by
    have ha : (tripleCharges (sourceA933 + difference 2 4) (sourceB933 + difference 4 2) sourceC933) = raw15418 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15418; decide +kernel
    rw [ha]
    exact (canonical15418 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA933 + difference 2 5) (sourceB933 + difference 5 2) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA933 + difference 2 5) (sourceB933 + difference 5 2) sourceC933) = raw15419 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15419; decide +kernel
    rw [ha]
    exact (canonical15419 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA933 + difference 3 0) (sourceB933 + difference 0 3) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4836) := by
    have ha : (tripleCharges (sourceA933 + difference 3 0) (sourceB933 + difference 0 3) sourceC933) = raw15420 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15420; decide +kernel
    rw [ha]
    exact (canonical15420 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA933 + difference 3 1) (sourceB933 + difference 1 3) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA933 + difference 3 1) (sourceB933 + difference 1 3) sourceC933) = raw15421 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15421; decide +kernel
    rw [ha]
    exact (canonical15421 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA933 + difference 3 2) (sourceB933 + difference 2 3) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5254) := by
    have ha : (tripleCharges (sourceA933 + difference 3 2) (sourceB933 + difference 2 3) sourceC933) = raw15422 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15422; decide +kernel
    rw [ha]
    exact (canonical15422 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA933 + difference 3 4) (sourceB933 + difference 4 3) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA933 + difference 3 4) (sourceB933 + difference 4 3) sourceC933) = raw15423 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15423; decide +kernel
    rw [ha]
    exact (canonical15423 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA933 + difference 3 5) (sourceB933 + difference 5 3) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA933 + difference 3 5) (sourceB933 + difference 5 3) sourceC933) = raw15424 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15424; decide +kernel
    rw [ha]
    exact (canonical15424 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA933 + difference 4 0) (sourceB933 + difference 0 4) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4821) := by
    have ha : (tripleCharges (sourceA933 + difference 4 0) (sourceB933 + difference 0 4) sourceC933) = raw15425 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15425; decide +kernel
    rw [ha]
    exact (canonical15425 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA933 + difference 4 1) (sourceB933 + difference 1 4) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5361) := by
    have ha : (tripleCharges (sourceA933 + difference 4 1) (sourceB933 + difference 1 4) sourceC933) = raw15426 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15426; decide +kernel
    rw [ha]
    exact (canonical15426 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA933 + difference 4 2) (sourceB933 + difference 2 4) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA933 + difference 4 2) (sourceB933 + difference 2 4) sourceC933) = raw15427 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15427; decide +kernel
    rw [ha]
    exact (canonical15427 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA933 + difference 4 3) (sourceB933 + difference 3 4) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5370) := by
    have ha : (tripleCharges (sourceA933 + difference 4 3) (sourceB933 + difference 3 4) sourceC933) = raw15428 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15428; decide +kernel
    rw [ha]
    exact (canonical15428 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA933 + difference 4 5) (sourceB933 + difference 5 4) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA933 + difference 4 5) (sourceB933 + difference 5 4) sourceC933) = raw15429 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15429; decide +kernel
    rw [ha]
    exact (canonical15429 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA933 + difference 5 0) (sourceB933 + difference 0 5) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA933 + difference 5 0) (sourceB933 + difference 0 5) sourceC933) = raw15430 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15430; decide +kernel
    rw [ha]
    exact (canonical15430 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA933 + difference 5 1) (sourceB933 + difference 1 5) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5090) := by
    have ha : (tripleCharges (sourceA933 + difference 5 1) (sourceB933 + difference 1 5) sourceC933) = raw15431 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15431; decide +kernel
    rw [ha]
    exact (canonical15431 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA933 + difference 5 2) (sourceB933 + difference 2 5) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5086) := by
    have ha : (tripleCharges (sourceA933 + difference 5 2) (sourceB933 + difference 2 5) sourceC933) = raw15432 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15432; decide +kernel
    rw [ha]
    exact (canonical15432 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA933 + difference 5 3) (sourceB933 + difference 3 5) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA933 + difference 5 3) (sourceB933 + difference 3 5) sourceC933) = raw15433 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15433; decide +kernel
    rw [ha]
    exact (canonical15433 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA933 + difference 5 4) (sourceB933 + difference 4 5) sourceC933) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA933 + difference 5 4) (sourceB933 + difference 4 5) sourceC933) = raw15434 := by
      apply Matrix.ext; unfold tripleCharges sourceA933 sourceB933 sourceC933 difference raw15434; decide +kernel
    rw [ha]
    exact (canonical15434 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA933 sourceB933 sourceC933
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm933, Integer.Sparse.eval]
  linarith only [hs]

def sourceA934 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB934 : Charge := ![2, 0, 0, -2, 0, 0]
def sourceC934 : Charge := ![0, 1, 0, 2, -1, -2]
def sourceForm934 : Integer.Sparse Master := [(Sum.inr 2196, 1), (Sum.inr 2197, 1), (Sum.inr 2207, 1), (Sum.inr 2217, 1), (Sum.inr 2253, 1), (Sum.inr 3016, 1), (Sum.inr 3025, 1), (Sum.inr 3038, 1), (Sum.inr 3086, 1), (Sum.inr 3464, 1), (Sum.inr 3479, 1), (Sum.inr 3480, 1), (Sum.inr 3541, 1), (Sum.inr 3762, 2), (Sum.inr 3771, 1), (Sum.inr 3772, 1), (Sum.inr 3796, 1), (Sum.inr 3801, 1), (Sum.inr 3803, 1), (Sum.inr 3808, 1), (Sum.inr 3809, 1), (Sum.inr 3813, 1), (Sum.inr 3841, 1), (Sum.inr 3853, 1), (Sum.inr 3856, 1), (Sum.inr 3872, 1), (Sum.inr 3877, 1), (Sum.inr 3883, 1), (Sum.inr 3982, 1)]

theorem sourceEq934 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm934 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA934 + difference 0 1) (sourceB934 + difference 1 0) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA934 + difference 0 1) (sourceB934 + difference 1 0) sourceC934) = raw15435 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15435; decide +kernel
    rw [ha]
    exact (canonical15435 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA934 + difference 0 2) (sourceB934 + difference 2 0) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA934 + difference 0 2) (sourceB934 + difference 2 0) sourceC934) = raw15436 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15436; decide +kernel
    rw [ha]
    exact (canonical15436 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA934 + difference 0 3) (sourceB934 + difference 3 0) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3808) := by
    have ha : (tripleCharges (sourceA934 + difference 0 3) (sourceB934 + difference 3 0) sourceC934) = raw15437 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15437; decide +kernel
    rw [ha]
    exact (canonical15437 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA934 + difference 0 4) (sourceB934 + difference 4 0) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA934 + difference 0 4) (sourceB934 + difference 4 0) sourceC934) = raw15438 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15438; decide +kernel
    rw [ha]
    exact (canonical15438 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA934 + difference 0 5) (sourceB934 + difference 5 0) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA934 + difference 0 5) (sourceB934 + difference 5 0) sourceC934) = raw15439 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15439; decide +kernel
    rw [ha]
    exact (canonical15439 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA934 + difference 1 0) (sourceB934 + difference 0 1) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2253) := by
    have ha : (tripleCharges (sourceA934 + difference 1 0) (sourceB934 + difference 0 1) sourceC934) = raw15440 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15440; decide +kernel
    rw [ha]
    exact (canonical15440 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA934 + difference 1 2) (sourceB934 + difference 2 1) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3803) := by
    have ha : (tripleCharges (sourceA934 + difference 1 2) (sourceB934 + difference 2 1) sourceC934) = raw15441 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15441; decide +kernel
    rw [ha]
    exact (canonical15441 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA934 + difference 1 3) (sourceB934 + difference 3 1) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA934 + difference 1 3) (sourceB934 + difference 3 1) sourceC934) = raw15442 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15442; decide +kernel
    rw [ha]
    exact (canonical15442 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA934 + difference 1 4) (sourceB934 + difference 4 1) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3856) := by
    have ha : (tripleCharges (sourceA934 + difference 1 4) (sourceB934 + difference 4 1) sourceC934) = raw15443 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15443; decide +kernel
    rw [ha]
    exact (canonical15443 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA934 + difference 1 5) (sourceB934 + difference 5 1) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA934 + difference 1 5) (sourceB934 + difference 5 1) sourceC934) = raw15444 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15444; decide +kernel
    rw [ha]
    exact (canonical15444 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA934 + difference 2 0) (sourceB934 + difference 0 2) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2196) := by
    have ha : (tripleCharges (sourceA934 + difference 2 0) (sourceB934 + difference 0 2) sourceC934) = raw15445 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15445; decide +kernel
    rw [ha]
    exact (canonical15445 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA934 + difference 2 1) (sourceB934 + difference 1 2) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA934 + difference 2 1) (sourceB934 + difference 1 2) sourceC934) = raw15446 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15446; decide +kernel
    rw [ha]
    exact (canonical15446 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA934 + difference 2 3) (sourceB934 + difference 3 2) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA934 + difference 2 3) (sourceB934 + difference 3 2) sourceC934) = raw15447 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15447; decide +kernel
    rw [ha]
    exact (canonical15447 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA934 + difference 2 4) (sourceB934 + difference 4 2) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3841) := by
    have ha : (tripleCharges (sourceA934 + difference 2 4) (sourceB934 + difference 4 2) sourceC934) = raw15448 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15448; decide +kernel
    rw [ha]
    exact (canonical15448 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA934 + difference 2 5) (sourceB934 + difference 5 2) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA934 + difference 2 5) (sourceB934 + difference 5 2) sourceC934) = raw15449 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15449; decide +kernel
    rw [ha]
    exact (canonical15449 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA934 + difference 3 0) (sourceB934 + difference 0 3) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA934 + difference 3 0) (sourceB934 + difference 0 3) sourceC934) = raw15450 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15450; decide +kernel
    rw [ha]
    exact (canonical15450 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA934 + difference 3 1) (sourceB934 + difference 1 3) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA934 + difference 3 1) (sourceB934 + difference 1 3) sourceC934) = raw15451 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15451; decide +kernel
    rw [ha]
    exact (canonical15451 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA934 + difference 3 2) (sourceB934 + difference 2 3) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3016) := by
    have ha : (tripleCharges (sourceA934 + difference 3 2) (sourceB934 + difference 2 3) sourceC934) = raw15452 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15452; decide +kernel
    rw [ha]
    exact (canonical15452 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA934 + difference 3 4) (sourceB934 + difference 4 3) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA934 + difference 3 4) (sourceB934 + difference 4 3) sourceC934) = raw15453 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15453; decide +kernel
    rw [ha]
    exact (canonical15453 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA934 + difference 3 5) (sourceB934 + difference 5 3) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA934 + difference 3 5) (sourceB934 + difference 5 3) sourceC934) = raw15454 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15454; decide +kernel
    rw [ha]
    exact (canonical15454 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA934 + difference 4 0) (sourceB934 + difference 0 4) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2217) := by
    have ha : (tripleCharges (sourceA934 + difference 4 0) (sourceB934 + difference 0 4) sourceC934) = raw15455 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15455; decide +kernel
    rw [ha]
    exact (canonical15455 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA934 + difference 4 1) (sourceB934 + difference 1 4) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3772) := by
    have ha : (tripleCharges (sourceA934 + difference 4 1) (sourceB934 + difference 1 4) sourceC934) = raw15456 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15456; decide +kernel
    rw [ha]
    exact (canonical15456 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA934 + difference 4 2) (sourceB934 + difference 2 4) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA934 + difference 4 2) (sourceB934 + difference 2 4) sourceC934) = raw15457 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15457; decide +kernel
    rw [ha]
    exact (canonical15457 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA934 + difference 4 3) (sourceB934 + difference 3 4) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3771) := by
    have ha : (tripleCharges (sourceA934 + difference 4 3) (sourceB934 + difference 3 4) sourceC934) = raw15458 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15458; decide +kernel
    rw [ha]
    exact (canonical15458 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA934 + difference 4 5) (sourceB934 + difference 5 4) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA934 + difference 4 5) (sourceB934 + difference 5 4) sourceC934) = raw15459 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15459; decide +kernel
    rw [ha]
    exact (canonical15459 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA934 + difference 5 0) (sourceB934 + difference 0 5) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2207) := by
    have ha : (tripleCharges (sourceA934 + difference 5 0) (sourceB934 + difference 0 5) sourceC934) = raw15460 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15460; decide +kernel
    rw [ha]
    exact (canonical15460 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA934 + difference 5 1) (sourceB934 + difference 1 5) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA934 + difference 5 1) (sourceB934 + difference 1 5) sourceC934) = raw15461 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15461; decide +kernel
    rw [ha]
    exact (canonical15461 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA934 + difference 5 2) (sourceB934 + difference 2 5) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3464) := by
    have ha : (tripleCharges (sourceA934 + difference 5 2) (sourceB934 + difference 2 5) sourceC934) = raw15462 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15462; decide +kernel
    rw [ha]
    exact (canonical15462 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA934 + difference 5 3) (sourceB934 + difference 3 5) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3479) := by
    have ha : (tripleCharges (sourceA934 + difference 5 3) (sourceB934 + difference 3 5) sourceC934) = raw15463 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15463; decide +kernel
    rw [ha]
    exact (canonical15463 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA934 + difference 5 4) (sourceB934 + difference 4 5) sourceC934) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA934 + difference 5 4) (sourceB934 + difference 4 5) sourceC934) = raw15464 := by
      apply Matrix.ext; unfold tripleCharges sourceA934 sourceB934 sourceC934 difference raw15464; decide +kernel
    rw [ha]
    exact (canonical15464 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA934 sourceB934 sourceC934
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm934, Integer.Sparse.eval]
  linarith only [hs]

def sourceA935 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB935 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC935 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceForm935 : Integer.Sparse Master := [(Sum.inr 4992, 1), (Sum.inr 4993, 1), (Sum.inr 4999, 2), (Sum.inr 5004, 1), (Sum.inr 5005, 2), (Sum.inr 5011, 1), (Sum.inr 5145, 2), (Sum.inr 5251, 1), (Sum.inr 5265, 1), (Sum.inr 5282, 1), (Sum.inr 5379, 2), (Sum.inr 5414, 1), (Sum.inr 5421, 2), (Sum.inr 5424, 2), (Sum.inr 5431, 2), (Sum.inr 5439, 1), (Sum.inr 5446, 2), (Sum.inr 5450, 1), (Sum.inr 5470, 2), (Sum.inr 5472, 1), (Sum.inr 5481, 1)]

theorem sourceEq935 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm935 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA935 + difference 0 1) (sourceB935 + difference 1 0) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA935 + difference 0 1) (sourceB935 + difference 1 0) sourceC935) = raw15465 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15465; decide +kernel
    rw [ha]
    exact (canonical15465 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA935 + difference 0 2) (sourceB935 + difference 2 0) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA935 + difference 0 2) (sourceB935 + difference 2 0) sourceC935) = raw15466 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15466; decide +kernel
    rw [ha]
    exact (canonical15466 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA935 + difference 0 3) (sourceB935 + difference 3 0) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5470) := by
    have ha : (tripleCharges (sourceA935 + difference 0 3) (sourceB935 + difference 3 0) sourceC935) = raw15467 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15467; decide +kernel
    rw [ha]
    exact (canonical15467 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA935 + difference 0 4) (sourceB935 + difference 4 0) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5481) := by
    have ha : (tripleCharges (sourceA935 + difference 0 4) (sourceB935 + difference 4 0) sourceC935) = raw15468 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15468; decide +kernel
    rw [ha]
    exact (canonical15468 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA935 + difference 0 5) (sourceB935 + difference 5 0) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA935 + difference 0 5) (sourceB935 + difference 5 0) sourceC935) = raw15469 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15469; decide +kernel
    rw [ha]
    exact (canonical15469 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA935 + difference 1 0) (sourceB935 + difference 0 1) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA935 + difference 1 0) (sourceB935 + difference 0 1) sourceC935) = raw15470 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15470; decide +kernel
    rw [ha]
    exact (canonical15470 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA935 + difference 1 2) (sourceB935 + difference 2 1) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA935 + difference 1 2) (sourceB935 + difference 2 1) sourceC935) = raw8803 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw8803; decide +kernel
    rw [ha]
    exact (canonical8803 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA935 + difference 1 3) (sourceB935 + difference 3 1) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA935 + difference 1 3) (sourceB935 + difference 3 1) sourceC935) = raw8804 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw8804; decide +kernel
    rw [ha]
    exact (canonical8804 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA935 + difference 1 4) (sourceB935 + difference 4 1) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5439) := by
    have ha : (tripleCharges (sourceA935 + difference 1 4) (sourceB935 + difference 4 1) sourceC935) = raw8805 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw8805; decide +kernel
    rw [ha]
    exact (canonical8805 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA935 + difference 1 5) (sourceB935 + difference 5 1) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA935 + difference 1 5) (sourceB935 + difference 5 1) sourceC935) = raw8806 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw8806; decide +kernel
    rw [ha]
    exact (canonical8806 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA935 + difference 2 0) (sourceB935 + difference 0 2) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA935 + difference 2 0) (sourceB935 + difference 0 2) sourceC935) = raw8813 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw8813; decide +kernel
    rw [ha]
    exact (canonical8813 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA935 + difference 2 1) (sourceB935 + difference 1 2) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA935 + difference 2 1) (sourceB935 + difference 1 2) sourceC935) = raw15471 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15471; decide +kernel
    rw [ha]
    exact (canonical15471 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA935 + difference 2 3) (sourceB935 + difference 3 2) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA935 + difference 2 3) (sourceB935 + difference 3 2) sourceC935) = raw15472 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15472; decide +kernel
    rw [ha]
    exact (canonical15472 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA935 + difference 2 4) (sourceB935 + difference 4 2) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA935 + difference 2 4) (sourceB935 + difference 4 2) sourceC935) = raw15473 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15473; decide +kernel
    rw [ha]
    exact (canonical15473 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA935 + difference 2 5) (sourceB935 + difference 5 2) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA935 + difference 2 5) (sourceB935 + difference 5 2) sourceC935) = raw15474 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15474; decide +kernel
    rw [ha]
    exact (canonical15474 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA935 + difference 3 0) (sourceB935 + difference 0 3) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5145) := by
    have ha : (tripleCharges (sourceA935 + difference 3 0) (sourceB935 + difference 0 3) sourceC935) = raw8818 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw8818; decide +kernel
    rw [ha]
    exact (canonical8818 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA935 + difference 3 1) (sourceB935 + difference 1 3) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA935 + difference 3 1) (sourceB935 + difference 1 3) sourceC935) = raw15475 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15475; decide +kernel
    rw [ha]
    exact (canonical15475 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA935 + difference 3 2) (sourceB935 + difference 2 3) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5421) := by
    have ha : (tripleCharges (sourceA935 + difference 3 2) (sourceB935 + difference 2 3) sourceC935) = raw15476 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15476; decide +kernel
    rw [ha]
    exact (canonical15476 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA935 + difference 3 4) (sourceB935 + difference 4 3) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5424) := by
    have ha : (tripleCharges (sourceA935 + difference 3 4) (sourceB935 + difference 4 3) sourceC935) = raw15477 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15477; decide +kernel
    rw [ha]
    exact (canonical15477 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA935 + difference 3 5) (sourceB935 + difference 5 3) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA935 + difference 3 5) (sourceB935 + difference 5 3) sourceC935) = raw15478 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15478; decide +kernel
    rw [ha]
    exact (canonical15478 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA935 + difference 4 0) (sourceB935 + difference 0 4) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5011) := by
    have ha : (tripleCharges (sourceA935 + difference 4 0) (sourceB935 + difference 0 4) sourceC935) = raw8823 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw8823; decide +kernel
    rw [ha]
    exact (canonical8823 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA935 + difference 4 1) (sourceB935 + difference 1 4) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5004) := by
    have ha : (tripleCharges (sourceA935 + difference 4 1) (sourceB935 + difference 1 4) sourceC935) = raw15479 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15479; decide +kernel
    rw [ha]
    exact (canonical15479 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA935 + difference 4 2) (sourceB935 + difference 2 4) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5005) := by
    have ha : (tripleCharges (sourceA935 + difference 4 2) (sourceB935 + difference 2 4) sourceC935) = raw15480 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15480; decide +kernel
    rw [ha]
    exact (canonical15480 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA935 + difference 4 3) (sourceB935 + difference 3 4) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5005) := by
    have ha : (tripleCharges (sourceA935 + difference 4 3) (sourceB935 + difference 3 4) sourceC935) = raw15481 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15481; decide +kernel
    rw [ha]
    exact (canonical15481 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA935 + difference 4 5) (sourceB935 + difference 5 4) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA935 + difference 4 5) (sourceB935 + difference 5 4) sourceC935) = raw15482 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15482; decide +kernel
    rw [ha]
    exact (canonical15482 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA935 + difference 5 0) (sourceB935 + difference 0 5) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4992) := by
    have ha : (tripleCharges (sourceA935 + difference 5 0) (sourceB935 + difference 0 5) sourceC935) = raw8828 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw8828; decide +kernel
    rw [ha]
    exact (canonical8828 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA935 + difference 5 1) (sourceB935 + difference 1 5) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4993) := by
    have ha : (tripleCharges (sourceA935 + difference 5 1) (sourceB935 + difference 1 5) sourceC935) = raw15483 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15483; decide +kernel
    rw [ha]
    exact (canonical15483 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA935 + difference 5 2) (sourceB935 + difference 2 5) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4999) := by
    have ha : (tripleCharges (sourceA935 + difference 5 2) (sourceB935 + difference 2 5) sourceC935) = raw15484 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15484; decide +kernel
    rw [ha]
    exact (canonical15484 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA935 + difference 5 3) (sourceB935 + difference 3 5) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4999) := by
    have ha : (tripleCharges (sourceA935 + difference 5 3) (sourceB935 + difference 3 5) sourceC935) = raw15485 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15485; decide +kernel
    rw [ha]
    exact (canonical15485 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA935 + difference 5 4) (sourceB935 + difference 4 5) sourceC935) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5251) := by
    have ha : (tripleCharges (sourceA935 + difference 5 4) (sourceB935 + difference 4 5) sourceC935) = raw15486 := by
      apply Matrix.ext; unfold tripleCharges sourceA935 sourceB935 sourceC935 difference raw15486; decide +kernel
    rw [ha]
    exact (canonical15486 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA935 sourceB935 sourceC935
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm935, Integer.Sparse.eval]
  linarith only [hs]

def sourceA936 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB936 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC936 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceForm936 : Integer.Sparse Master := [(Sum.inr 2378, 1), (Sum.inr 2379, 1), (Sum.inr 2384, 2), (Sum.inr 2710, 1), (Sum.inr 2912, 1), (Sum.inr 2925, 2), (Sum.inr 3078, 1), (Sum.inr 3337, 1), (Sum.inr 3342, 2), (Sum.inr 3526, 1), (Sum.inr 3720, 2), (Sum.inr 3869, 1), (Sum.inr 3946, 2), (Sum.inr 3955, 2), (Sum.inr 3957, 1), (Sum.inr 3959, 2), (Sum.inr 3979, 1), (Sum.inr 3990, 2), (Sum.inr 4012, 1), (Sum.inr 4026, 2), (Sum.inr 4029, 1)]

theorem sourceEq936 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm936 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA936 + difference 0 1) (sourceB936 + difference 1 0) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA936 + difference 0 1) (sourceB936 + difference 1 0) sourceC936) = raw15487 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15487; decide +kernel
    rw [ha]
    exact (canonical15487 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA936 + difference 0 2) (sourceB936 + difference 2 0) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3955) := by
    have ha : (tripleCharges (sourceA936 + difference 0 2) (sourceB936 + difference 2 0) sourceC936) = raw15488 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15488; decide +kernel
    rw [ha]
    exact (canonical15488 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA936 + difference 0 3) (sourceB936 + difference 3 0) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3955) := by
    have ha : (tripleCharges (sourceA936 + difference 0 3) (sourceB936 + difference 3 0) sourceC936) = raw15489 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15489; decide +kernel
    rw [ha]
    exact (canonical15489 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA936 + difference 0 4) (sourceB936 + difference 4 0) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3979) := by
    have ha : (tripleCharges (sourceA936 + difference 0 4) (sourceB936 + difference 4 0) sourceC936) = raw15490 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15490; decide +kernel
    rw [ha]
    exact (canonical15490 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA936 + difference 0 5) (sourceB936 + difference 5 0) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA936 + difference 0 5) (sourceB936 + difference 5 0) sourceC936) = raw15491 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15491; decide +kernel
    rw [ha]
    exact (canonical15491 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA936 + difference 1 0) (sourceB936 + difference 0 1) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA936 + difference 1 0) (sourceB936 + difference 0 1) sourceC936) = raw15492 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15492; decide +kernel
    rw [ha]
    exact (canonical15492 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA936 + difference 1 2) (sourceB936 + difference 2 1) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA936 + difference 1 2) (sourceB936 + difference 2 1) sourceC936) = raw8833 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw8833; decide +kernel
    rw [ha]
    exact (canonical8833 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA936 + difference 1 3) (sourceB936 + difference 3 1) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA936 + difference 1 3) (sourceB936 + difference 3 1) sourceC936) = raw8834 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw8834; decide +kernel
    rw [ha]
    exact (canonical8834 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA936 + difference 1 4) (sourceB936 + difference 4 1) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4012) := by
    have ha : (tripleCharges (sourceA936 + difference 1 4) (sourceB936 + difference 4 1) sourceC936) = raw8835 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw8835; decide +kernel
    rw [ha]
    exact (canonical8835 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA936 + difference 1 5) (sourceB936 + difference 5 1) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA936 + difference 1 5) (sourceB936 + difference 5 1) sourceC936) = raw8836 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw8836; decide +kernel
    rw [ha]
    exact (canonical8836 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA936 + difference 2 0) (sourceB936 + difference 0 2) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA936 + difference 2 0) (sourceB936 + difference 0 2) sourceC936) = raw8843 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw8843; decide +kernel
    rw [ha]
    exact (canonical8843 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA936 + difference 2 1) (sourceB936 + difference 1 2) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3720) := by
    have ha : (tripleCharges (sourceA936 + difference 2 1) (sourceB936 + difference 1 2) sourceC936) = raw15493 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15493; decide +kernel
    rw [ha]
    exact (canonical15493 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA936 + difference 2 3) (sourceB936 + difference 3 2) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3946) := by
    have ha : (tripleCharges (sourceA936 + difference 2 3) (sourceB936 + difference 3 2) sourceC936) = raw15494 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15494; decide +kernel
    rw [ha]
    exact (canonical15494 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA936 + difference 2 4) (sourceB936 + difference 4 2) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA936 + difference 2 4) (sourceB936 + difference 4 2) sourceC936) = raw15495 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15495; decide +kernel
    rw [ha]
    exact (canonical15495 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA936 + difference 2 5) (sourceB936 + difference 5 2) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4026) := by
    have ha : (tripleCharges (sourceA936 + difference 2 5) (sourceB936 + difference 5 2) sourceC936) = raw15496 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15496; decide +kernel
    rw [ha]
    exact (canonical15496 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA936 + difference 3 0) (sourceB936 + difference 0 3) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA936 + difference 3 0) (sourceB936 + difference 0 3) sourceC936) = raw8848 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw8848; decide +kernel
    rw [ha]
    exact (canonical8848 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA936 + difference 3 1) (sourceB936 + difference 1 3) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3720) := by
    have ha : (tripleCharges (sourceA936 + difference 3 1) (sourceB936 + difference 1 3) sourceC936) = raw15497 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15497; decide +kernel
    rw [ha]
    exact (canonical15497 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA936 + difference 3 2) (sourceB936 + difference 2 3) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3946) := by
    have ha : (tripleCharges (sourceA936 + difference 3 2) (sourceB936 + difference 2 3) sourceC936) = raw15498 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15498; decide +kernel
    rw [ha]
    exact (canonical15498 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA936 + difference 3 4) (sourceB936 + difference 4 3) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3990) := by
    have ha : (tripleCharges (sourceA936 + difference 3 4) (sourceB936 + difference 4 3) sourceC936) = raw15499 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15499; decide +kernel
    rw [ha]
    exact (canonical15499 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA936 + difference 3 5) (sourceB936 + difference 5 3) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4026) := by
    have ha : (tripleCharges (sourceA936 + difference 3 5) (sourceB936 + difference 5 3) sourceC936) = raw15500 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15500; decide +kernel
    rw [ha]
    exact (canonical15500 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA936 + difference 4 0) (sourceB936 + difference 0 4) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2912) := by
    have ha : (tripleCharges (sourceA936 + difference 4 0) (sourceB936 + difference 0 4) sourceC936) = raw8853 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw8853; decide +kernel
    rw [ha]
    exact (canonical8853 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA936 + difference 4 1) (sourceB936 + difference 1 4) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3337) := by
    have ha : (tripleCharges (sourceA936 + difference 4 1) (sourceB936 + difference 1 4) sourceC936) = raw15501 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15501; decide +kernel
    rw [ha]
    exact (canonical15501 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA936 + difference 4 2) (sourceB936 + difference 2 4) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3342) := by
    have ha : (tripleCharges (sourceA936 + difference 4 2) (sourceB936 + difference 2 4) sourceC936) = raw15502 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15502; decide +kernel
    rw [ha]
    exact (canonical15502 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA936 + difference 4 3) (sourceB936 + difference 3 4) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3342) := by
    have ha : (tripleCharges (sourceA936 + difference 4 3) (sourceB936 + difference 3 4) sourceC936) = raw15503 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15503; decide +kernel
    rw [ha]
    exact (canonical15503 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA936 + difference 4 5) (sourceB936 + difference 5 4) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA936 + difference 4 5) (sourceB936 + difference 5 4) sourceC936) = raw15504 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15504; decide +kernel
    rw [ha]
    exact (canonical15504 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA936 + difference 5 0) (sourceB936 + difference 0 5) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2378) := by
    have ha : (tripleCharges (sourceA936 + difference 5 0) (sourceB936 + difference 0 5) sourceC936) = raw8858 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw8858; decide +kernel
    rw [ha]
    exact (canonical8858 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA936 + difference 5 1) (sourceB936 + difference 1 5) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2379) := by
    have ha : (tripleCharges (sourceA936 + difference 5 1) (sourceB936 + difference 1 5) sourceC936) = raw15505 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15505; decide +kernel
    rw [ha]
    exact (canonical15505 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA936 + difference 5 2) (sourceB936 + difference 2 5) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2384) := by
    have ha : (tripleCharges (sourceA936 + difference 5 2) (sourceB936 + difference 2 5) sourceC936) = raw15506 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15506; decide +kernel
    rw [ha]
    exact (canonical15506 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA936 + difference 5 3) (sourceB936 + difference 3 5) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2384) := by
    have ha : (tripleCharges (sourceA936 + difference 5 3) (sourceB936 + difference 3 5) sourceC936) = raw15507 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15507; decide +kernel
    rw [ha]
    exact (canonical15507 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA936 + difference 5 4) (sourceB936 + difference 4 5) sourceC936) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2710) := by
    have ha : (tripleCharges (sourceA936 + difference 5 4) (sourceB936 + difference 4 5) sourceC936) = raw15508 := by
      apply Matrix.ext; unfold tripleCharges sourceA936 sourceB936 sourceC936 difference raw15508; decide +kernel
    rw [ha]
    exact (canonical15508 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA936 sourceB936 sourceC936
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm936, Integer.Sparse.eval]
  linarith only [hs]

def sourceA937 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB937 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC937 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceForm937 : Integer.Sparse Master := [(Sum.inr 2389, 1), (Sum.inr 2390, 2), (Sum.inr 2396, 1), (Sum.inr 2730, 1), (Sum.inr 3345, 1), (Sum.inr 3346, 2), (Sum.inr 3350, 1), (Sum.inr 3539, 1), (Sum.inr 3562, 2), (Sum.inr 3580, 1), (Sum.inr 3819, 1), (Sum.inr 3832, 2), (Sum.inr 3843, 2), (Sum.inr 3858, 1), (Sum.inr 3873, 2), (Sum.inr 3875, 2), (Sum.inr 3884, 2), (Sum.inr 3887, 1), (Sum.inr 3947, 2), (Sum.inr 3991, 1), (Sum.inr 4002, 1)]

theorem sourceEq937 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm937 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA937 + difference 0 1) (sourceB937 + difference 1 0) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3819) := by
    have ha : (tripleCharges (sourceA937 + difference 0 1) (sourceB937 + difference 1 0) sourceC937) = raw15509 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15509; decide +kernel
    rw [ha]
    exact (canonical15509 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA937 + difference 0 2) (sourceB937 + difference 2 0) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3947) := by
    have ha : (tripleCharges (sourceA937 + difference 0 2) (sourceB937 + difference 2 0) sourceC937) = raw15510 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15510; decide +kernel
    rw [ha]
    exact (canonical15510 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA937 + difference 0 3) (sourceB937 + difference 3 0) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3947) := by
    have ha : (tripleCharges (sourceA937 + difference 0 3) (sourceB937 + difference 3 0) sourceC937) = raw15511 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15511; decide +kernel
    rw [ha]
    exact (canonical15511 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA937 + difference 0 4) (sourceB937 + difference 4 0) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3991) := by
    have ha : (tripleCharges (sourceA937 + difference 0 4) (sourceB937 + difference 4 0) sourceC937) = raw15512 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15512; decide +kernel
    rw [ha]
    exact (canonical15512 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA937 + difference 0 5) (sourceB937 + difference 5 0) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4002) := by
    have ha : (tripleCharges (sourceA937 + difference 0 5) (sourceB937 + difference 5 0) sourceC937) = raw15513 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15513; decide +kernel
    rw [ha]
    exact (canonical15513 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA937 + difference 1 0) (sourceB937 + difference 0 1) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA937 + difference 1 0) (sourceB937 + difference 0 1) sourceC937) = raw15514 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15514; decide +kernel
    rw [ha]
    exact (canonical15514 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA937 + difference 1 2) (sourceB937 + difference 2 1) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA937 + difference 1 2) (sourceB937 + difference 2 1) sourceC937) = raw8863 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw8863; decide +kernel
    rw [ha]
    exact (canonical8863 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA937 + difference 1 3) (sourceB937 + difference 3 1) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA937 + difference 1 3) (sourceB937 + difference 3 1) sourceC937) = raw8864 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw8864; decide +kernel
    rw [ha]
    exact (canonical8864 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA937 + difference 1 4) (sourceB937 + difference 4 1) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3858) := by
    have ha : (tripleCharges (sourceA937 + difference 1 4) (sourceB937 + difference 4 1) sourceC937) = raw8865 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw8865; decide +kernel
    rw [ha]
    exact (canonical8865 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA937 + difference 1 5) (sourceB937 + difference 5 1) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3887) := by
    have ha : (tripleCharges (sourceA937 + difference 1 5) (sourceB937 + difference 5 1) sourceC937) = raw8866 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw8866; decide +kernel
    rw [ha]
    exact (canonical8866 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA937 + difference 2 0) (sourceB937 + difference 0 2) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA937 + difference 2 0) (sourceB937 + difference 0 2) sourceC937) = raw8873 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw8873; decide +kernel
    rw [ha]
    exact (canonical8873 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA937 + difference 2 1) (sourceB937 + difference 1 2) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA937 + difference 2 1) (sourceB937 + difference 1 2) sourceC937) = raw15515 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15515; decide +kernel
    rw [ha]
    exact (canonical15515 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA937 + difference 2 3) (sourceB937 + difference 3 2) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA937 + difference 2 3) (sourceB937 + difference 3 2) sourceC937) = raw15516 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15516; decide +kernel
    rw [ha]
    exact (canonical15516 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA937 + difference 2 4) (sourceB937 + difference 4 2) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA937 + difference 2 4) (sourceB937 + difference 4 2) sourceC937) = raw15517 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15517; decide +kernel
    rw [ha]
    exact (canonical15517 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA937 + difference 2 5) (sourceB937 + difference 5 2) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA937 + difference 2 5) (sourceB937 + difference 5 2) sourceC937) = raw15518 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15518; decide +kernel
    rw [ha]
    exact (canonical15518 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA937 + difference 3 0) (sourceB937 + difference 0 3) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3562) := by
    have ha : (tripleCharges (sourceA937 + difference 3 0) (sourceB937 + difference 0 3) sourceC937) = raw8878 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw8878; decide +kernel
    rw [ha]
    exact (canonical8878 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA937 + difference 3 1) (sourceB937 + difference 1 3) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA937 + difference 3 1) (sourceB937 + difference 1 3) sourceC937) = raw15519 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15519; decide +kernel
    rw [ha]
    exact (canonical15519 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA937 + difference 3 2) (sourceB937 + difference 2 3) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3873) := by
    have ha : (tripleCharges (sourceA937 + difference 3 2) (sourceB937 + difference 2 3) sourceC937) = raw15520 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15520; decide +kernel
    rw [ha]
    exact (canonical15520 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA937 + difference 3 4) (sourceB937 + difference 4 3) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA937 + difference 3 4) (sourceB937 + difference 4 3) sourceC937) = raw15521 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15521; decide +kernel
    rw [ha]
    exact (canonical15521 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA937 + difference 3 5) (sourceB937 + difference 5 3) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA937 + difference 3 5) (sourceB937 + difference 5 3) sourceC937) = raw15522 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15522; decide +kernel
    rw [ha]
    exact (canonical15522 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA937 + difference 4 0) (sourceB937 + difference 0 4) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2396) := by
    have ha : (tripleCharges (sourceA937 + difference 4 0) (sourceB937 + difference 0 4) sourceC937) = raw8883 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw8883; decide +kernel
    rw [ha]
    exact (canonical8883 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA937 + difference 4 1) (sourceB937 + difference 1 4) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2389) := by
    have ha : (tripleCharges (sourceA937 + difference 4 1) (sourceB937 + difference 1 4) sourceC937) = raw15523 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15523; decide +kernel
    rw [ha]
    exact (canonical15523 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA937 + difference 4 2) (sourceB937 + difference 2 4) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2390) := by
    have ha : (tripleCharges (sourceA937 + difference 4 2) (sourceB937 + difference 2 4) sourceC937) = raw15524 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15524; decide +kernel
    rw [ha]
    exact (canonical15524 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA937 + difference 4 3) (sourceB937 + difference 3 4) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2390) := by
    have ha : (tripleCharges (sourceA937 + difference 4 3) (sourceB937 + difference 3 4) sourceC937) = raw15525 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15525; decide +kernel
    rw [ha]
    exact (canonical15525 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA937 + difference 4 5) (sourceB937 + difference 5 4) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA937 + difference 4 5) (sourceB937 + difference 5 4) sourceC937) = raw15526 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15526; decide +kernel
    rw [ha]
    exact (canonical15526 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA937 + difference 5 0) (sourceB937 + difference 0 5) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3350) := by
    have ha : (tripleCharges (sourceA937 + difference 5 0) (sourceB937 + difference 0 5) sourceC937) = raw8888 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw8888; decide +kernel
    rw [ha]
    exact (canonical8888 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA937 + difference 5 1) (sourceB937 + difference 1 5) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3345) := by
    have ha : (tripleCharges (sourceA937 + difference 5 1) (sourceB937 + difference 1 5) sourceC937) = raw15527 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15527; decide +kernel
    rw [ha]
    exact (canonical15527 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA937 + difference 5 2) (sourceB937 + difference 2 5) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3346) := by
    have ha : (tripleCharges (sourceA937 + difference 5 2) (sourceB937 + difference 2 5) sourceC937) = raw15528 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15528; decide +kernel
    rw [ha]
    exact (canonical15528 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA937 + difference 5 3) (sourceB937 + difference 3 5) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3346) := by
    have ha : (tripleCharges (sourceA937 + difference 5 3) (sourceB937 + difference 3 5) sourceC937) = raw15529 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15529; decide +kernel
    rw [ha]
    exact (canonical15529 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA937 + difference 5 4) (sourceB937 + difference 4 5) sourceC937) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA937 + difference 5 4) (sourceB937 + difference 4 5) sourceC937) = raw15530 := by
      apply Matrix.ext; unfold tripleCharges sourceA937 sourceB937 sourceC937 difference raw15530; decide +kernel
    rw [ha]
    exact (canonical15530 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA937 sourceB937 sourceC937
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm937, Integer.Sparse.eval]
  linarith only [hs]

def sourceA938 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB938 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC938 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceForm938 : Integer.Sparse Master := [(Sum.inr 3846, 1), (Sum.inr 3947, 2), (Sum.inr 3949, 1), (Sum.inr 3957, 1), (Sum.inr 4008, 1), (Sum.inr 4091, -1)]

theorem sourceEq938 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm938 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA938 + difference 0 0) (sourceB938 + difference 0 0) sourceC938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA938 + difference 0 0) (sourceB938 + difference 0 0) sourceC938) = raw8893 := by
      apply Matrix.ext; unfold tripleCharges sourceA938 sourceB938 sourceC938 difference raw8893; decide +kernel
    rw [ha]
    exact (canonical8893 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA938 + difference 0 1) (sourceB938 + difference 1 0) sourceC938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3949) := by
    have ha : (tripleCharges (sourceA938 + difference 0 1) (sourceB938 + difference 1 0) sourceC938) = raw15531 := by
      apply Matrix.ext; unfold tripleCharges sourceA938 sourceB938 sourceC938 difference raw15531; decide +kernel
    rw [ha]
    exact (canonical15531 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA938 + difference 0 2) (sourceB938 + difference 2 0) sourceC938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3947) := by
    have ha : (tripleCharges (sourceA938 + difference 0 2) (sourceB938 + difference 2 0) sourceC938) = raw15532 := by
      apply Matrix.ext; unfold tripleCharges sourceA938 sourceB938 sourceC938 difference raw15532; decide +kernel
    rw [ha]
    exact (canonical15532 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA938 + difference 0 3) (sourceB938 + difference 3 0) sourceC938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3947) := by
    have ha : (tripleCharges (sourceA938 + difference 0 3) (sourceB938 + difference 3 0) sourceC938) = raw15533 := by
      apply Matrix.ext; unfold tripleCharges sourceA938 sourceB938 sourceC938 difference raw15533; decide +kernel
    rw [ha]
    exact (canonical15533 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA938 + difference 0 4) (sourceB938 + difference 4 0) sourceC938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4008) := by
    have ha : (tripleCharges (sourceA938 + difference 0 4) (sourceB938 + difference 4 0) sourceC938) = raw15534 := by
      apply Matrix.ext; unfold tripleCharges sourceA938 sourceB938 sourceC938 difference raw15534; decide +kernel
    rw [ha]
    exact (canonical15534 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA938 + difference 0 5) (sourceB938 + difference 5 0) sourceC938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA938 + difference 0 5) (sourceB938 + difference 5 0) sourceC938) = raw15535 := by
      apply Matrix.ext; unfold tripleCharges sourceA938 sourceB938 sourceC938 difference raw15535; decide +kernel
    rw [ha]
    exact (canonical15535 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA938 + sourceB938) sourceC938) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA938 + sourceB938) sourceC938) = raw8898 := by
      apply Matrix.ext; unfold doubleCharges sourceA938 sourceB938 sourceC938 raw8898; decide +kernel
    rw [ha]
    exact (canonical8898 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA938 sourceB938 sourceC938
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm938, Integer.Sparse.eval]
  linarith only [hs]

def sourceA939 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB939 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC939 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceForm939 : Integer.Sparse Master := [(Sum.inr 3009, 1), (Sum.inr 3012, 1), (Sum.inr 3724, 2), (Sum.inr 3846, 1), (Sum.inr 3949, 1), (Sum.inr 4091, -1)]

theorem sourceEq939 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm939 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA939 + difference 0 1) (sourceB939 + difference 1 0) sourceC939) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3949) := by
    have ha : (tripleCharges (sourceA939 + difference 0 1) (sourceB939 + difference 1 0) sourceC939) = raw15531 := by
      apply Matrix.ext; unfold tripleCharges sourceA939 sourceB939 sourceC939 difference raw15531; decide +kernel
    rw [ha]
    exact (canonical15531 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA939 + difference 1 1) (sourceB939 + difference 1 1) sourceC939) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA939 + difference 1 1) (sourceB939 + difference 1 1) sourceC939) = raw8893 := by
      apply Matrix.ext; unfold tripleCharges sourceA939 sourceB939 sourceC939 difference raw8893; decide +kernel
    rw [ha]
    exact (canonical8893 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA939 + difference 2 1) (sourceB939 + difference 1 2) sourceC939) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3724) := by
    have ha : (tripleCharges (sourceA939 + difference 2 1) (sourceB939 + difference 1 2) sourceC939) = raw15536 := by
      apply Matrix.ext; unfold tripleCharges sourceA939 sourceB939 sourceC939 difference raw15536; decide +kernel
    rw [ha]
    exact (canonical15536 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA939 + difference 3 1) (sourceB939 + difference 1 3) sourceC939) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3724) := by
    have ha : (tripleCharges (sourceA939 + difference 3 1) (sourceB939 + difference 1 3) sourceC939) = raw15537 := by
      apply Matrix.ext; unfold tripleCharges sourceA939 sourceB939 sourceC939 difference raw15537; decide +kernel
    rw [ha]
    exact (canonical15537 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA939 + difference 4 1) (sourceB939 + difference 1 4) sourceC939) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3009) := by
    have ha : (tripleCharges (sourceA939 + difference 4 1) (sourceB939 + difference 1 4) sourceC939) = raw15538 := by
      apply Matrix.ext; unfold tripleCharges sourceA939 sourceB939 sourceC939 difference raw15538; decide +kernel
    rw [ha]
    exact (canonical15538 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA939 + difference 5 1) (sourceB939 + difference 1 5) sourceC939) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3012) := by
    have ha : (tripleCharges (sourceA939 + difference 5 1) (sourceB939 + difference 1 5) sourceC939) = raw15539 := by
      apply Matrix.ext; unfold tripleCharges sourceA939 sourceB939 sourceC939 difference raw15539; decide +kernel
    rw [ha]
    exact (canonical15539 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA939 + sourceB939) sourceC939) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA939 + sourceB939) sourceC939) = raw8898 := by
      apply Matrix.ext; unfold doubleCharges sourceA939 sourceB939 sourceC939 raw8898; decide +kernel
    rw [ha]
    exact (canonical8898 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA939 sourceB939 sourceC939
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm939, Integer.Sparse.eval]
  linarith only [hs]

def sourceA940 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB940 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceC940 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceForm940 : Integer.Sparse Master := [(Sum.inr 2567, 1), (Sum.inr 3724, 1), (Sum.inr 3827, 1), (Sum.inr 3838, 1), (Sum.inr 3846, 1), (Sum.inr 3849, 1), (Sum.inr 4091, -1)]

theorem sourceEq940 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm940 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA940 + difference 2 0) (sourceB940 + difference 0 2) sourceC940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2567) := by
    have ha : (tripleCharges (sourceA940 + difference 2 0) (sourceB940 + difference 0 2) sourceC940) = raw8904 := by
      apply Matrix.ext; unfold tripleCharges sourceA940 sourceB940 sourceC940 difference raw8904; decide +kernel
    rw [ha]
    exact (canonical8904 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA940 + difference 2 1) (sourceB940 + difference 1 2) sourceC940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3724) := by
    have ha : (tripleCharges (sourceA940 + difference 2 1) (sourceB940 + difference 1 2) sourceC940) = raw15536 := by
      apply Matrix.ext; unfold tripleCharges sourceA940 sourceB940 sourceC940 difference raw15536; decide +kernel
    rw [ha]
    exact (canonical15536 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA940 + difference 2 2) (sourceB940 + difference 2 2) sourceC940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA940 + difference 2 2) (sourceB940 + difference 2 2) sourceC940) = raw8893 := by
      apply Matrix.ext; unfold tripleCharges sourceA940 sourceB940 sourceC940 difference raw8893; decide +kernel
    rw [ha]
    exact (canonical8893 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA940 + difference 2 3) (sourceB940 + difference 3 2) sourceC940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3827) := by
    have ha : (tripleCharges (sourceA940 + difference 2 3) (sourceB940 + difference 3 2) sourceC940) = raw15540 := by
      apply Matrix.ext; unfold tripleCharges sourceA940 sourceB940 sourceC940 difference raw15540; decide +kernel
    rw [ha]
    exact (canonical15540 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA940 + difference 2 4) (sourceB940 + difference 4 2) sourceC940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3838) := by
    have ha : (tripleCharges (sourceA940 + difference 2 4) (sourceB940 + difference 4 2) sourceC940) = raw15541 := by
      apply Matrix.ext; unfold tripleCharges sourceA940 sourceB940 sourceC940 difference raw15541; decide +kernel
    rw [ha]
    exact (canonical15541 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA940 + difference 2 5) (sourceB940 + difference 5 2) sourceC940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA940 + difference 2 5) (sourceB940 + difference 5 2) sourceC940) = raw15542 := by
      apply Matrix.ext; unfold tripleCharges sourceA940 sourceB940 sourceC940 difference raw15542; decide +kernel
    rw [ha]
    exact (canonical15542 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA940 + sourceB940) sourceC940) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA940 + sourceB940) sourceC940) = raw8898 := by
      apply Matrix.ext; unfold doubleCharges sourceA940 sourceB940 sourceC940 raw8898; decide +kernel
    rw [ha]
    exact (canonical8898 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA940 sourceB940 sourceC940
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm940, Integer.Sparse.eval]
  linarith only [hs]

def sourceA941 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB941 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC941 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceForm941 : Integer.Sparse Master := [(Sum.inr 4791, 1), (Sum.inr 4795, 1), (Sum.inr 4799, 2), (Sum.inr 4863, 1), (Sum.inr 5181, 1), (Sum.inr 5184, 2), (Sum.inr 5243, 1), (Sum.inr 5348, 1), (Sum.inr 5350, 2), (Sum.inr 5354, 2), (Sum.inr 5379, 2), (Sum.inr 5383, 1), (Sum.inr 5406, 1), (Sum.inr 5414, 2), (Sum.inr 5429, 2), (Sum.inr 5430, 2), (Sum.inr 5431, 1), (Sum.inr 5447, 1), (Sum.inr 5471, 1), (Sum.inr 5472, 2), (Sum.inr 5482, 1)]

theorem sourceEq941 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm941 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA941 + difference 0 1) (sourceB941 + difference 1 0) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA941 + difference 0 1) (sourceB941 + difference 1 0) sourceC941) = raw15543 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15543; decide +kernel
    rw [ha]
    exact (canonical15543 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA941 + difference 0 2) (sourceB941 + difference 2 0) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA941 + difference 0 2) (sourceB941 + difference 2 0) sourceC941) = raw15544 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15544; decide +kernel
    rw [ha]
    exact (canonical15544 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA941 + difference 0 3) (sourceB941 + difference 3 0) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5472) := by
    have ha : (tripleCharges (sourceA941 + difference 0 3) (sourceB941 + difference 3 0) sourceC941) = raw15545 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15545; decide +kernel
    rw [ha]
    exact (canonical15545 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA941 + difference 0 4) (sourceB941 + difference 4 0) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5431) := by
    have ha : (tripleCharges (sourceA941 + difference 0 4) (sourceB941 + difference 4 0) sourceC941) = raw15546 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15546; decide +kernel
    rw [ha]
    exact (canonical15546 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA941 + difference 0 5) (sourceB941 + difference 5 0) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA941 + difference 0 5) (sourceB941 + difference 5 0) sourceC941) = raw15547 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15547; decide +kernel
    rw [ha]
    exact (canonical15547 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA941 + difference 1 0) (sourceB941 + difference 0 1) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4863) := by
    have ha : (tripleCharges (sourceA941 + difference 1 0) (sourceB941 + difference 0 1) sourceC941) = raw15548 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15548; decide +kernel
    rw [ha]
    exact (canonical15548 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA941 + difference 1 2) (sourceB941 + difference 2 1) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA941 + difference 1 2) (sourceB941 + difference 2 1) sourceC941) = raw15549 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15549; decide +kernel
    rw [ha]
    exact (canonical15549 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA941 + difference 1 3) (sourceB941 + difference 3 1) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5429) := by
    have ha : (tripleCharges (sourceA941 + difference 1 3) (sourceB941 + difference 3 1) sourceC941) = raw15550 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15550; decide +kernel
    rw [ha]
    exact (canonical15550 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA941 + difference 1 4) (sourceB941 + difference 4 1) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5383) := by
    have ha : (tripleCharges (sourceA941 + difference 1 4) (sourceB941 + difference 4 1) sourceC941) = raw15551 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15551; decide +kernel
    rw [ha]
    exact (canonical15551 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA941 + difference 1 5) (sourceB941 + difference 5 1) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5447) := by
    have ha : (tripleCharges (sourceA941 + difference 1 5) (sourceB941 + difference 5 1) sourceC941) = raw15552 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15552; decide +kernel
    rw [ha]
    exact (canonical15552 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA941 + difference 2 0) (sourceB941 + difference 0 2) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4799) := by
    have ha : (tripleCharges (sourceA941 + difference 2 0) (sourceB941 + difference 0 2) sourceC941) = raw15553 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15553; decide +kernel
    rw [ha]
    exact (canonical15553 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA941 + difference 2 1) (sourceB941 + difference 1 2) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5350) := by
    have ha : (tripleCharges (sourceA941 + difference 2 1) (sourceB941 + difference 1 2) sourceC941) = raw15554 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15554; decide +kernel
    rw [ha]
    exact (canonical15554 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA941 + difference 2 3) (sourceB941 + difference 3 2) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA941 + difference 2 3) (sourceB941 + difference 3 2) sourceC941) = raw15555 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15555; decide +kernel
    rw [ha]
    exact (canonical15555 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA941 + difference 2 4) (sourceB941 + difference 4 2) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA941 + difference 2 4) (sourceB941 + difference 4 2) sourceC941) = raw15556 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15556; decide +kernel
    rw [ha]
    exact (canonical15556 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA941 + difference 2 5) (sourceB941 + difference 5 2) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA941 + difference 2 5) (sourceB941 + difference 5 2) sourceC941) = raw15557 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15557; decide +kernel
    rw [ha]
    exact (canonical15557 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA941 + difference 3 0) (sourceB941 + difference 0 3) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4799) := by
    have ha : (tripleCharges (sourceA941 + difference 3 0) (sourceB941 + difference 0 3) sourceC941) = raw15558 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15558; decide +kernel
    rw [ha]
    exact (canonical15558 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA941 + difference 3 1) (sourceB941 + difference 1 3) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5350) := by
    have ha : (tripleCharges (sourceA941 + difference 3 1) (sourceB941 + difference 1 3) sourceC941) = raw15559 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15559; decide +kernel
    rw [ha]
    exact (canonical15559 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA941 + difference 3 2) (sourceB941 + difference 2 3) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5414) := by
    have ha : (tripleCharges (sourceA941 + difference 3 2) (sourceB941 + difference 2 3) sourceC941) = raw15560 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15560; decide +kernel
    rw [ha]
    exact (canonical15560 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA941 + difference 3 4) (sourceB941 + difference 4 3) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5379) := by
    have ha : (tripleCharges (sourceA941 + difference 3 4) (sourceB941 + difference 4 3) sourceC941) = raw15561 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15561; decide +kernel
    rw [ha]
    exact (canonical15561 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA941 + difference 3 5) (sourceB941 + difference 5 3) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5430) := by
    have ha : (tripleCharges (sourceA941 + difference 3 5) (sourceB941 + difference 5 3) sourceC941) = raw15562 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15562; decide +kernel
    rw [ha]
    exact (canonical15562 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA941 + difference 4 0) (sourceB941 + difference 0 4) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4795) := by
    have ha : (tripleCharges (sourceA941 + difference 4 0) (sourceB941 + difference 0 4) sourceC941) = raw15563 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15563; decide +kernel
    rw [ha]
    exact (canonical15563 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA941 + difference 4 1) (sourceB941 + difference 1 4) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5348) := by
    have ha : (tripleCharges (sourceA941 + difference 4 1) (sourceB941 + difference 1 4) sourceC941) = raw15564 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15564; decide +kernel
    rw [ha]
    exact (canonical15564 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA941 + difference 4 2) (sourceB941 + difference 2 4) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA941 + difference 4 2) (sourceB941 + difference 2 4) sourceC941) = raw15565 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15565; decide +kernel
    rw [ha]
    exact (canonical15565 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA941 + difference 4 3) (sourceB941 + difference 3 4) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5354) := by
    have ha : (tripleCharges (sourceA941 + difference 4 3) (sourceB941 + difference 3 4) sourceC941) = raw15566 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15566; decide +kernel
    rw [ha]
    exact (canonical15566 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA941 + difference 4 5) (sourceB941 + difference 5 4) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA941 + difference 4 5) (sourceB941 + difference 5 4) sourceC941) = raw15567 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15567; decide +kernel
    rw [ha]
    exact (canonical15567 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA941 + difference 5 0) (sourceB941 + difference 0 5) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4791) := by
    have ha : (tripleCharges (sourceA941 + difference 5 0) (sourceB941 + difference 0 5) sourceC941) = raw15568 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15568; decide +kernel
    rw [ha]
    exact (canonical15568 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA941 + difference 5 1) (sourceB941 + difference 1 5) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5181) := by
    have ha : (tripleCharges (sourceA941 + difference 5 1) (sourceB941 + difference 1 5) sourceC941) = raw15569 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15569; decide +kernel
    rw [ha]
    exact (canonical15569 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA941 + difference 5 2) (sourceB941 + difference 2 5) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5184) := by
    have ha : (tripleCharges (sourceA941 + difference 5 2) (sourceB941 + difference 2 5) sourceC941) = raw15570 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15570; decide +kernel
    rw [ha]
    exact (canonical15570 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA941 + difference 5 3) (sourceB941 + difference 3 5) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5184) := by
    have ha : (tripleCharges (sourceA941 + difference 5 3) (sourceB941 + difference 3 5) sourceC941) = raw15571 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15571; decide +kernel
    rw [ha]
    exact (canonical15571 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA941 + difference 5 4) (sourceB941 + difference 4 5) sourceC941) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5243) := by
    have ha : (tripleCharges (sourceA941 + difference 5 4) (sourceB941 + difference 4 5) sourceC941) = raw15572 := by
      apply Matrix.ext; unfold tripleCharges sourceA941 sourceB941 sourceC941 difference raw15572; decide +kernel
    rw [ha]
    exact (canonical15572 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA941 sourceB941 sourceC941
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm941, Integer.Sparse.eval]
  linarith only [hs]

def sourceA942 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB942 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC942 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceForm942 : Integer.Sparse Master := [(Sum.inr 2008, 1), (Sum.inr 2012, 1), (Sum.inr 2017, 2), (Sum.inr 2232, 1), (Sum.inr 2609, 1), (Sum.inr 2614, 2), (Sum.inr 2697, 1), (Sum.inr 3685, 1), (Sum.inr 3688, 2), (Sum.inr 3818, 2), (Sum.inr 3819, 2), (Sum.inr 3832, 2), (Sum.inr 3846, 2), (Sum.inr 3847, 1), (Sum.inr 3848, 2), (Sum.inr 3867, 1), (Sum.inr 3875, 1), (Sum.inr 3909, 1), (Sum.inr 3976, 1), (Sum.inr 3992, 1), (Sum.inr 4002, 2)]

theorem sourceEq942 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm942 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA942 + difference 0 1) (sourceB942 + difference 1 0) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3976) := by
    have ha : (tripleCharges (sourceA942 + difference 0 1) (sourceB942 + difference 1 0) sourceC942) = raw15573 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15573; decide +kernel
    rw [ha]
    exact (canonical15573 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA942 + difference 0 2) (sourceB942 + difference 2 0) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4002) := by
    have ha : (tripleCharges (sourceA942 + difference 0 2) (sourceB942 + difference 2 0) sourceC942) = raw15574 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15574; decide +kernel
    rw [ha]
    exact (canonical15574 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA942 + difference 0 3) (sourceB942 + difference 3 0) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4002) := by
    have ha : (tripleCharges (sourceA942 + difference 0 3) (sourceB942 + difference 3 0) sourceC942) = raw15575 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15575; decide +kernel
    rw [ha]
    exact (canonical15575 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA942 + difference 0 4) (sourceB942 + difference 4 0) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA942 + difference 0 4) (sourceB942 + difference 4 0) sourceC942) = raw15576 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15576; decide +kernel
    rw [ha]
    exact (canonical15576 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA942 + difference 0 5) (sourceB942 + difference 5 0) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3992) := by
    have ha : (tripleCharges (sourceA942 + difference 0 5) (sourceB942 + difference 5 0) sourceC942) = raw15577 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15577; decide +kernel
    rw [ha]
    exact (canonical15577 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA942 + difference 1 0) (sourceB942 + difference 0 1) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2232) := by
    have ha : (tripleCharges (sourceA942 + difference 1 0) (sourceB942 + difference 0 1) sourceC942) = raw15578 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15578; decide +kernel
    rw [ha]
    exact (canonical15578 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA942 + difference 1 2) (sourceB942 + difference 2 1) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA942 + difference 1 2) (sourceB942 + difference 2 1) sourceC942) = raw15579 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15579; decide +kernel
    rw [ha]
    exact (canonical15579 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA942 + difference 1 3) (sourceB942 + difference 3 1) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3846) := by
    have ha : (tripleCharges (sourceA942 + difference 1 3) (sourceB942 + difference 3 1) sourceC942) = raw15580 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15580; decide +kernel
    rw [ha]
    exact (canonical15580 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA942 + difference 1 4) (sourceB942 + difference 4 1) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3867) := by
    have ha : (tripleCharges (sourceA942 + difference 1 4) (sourceB942 + difference 4 1) sourceC942) = raw15581 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15581; decide +kernel
    rw [ha]
    exact (canonical15581 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA942 + difference 1 5) (sourceB942 + difference 5 1) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3909) := by
    have ha : (tripleCharges (sourceA942 + difference 1 5) (sourceB942 + difference 5 1) sourceC942) = raw15582 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15582; decide +kernel
    rw [ha]
    exact (canonical15582 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA942 + difference 2 0) (sourceB942 + difference 0 2) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2017) := by
    have ha : (tripleCharges (sourceA942 + difference 2 0) (sourceB942 + difference 0 2) sourceC942) = raw15583 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15583; decide +kernel
    rw [ha]
    exact (canonical15583 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA942 + difference 2 1) (sourceB942 + difference 1 2) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3688) := by
    have ha : (tripleCharges (sourceA942 + difference 2 1) (sourceB942 + difference 1 2) sourceC942) = raw15584 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15584; decide +kernel
    rw [ha]
    exact (canonical15584 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA942 + difference 2 3) (sourceB942 + difference 3 2) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3819) := by
    have ha : (tripleCharges (sourceA942 + difference 2 3) (sourceB942 + difference 3 2) sourceC942) = raw15585 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15585; decide +kernel
    rw [ha]
    exact (canonical15585 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA942 + difference 2 4) (sourceB942 + difference 4 2) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA942 + difference 2 4) (sourceB942 + difference 4 2) sourceC942) = raw15586 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15586; decide +kernel
    rw [ha]
    exact (canonical15586 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA942 + difference 2 5) (sourceB942 + difference 5 2) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA942 + difference 2 5) (sourceB942 + difference 5 2) sourceC942) = raw15587 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15587; decide +kernel
    rw [ha]
    exact (canonical15587 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA942 + difference 3 0) (sourceB942 + difference 0 3) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2017) := by
    have ha : (tripleCharges (sourceA942 + difference 3 0) (sourceB942 + difference 0 3) sourceC942) = raw15588 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15588; decide +kernel
    rw [ha]
    exact (canonical15588 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA942 + difference 3 1) (sourceB942 + difference 1 3) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3688) := by
    have ha : (tripleCharges (sourceA942 + difference 3 1) (sourceB942 + difference 1 3) sourceC942) = raw15589 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15589; decide +kernel
    rw [ha]
    exact (canonical15589 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA942 + difference 3 2) (sourceB942 + difference 2 3) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3819) := by
    have ha : (tripleCharges (sourceA942 + difference 3 2) (sourceB942 + difference 2 3) sourceC942) = raw15590 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15590; decide +kernel
    rw [ha]
    exact (canonical15590 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA942 + difference 3 4) (sourceB942 + difference 4 3) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3832) := by
    have ha : (tripleCharges (sourceA942 + difference 3 4) (sourceB942 + difference 4 3) sourceC942) = raw15591 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15591; decide +kernel
    rw [ha]
    exact (canonical15591 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA942 + difference 3 5) (sourceB942 + difference 5 3) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA942 + difference 3 5) (sourceB942 + difference 5 3) sourceC942) = raw15592 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15592; decide +kernel
    rw [ha]
    exact (canonical15592 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA942 + difference 4 0) (sourceB942 + difference 0 4) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2012) := by
    have ha : (tripleCharges (sourceA942 + difference 4 0) (sourceB942 + difference 0 4) sourceC942) = raw15593 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15593; decide +kernel
    rw [ha]
    exact (canonical15593 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA942 + difference 4 1) (sourceB942 + difference 1 4) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3685) := by
    have ha : (tripleCharges (sourceA942 + difference 4 1) (sourceB942 + difference 1 4) sourceC942) = raw15594 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15594; decide +kernel
    rw [ha]
    exact (canonical15594 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA942 + difference 4 2) (sourceB942 + difference 2 4) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3818) := by
    have ha : (tripleCharges (sourceA942 + difference 4 2) (sourceB942 + difference 2 4) sourceC942) = raw15595 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15595; decide +kernel
    rw [ha]
    exact (canonical15595 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA942 + difference 4 3) (sourceB942 + difference 3 4) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3818) := by
    have ha : (tripleCharges (sourceA942 + difference 4 3) (sourceB942 + difference 3 4) sourceC942) = raw15596 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15596; decide +kernel
    rw [ha]
    exact (canonical15596 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA942 + difference 4 5) (sourceB942 + difference 5 4) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA942 + difference 4 5) (sourceB942 + difference 5 4) sourceC942) = raw15597 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15597; decide +kernel
    rw [ha]
    exact (canonical15597 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA942 + difference 5 0) (sourceB942 + difference 0 5) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2008) := by
    have ha : (tripleCharges (sourceA942 + difference 5 0) (sourceB942 + difference 0 5) sourceC942) = raw15598 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15598; decide +kernel
    rw [ha]
    exact (canonical15598 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA942 + difference 5 1) (sourceB942 + difference 1 5) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2609) := by
    have ha : (tripleCharges (sourceA942 + difference 5 1) (sourceB942 + difference 1 5) sourceC942) = raw15599 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15599; decide +kernel
    rw [ha]
    exact (canonical15599 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA942 + difference 5 2) (sourceB942 + difference 2 5) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2614) := by
    have ha : (tripleCharges (sourceA942 + difference 5 2) (sourceB942 + difference 2 5) sourceC942) = raw15600 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15600; decide +kernel
    rw [ha]
    exact (canonical15600 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA942 + difference 5 3) (sourceB942 + difference 3 5) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2614) := by
    have ha : (tripleCharges (sourceA942 + difference 5 3) (sourceB942 + difference 3 5) sourceC942) = raw15601 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15601; decide +kernel
    rw [ha]
    exact (canonical15601 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA942 + difference 5 4) (sourceB942 + difference 4 5) sourceC942) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2697) := by
    have ha : (tripleCharges (sourceA942 + difference 5 4) (sourceB942 + difference 4 5) sourceC942) = raw15602 := by
      apply Matrix.ext; unfold tripleCharges sourceA942 sourceB942 sourceC942 difference raw15602; decide +kernel
    rw [ha]
    exact (canonical15602 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA942 sourceB942 sourceC942
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm942, Integer.Sparse.eval]
  linarith only [hs]

def sourceA943 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB943 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC943 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceForm943 : Integer.Sparse Master := [(Sum.inr 2074, 1), (Sum.inr 2076, 2), (Sum.inr 2104, 1), (Sum.inr 2213, 1), (Sum.inr 3488, 1), (Sum.inr 3491, 1), (Sum.inr 3524, 2), (Sum.inr 3720, 2), (Sum.inr 3734, 1), (Sum.inr 3750, 2), (Sum.inr 3768, 1), (Sum.inr 3769, 2), (Sum.inr 3812, 1), (Sum.inr 3869, 2), (Sum.inr 3871, 2), (Sum.inr 3874, 2), (Sum.inr 3882, 1), (Sum.inr 3956, 1), (Sum.inr 3957, 2), (Sum.inr 3980, 1), (Sum.inr 4026, 1)]

theorem sourceEq943 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm943 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA943 + difference 0 1) (sourceB943 + difference 1 0) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3956) := by
    have ha : (tripleCharges (sourceA943 + difference 0 1) (sourceB943 + difference 1 0) sourceC943) = raw15603 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15603; decide +kernel
    rw [ha]
    exact (canonical15603 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA943 + difference 0 2) (sourceB943 + difference 2 0) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA943 + difference 0 2) (sourceB943 + difference 2 0) sourceC943) = raw15604 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15604; decide +kernel
    rw [ha]
    exact (canonical15604 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA943 + difference 0 3) (sourceB943 + difference 3 0) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA943 + difference 0 3) (sourceB943 + difference 3 0) sourceC943) = raw15605 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15605; decide +kernel
    rw [ha]
    exact (canonical15605 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA943 + difference 0 4) (sourceB943 + difference 4 0) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4026) := by
    have ha : (tripleCharges (sourceA943 + difference 0 4) (sourceB943 + difference 4 0) sourceC943) = raw15606 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15606; decide +kernel
    rw [ha]
    exact (canonical15606 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA943 + difference 0 5) (sourceB943 + difference 5 0) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA943 + difference 0 5) (sourceB943 + difference 5 0) sourceC943) = raw15607 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15607; decide +kernel
    rw [ha]
    exact (canonical15607 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA943 + difference 1 0) (sourceB943 + difference 0 1) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2104) := by
    have ha : (tripleCharges (sourceA943 + difference 1 0) (sourceB943 + difference 0 1) sourceC943) = raw15608 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15608; decide +kernel
    rw [ha]
    exact (canonical15608 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA943 + difference 1 2) (sourceB943 + difference 2 1) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA943 + difference 1 2) (sourceB943 + difference 2 1) sourceC943) = raw15609 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15609; decide +kernel
    rw [ha]
    exact (canonical15609 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA943 + difference 1 3) (sourceB943 + difference 3 1) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA943 + difference 1 3) (sourceB943 + difference 3 1) sourceC943) = raw15610 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15610; decide +kernel
    rw [ha]
    exact (canonical15610 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA943 + difference 1 4) (sourceB943 + difference 4 1) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3734) := by
    have ha : (tripleCharges (sourceA943 + difference 1 4) (sourceB943 + difference 4 1) sourceC943) = raw15611 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15611; decide +kernel
    rw [ha]
    exact (canonical15611 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA943 + difference 1 5) (sourceB943 + difference 5 1) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3882) := by
    have ha : (tripleCharges (sourceA943 + difference 1 5) (sourceB943 + difference 5 1) sourceC943) = raw15612 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15612; decide +kernel
    rw [ha]
    exact (canonical15612 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA943 + difference 2 0) (sourceB943 + difference 0 2) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2076) := by
    have ha : (tripleCharges (sourceA943 + difference 2 0) (sourceB943 + difference 0 2) sourceC943) = raw15613 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15613; decide +kernel
    rw [ha]
    exact (canonical15613 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA943 + difference 2 1) (sourceB943 + difference 1 2) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3750) := by
    have ha : (tripleCharges (sourceA943 + difference 2 1) (sourceB943 + difference 1 2) sourceC943) = raw15614 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15614; decide +kernel
    rw [ha]
    exact (canonical15614 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA943 + difference 2 3) (sourceB943 + difference 3 2) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA943 + difference 2 3) (sourceB943 + difference 3 2) sourceC943) = raw15615 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15615; decide +kernel
    rw [ha]
    exact (canonical15615 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA943 + difference 2 4) (sourceB943 + difference 4 2) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3720) := by
    have ha : (tripleCharges (sourceA943 + difference 2 4) (sourceB943 + difference 4 2) sourceC943) = raw15616 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15616; decide +kernel
    rw [ha]
    exact (canonical15616 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA943 + difference 2 5) (sourceB943 + difference 5 2) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA943 + difference 2 5) (sourceB943 + difference 5 2) sourceC943) = raw15617 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15617; decide +kernel
    rw [ha]
    exact (canonical15617 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA943 + difference 3 0) (sourceB943 + difference 0 3) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2076) := by
    have ha : (tripleCharges (sourceA943 + difference 3 0) (sourceB943 + difference 0 3) sourceC943) = raw15618 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15618; decide +kernel
    rw [ha]
    exact (canonical15618 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA943 + difference 3 1) (sourceB943 + difference 1 3) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3750) := by
    have ha : (tripleCharges (sourceA943 + difference 3 1) (sourceB943 + difference 1 3) sourceC943) = raw15619 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15619; decide +kernel
    rw [ha]
    exact (canonical15619 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA943 + difference 3 2) (sourceB943 + difference 2 3) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3869) := by
    have ha : (tripleCharges (sourceA943 + difference 3 2) (sourceB943 + difference 2 3) sourceC943) = raw15620 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15620; decide +kernel
    rw [ha]
    exact (canonical15620 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA943 + difference 3 4) (sourceB943 + difference 4 3) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3720) := by
    have ha : (tripleCharges (sourceA943 + difference 3 4) (sourceB943 + difference 4 3) sourceC943) = raw15621 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15621; decide +kernel
    rw [ha]
    exact (canonical15621 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA943 + difference 3 5) (sourceB943 + difference 5 3) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA943 + difference 3 5) (sourceB943 + difference 5 3) sourceC943) = raw15622 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15622; decide +kernel
    rw [ha]
    exact (canonical15622 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA943 + difference 4 0) (sourceB943 + difference 0 4) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2213) := by
    have ha : (tripleCharges (sourceA943 + difference 4 0) (sourceB943 + difference 0 4) sourceC943) = raw15623 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15623; decide +kernel
    rw [ha]
    exact (canonical15623 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA943 + difference 4 1) (sourceB943 + difference 1 4) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3768) := by
    have ha : (tripleCharges (sourceA943 + difference 4 1) (sourceB943 + difference 1 4) sourceC943) = raw15624 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15624; decide +kernel
    rw [ha]
    exact (canonical15624 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA943 + difference 4 2) (sourceB943 + difference 2 4) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3769) := by
    have ha : (tripleCharges (sourceA943 + difference 4 2) (sourceB943 + difference 2 4) sourceC943) = raw15625 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15625; decide +kernel
    rw [ha]
    exact (canonical15625 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA943 + difference 4 3) (sourceB943 + difference 3 4) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3769) := by
    have ha : (tripleCharges (sourceA943 + difference 4 3) (sourceB943 + difference 3 4) sourceC943) = raw15626 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15626; decide +kernel
    rw [ha]
    exact (canonical15626 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA943 + difference 4 5) (sourceB943 + difference 5 4) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3812) := by
    have ha : (tripleCharges (sourceA943 + difference 4 5) (sourceB943 + difference 5 4) sourceC943) = raw15627 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15627; decide +kernel
    rw [ha]
    exact (canonical15627 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA943 + difference 5 0) (sourceB943 + difference 0 5) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2074) := by
    have ha : (tripleCharges (sourceA943 + difference 5 0) (sourceB943 + difference 0 5) sourceC943) = raw15628 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15628; decide +kernel
    rw [ha]
    exact (canonical15628 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA943 + difference 5 1) (sourceB943 + difference 1 5) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3491) := by
    have ha : (tripleCharges (sourceA943 + difference 5 1) (sourceB943 + difference 1 5) sourceC943) = raw15629 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15629; decide +kernel
    rw [ha]
    exact (canonical15629 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA943 + difference 5 2) (sourceB943 + difference 2 5) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA943 + difference 5 2) (sourceB943 + difference 2 5) sourceC943) = raw15630 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15630; decide +kernel
    rw [ha]
    exact (canonical15630 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA943 + difference 5 3) (sourceB943 + difference 3 5) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA943 + difference 5 3) (sourceB943 + difference 3 5) sourceC943) = raw15631 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15631; decide +kernel
    rw [ha]
    exact (canonical15631 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA943 + difference 5 4) (sourceB943 + difference 4 5) sourceC943) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3488) := by
    have ha : (tripleCharges (sourceA943 + difference 5 4) (sourceB943 + difference 4 5) sourceC943) = raw15632 := by
      apply Matrix.ext; unfold tripleCharges sourceA943 sourceB943 sourceC943 difference raw15632; decide +kernel
    rw [ha]
    exact (canonical15632 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA943 sourceB943 sourceC943
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm943, Integer.Sparse.eval]
  linarith only [hs]

def sourceA944 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB944 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC944 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceForm944 : Integer.Sparse Master := [(Sum.inr 3849, 1), (Sum.inr 3953, 1), (Sum.inr 3954, 1), (Sum.inr 3957, 2), (Sum.inr 4046, 1), (Sum.inr 4091, -1)]

theorem sourceEq944 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm944 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA944 + difference 0 0) (sourceB944 + difference 0 0) sourceC944) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA944 + difference 0 0) (sourceB944 + difference 0 0) sourceC944) = raw15633 := by
      apply Matrix.ext; unfold tripleCharges sourceA944 sourceB944 sourceC944 difference raw15633; decide +kernel
    rw [ha]
    exact (canonical15633 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA944 + difference 0 1) (sourceB944 + difference 1 0) sourceC944) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA944 + difference 0 1) (sourceB944 + difference 1 0) sourceC944) = raw15634 := by
      apply Matrix.ext; unfold tripleCharges sourceA944 sourceB944 sourceC944 difference raw15634; decide +kernel
    rw [ha]
    exact (canonical15634 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA944 + difference 0 2) (sourceB944 + difference 2 0) sourceC944) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA944 + difference 0 2) (sourceB944 + difference 2 0) sourceC944) = raw15635 := by
      apply Matrix.ext; unfold tripleCharges sourceA944 sourceB944 sourceC944 difference raw15635; decide +kernel
    rw [ha]
    exact (canonical15635 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA944 + difference 0 3) (sourceB944 + difference 3 0) sourceC944) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA944 + difference 0 3) (sourceB944 + difference 3 0) sourceC944) = raw15636 := by
      apply Matrix.ext; unfold tripleCharges sourceA944 sourceB944 sourceC944 difference raw15636; decide +kernel
    rw [ha]
    exact (canonical15636 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA944 + difference 0 4) (sourceB944 + difference 4 0) sourceC944) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA944 + difference 0 4) (sourceB944 + difference 4 0) sourceC944) = raw15637 := by
      apply Matrix.ext; unfold tripleCharges sourceA944 sourceB944 sourceC944 difference raw15637; decide +kernel
    rw [ha]
    exact (canonical15637 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA944 + difference 0 5) (sourceB944 + difference 5 0) sourceC944) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4046) := by
    have ha : (tripleCharges (sourceA944 + difference 0 5) (sourceB944 + difference 5 0) sourceC944) = raw15638 := by
      apply Matrix.ext; unfold tripleCharges sourceA944 sourceB944 sourceC944 difference raw15638; decide +kernel
    rw [ha]
    exact (canonical15638 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA944 + sourceB944) sourceC944) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA944 + sourceB944) sourceC944) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA944 sourceB944 sourceC944 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA944 sourceB944 sourceC944
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm944, Integer.Sparse.eval]
  linarith only [hs]

def sourceA945 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB945 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC945 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceForm945 : Integer.Sparse Master := [(Sum.inr 2858, 1), (Sum.inr 3176, 2), (Sum.inr 3179, 1), (Sum.inr 3199, 1), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

theorem sourceEq945 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm945 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA945 + difference 0 0) (sourceB945 + difference 0 0) sourceC945) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA945 + difference 0 0) (sourceB945 + difference 0 0) sourceC945) = raw15633 := by
      apply Matrix.ext; unfold tripleCharges sourceA945 sourceB945 sourceC945 difference raw15633; decide +kernel
    rw [ha]
    exact (canonical15633 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA945 + difference 1 0) (sourceB945 + difference 0 1) sourceC945) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3179) := by
    have ha : (tripleCharges (sourceA945 + difference 1 0) (sourceB945 + difference 0 1) sourceC945) = raw15640 := by
      apply Matrix.ext; unfold tripleCharges sourceA945 sourceB945 sourceC945 difference raw15640; decide +kernel
    rw [ha]
    exact (canonical15640 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA945 + difference 2 0) (sourceB945 + difference 0 2) sourceC945) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3176) := by
    have ha : (tripleCharges (sourceA945 + difference 2 0) (sourceB945 + difference 0 2) sourceC945) = raw15641 := by
      apply Matrix.ext; unfold tripleCharges sourceA945 sourceB945 sourceC945 difference raw15641; decide +kernel
    rw [ha]
    exact (canonical15641 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA945 + difference 3 0) (sourceB945 + difference 0 3) sourceC945) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3176) := by
    have ha : (tripleCharges (sourceA945 + difference 3 0) (sourceB945 + difference 0 3) sourceC945) = raw15642 := by
      apply Matrix.ext; unfold tripleCharges sourceA945 sourceB945 sourceC945 difference raw15642; decide +kernel
    rw [ha]
    exact (canonical15642 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA945 + difference 4 0) (sourceB945 + difference 0 4) sourceC945) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA945 + difference 4 0) (sourceB945 + difference 0 4) sourceC945) = raw15643 := by
      apply Matrix.ext; unfold tripleCharges sourceA945 sourceB945 sourceC945 difference raw15643; decide +kernel
    rw [ha]
    exact (canonical15643 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA945 + difference 5 0) (sourceB945 + difference 0 5) sourceC945) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2858) := by
    have ha : (tripleCharges (sourceA945 + difference 5 0) (sourceB945 + difference 0 5) sourceC945) = raw15644 := by
      apply Matrix.ext; unfold tripleCharges sourceA945 sourceB945 sourceC945 difference raw15644; decide +kernel
    rw [ha]
    exact (canonical15644 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA945 + sourceB945) sourceC945) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA945 + sourceB945) sourceC945) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA945 sourceB945 sourceC945 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA945 sourceB945 sourceC945
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm945, Integer.Sparse.eval]
  linarith only [hs]

def sourceA946 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB946 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC946 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceForm946 : Integer.Sparse Master := [(Sum.inr 3179, 1), (Sum.inr 3731, 1), (Sum.inr 3954, 3), (Sum.inr 4025, 1), (Sum.inr 4091, -1)]

theorem sourceEq946 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm946 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA946 + difference 1 0) (sourceB946 + difference 0 1) sourceC946) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3179) := by
    have ha : (tripleCharges (sourceA946 + difference 1 0) (sourceB946 + difference 0 1) sourceC946) = raw15640 := by
      apply Matrix.ext; unfold tripleCharges sourceA946 sourceB946 sourceC946 difference raw15640; decide +kernel
    rw [ha]
    exact (canonical15640 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA946 + difference 1 1) (sourceB946 + difference 1 1) sourceC946) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA946 + difference 1 1) (sourceB946 + difference 1 1) sourceC946) = raw15633 := by
      apply Matrix.ext; unfold tripleCharges sourceA946 sourceB946 sourceC946 difference raw15633; decide +kernel
    rw [ha]
    exact (canonical15633 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA946 + difference 1 2) (sourceB946 + difference 2 1) sourceC946) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA946 + difference 1 2) (sourceB946 + difference 2 1) sourceC946) = raw15645 := by
      apply Matrix.ext; unfold tripleCharges sourceA946 sourceB946 sourceC946 difference raw15645; decide +kernel
    rw [ha]
    exact (canonical15645 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA946 + difference 1 3) (sourceB946 + difference 3 1) sourceC946) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA946 + difference 1 3) (sourceB946 + difference 3 1) sourceC946) = raw15646 := by
      apply Matrix.ext; unfold tripleCharges sourceA946 sourceB946 sourceC946 difference raw15646; decide +kernel
    rw [ha]
    exact (canonical15646 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA946 + difference 1 4) (sourceB946 + difference 4 1) sourceC946) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3731) := by
    have ha : (tripleCharges (sourceA946 + difference 1 4) (sourceB946 + difference 4 1) sourceC946) = raw15647 := by
      apply Matrix.ext; unfold tripleCharges sourceA946 sourceB946 sourceC946 difference raw15647; decide +kernel
    rw [ha]
    exact (canonical15647 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA946 + difference 1 5) (sourceB946 + difference 5 1) sourceC946) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4025) := by
    have ha : (tripleCharges (sourceA946 + difference 1 5) (sourceB946 + difference 5 1) sourceC946) = raw15648 := by
      apply Matrix.ext; unfold tripleCharges sourceA946 sourceB946 sourceC946 difference raw15648; decide +kernel
    rw [ha]
    exact (canonical15648 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA946 + sourceB946) sourceC946) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA946 + sourceB946) sourceC946) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA946 sourceB946 sourceC946 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA946 sourceB946 sourceC946
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm946, Integer.Sparse.eval]
  linarith only [hs]

def sourceA947 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB947 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC947 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceForm947 : Integer.Sparse Master := [(Sum.inr 2859, 1), (Sum.inr 3685, 1), (Sum.inr 3935, 2), (Sum.inr 3953, 1), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

theorem sourceEq947 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm947 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA947 + difference 0 1) (sourceB947 + difference 1 0) sourceC947) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA947 + difference 0 1) (sourceB947 + difference 1 0) sourceC947) = raw15634 := by
      apply Matrix.ext; unfold tripleCharges sourceA947 sourceB947 sourceC947 difference raw15634; decide +kernel
    rw [ha]
    exact (canonical15634 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA947 + difference 1 1) (sourceB947 + difference 1 1) sourceC947) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA947 + difference 1 1) (sourceB947 + difference 1 1) sourceC947) = raw15633 := by
      apply Matrix.ext; unfold tripleCharges sourceA947 sourceB947 sourceC947 difference raw15633; decide +kernel
    rw [ha]
    exact (canonical15633 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA947 + difference 2 1) (sourceB947 + difference 1 2) sourceC947) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3935) := by
    have ha : (tripleCharges (sourceA947 + difference 2 1) (sourceB947 + difference 1 2) sourceC947) = raw15649 := by
      apply Matrix.ext; unfold tripleCharges sourceA947 sourceB947 sourceC947 difference raw15649; decide +kernel
    rw [ha]
    exact (canonical15649 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA947 + difference 3 1) (sourceB947 + difference 1 3) sourceC947) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3935) := by
    have ha : (tripleCharges (sourceA947 + difference 3 1) (sourceB947 + difference 1 3) sourceC947) = raw15650 := by
      apply Matrix.ext; unfold tripleCharges sourceA947 sourceB947 sourceC947 difference raw15650; decide +kernel
    rw [ha]
    exact (canonical15650 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA947 + difference 4 1) (sourceB947 + difference 1 4) sourceC947) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3685) := by
    have ha : (tripleCharges (sourceA947 + difference 4 1) (sourceB947 + difference 1 4) sourceC947) = raw15651 := by
      apply Matrix.ext; unfold tripleCharges sourceA947 sourceB947 sourceC947 difference raw15651; decide +kernel
    rw [ha]
    exact (canonical15651 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA947 + difference 5 1) (sourceB947 + difference 1 5) sourceC947) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2859) := by
    have ha : (tripleCharges (sourceA947 + difference 5 1) (sourceB947 + difference 1 5) sourceC947) = raw15652 := by
      apply Matrix.ext; unfold tripleCharges sourceA947 sourceB947 sourceC947 difference raw15652; decide +kernel
    rw [ha]
    exact (canonical15652 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA947 + sourceB947) sourceC947) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA947 + sourceB947) sourceC947) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA947 sourceB947 sourceC947 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA947 sourceB947 sourceC947
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm947, Integer.Sparse.eval]
  linarith only [hs]

def sourceA948 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB948 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC948 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceForm948 : Integer.Sparse Master := [(Sum.inr 3176, 1), (Sum.inr 3724, 1), (Sum.inr 3935, 1), (Sum.inr 3949, 1), (Sum.inr 3954, 1), (Sum.inr 3972, 1), (Sum.inr 4091, -1)]

theorem sourceEq948 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm948 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA948 + difference 2 0) (sourceB948 + difference 0 2) sourceC948) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3176) := by
    have ha : (tripleCharges (sourceA948 + difference 2 0) (sourceB948 + difference 0 2) sourceC948) = raw15641 := by
      apply Matrix.ext; unfold tripleCharges sourceA948 sourceB948 sourceC948 difference raw15641; decide +kernel
    rw [ha]
    exact (canonical15641 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA948 + difference 2 1) (sourceB948 + difference 1 2) sourceC948) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3935) := by
    have ha : (tripleCharges (sourceA948 + difference 2 1) (sourceB948 + difference 1 2) sourceC948) = raw15649 := by
      apply Matrix.ext; unfold tripleCharges sourceA948 sourceB948 sourceC948 difference raw15649; decide +kernel
    rw [ha]
    exact (canonical15649 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA948 + difference 2 2) (sourceB948 + difference 2 2) sourceC948) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA948 + difference 2 2) (sourceB948 + difference 2 2) sourceC948) = raw15633 := by
      apply Matrix.ext; unfold tripleCharges sourceA948 sourceB948 sourceC948 difference raw15633; decide +kernel
    rw [ha]
    exact (canonical15633 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA948 + difference 2 3) (sourceB948 + difference 3 2) sourceC948) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3949) := by
    have ha : (tripleCharges (sourceA948 + difference 2 3) (sourceB948 + difference 3 2) sourceC948) = raw15653 := by
      apply Matrix.ext; unfold tripleCharges sourceA948 sourceB948 sourceC948 difference raw15653; decide +kernel
    rw [ha]
    exact (canonical15653 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA948 + difference 2 4) (sourceB948 + difference 4 2) sourceC948) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3724) := by
    have ha : (tripleCharges (sourceA948 + difference 2 4) (sourceB948 + difference 4 2) sourceC948) = raw15654 := by
      apply Matrix.ext; unfold tripleCharges sourceA948 sourceB948 sourceC948 difference raw15654; decide +kernel
    rw [ha]
    exact (canonical15654 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA948 + difference 2 5) (sourceB948 + difference 5 2) sourceC948) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA948 + difference 2 5) (sourceB948 + difference 5 2) sourceC948) = raw15655 := by
      apply Matrix.ext; unfold tripleCharges sourceA948 sourceB948 sourceC948 difference raw15655; decide +kernel
    rw [ha]
    exact (canonical15655 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA948 + sourceB948) sourceC948) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA948 + sourceB948) sourceC948) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA948 sourceB948 sourceC948 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA948 sourceB948 sourceC948
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm948, Integer.Sparse.eval]
  linarith only [hs]

def sourceA949 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB949 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC949 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceForm949 : Integer.Sparse Master := [(Sum.inr 2864, 1), (Sum.inr 3692, 1), (Sum.inr 3949, 1), (Sum.inr 3954, 2), (Sum.inr 3957, 1), (Sum.inr 4091, -1)]

theorem sourceEq949 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm949 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA949 + difference 0 2) (sourceB949 + difference 2 0) sourceC949) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3957) := by
    have ha : (tripleCharges (sourceA949 + difference 0 2) (sourceB949 + difference 2 0) sourceC949) = raw15635 := by
      apply Matrix.ext; unfold tripleCharges sourceA949 sourceB949 sourceC949 difference raw15635; decide +kernel
    rw [ha]
    exact (canonical15635 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA949 + difference 1 2) (sourceB949 + difference 2 1) sourceC949) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA949 + difference 1 2) (sourceB949 + difference 2 1) sourceC949) = raw15645 := by
      apply Matrix.ext; unfold tripleCharges sourceA949 sourceB949 sourceC949 difference raw15645; decide +kernel
    rw [ha]
    exact (canonical15645 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA949 + difference 2 2) (sourceB949 + difference 2 2) sourceC949) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA949 + difference 2 2) (sourceB949 + difference 2 2) sourceC949) = raw15633 := by
      apply Matrix.ext; unfold tripleCharges sourceA949 sourceB949 sourceC949 difference raw15633; decide +kernel
    rw [ha]
    exact (canonical15633 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA949 + difference 3 2) (sourceB949 + difference 2 3) sourceC949) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3949) := by
    have ha : (tripleCharges (sourceA949 + difference 3 2) (sourceB949 + difference 2 3) sourceC949) = raw15656 := by
      apply Matrix.ext; unfold tripleCharges sourceA949 sourceB949 sourceC949 difference raw15656; decide +kernel
    rw [ha]
    exact (canonical15656 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA949 + difference 4 2) (sourceB949 + difference 2 4) sourceC949) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3692) := by
    have ha : (tripleCharges (sourceA949 + difference 4 2) (sourceB949 + difference 2 4) sourceC949) = raw15657 := by
      apply Matrix.ext; unfold tripleCharges sourceA949 sourceB949 sourceC949 difference raw15657; decide +kernel
    rw [ha]
    exact (canonical15657 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA949 + difference 5 2) (sourceB949 + difference 2 5) sourceC949) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2864) := by
    have ha : (tripleCharges (sourceA949 + difference 5 2) (sourceB949 + difference 2 5) sourceC949) = raw15658 := by
      apply Matrix.ext; unfold tripleCharges sourceA949 sourceB949 sourceC949 difference raw15658; decide +kernel
    rw [ha]
    exact (canonical15658 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA949 + sourceB949) sourceC949) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA949 + sourceB949) sourceC949) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA949 sourceB949 sourceC949 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA949 sourceB949 sourceC949
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm949, Integer.Sparse.eval]
  linarith only [hs]

def sourceA950 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB950 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC950 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceForm950 : Integer.Sparse Master := [(Sum.inr 3199, 1), (Sum.inr 3685, 1), (Sum.inr 3692, 2), (Sum.inr 3801, 1), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

theorem sourceEq950 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm950 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA950 + difference 4 0) (sourceB950 + difference 0 4) sourceC950) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA950 + difference 4 0) (sourceB950 + difference 0 4) sourceC950) = raw15643 := by
      apply Matrix.ext; unfold tripleCharges sourceA950 sourceB950 sourceC950 difference raw15643; decide +kernel
    rw [ha]
    exact (canonical15643 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA950 + difference 4 1) (sourceB950 + difference 1 4) sourceC950) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3685) := by
    have ha : (tripleCharges (sourceA950 + difference 4 1) (sourceB950 + difference 1 4) sourceC950) = raw15651 := by
      apply Matrix.ext; unfold tripleCharges sourceA950 sourceB950 sourceC950 difference raw15651; decide +kernel
    rw [ha]
    exact (canonical15651 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA950 + difference 4 2) (sourceB950 + difference 2 4) sourceC950) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3692) := by
    have ha : (tripleCharges (sourceA950 + difference 4 2) (sourceB950 + difference 2 4) sourceC950) = raw15657 := by
      apply Matrix.ext; unfold tripleCharges sourceA950 sourceB950 sourceC950 difference raw15657; decide +kernel
    rw [ha]
    exact (canonical15657 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA950 + difference 4 3) (sourceB950 + difference 3 4) sourceC950) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3692) := by
    have ha : (tripleCharges (sourceA950 + difference 4 3) (sourceB950 + difference 3 4) sourceC950) = raw15659 := by
      apply Matrix.ext; unfold tripleCharges sourceA950 sourceB950 sourceC950 difference raw15659; decide +kernel
    rw [ha]
    exact (canonical15659 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA950 + difference 4 4) (sourceB950 + difference 4 4) sourceC950) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA950 + difference 4 4) (sourceB950 + difference 4 4) sourceC950) = raw15633 := by
      apply Matrix.ext; unfold tripleCharges sourceA950 sourceB950 sourceC950 difference raw15633; decide +kernel
    rw [ha]
    exact (canonical15633 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA950 + difference 4 5) (sourceB950 + difference 5 4) sourceC950) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA950 + difference 4 5) (sourceB950 + difference 5 4) sourceC950) = raw15660 := by
      apply Matrix.ext; unfold tripleCharges sourceA950 sourceB950 sourceC950 difference raw15660; decide +kernel
    rw [ha]
    exact (canonical15660 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA950 + sourceB950) sourceC950) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA950 + sourceB950) sourceC950) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA950 sourceB950 sourceC950 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA950 sourceB950 sourceC950
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm950, Integer.Sparse.eval]
  linarith only [hs]

def sourceA951 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB951 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC951 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceForm951 : Integer.Sparse Master := [(Sum.inr 3030, 1), (Sum.inr 3724, 2), (Sum.inr 3731, 1), (Sum.inr 3849, 1), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

theorem sourceEq951 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm951 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA951 + difference 0 4) (sourceB951 + difference 4 0) sourceC951) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3849) := by
    have ha : (tripleCharges (sourceA951 + difference 0 4) (sourceB951 + difference 4 0) sourceC951) = raw15637 := by
      apply Matrix.ext; unfold tripleCharges sourceA951 sourceB951 sourceC951 difference raw15637; decide +kernel
    rw [ha]
    exact (canonical15637 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA951 + difference 1 4) (sourceB951 + difference 4 1) sourceC951) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3731) := by
    have ha : (tripleCharges (sourceA951 + difference 1 4) (sourceB951 + difference 4 1) sourceC951) = raw15647 := by
      apply Matrix.ext; unfold tripleCharges sourceA951 sourceB951 sourceC951 difference raw15647; decide +kernel
    rw [ha]
    exact (canonical15647 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA951 + difference 2 4) (sourceB951 + difference 4 2) sourceC951) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3724) := by
    have ha : (tripleCharges (sourceA951 + difference 2 4) (sourceB951 + difference 4 2) sourceC951) = raw15654 := by
      apply Matrix.ext; unfold tripleCharges sourceA951 sourceB951 sourceC951 difference raw15654; decide +kernel
    rw [ha]
    exact (canonical15654 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA951 + difference 3 4) (sourceB951 + difference 4 3) sourceC951) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3724) := by
    have ha : (tripleCharges (sourceA951 + difference 3 4) (sourceB951 + difference 4 3) sourceC951) = raw15661 := by
      apply Matrix.ext; unfold tripleCharges sourceA951 sourceB951 sourceC951 difference raw15661; decide +kernel
    rw [ha]
    exact (canonical15661 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA951 + difference 4 4) (sourceB951 + difference 4 4) sourceC951) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA951 + difference 4 4) (sourceB951 + difference 4 4) sourceC951) = raw15633 := by
      apply Matrix.ext; unfold tripleCharges sourceA951 sourceB951 sourceC951 difference raw15633; decide +kernel
    rw [ha]
    exact (canonical15633 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA951 + difference 5 4) (sourceB951 + difference 4 5) sourceC951) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3030) := by
    have ha : (tripleCharges (sourceA951 + difference 5 4) (sourceB951 + difference 4 5) sourceC951) = raw15662 := by
      apply Matrix.ext; unfold tripleCharges sourceA951 sourceB951 sourceC951 difference raw15662; decide +kernel
    rw [ha]
    exact (canonical15662 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA951 + sourceB951) sourceC951) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA951 + sourceB951) sourceC951) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA951 sourceB951 sourceC951 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA951 sourceB951 sourceC951
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm951, Integer.Sparse.eval]
  linarith only [hs]

def sourceA952 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceB952 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC952 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceForm952 : Integer.Sparse Master := [(Sum.inr 2858, 1), (Sum.inr 2859, 1), (Sum.inr 2864, 2), (Sum.inr 3030, 1), (Sum.inr 3954, 1), (Sum.inr 4091, -1)]

theorem sourceEq952 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm952 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA952 + difference 5 0) (sourceB952 + difference 0 5) sourceC952) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2858) := by
    have ha : (tripleCharges (sourceA952 + difference 5 0) (sourceB952 + difference 0 5) sourceC952) = raw15644 := by
      apply Matrix.ext; unfold tripleCharges sourceA952 sourceB952 sourceC952 difference raw15644; decide +kernel
    rw [ha]
    exact (canonical15644 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA952 + difference 5 1) (sourceB952 + difference 1 5) sourceC952) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2859) := by
    have ha : (tripleCharges (sourceA952 + difference 5 1) (sourceB952 + difference 1 5) sourceC952) = raw15652 := by
      apply Matrix.ext; unfold tripleCharges sourceA952 sourceB952 sourceC952 difference raw15652; decide +kernel
    rw [ha]
    exact (canonical15652 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA952 + difference 5 2) (sourceB952 + difference 2 5) sourceC952) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2864) := by
    have ha : (tripleCharges (sourceA952 + difference 5 2) (sourceB952 + difference 2 5) sourceC952) = raw15658 := by
      apply Matrix.ext; unfold tripleCharges sourceA952 sourceB952 sourceC952 difference raw15658; decide +kernel
    rw [ha]
    exact (canonical15658 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA952 + difference 5 3) (sourceB952 + difference 3 5) sourceC952) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2864) := by
    have ha : (tripleCharges (sourceA952 + difference 5 3) (sourceB952 + difference 3 5) sourceC952) = raw15663 := by
      apply Matrix.ext; unfold tripleCharges sourceA952 sourceB952 sourceC952 difference raw15663; decide +kernel
    rw [ha]
    exact (canonical15663 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA952 + difference 5 4) (sourceB952 + difference 4 5) sourceC952) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3030) := by
    have ha : (tripleCharges (sourceA952 + difference 5 4) (sourceB952 + difference 4 5) sourceC952) = raw15662 := by
      apply Matrix.ext; unfold tripleCharges sourceA952 sourceB952 sourceC952 difference raw15662; decide +kernel
    rw [ha]
    exact (canonical15662 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA952 + difference 5 5) (sourceB952 + difference 5 5) sourceC952) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3954) := by
    have ha : (tripleCharges (sourceA952 + difference 5 5) (sourceB952 + difference 5 5) sourceC952) = raw15633 := by
      apply Matrix.ext; unfold tripleCharges sourceA952 sourceB952 sourceC952 difference raw15633; decide +kernel
    rw [ha]
    exact (canonical15633 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA952 + sourceB952) sourceC952) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA952 + sourceB952) sourceC952) = raw15639 := by
      apply Matrix.ext; unfold doubleCharges sourceA952 sourceB952 sourceC952 raw15639; decide +kernel
    rw [ha]
    exact (canonical15639 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA952 sourceB952 sourceC952
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm952, Integer.Sparse.eval]
  linarith only [hs]

def sourceA953 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB953 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC953 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm953 : Integer.Sparse Master := [(Sum.inr 5178, 2), (Sum.inr 5179, 1), (Sum.inr 5184, 1), (Sum.inr 5186, 2), (Sum.inr 5196, 1), (Sum.inr 5197, 1), (Sum.inr 5231, 1), (Sum.inr 5256, 1), (Sum.inr 5359, 1), (Sum.inr 5360, 2), (Sum.inr 5365, 1), (Sum.inr 5400, 1), (Sum.inr 5402, 2), (Sum.inr 5405, 1), (Sum.inr 5406, 1), (Sum.inr 5432, 2), (Sum.inr 5434, 2), (Sum.inr 5436, 2), (Sum.inr 5446, 2), (Sum.inr 5471, 1), (Sum.inr 5473, 2)]

theorem sourceEq953 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm953 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA953 + difference 0 1) (sourceB953 + difference 1 0) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5471) := by
    have ha : (tripleCharges (sourceA953 + difference 0 1) (sourceB953 + difference 1 0) sourceC953) = raw15664 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15664; decide +kernel
    rw [ha]
    exact (canonical15664 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA953 + difference 0 2) (sourceB953 + difference 2 0) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA953 + difference 0 2) (sourceB953 + difference 2 0) sourceC953) = raw15116 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15116; decide +kernel
    rw [ha]
    exact (canonical15116 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA953 + difference 0 3) (sourceB953 + difference 3 0) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5473) := by
    have ha : (tripleCharges (sourceA953 + difference 0 3) (sourceB953 + difference 3 0) sourceC953) = raw15665 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15665; decide +kernel
    rw [ha]
    exact (canonical15665 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA953 + difference 0 4) (sourceB953 + difference 4 0) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5197) := by
    have ha : (tripleCharges (sourceA953 + difference 0 4) (sourceB953 + difference 4 0) sourceC953) = raw15666 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15666; decide +kernel
    rw [ha]
    exact (canonical15666 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA953 + difference 0 5) (sourceB953 + difference 5 0) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5365) := by
    have ha : (tripleCharges (sourceA953 + difference 0 5) (sourceB953 + difference 5 0) sourceC953) = raw15667 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15667; decide +kernel
    rw [ha]
    exact (canonical15667 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA953 + difference 1 0) (sourceB953 + difference 0 1) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5196) := by
    have ha : (tripleCharges (sourceA953 + difference 1 0) (sourceB953 + difference 0 1) sourceC953) = raw15668 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15668; decide +kernel
    rw [ha]
    exact (canonical15668 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA953 + difference 1 2) (sourceB953 + difference 2 1) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA953 + difference 1 2) (sourceB953 + difference 2 1) sourceC953) = raw15121 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15121; decide +kernel
    rw [ha]
    exact (canonical15121 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA953 + difference 1 3) (sourceB953 + difference 3 1) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5446) := by
    have ha : (tripleCharges (sourceA953 + difference 1 3) (sourceB953 + difference 3 1) sourceC953) = raw15669 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15669; decide +kernel
    rw [ha]
    exact (canonical15669 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA953 + difference 1 4) (sourceB953 + difference 4 1) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5179) := by
    have ha : (tripleCharges (sourceA953 + difference 1 4) (sourceB953 + difference 4 1) sourceC953) = raw15670 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15670; decide +kernel
    rw [ha]
    exact (canonical15670 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA953 + difference 1 5) (sourceB953 + difference 5 1) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5359) := by
    have ha : (tripleCharges (sourceA953 + difference 1 5) (sourceB953 + difference 5 1) sourceC953) = raw15671 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15671; decide +kernel
    rw [ha]
    exact (canonical15671 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA953 + difference 2 0) (sourceB953 + difference 0 2) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5186) := by
    have ha : (tripleCharges (sourceA953 + difference 2 0) (sourceB953 + difference 0 2) sourceC953) = raw15672 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15672; decide +kernel
    rw [ha]
    exact (canonical15672 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA953 + difference 2 1) (sourceB953 + difference 1 2) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5402) := by
    have ha : (tripleCharges (sourceA953 + difference 2 1) (sourceB953 + difference 1 2) sourceC953) = raw15673 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15673; decide +kernel
    rw [ha]
    exact (canonical15673 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA953 + difference 2 3) (sourceB953 + difference 3 2) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA953 + difference 2 3) (sourceB953 + difference 3 2) sourceC953) = raw15674 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15674; decide +kernel
    rw [ha]
    exact (canonical15674 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA953 + difference 2 4) (sourceB953 + difference 4 2) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5178) := by
    have ha : (tripleCharges (sourceA953 + difference 2 4) (sourceB953 + difference 4 2) sourceC953) = raw15675 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15675; decide +kernel
    rw [ha]
    exact (canonical15675 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA953 + difference 2 5) (sourceB953 + difference 5 2) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA953 + difference 2 5) (sourceB953 + difference 5 2) sourceC953) = raw15676 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15676; decide +kernel
    rw [ha]
    exact (canonical15676 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA953 + difference 3 0) (sourceB953 + difference 0 3) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5186) := by
    have ha : (tripleCharges (sourceA953 + difference 3 0) (sourceB953 + difference 0 3) sourceC953) = raw15677 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15677; decide +kernel
    rw [ha]
    exact (canonical15677 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA953 + difference 3 1) (sourceB953 + difference 1 3) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5402) := by
    have ha : (tripleCharges (sourceA953 + difference 3 1) (sourceB953 + difference 1 3) sourceC953) = raw15678 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15678; decide +kernel
    rw [ha]
    exact (canonical15678 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA953 + difference 3 2) (sourceB953 + difference 2 3) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5436) := by
    have ha : (tripleCharges (sourceA953 + difference 3 2) (sourceB953 + difference 2 3) sourceC953) = raw15131 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15131; decide +kernel
    rw [ha]
    exact (canonical15131 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA953 + difference 3 4) (sourceB953 + difference 4 3) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5178) := by
    have ha : (tripleCharges (sourceA953 + difference 3 4) (sourceB953 + difference 4 3) sourceC953) = raw15679 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15679; decide +kernel
    rw [ha]
    exact (canonical15679 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA953 + difference 3 5) (sourceB953 + difference 5 3) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5360) := by
    have ha : (tripleCharges (sourceA953 + difference 3 5) (sourceB953 + difference 5 3) sourceC953) = raw15680 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15680; decide +kernel
    rw [ha]
    exact (canonical15680 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA953 + difference 4 0) (sourceB953 + difference 0 4) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA953 + difference 4 0) (sourceB953 + difference 0 4) sourceC953) = raw15123 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15123; decide +kernel
    rw [ha]
    exact (canonical15123 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA953 + difference 4 1) (sourceB953 + difference 1 4) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5405) := by
    have ha : (tripleCharges (sourceA953 + difference 4 1) (sourceB953 + difference 1 4) sourceC953) = raw15124 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15124; decide +kernel
    rw [ha]
    exact (canonical15124 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA953 + difference 4 2) (sourceB953 + difference 2 4) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA953 + difference 4 2) (sourceB953 + difference 2 4) sourceC953) = raw15210 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15210; decide +kernel
    rw [ha]
    exact (canonical15210 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA953 + difference 4 3) (sourceB953 + difference 3 4) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA953 + difference 4 3) (sourceB953 + difference 3 4) sourceC953) = raw15125 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15125; decide +kernel
    rw [ha]
    exact (canonical15125 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA953 + difference 4 5) (sourceB953 + difference 5 4) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5406) := by
    have ha : (tripleCharges (sourceA953 + difference 4 5) (sourceB953 + difference 5 4) sourceC953) = raw15127 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15127; decide +kernel
    rw [ha]
    exact (canonical15127 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA953 + difference 5 0) (sourceB953 + difference 0 5) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5184) := by
    have ha : (tripleCharges (sourceA953 + difference 5 0) (sourceB953 + difference 0 5) sourceC953) = raw15681 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15681; decide +kernel
    rw [ha]
    exact (canonical15681 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA953 + difference 5 1) (sourceB953 + difference 1 5) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5400) := by
    have ha : (tripleCharges (sourceA953 + difference 5 1) (sourceB953 + difference 1 5) sourceC953) = raw15682 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15682; decide +kernel
    rw [ha]
    exact (canonical15682 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA953 + difference 5 2) (sourceB953 + difference 2 5) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA953 + difference 5 2) (sourceB953 + difference 2 5) sourceC953) = raw15139 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15139; decide +kernel
    rw [ha]
    exact (canonical15139 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA953 + difference 5 3) (sourceB953 + difference 3 5) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5432) := by
    have ha : (tripleCharges (sourceA953 + difference 5 3) (sourceB953 + difference 3 5) sourceC953) = raw15683 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15683; decide +kernel
    rw [ha]
    exact (canonical15683 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA953 + difference 5 4) (sourceB953 + difference 4 5) sourceC953) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5231) := by
    have ha : (tripleCharges (sourceA953 + difference 5 4) (sourceB953 + difference 4 5) sourceC953) = raw15684 := by
      apply Matrix.ext; unfold tripleCharges sourceA953 sourceB953 sourceC953 difference raw15684; decide +kernel
    rw [ha]
    exact (canonical15684 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA953 sourceB953 sourceC953
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm953, Integer.Sparse.eval]
  linarith only [hs]

def sourceA954 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB954 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC954 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm954 : Integer.Sparse Master := [(Sum.inr 2606, 2), (Sum.inr 2607, 1), (Sum.inr 2631, 1), (Sum.inr 2676, 1), (Sum.inr 3524, 1), (Sum.inr 3525, 1), (Sum.inr 3527, 2), (Sum.inr 3566, 1), (Sum.inr 3780, 2), (Sum.inr 3799, 1), (Sum.inr 3800, 1), (Sum.inr 3802, 2), (Sum.inr 3847, 1), (Sum.inr 3850, 2), (Sum.inr 3852, 2), (Sum.inr 3854, 2), (Sum.inr 3878, 1), (Sum.inr 3881, 2), (Sum.inr 3938, 1), (Sum.inr 3976, 1), (Sum.inr 3995, 2)]

theorem sourceEq954 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm954 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA954 + difference 0 1) (sourceB954 + difference 1 0) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3976) := by
    have ha : (tripleCharges (sourceA954 + difference 0 1) (sourceB954 + difference 1 0) sourceC954) = raw15685 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15685; decide +kernel
    rw [ha]
    exact (canonical15685 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA954 + difference 0 2) (sourceB954 + difference 2 0) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA954 + difference 0 2) (sourceB954 + difference 2 0) sourceC954) = raw15686 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15686; decide +kernel
    rw [ha]
    exact (canonical15686 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA954 + difference 0 3) (sourceB954 + difference 3 0) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3995) := by
    have ha : (tripleCharges (sourceA954 + difference 0 3) (sourceB954 + difference 3 0) sourceC954) = raw15687 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15687; decide +kernel
    rw [ha]
    exact (canonical15687 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA954 + difference 0 4) (sourceB954 + difference 4 0) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2631) := by
    have ha : (tripleCharges (sourceA954 + difference 0 4) (sourceB954 + difference 4 0) sourceC954) = raw15688 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15688; decide +kernel
    rw [ha]
    exact (canonical15688 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA954 + difference 0 5) (sourceB954 + difference 5 0) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3938) := by
    have ha : (tripleCharges (sourceA954 + difference 0 5) (sourceB954 + difference 5 0) sourceC954) = raw15689 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15689; decide +kernel
    rw [ha]
    exact (canonical15689 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA954 + difference 1 0) (sourceB954 + difference 0 1) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3566) := by
    have ha : (tripleCharges (sourceA954 + difference 1 0) (sourceB954 + difference 0 1) sourceC954) = raw15690 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15690; decide +kernel
    rw [ha]
    exact (canonical15690 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA954 + difference 1 2) (sourceB954 + difference 2 1) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA954 + difference 1 2) (sourceB954 + difference 2 1) sourceC954) = raw15691 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15691; decide +kernel
    rw [ha]
    exact (canonical15691 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA954 + difference 1 3) (sourceB954 + difference 3 1) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA954 + difference 1 3) (sourceB954 + difference 3 1) sourceC954) = raw15692 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15692; decide +kernel
    rw [ha]
    exact (canonical15692 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA954 + difference 1 4) (sourceB954 + difference 4 1) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2607) := by
    have ha : (tripleCharges (sourceA954 + difference 1 4) (sourceB954 + difference 4 1) sourceC954) = raw15693 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15693; decide +kernel
    rw [ha]
    exact (canonical15693 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA954 + difference 1 5) (sourceB954 + difference 5 1) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3878) := by
    have ha : (tripleCharges (sourceA954 + difference 1 5) (sourceB954 + difference 5 1) sourceC954) = raw15694 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15694; decide +kernel
    rw [ha]
    exact (canonical15694 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA954 + difference 2 0) (sourceB954 + difference 0 2) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3527) := by
    have ha : (tripleCharges (sourceA954 + difference 2 0) (sourceB954 + difference 0 2) sourceC954) = raw15695 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15695; decide +kernel
    rw [ha]
    exact (canonical15695 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA954 + difference 2 1) (sourceB954 + difference 1 2) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3802) := by
    have ha : (tripleCharges (sourceA954 + difference 2 1) (sourceB954 + difference 1 2) sourceC954) = raw15696 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15696; decide +kernel
    rw [ha]
    exact (canonical15696 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA954 + difference 2 3) (sourceB954 + difference 3 2) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA954 + difference 2 3) (sourceB954 + difference 3 2) sourceC954) = raw15697 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15697; decide +kernel
    rw [ha]
    exact (canonical15697 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA954 + difference 2 4) (sourceB954 + difference 4 2) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2606) := by
    have ha : (tripleCharges (sourceA954 + difference 2 4) (sourceB954 + difference 4 2) sourceC954) = raw15698 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15698; decide +kernel
    rw [ha]
    exact (canonical15698 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA954 + difference 2 5) (sourceB954 + difference 5 2) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3780) := by
    have ha : (tripleCharges (sourceA954 + difference 2 5) (sourceB954 + difference 5 2) sourceC954) = raw15699 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15699; decide +kernel
    rw [ha]
    exact (canonical15699 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA954 + difference 3 0) (sourceB954 + difference 0 3) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3527) := by
    have ha : (tripleCharges (sourceA954 + difference 3 0) (sourceB954 + difference 0 3) sourceC954) = raw15700 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15700; decide +kernel
    rw [ha]
    exact (canonical15700 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA954 + difference 3 1) (sourceB954 + difference 1 3) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3802) := by
    have ha : (tripleCharges (sourceA954 + difference 3 1) (sourceB954 + difference 1 3) sourceC954) = raw15701 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15701; decide +kernel
    rw [ha]
    exact (canonical15701 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA954 + difference 3 2) (sourceB954 + difference 2 3) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA954 + difference 3 2) (sourceB954 + difference 2 3) sourceC954) = raw15702 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15702; decide +kernel
    rw [ha]
    exact (canonical15702 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA954 + difference 3 4) (sourceB954 + difference 4 3) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2606) := by
    have ha : (tripleCharges (sourceA954 + difference 3 4) (sourceB954 + difference 4 3) sourceC954) = raw15703 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15703; decide +kernel
    rw [ha]
    exact (canonical15703 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA954 + difference 3 5) (sourceB954 + difference 5 3) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3780) := by
    have ha : (tripleCharges (sourceA954 + difference 3 5) (sourceB954 + difference 5 3) sourceC954) = raw15704 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15704; decide +kernel
    rw [ha]
    exact (canonical15704 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA954 + difference 4 0) (sourceB954 + difference 0 4) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3525) := by
    have ha : (tripleCharges (sourceA954 + difference 4 0) (sourceB954 + difference 0 4) sourceC954) = raw15705 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15705; decide +kernel
    rw [ha]
    exact (canonical15705 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA954 + difference 4 1) (sourceB954 + difference 1 4) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA954 + difference 4 1) (sourceB954 + difference 1 4) sourceC954) = raw15706 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15706; decide +kernel
    rw [ha]
    exact (canonical15706 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA954 + difference 4 2) (sourceB954 + difference 2 4) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA954 + difference 4 2) (sourceB954 + difference 2 4) sourceC954) = raw15707 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15707; decide +kernel
    rw [ha]
    exact (canonical15707 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA954 + difference 4 3) (sourceB954 + difference 3 4) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3852) := by
    have ha : (tripleCharges (sourceA954 + difference 4 3) (sourceB954 + difference 3 4) sourceC954) = raw15708 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15708; decide +kernel
    rw [ha]
    exact (canonical15708 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA954 + difference 4 5) (sourceB954 + difference 5 4) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA954 + difference 4 5) (sourceB954 + difference 5 4) sourceC954) = raw15709 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15709; decide +kernel
    rw [ha]
    exact (canonical15709 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA954 + difference 5 0) (sourceB954 + difference 0 5) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3524) := by
    have ha : (tripleCharges (sourceA954 + difference 5 0) (sourceB954 + difference 0 5) sourceC954) = raw15710 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15710; decide +kernel
    rw [ha]
    exact (canonical15710 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA954 + difference 5 1) (sourceB954 + difference 1 5) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3799) := by
    have ha : (tripleCharges (sourceA954 + difference 5 1) (sourceB954 + difference 1 5) sourceC954) = raw15711 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15711; decide +kernel
    rw [ha]
    exact (canonical15711 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA954 + difference 5 2) (sourceB954 + difference 2 5) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA954 + difference 5 2) (sourceB954 + difference 2 5) sourceC954) = raw15712 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15712; decide +kernel
    rw [ha]
    exact (canonical15712 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA954 + difference 5 3) (sourceB954 + difference 3 5) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3850) := by
    have ha : (tripleCharges (sourceA954 + difference 5 3) (sourceB954 + difference 3 5) sourceC954) = raw15713 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15713; decide +kernel
    rw [ha]
    exact (canonical15713 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA954 + difference 5 4) (sourceB954 + difference 4 5) sourceC954) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2676) := by
    have ha : (tripleCharges (sourceA954 + difference 5 4) (sourceB954 + difference 4 5) sourceC954) = raw15714 := by
      apply Matrix.ext; unfold tripleCharges sourceA954 sourceB954 sourceC954 difference raw15714; decide +kernel
    rw [ha]
    exact (canonical15714 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA954 sourceB954 sourceC954
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm954, Integer.Sparse.eval]
  linarith only [hs]

def sourceA955 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB955 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC955 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm955 : Integer.Sparse Master := [(Sum.inr 2860, 2), (Sum.inr 2864, 1), (Sum.inr 2874, 1), (Sum.inr 3085, 1), (Sum.inr 3374, 2), (Sum.inr 3378, 1), (Sum.inr 3384, 1), (Sum.inr 3569, 1), (Sum.inr 3758, 1), (Sum.inr 3759, 1), (Sum.inr 3762, 2), (Sum.inr 3788, 2), (Sum.inr 3801, 1), (Sum.inr 3877, 2), (Sum.inr 3953, 1), (Sum.inr 3958, 2), (Sum.inr 3959, 2), (Sum.inr 3977, 1), (Sum.inr 3982, 2), (Sum.inr 4023, 1), (Sum.inr 4027, 2)]

theorem sourceEq955 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm955 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA955 + difference 0 1) (sourceB955 + difference 1 0) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA955 + difference 0 1) (sourceB955 + difference 1 0) sourceC955) = raw15715 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15715; decide +kernel
    rw [ha]
    exact (canonical15715 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA955 + difference 0 2) (sourceB955 + difference 2 0) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA955 + difference 0 2) (sourceB955 + difference 2 0) sourceC955) = raw15143 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15143; decide +kernel
    rw [ha]
    exact (canonical15143 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA955 + difference 0 3) (sourceB955 + difference 3 0) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA955 + difference 0 3) (sourceB955 + difference 3 0) sourceC955) = raw15716 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15716; decide +kernel
    rw [ha]
    exact (canonical15716 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA955 + difference 0 4) (sourceB955 + difference 4 0) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3569) := by
    have ha : (tripleCharges (sourceA955 + difference 0 4) (sourceB955 + difference 4 0) sourceC955) = raw15717 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15717; decide +kernel
    rw [ha]
    exact (canonical15717 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA955 + difference 0 5) (sourceB955 + difference 5 0) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3758) := by
    have ha : (tripleCharges (sourceA955 + difference 0 5) (sourceB955 + difference 5 0) sourceC955) = raw15718 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15718; decide +kernel
    rw [ha]
    exact (canonical15718 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA955 + difference 1 0) (sourceB955 + difference 0 1) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2874) := by
    have ha : (tripleCharges (sourceA955 + difference 1 0) (sourceB955 + difference 0 1) sourceC955) = raw15719 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15719; decide +kernel
    rw [ha]
    exact (canonical15719 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA955 + difference 1 2) (sourceB955 + difference 2 1) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA955 + difference 1 2) (sourceB955 + difference 2 1) sourceC955) = raw15148 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15148; decide +kernel
    rw [ha]
    exact (canonical15148 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA955 + difference 1 3) (sourceB955 + difference 3 1) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3959) := by
    have ha : (tripleCharges (sourceA955 + difference 1 3) (sourceB955 + difference 3 1) sourceC955) = raw15720 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15720; decide +kernel
    rw [ha]
    exact (canonical15720 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA955 + difference 1 4) (sourceB955 + difference 4 1) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3384) := by
    have ha : (tripleCharges (sourceA955 + difference 1 4) (sourceB955 + difference 4 1) sourceC955) = raw15721 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15721; decide +kernel
    rw [ha]
    exact (canonical15721 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA955 + difference 1 5) (sourceB955 + difference 5 1) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3759) := by
    have ha : (tripleCharges (sourceA955 + difference 1 5) (sourceB955 + difference 5 1) sourceC955) = raw15722 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15722; decide +kernel
    rw [ha]
    exact (canonical15722 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA955 + difference 2 0) (sourceB955 + difference 0 2) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2860) := by
    have ha : (tripleCharges (sourceA955 + difference 2 0) (sourceB955 + difference 0 2) sourceC955) = raw15723 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15723; decide +kernel
    rw [ha]
    exact (canonical15723 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA955 + difference 2 1) (sourceB955 + difference 1 2) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA955 + difference 2 1) (sourceB955 + difference 1 2) sourceC955) = raw15724 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15724; decide +kernel
    rw [ha]
    exact (canonical15724 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA955 + difference 2 3) (sourceB955 + difference 3 2) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA955 + difference 2 3) (sourceB955 + difference 3 2) sourceC955) = raw15725 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15725; decide +kernel
    rw [ha]
    exact (canonical15725 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA955 + difference 2 4) (sourceB955 + difference 4 2) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3374) := by
    have ha : (tripleCharges (sourceA955 + difference 2 4) (sourceB955 + difference 4 2) sourceC955) = raw15726 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15726; decide +kernel
    rw [ha]
    exact (canonical15726 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA955 + difference 2 5) (sourceB955 + difference 5 2) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA955 + difference 2 5) (sourceB955 + difference 5 2) sourceC955) = raw15727 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15727; decide +kernel
    rw [ha]
    exact (canonical15727 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA955 + difference 3 0) (sourceB955 + difference 0 3) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2860) := by
    have ha : (tripleCharges (sourceA955 + difference 3 0) (sourceB955 + difference 0 3) sourceC955) = raw15728 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15728; decide +kernel
    rw [ha]
    exact (canonical15728 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA955 + difference 3 1) (sourceB955 + difference 1 3) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA955 + difference 3 1) (sourceB955 + difference 1 3) sourceC955) = raw15729 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15729; decide +kernel
    rw [ha]
    exact (canonical15729 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA955 + difference 3 2) (sourceB955 + difference 2 3) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA955 + difference 3 2) (sourceB955 + difference 2 3) sourceC955) = raw15158 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15158; decide +kernel
    rw [ha]
    exact (canonical15158 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA955 + difference 3 4) (sourceB955 + difference 4 3) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3374) := by
    have ha : (tripleCharges (sourceA955 + difference 3 4) (sourceB955 + difference 4 3) sourceC955) = raw15730 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15730; decide +kernel
    rw [ha]
    exact (canonical15730 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA955 + difference 3 5) (sourceB955 + difference 5 3) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3762) := by
    have ha : (tripleCharges (sourceA955 + difference 3 5) (sourceB955 + difference 5 3) sourceC955) = raw15731 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15731; decide +kernel
    rw [ha]
    exact (canonical15731 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA955 + difference 4 0) (sourceB955 + difference 0 4) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA955 + difference 4 0) (sourceB955 + difference 0 4) sourceC955) = raw15150 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15150; decide +kernel
    rw [ha]
    exact (canonical15150 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA955 + difference 4 1) (sourceB955 + difference 1 4) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3977) := by
    have ha : (tripleCharges (sourceA955 + difference 4 1) (sourceB955 + difference 1 4) sourceC955) = raw15151 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15151; decide +kernel
    rw [ha]
    exact (canonical15151 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA955 + difference 4 2) (sourceB955 + difference 2 4) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA955 + difference 4 2) (sourceB955 + difference 2 4) sourceC955) = raw15732 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15732; decide +kernel
    rw [ha]
    exact (canonical15732 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA955 + difference 4 3) (sourceB955 + difference 3 4) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3982) := by
    have ha : (tripleCharges (sourceA955 + difference 4 3) (sourceB955 + difference 3 4) sourceC955) = raw15152 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15152; decide +kernel
    rw [ha]
    exact (canonical15152 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA955 + difference 4 5) (sourceB955 + difference 5 4) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA955 + difference 4 5) (sourceB955 + difference 5 4) sourceC955) = raw15154 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15154; decide +kernel
    rw [ha]
    exact (canonical15154 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA955 + difference 5 0) (sourceB955 + difference 0 5) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2864) := by
    have ha : (tripleCharges (sourceA955 + difference 5 0) (sourceB955 + difference 0 5) sourceC955) = raw15733 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15733; decide +kernel
    rw [ha]
    exact (canonical15733 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA955 + difference 5 1) (sourceB955 + difference 1 5) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4023) := by
    have ha : (tripleCharges (sourceA955 + difference 5 1) (sourceB955 + difference 1 5) sourceC955) = raw15734 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15734; decide +kernel
    rw [ha]
    exact (canonical15734 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA955 + difference 5 2) (sourceB955 + difference 2 5) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4027) := by
    have ha : (tripleCharges (sourceA955 + difference 5 2) (sourceB955 + difference 2 5) sourceC955) = raw15166 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15166; decide +kernel
    rw [ha]
    exact (canonical15166 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA955 + difference 5 3) (sourceB955 + difference 3 5) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4027) := by
    have ha : (tripleCharges (sourceA955 + difference 5 3) (sourceB955 + difference 3 5) sourceC955) = raw15735 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15735; decide +kernel
    rw [ha]
    exact (canonical15735 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA955 + difference 5 4) (sourceB955 + difference 4 5) sourceC955) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3378) := by
    have ha : (tripleCharges (sourceA955 + difference 5 4) (sourceB955 + difference 4 5) sourceC955) = raw15736 := by
      apply Matrix.ext; unfold tripleCharges sourceA955 sourceB955 sourceC955 difference raw15736; decide +kernel
    rw [ha]
    exact (canonical15736 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA955 sourceB955 sourceC955
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm955, Integer.Sparse.eval]
  linarith only [hs]

def sourceA956 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB956 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC956 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm956 : Integer.Sparse Master := [(Sum.inr 2878, 1), (Sum.inr 3703, 1), (Sum.inr 3874, 1), (Sum.inr 3956, 1), (Sum.inr 3961, 2), (Sum.inr 4092, -1)]

theorem sourceEq956 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm956 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA956 + difference 0 0) (sourceB956 + difference 0 0) sourceC956) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA956 + difference 0 0) (sourceB956 + difference 0 0) sourceC956) = raw15737 := by
      apply Matrix.ext; unfold tripleCharges sourceA956 sourceB956 sourceC956 difference raw15737; decide +kernel
    rw [ha]
    exact (canonical15737 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA956 + difference 0 1) (sourceB956 + difference 1 0) sourceC956) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3956) := by
    have ha : (tripleCharges (sourceA956 + difference 0 1) (sourceB956 + difference 1 0) sourceC956) = raw15738 := by
      apply Matrix.ext; unfold tripleCharges sourceA956 sourceB956 sourceC956 difference raw15738; decide +kernel
    rw [ha]
    exact (canonical15738 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA956 + difference 0 2) (sourceB956 + difference 2 0) sourceC956) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA956 + difference 0 2) (sourceB956 + difference 2 0) sourceC956) = raw15739 := by
      apply Matrix.ext; unfold tripleCharges sourceA956 sourceB956 sourceC956 difference raw15739; decide +kernel
    rw [ha]
    exact (canonical15739 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA956 + difference 0 3) (sourceB956 + difference 3 0) sourceC956) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3961) := by
    have ha : (tripleCharges (sourceA956 + difference 0 3) (sourceB956 + difference 3 0) sourceC956) = raw15740 := by
      apply Matrix.ext; unfold tripleCharges sourceA956 sourceB956 sourceC956 difference raw15740; decide +kernel
    rw [ha]
    exact (canonical15740 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA956 + difference 0 4) (sourceB956 + difference 4 0) sourceC956) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2878) := by
    have ha : (tripleCharges (sourceA956 + difference 0 4) (sourceB956 + difference 4 0) sourceC956) = raw15741 := by
      apply Matrix.ext; unfold tripleCharges sourceA956 sourceB956 sourceC956 difference raw15741; decide +kernel
    rw [ha]
    exact (canonical15741 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA956 + difference 0 5) (sourceB956 + difference 5 0) sourceC956) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3703) := by
    have ha : (tripleCharges (sourceA956 + difference 0 5) (sourceB956 + difference 5 0) sourceC956) = raw15742 := by
      apply Matrix.ext; unfold tripleCharges sourceA956 sourceB956 sourceC956 difference raw15742; decide +kernel
    rw [ha]
    exact (canonical15742 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA956 + sourceB956) sourceC956) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA956 + sourceB956) sourceC956) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA956 sourceB956 sourceC956 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA956 sourceB956 sourceC956
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm956, Integer.Sparse.eval]
  linarith only [hs]

def sourceA957 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB957 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC957 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm957 : Integer.Sparse Master := [(Sum.inr 2630, 1), (Sum.inr 2869, 1), (Sum.inr 3697, 1), (Sum.inr 3874, 1), (Sum.inr 3884, 2), (Sum.inr 4092, -1)]

theorem sourceEq957 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm957 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA957 + difference 1 0) (sourceB957 + difference 0 1) sourceC957) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2630) := by
    have ha : (tripleCharges (sourceA957 + difference 1 0) (sourceB957 + difference 0 1) sourceC957) = raw15743 := by
      apply Matrix.ext; unfold tripleCharges sourceA957 sourceB957 sourceC957 difference raw15743; decide +kernel
    rw [ha]
    exact (canonical15743 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA957 + difference 1 1) (sourceB957 + difference 1 1) sourceC957) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA957 + difference 1 1) (sourceB957 + difference 1 1) sourceC957) = raw15737 := by
      apply Matrix.ext; unfold tripleCharges sourceA957 sourceB957 sourceC957 difference raw15737; decide +kernel
    rw [ha]
    exact (canonical15737 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA957 + difference 1 2) (sourceB957 + difference 2 1) sourceC957) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA957 + difference 1 2) (sourceB957 + difference 2 1) sourceC957) = raw15744 := by
      apply Matrix.ext; unfold tripleCharges sourceA957 sourceB957 sourceC957 difference raw15744; decide +kernel
    rw [ha]
    exact (canonical15744 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA957 + difference 1 3) (sourceB957 + difference 3 1) sourceC957) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA957 + difference 1 3) (sourceB957 + difference 3 1) sourceC957) = raw15745 := by
      apply Matrix.ext; unfold tripleCharges sourceA957 sourceB957 sourceC957 difference raw15745; decide +kernel
    rw [ha]
    exact (canonical15745 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA957 + difference 1 4) (sourceB957 + difference 4 1) sourceC957) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2869) := by
    have ha : (tripleCharges (sourceA957 + difference 1 4) (sourceB957 + difference 4 1) sourceC957) = raw15746 := by
      apply Matrix.ext; unfold tripleCharges sourceA957 sourceB957 sourceC957 difference raw15746; decide +kernel
    rw [ha]
    exact (canonical15746 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA957 + difference 1 5) (sourceB957 + difference 5 1) sourceC957) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3697) := by
    have ha : (tripleCharges (sourceA957 + difference 1 5) (sourceB957 + difference 5 1) sourceC957) = raw15747 := by
      apply Matrix.ext; unfold tripleCharges sourceA957 sourceB957 sourceC957 difference raw15747; decide +kernel
    rw [ha]
    exact (canonical15747 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA957 + sourceB957) sourceC957) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA957 + sourceB957) sourceC957) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA957 sourceB957 sourceC957 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA957 sourceB957 sourceC957
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm957, Integer.Sparse.eval]
  linarith only [hs]

def sourceA958 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB958 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC958 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm958 : Integer.Sparse Master := [(Sum.inr 3786, 1), (Sum.inr 3788, 2), (Sum.inr 3805, 1), (Sum.inr 3874, 1), (Sum.inr 3956, 1), (Sum.inr 4092, -1)]

theorem sourceEq958 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm958 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA958 + difference 0 1) (sourceB958 + difference 1 0) sourceC958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3956) := by
    have ha : (tripleCharges (sourceA958 + difference 0 1) (sourceB958 + difference 1 0) sourceC958) = raw15738 := by
      apply Matrix.ext; unfold tripleCharges sourceA958 sourceB958 sourceC958 difference raw15738; decide +kernel
    rw [ha]
    exact (canonical15738 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA958 + difference 1 1) (sourceB958 + difference 1 1) sourceC958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA958 + difference 1 1) (sourceB958 + difference 1 1) sourceC958) = raw15737 := by
      apply Matrix.ext; unfold tripleCharges sourceA958 sourceB958 sourceC958 difference raw15737; decide +kernel
    rw [ha]
    exact (canonical15737 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA958 + difference 2 1) (sourceB958 + difference 1 2) sourceC958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA958 + difference 2 1) (sourceB958 + difference 1 2) sourceC958) = raw15748 := by
      apply Matrix.ext; unfold tripleCharges sourceA958 sourceB958 sourceC958 difference raw15748; decide +kernel
    rw [ha]
    exact (canonical15748 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA958 + difference 3 1) (sourceB958 + difference 1 3) sourceC958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3788) := by
    have ha : (tripleCharges (sourceA958 + difference 3 1) (sourceB958 + difference 1 3) sourceC958) = raw15749 := by
      apply Matrix.ext; unfold tripleCharges sourceA958 sourceB958 sourceC958 difference raw15749; decide +kernel
    rw [ha]
    exact (canonical15749 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA958 + difference 4 1) (sourceB958 + difference 1 4) sourceC958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3805) := by
    have ha : (tripleCharges (sourceA958 + difference 4 1) (sourceB958 + difference 1 4) sourceC958) = raw15750 := by
      apply Matrix.ext; unfold tripleCharges sourceA958 sourceB958 sourceC958 difference raw15750; decide +kernel
    rw [ha]
    exact (canonical15750 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA958 + difference 5 1) (sourceB958 + difference 1 5) sourceC958) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3786) := by
    have ha : (tripleCharges (sourceA958 + difference 5 1) (sourceB958 + difference 1 5) sourceC958) = raw15751 := by
      apply Matrix.ext; unfold tripleCharges sourceA958 sourceB958 sourceC958 difference raw15751; decide +kernel
    rw [ha]
    exact (canonical15751 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA958 + sourceB958) sourceC958) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA958 + sourceB958) sourceC958) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA958 sourceB958 sourceC958 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA958 sourceB958 sourceC958
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm958, Integer.Sparse.eval]
  linarith only [hs]

def sourceA959 : Charge := ![0, 1, 1, 1, -2, -1]
def sourceB959 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceC959 : Charge := ![-2, -1, 0, 0, 1, 2]
def sourceForm959 : Integer.Sparse Master := [(Sum.inr 2869, 1), (Sum.inr 2870, 2), (Sum.inr 2878, 1), (Sum.inr 3043, 1), (Sum.inr 3874, 1), (Sum.inr 4092, -1)]

theorem sourceEq959 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm959 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA959 + difference 0 4) (sourceB959 + difference 4 0) sourceC959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2878) := by
    have ha : (tripleCharges (sourceA959 + difference 0 4) (sourceB959 + difference 4 0) sourceC959) = raw15741 := by
      apply Matrix.ext; unfold tripleCharges sourceA959 sourceB959 sourceC959 difference raw15741; decide +kernel
    rw [ha]
    exact (canonical15741 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA959 + difference 1 4) (sourceB959 + difference 4 1) sourceC959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2869) := by
    have ha : (tripleCharges (sourceA959 + difference 1 4) (sourceB959 + difference 4 1) sourceC959) = raw15746 := by
      apply Matrix.ext; unfold tripleCharges sourceA959 sourceB959 sourceC959 difference raw15746; decide +kernel
    rw [ha]
    exact (canonical15746 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA959 + difference 2 4) (sourceB959 + difference 4 2) sourceC959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2870) := by
    have ha : (tripleCharges (sourceA959 + difference 2 4) (sourceB959 + difference 4 2) sourceC959) = raw15752 := by
      apply Matrix.ext; unfold tripleCharges sourceA959 sourceB959 sourceC959 difference raw15752; decide +kernel
    rw [ha]
    exact (canonical15752 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA959 + difference 3 4) (sourceB959 + difference 4 3) sourceC959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2870) := by
    have ha : (tripleCharges (sourceA959 + difference 3 4) (sourceB959 + difference 4 3) sourceC959) = raw15753 := by
      apply Matrix.ext; unfold tripleCharges sourceA959 sourceB959 sourceC959 difference raw15753; decide +kernel
    rw [ha]
    exact (canonical15753 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA959 + difference 4 4) (sourceB959 + difference 4 4) sourceC959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3874) := by
    have ha : (tripleCharges (sourceA959 + difference 4 4) (sourceB959 + difference 4 4) sourceC959) = raw15737 := by
      apply Matrix.ext; unfold tripleCharges sourceA959 sourceB959 sourceC959 difference raw15737; decide +kernel
    rw [ha]
    exact (canonical15737 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA959 + difference 5 4) (sourceB959 + difference 4 5) sourceC959) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3043) := by
    have ha : (tripleCharges (sourceA959 + difference 5 4) (sourceB959 + difference 4 5) sourceC959) = raw15754 := by
      apply Matrix.ext; unfold tripleCharges sourceA959 sourceB959 sourceC959 difference raw15754; decide +kernel
    rw [ha]
    exact (canonical15754 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA959 + sourceB959) sourceC959) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA959 + sourceB959) sourceC959) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA959 sourceB959 sourceC959 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA959 sourceB959 sourceC959
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm959, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
