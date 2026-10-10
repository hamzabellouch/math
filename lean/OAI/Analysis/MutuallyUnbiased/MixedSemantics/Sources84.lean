import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical292
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical293

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2688 : Charge := ![2, 0, -1, -1, 1, -1]
def sourceB2688 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2688 : Charge := ![-5, 0, 1, 1, 1, 2]
def sourceForm2688 : Integer.Sparse Master := [(Sum.inr 1504, 1), (Sum.inr 1507, 1), (Sum.inr 1508, 1), (Sum.inr 1517, 3), (Sum.inr 4057, -1)]

theorem sourceEq2688 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2688 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2688 + difference 0 4) (sourceB2688 + difference 4 0) sourceC2688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1517) := by
    have ha : (tripleCharges (sourceA2688 + difference 0 4) (sourceB2688 + difference 4 0) sourceC2688) = raw37483 := by
      apply Matrix.ext; unfold tripleCharges sourceA2688 sourceB2688 sourceC2688 difference raw37483; decide +kernel
    rw [ha]
    exact (canonical37483 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2688 + difference 1 4) (sourceB2688 + difference 4 1) sourceC2688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1504) := by
    have ha : (tripleCharges (sourceA2688 + difference 1 4) (sourceB2688 + difference 4 1) sourceC2688) = raw37484 := by
      apply Matrix.ext; unfold tripleCharges sourceA2688 sourceB2688 sourceC2688 difference raw37484; decide +kernel
    rw [ha]
    exact (canonical37484 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2688 + difference 2 4) (sourceB2688 + difference 4 2) sourceC2688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1517) := by
    have ha : (tripleCharges (sourceA2688 + difference 2 4) (sourceB2688 + difference 4 2) sourceC2688) = raw37485 := by
      apply Matrix.ext; unfold tripleCharges sourceA2688 sourceB2688 sourceC2688 difference raw37485; decide +kernel
    rw [ha]
    exact (canonical37485 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2688 + difference 3 4) (sourceB2688 + difference 4 3) sourceC2688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1517) := by
    have ha : (tripleCharges (sourceA2688 + difference 3 4) (sourceB2688 + difference 4 3) sourceC2688) = raw37486 := by
      apply Matrix.ext; unfold tripleCharges sourceA2688 sourceB2688 sourceC2688 difference raw37486; decide +kernel
    rw [ha]
    exact (canonical37486 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2688 + difference 4 4) (sourceB2688 + difference 4 4) sourceC2688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1508) := by
    have ha : (tripleCharges (sourceA2688 + difference 4 4) (sourceB2688 + difference 4 4) sourceC2688) = raw37487 := by
      apply Matrix.ext; unfold tripleCharges sourceA2688 sourceB2688 sourceC2688 difference raw37487; decide +kernel
    rw [ha]
    exact (canonical37487 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2688 + difference 5 4) (sourceB2688 + difference 4 5) sourceC2688) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1507) := by
    have ha : (tripleCharges (sourceA2688 + difference 5 4) (sourceB2688 + difference 4 5) sourceC2688) = raw37480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2688 sourceB2688 sourceC2688 difference raw37480; decide +kernel
    rw [ha]
    exact (canonical37480 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2688 + sourceB2688) sourceC2688) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (doubleCharges (sourceA2688 + sourceB2688) sourceC2688) = raw37482 := by
      apply Matrix.ext; unfold doubleCharges sourceA2688 sourceB2688 sourceC2688 raw37482; decide +kernel
    rw [ha]
    exact (canonical37482 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2688 sourceB2688 sourceC2688
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2688, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2689 : Charge := ![2, 0, -1, 0, 1, -2]
def sourceB2689 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC2689 : Charge := ![-5, 0, 1, 1, 1, 2]
def sourceForm2689 : Integer.Sparse Master := [(Sum.inr 1507, 1), (Sum.inr 1510, 1), (Sum.inr 1512, 2), (Sum.inr 1517, 1), (Sum.inr 1524, 1), (Sum.inr 4057, -1)]

theorem sourceEq2689 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2689 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2689 + difference 0 4) (sourceB2689 + difference 4 0) sourceC2689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1507) := by
    have ha : (tripleCharges (sourceA2689 + difference 0 4) (sourceB2689 + difference 4 0) sourceC2689) = raw37488 := by
      apply Matrix.ext; unfold tripleCharges sourceA2689 sourceB2689 sourceC2689 difference raw37488; decide +kernel
    rw [ha]
    exact (canonical37488 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2689 + difference 1 4) (sourceB2689 + difference 4 1) sourceC2689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1510) := by
    have ha : (tripleCharges (sourceA2689 + difference 1 4) (sourceB2689 + difference 4 1) sourceC2689) = raw37489 := by
      apply Matrix.ext; unfold tripleCharges sourceA2689 sourceB2689 sourceC2689 difference raw37489; decide +kernel
    rw [ha]
    exact (canonical37489 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2689 + difference 2 4) (sourceB2689 + difference 4 2) sourceC2689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1524) := by
    have ha : (tripleCharges (sourceA2689 + difference 2 4) (sourceB2689 + difference 4 2) sourceC2689) = raw37490 := by
      apply Matrix.ext; unfold tripleCharges sourceA2689 sourceB2689 sourceC2689 difference raw37490; decide +kernel
    rw [ha]
    exact (canonical37490 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2689 + difference 3 4) (sourceB2689 + difference 4 3) sourceC2689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1512) := by
    have ha : (tripleCharges (sourceA2689 + difference 3 4) (sourceB2689 + difference 4 3) sourceC2689) = raw37491 := by
      apply Matrix.ext; unfold tripleCharges sourceA2689 sourceB2689 sourceC2689 difference raw37491; decide +kernel
    rw [ha]
    exact (canonical37491 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2689 + difference 4 4) (sourceB2689 + difference 4 4) sourceC2689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1512) := by
    have ha : (tripleCharges (sourceA2689 + difference 4 4) (sourceB2689 + difference 4 4) sourceC2689) = raw37492 := by
      apply Matrix.ext; unfold tripleCharges sourceA2689 sourceB2689 sourceC2689 difference raw37492; decide +kernel
    rw [ha]
    exact (canonical37492 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2689 + difference 5 4) (sourceB2689 + difference 4 5) sourceC2689) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1517) := by
    have ha : (tripleCharges (sourceA2689 + difference 5 4) (sourceB2689 + difference 4 5) sourceC2689) = raw37486 := by
      apply Matrix.ext; unfold tripleCharges sourceA2689 sourceB2689 sourceC2689 difference raw37486; decide +kernel
    rw [ha]
    exact (canonical37486 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2689 + sourceB2689) sourceC2689) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (doubleCharges (sourceA2689 + sourceB2689) sourceC2689) = raw37482 := by
      apply Matrix.ext; unfold doubleCharges sourceA2689 sourceB2689 sourceC2689 raw37482; decide +kernel
    rw [ha]
    exact (canonical37482 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2689 sourceB2689 sourceC2689
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2689, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2690 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2690 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC2690 : Charge := ![-5, 0, 1, 1, 1, 2]
def sourceForm2690 : Integer.Sparse Master := [(Sum.inr 674, 1), (Sum.inr 677, 3), (Sum.inr 687, 1), (Sum.inr 1524, 1), (Sum.inr 4057, -1)]

theorem sourceEq2690 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2690 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2690 + difference 0 0) (sourceB2690 + difference 0 0) sourceC2690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1524) := by
    have ha : (tripleCharges (sourceA2690 + difference 0 0) (sourceB2690 + difference 0 0) sourceC2690) = raw37490 := by
      apply Matrix.ext; unfold tripleCharges sourceA2690 sourceB2690 sourceC2690 difference raw37490; decide +kernel
    rw [ha]
    exact (canonical37490 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2690 + difference 1 0) (sourceB2690 + difference 0 1) sourceC2690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 674) := by
    have ha : (tripleCharges (sourceA2690 + difference 1 0) (sourceB2690 + difference 0 1) sourceC2690) = raw37493 := by
      apply Matrix.ext; unfold tripleCharges sourceA2690 sourceB2690 sourceC2690 difference raw37493; decide +kernel
    rw [ha]
    exact (canonical37493 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2690 + difference 2 0) (sourceB2690 + difference 0 2) sourceC2690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 677) := by
    have ha : (tripleCharges (sourceA2690 + difference 2 0) (sourceB2690 + difference 0 2) sourceC2690) = raw37494 := by
      apply Matrix.ext; unfold tripleCharges sourceA2690 sourceB2690 sourceC2690 difference raw37494; decide +kernel
    rw [ha]
    exact (canonical37494 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2690 + difference 3 0) (sourceB2690 + difference 0 3) sourceC2690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 677) := by
    have ha : (tripleCharges (sourceA2690 + difference 3 0) (sourceB2690 + difference 0 3) sourceC2690) = raw37495 := by
      apply Matrix.ext; unfold tripleCharges sourceA2690 sourceB2690 sourceC2690 difference raw37495; decide +kernel
    rw [ha]
    exact (canonical37495 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2690 + difference 4 0) (sourceB2690 + difference 0 4) sourceC2690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 677) := by
    have ha : (tripleCharges (sourceA2690 + difference 4 0) (sourceB2690 + difference 0 4) sourceC2690) = raw37496 := by
      apply Matrix.ext; unfold tripleCharges sourceA2690 sourceB2690 sourceC2690 difference raw37496; decide +kernel
    rw [ha]
    exact (canonical37496 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2690 + difference 5 0) (sourceB2690 + difference 0 5) sourceC2690) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 687) := by
    have ha : (tripleCharges (sourceA2690 + difference 5 0) (sourceB2690 + difference 0 5) sourceC2690) = raw37497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2690 sourceB2690 sourceC2690 difference raw37497; decide +kernel
    rw [ha]
    exact (canonical37497 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2690 + sourceB2690) sourceC2690) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (doubleCharges (sourceA2690 + sourceB2690) sourceC2690) = raw37482 := by
      apply Matrix.ext; unfold doubleCharges sourceA2690 sourceB2690 sourceC2690 raw37482; decide +kernel
    rw [ha]
    exact (canonical37482 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2690 sourceB2690 sourceC2690
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2690, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2691 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2691 : Charge := ![3, 0, -1, -1, -1, 0]
def sourceC2691 : Charge := ![-5, 0, 1, 1, 1, 2]
def sourceForm2691 : Integer.Sparse Master := [(Sum.inr 687, 1), (Sum.inr 1491, 1), (Sum.inr 1517, 3), (Sum.inr 1524, 1), (Sum.inr 4057, -1)]

theorem sourceEq2691 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2691 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2691 + difference 5 0) (sourceB2691 + difference 0 5) sourceC2691) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 687) := by
    have ha : (tripleCharges (sourceA2691 + difference 5 0) (sourceB2691 + difference 0 5) sourceC2691) = raw37497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2691 sourceB2691 sourceC2691 difference raw37497; decide +kernel
    rw [ha]
    exact (canonical37497 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2691 + difference 5 1) (sourceB2691 + difference 1 5) sourceC2691) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1491) := by
    have ha : (tripleCharges (sourceA2691 + difference 5 1) (sourceB2691 + difference 1 5) sourceC2691) = raw37498 := by
      apply Matrix.ext; unfold tripleCharges sourceA2691 sourceB2691 sourceC2691 difference raw37498; decide +kernel
    rw [ha]
    exact (canonical37498 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2691 + difference 5 2) (sourceB2691 + difference 2 5) sourceC2691) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1517) := by
    have ha : (tripleCharges (sourceA2691 + difference 5 2) (sourceB2691 + difference 2 5) sourceC2691) = raw37486 := by
      apply Matrix.ext; unfold tripleCharges sourceA2691 sourceB2691 sourceC2691 difference raw37486; decide +kernel
    rw [ha]
    exact (canonical37486 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2691 + difference 5 3) (sourceB2691 + difference 3 5) sourceC2691) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1517) := by
    have ha : (tripleCharges (sourceA2691 + difference 5 3) (sourceB2691 + difference 3 5) sourceC2691) = raw37485 := by
      apply Matrix.ext; unfold tripleCharges sourceA2691 sourceB2691 sourceC2691 difference raw37485; decide +kernel
    rw [ha]
    exact (canonical37485 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2691 + difference 5 4) (sourceB2691 + difference 4 5) sourceC2691) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1517) := by
    have ha : (tripleCharges (sourceA2691 + difference 5 4) (sourceB2691 + difference 4 5) sourceC2691) = raw37499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2691 sourceB2691 sourceC2691 difference raw37499; decide +kernel
    rw [ha]
    exact (canonical37499 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2691 + difference 5 5) (sourceB2691 + difference 5 5) sourceC2691) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1524) := by
    have ha : (tripleCharges (sourceA2691 + difference 5 5) (sourceB2691 + difference 5 5) sourceC2691) = raw37490 := by
      apply Matrix.ext; unfold tripleCharges sourceA2691 sourceB2691 sourceC2691 difference raw37490; decide +kernel
    rw [ha]
    exact (canonical37490 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2691 + sourceB2691) sourceC2691) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (doubleCharges (sourceA2691 + sourceB2691) sourceC2691) = raw37482 := by
      apply Matrix.ext; unfold doubleCharges sourceA2691 sourceB2691 sourceC2691 raw37482; decide +kernel
    rw [ha]
    exact (canonical37482 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2691 sourceB2691 sourceC2691
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2691, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2692 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2692 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC2692 : Charge := ![-5, 0, 1, 1, 1, 2]
def sourceForm2692 : Integer.Sparse Master := [(Sum.inr 662, 1), (Sum.inr 667, 1), (Sum.inr 668, 2), (Sum.inr 687, 1), (Sum.inr 1517, 1), (Sum.inr 4057, -1)]

theorem sourceEq2692 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2692 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2692 + difference 0 0) (sourceB2692 + difference 0 0) sourceC2692) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1517) := by
    have ha : (tripleCharges (sourceA2692 + difference 0 0) (sourceB2692 + difference 0 0) sourceC2692) = raw37499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2692 sourceB2692 sourceC2692 difference raw37499; decide +kernel
    rw [ha]
    exact (canonical37499 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2692 + difference 1 0) (sourceB2692 + difference 0 1) sourceC2692) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 662) := by
    have ha : (tripleCharges (sourceA2692 + difference 1 0) (sourceB2692 + difference 0 1) sourceC2692) = raw37500 := by
      apply Matrix.ext; unfold tripleCharges sourceA2692 sourceB2692 sourceC2692 difference raw37500; decide +kernel
    rw [ha]
    exact (canonical37500 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2692 + difference 2 0) (sourceB2692 + difference 0 2) sourceC2692) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 668) := by
    have ha : (tripleCharges (sourceA2692 + difference 2 0) (sourceB2692 + difference 0 2) sourceC2692) = raw37501 := by
      apply Matrix.ext; unfold tripleCharges sourceA2692 sourceB2692 sourceC2692 difference raw37501; decide +kernel
    rw [ha]
    exact (canonical37501 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2692 + difference 3 0) (sourceB2692 + difference 0 3) sourceC2692) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 668) := by
    have ha : (tripleCharges (sourceA2692 + difference 3 0) (sourceB2692 + difference 0 3) sourceC2692) = raw37502 := by
      apply Matrix.ext; unfold tripleCharges sourceA2692 sourceB2692 sourceC2692 difference raw37502; decide +kernel
    rw [ha]
    exact (canonical37502 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2692 + difference 4 0) (sourceB2692 + difference 0 4) sourceC2692) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 687) := by
    have ha : (tripleCharges (sourceA2692 + difference 4 0) (sourceB2692 + difference 0 4) sourceC2692) = raw37497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2692 sourceB2692 sourceC2692 difference raw37497; decide +kernel
    rw [ha]
    exact (canonical37497 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2692 + difference 5 0) (sourceB2692 + difference 0 5) sourceC2692) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 667) := by
    have ha : (tripleCharges (sourceA2692 + difference 5 0) (sourceB2692 + difference 0 5) sourceC2692) = raw37503 := by
      apply Matrix.ext; unfold tripleCharges sourceA2692 sourceB2692 sourceC2692 difference raw37503; decide +kernel
    rw [ha]
    exact (canonical37503 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2692 + sourceB2692) sourceC2692) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (doubleCharges (sourceA2692 + sourceB2692) sourceC2692) = raw37482 := by
      apply Matrix.ext; unfold doubleCharges sourceA2692 sourceB2692 sourceC2692 raw37482; decide +kernel
    rw [ha]
    exact (canonical37482 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2692 sourceB2692 sourceC2692
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2692, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2693 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2693 : Charge := ![3, 0, -1, -1, 0, -1]
def sourceC2693 : Charge := ![-5, 0, 1, 1, 1, 2]
def sourceForm2693 : Integer.Sparse Master := [(Sum.inr 667, 1), (Sum.inr 1488, 1), (Sum.inr 1498, 1), (Sum.inr 1507, 2), (Sum.inr 1517, 1), (Sum.inr 4057, -1)]

theorem sourceEq2693 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2693 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2693 + difference 5 0) (sourceB2693 + difference 0 5) sourceC2693) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 667) := by
    have ha : (tripleCharges (sourceA2693 + difference 5 0) (sourceB2693 + difference 0 5) sourceC2693) = raw37503 := by
      apply Matrix.ext; unfold tripleCharges sourceA2693 sourceB2693 sourceC2693 difference raw37503; decide +kernel
    rw [ha]
    exact (canonical37503 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2693 + difference 5 1) (sourceB2693 + difference 1 5) sourceC2693) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1488) := by
    have ha : (tripleCharges (sourceA2693 + difference 5 1) (sourceB2693 + difference 1 5) sourceC2693) = raw37504 := by
      apply Matrix.ext; unfold tripleCharges sourceA2693 sourceB2693 sourceC2693 difference raw37504; decide +kernel
    rw [ha]
    exact (canonical37504 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2693 + difference 5 2) (sourceB2693 + difference 2 5) sourceC2693) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1507) := by
    have ha : (tripleCharges (sourceA2693 + difference 5 2) (sourceB2693 + difference 2 5) sourceC2693) = raw37479 := by
      apply Matrix.ext; unfold tripleCharges sourceA2693 sourceB2693 sourceC2693 difference raw37479; decide +kernel
    rw [ha]
    exact (canonical37479 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2693 + difference 5 3) (sourceB2693 + difference 3 5) sourceC2693) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1507) := by
    have ha : (tripleCharges (sourceA2693 + difference 5 3) (sourceB2693 + difference 3 5) sourceC2693) = raw37478 := by
      apply Matrix.ext; unfold tripleCharges sourceA2693 sourceB2693 sourceC2693 difference raw37478; decide +kernel
    rw [ha]
    exact (canonical37478 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2693 + difference 5 4) (sourceB2693 + difference 4 5) sourceC2693) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1498) := by
    have ha : (tripleCharges (sourceA2693 + difference 5 4) (sourceB2693 + difference 4 5) sourceC2693) = raw37505 := by
      apply Matrix.ext; unfold tripleCharges sourceA2693 sourceB2693 sourceC2693 difference raw37505; decide +kernel
    rw [ha]
    exact (canonical37505 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2693 + difference 5 5) (sourceB2693 + difference 5 5) sourceC2693) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1517) := by
    have ha : (tripleCharges (sourceA2693 + difference 5 5) (sourceB2693 + difference 5 5) sourceC2693) = raw37499 := by
      apply Matrix.ext; unfold tripleCharges sourceA2693 sourceB2693 sourceC2693 difference raw37499; decide +kernel
    rw [ha]
    exact (canonical37499 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2693 + sourceB2693) sourceC2693) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (doubleCharges (sourceA2693 + sourceB2693) sourceC2693) = raw37482 := by
      apply Matrix.ext; unfold doubleCharges sourceA2693 sourceB2693 sourceC2693 raw37482; decide +kernel
    rw [ha]
    exact (canonical37482 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2693 sourceB2693 sourceC2693
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2693, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2694 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB2694 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceC2694 : Charge := ![-5, 0, 1, 1, 1, 2]
def sourceForm2694 : Integer.Sparse Master := [(Sum.inr 656, 1), (Sum.inr 659, 1), (Sum.inr 660, 1), (Sum.inr 667, 2), (Sum.inr 1507, 1), (Sum.inr 4057, -1)]

theorem sourceEq2694 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2694 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2694 + difference 0 0) (sourceB2694 + difference 0 0) sourceC2694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1507) := by
    have ha : (tripleCharges (sourceA2694 + difference 0 0) (sourceB2694 + difference 0 0) sourceC2694) = raw37478 := by
      apply Matrix.ext; unfold tripleCharges sourceA2694 sourceB2694 sourceC2694 difference raw37478; decide +kernel
    rw [ha]
    exact (canonical37478 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2694 + difference 1 0) (sourceB2694 + difference 0 1) sourceC2694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 656) := by
    have ha : (tripleCharges (sourceA2694 + difference 1 0) (sourceB2694 + difference 0 1) sourceC2694) = raw37506 := by
      apply Matrix.ext; unfold tripleCharges sourceA2694 sourceB2694 sourceC2694 difference raw37506; decide +kernel
    rw [ha]
    exact (canonical37506 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2694 + difference 2 0) (sourceB2694 + difference 0 2) sourceC2694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 660) := by
    have ha : (tripleCharges (sourceA2694 + difference 2 0) (sourceB2694 + difference 0 2) sourceC2694) = raw37507 := by
      apply Matrix.ext; unfold tripleCharges sourceA2694 sourceB2694 sourceC2694 difference raw37507; decide +kernel
    rw [ha]
    exact (canonical37507 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2694 + difference 3 0) (sourceB2694 + difference 0 3) sourceC2694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 667) := by
    have ha : (tripleCharges (sourceA2694 + difference 3 0) (sourceB2694 + difference 0 3) sourceC2694) = raw37503 := by
      apply Matrix.ext; unfold tripleCharges sourceA2694 sourceB2694 sourceC2694 difference raw37503; decide +kernel
    rw [ha]
    exact (canonical37503 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2694 + difference 4 0) (sourceB2694 + difference 0 4) sourceC2694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 667) := by
    have ha : (tripleCharges (sourceA2694 + difference 4 0) (sourceB2694 + difference 0 4) sourceC2694) = raw37508 := by
      apply Matrix.ext; unfold tripleCharges sourceA2694 sourceB2694 sourceC2694 difference raw37508; decide +kernel
    rw [ha]
    exact (canonical37508 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2694 + difference 5 0) (sourceB2694 + difference 0 5) sourceC2694) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 659) := by
    have ha : (tripleCharges (sourceA2694 + difference 5 0) (sourceB2694 + difference 0 5) sourceC2694) = raw37509 := by
      apply Matrix.ext; unfold tripleCharges sourceA2694 sourceB2694 sourceC2694 difference raw37509; decide +kernel
    rw [ha]
    exact (canonical37509 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2694 + sourceB2694) sourceC2694) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (doubleCharges (sourceA2694 + sourceB2694) sourceC2694) = raw37482 := by
      apply Matrix.ext; unfold doubleCharges sourceA2694 sourceB2694 sourceC2694 raw37482; decide +kernel
    rw [ha]
    exact (canonical37482 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2694 sourceB2694 sourceC2694
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2694, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2695 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB2695 : Charge := ![4, -1, -1, -1, -1, 0]
def sourceC2695 : Charge := ![-5, 0, 1, 1, 1, 2]
def sourceForm2695 : Integer.Sparse Master := [(Sum.inr 534, 1), (Sum.inr 662, 3), (Sum.inr 674, 1), (Sum.inr 687, 1), (Sum.inr 4057, -1)]

theorem sourceEq2695 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2695 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2695 + difference 5 0) (sourceB2695 + difference 0 5) sourceC2695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 534) := by
    have ha : (tripleCharges (sourceA2695 + difference 5 0) (sourceB2695 + difference 0 5) sourceC2695) = raw37510 := by
      apply Matrix.ext; unfold tripleCharges sourceA2695 sourceB2695 sourceC2695 difference raw37510; decide +kernel
    rw [ha]
    exact (canonical37510 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2695 + difference 5 1) (sourceB2695 + difference 1 5) sourceC2695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 687) := by
    have ha : (tripleCharges (sourceA2695 + difference 5 1) (sourceB2695 + difference 1 5) sourceC2695) = raw37497 := by
      apply Matrix.ext; unfold tripleCharges sourceA2695 sourceB2695 sourceC2695 difference raw37497; decide +kernel
    rw [ha]
    exact (canonical37497 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2695 + difference 5 2) (sourceB2695 + difference 2 5) sourceC2695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 662) := by
    have ha : (tripleCharges (sourceA2695 + difference 5 2) (sourceB2695 + difference 2 5) sourceC2695) = raw37511 := by
      apply Matrix.ext; unfold tripleCharges sourceA2695 sourceB2695 sourceC2695 difference raw37511; decide +kernel
    rw [ha]
    exact (canonical37511 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2695 + difference 5 3) (sourceB2695 + difference 3 5) sourceC2695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 662) := by
    have ha : (tripleCharges (sourceA2695 + difference 5 3) (sourceB2695 + difference 3 5) sourceC2695) = raw37512 := by
      apply Matrix.ext; unfold tripleCharges sourceA2695 sourceB2695 sourceC2695 difference raw37512; decide +kernel
    rw [ha]
    exact (canonical37512 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2695 + difference 5 4) (sourceB2695 + difference 4 5) sourceC2695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 662) := by
    have ha : (tripleCharges (sourceA2695 + difference 5 4) (sourceB2695 + difference 4 5) sourceC2695) = raw37500 := by
      apply Matrix.ext; unfold tripleCharges sourceA2695 sourceB2695 sourceC2695 difference raw37500; decide +kernel
    rw [ha]
    exact (canonical37500 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2695 + difference 5 5) (sourceB2695 + difference 5 5) sourceC2695) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 674) := by
    have ha : (tripleCharges (sourceA2695 + difference 5 5) (sourceB2695 + difference 5 5) sourceC2695) = raw37493 := by
      apply Matrix.ext; unfold tripleCharges sourceA2695 sourceB2695 sourceC2695 difference raw37493; decide +kernel
    rw [ha]
    exact (canonical37493 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2695 + sourceB2695) sourceC2695) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (doubleCharges (sourceA2695 + sourceB2695) sourceC2695) = raw37482 := by
      apply Matrix.ext; unfold doubleCharges sourceA2695 sourceB2695 sourceC2695 raw37482; decide +kernel
    rw [ha]
    exact (canonical37482 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2695 sourceB2695 sourceC2695
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2695, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2696 : Charge := ![2, -1, -1, -1, 0, 1]
def sourceB2696 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC2696 : Charge := ![-5, 1, 1, 1, 1, 1]
def sourceForm2696 : Integer.Sparse Master := [(Sum.inr 1502, 2), (Sum.inr 1506, 4), (Sum.inr 4056, -1)]

theorem sourceEq2696 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2696 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2696 + difference 0 5) (sourceB2696 + difference 5 0) sourceC2696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA2696 + difference 0 5) (sourceB2696 + difference 5 0) sourceC2696) = raw37513 := by
      apply Matrix.ext; unfold tripleCharges sourceA2696 sourceB2696 sourceC2696 difference raw37513; decide +kernel
    rw [ha]
    exact (canonical37513 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2696 + difference 1 5) (sourceB2696 + difference 5 1) sourceC2696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA2696 + difference 1 5) (sourceB2696 + difference 5 1) sourceC2696) = raw37514 := by
      apply Matrix.ext; unfold tripleCharges sourceA2696 sourceB2696 sourceC2696 difference raw37514; decide +kernel
    rw [ha]
    exact (canonical37514 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2696 + difference 2 5) (sourceB2696 + difference 5 2) sourceC2696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA2696 + difference 2 5) (sourceB2696 + difference 5 2) sourceC2696) = raw37515 := by
      apply Matrix.ext; unfold tripleCharges sourceA2696 sourceB2696 sourceC2696 difference raw37515; decide +kernel
    rw [ha]
    exact (canonical37515 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2696 + difference 3 5) (sourceB2696 + difference 5 3) sourceC2696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA2696 + difference 3 5) (sourceB2696 + difference 5 3) sourceC2696) = raw37516 := by
      apply Matrix.ext; unfold tripleCharges sourceA2696 sourceB2696 sourceC2696 difference raw37516; decide +kernel
    rw [ha]
    exact (canonical37516 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2696 + difference 4 5) (sourceB2696 + difference 5 4) sourceC2696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1502) := by
    have ha : (tripleCharges (sourceA2696 + difference 4 5) (sourceB2696 + difference 5 4) sourceC2696) = raw37517 := by
      apply Matrix.ext; unfold tripleCharges sourceA2696 sourceB2696 sourceC2696 difference raw37517; decide +kernel
    rw [ha]
    exact (canonical37517 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2696 + difference 5 5) (sourceB2696 + difference 5 5) sourceC2696) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1502) := by
    have ha : (tripleCharges (sourceA2696 + difference 5 5) (sourceB2696 + difference 5 5) sourceC2696) = raw37518 := by
      apply Matrix.ext; unfold tripleCharges sourceA2696 sourceB2696 sourceC2696 difference raw37518; decide +kernel
    rw [ha]
    exact (canonical37518 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2696 + sourceB2696) sourceC2696) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4056) := by
    have ha : (doubleCharges (sourceA2696 + sourceB2696) sourceC2696) = raw37519 := by
      apply Matrix.ext; unfold doubleCharges sourceA2696 sourceB2696 sourceC2696 raw37519; decide +kernel
    rw [ha]
    exact (canonical37519 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2696 sourceB2696 sourceC2696
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2696, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2697 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2697 : Charge := ![3, -1, -1, -1, -1, 1]
def sourceC2697 : Charge := ![-5, 1, 1, 1, 1, 1]
def sourceForm2697 : Integer.Sparse Master := [(Sum.inr 666, 1), (Sum.inr 1497, 1), (Sum.inr 1506, 4), (Sum.inr 4056, -1)]

theorem sourceEq2697 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2697 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2697 + difference 5 0) (sourceB2697 + difference 0 5) sourceC2697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 666) := by
    have ha : (tripleCharges (sourceA2697 + difference 5 0) (sourceB2697 + difference 0 5) sourceC2697) = raw37520 := by
      apply Matrix.ext; unfold tripleCharges sourceA2697 sourceB2697 sourceC2697 difference raw37520; decide +kernel
    rw [ha]
    exact (canonical37520 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2697 + difference 5 1) (sourceB2697 + difference 1 5) sourceC2697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA2697 + difference 5 1) (sourceB2697 + difference 1 5) sourceC2697) = raw37521 := by
      apply Matrix.ext; unfold tripleCharges sourceA2697 sourceB2697 sourceC2697 difference raw37521; decide +kernel
    rw [ha]
    exact (canonical37521 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2697 + difference 5 2) (sourceB2697 + difference 2 5) sourceC2697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA2697 + difference 5 2) (sourceB2697 + difference 2 5) sourceC2697) = raw37522 := by
      apply Matrix.ext; unfold tripleCharges sourceA2697 sourceB2697 sourceC2697 difference raw37522; decide +kernel
    rw [ha]
    exact (canonical37522 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2697 + difference 5 3) (sourceB2697 + difference 3 5) sourceC2697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA2697 + difference 5 3) (sourceB2697 + difference 3 5) sourceC2697) = raw37523 := by
      apply Matrix.ext; unfold tripleCharges sourceA2697 sourceB2697 sourceC2697 difference raw37523; decide +kernel
    rw [ha]
    exact (canonical37523 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2697 + difference 5 4) (sourceB2697 + difference 4 5) sourceC2697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA2697 + difference 5 4) (sourceB2697 + difference 4 5) sourceC2697) = raw37524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2697 sourceB2697 sourceC2697 difference raw37524; decide +kernel
    rw [ha]
    exact (canonical37524 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2697 + difference 5 5) (sourceB2697 + difference 5 5) sourceC2697) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1497) := by
    have ha : (tripleCharges (sourceA2697 + difference 5 5) (sourceB2697 + difference 5 5) sourceC2697) = raw37525 := by
      apply Matrix.ext; unfold tripleCharges sourceA2697 sourceB2697 sourceC2697 difference raw37525; decide +kernel
    rw [ha]
    exact (canonical37525 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2697 + sourceB2697) sourceC2697) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4056) := by
    have ha : (doubleCharges (sourceA2697 + sourceB2697) sourceC2697) = raw37519 := by
      apply Matrix.ext; unfold doubleCharges sourceA2697 sourceB2697 sourceC2697 raw37519; decide +kernel
    rw [ha]
    exact (canonical37519 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2697 sourceB2697 sourceC2697
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2697, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2698 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2698 : Charge := ![3, -1, -1, -1, 0, 0]
def sourceC2698 : Charge := ![-5, 1, 1, 1, 1, 1]
def sourceForm2698 : Integer.Sparse Master := [(Sum.inr 658, 3), (Sum.inr 666, 2), (Sum.inr 1506, 1), (Sum.inr 4056, -1)]

theorem sourceEq2698 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2698 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2698 + difference 0 0) (sourceB2698 + difference 0 0) sourceC2698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1506) := by
    have ha : (tripleCharges (sourceA2698 + difference 0 0) (sourceB2698 + difference 0 0) sourceC2698) = raw37524 := by
      apply Matrix.ext; unfold tripleCharges sourceA2698 sourceB2698 sourceC2698 difference raw37524; decide +kernel
    rw [ha]
    exact (canonical37524 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2698 + difference 1 0) (sourceB2698 + difference 0 1) sourceC2698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 658) := by
    have ha : (tripleCharges (sourceA2698 + difference 1 0) (sourceB2698 + difference 0 1) sourceC2698) = raw37526 := by
      apply Matrix.ext; unfold tripleCharges sourceA2698 sourceB2698 sourceC2698 difference raw37526; decide +kernel
    rw [ha]
    exact (canonical37526 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2698 + difference 2 0) (sourceB2698 + difference 0 2) sourceC2698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 658) := by
    have ha : (tripleCharges (sourceA2698 + difference 2 0) (sourceB2698 + difference 0 2) sourceC2698) = raw37527 := by
      apply Matrix.ext; unfold tripleCharges sourceA2698 sourceB2698 sourceC2698 difference raw37527; decide +kernel
    rw [ha]
    exact (canonical37527 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2698 + difference 3 0) (sourceB2698 + difference 0 3) sourceC2698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 658) := by
    have ha : (tripleCharges (sourceA2698 + difference 3 0) (sourceB2698 + difference 0 3) sourceC2698) = raw37528 := by
      apply Matrix.ext; unfold tripleCharges sourceA2698 sourceB2698 sourceC2698 difference raw37528; decide +kernel
    rw [ha]
    exact (canonical37528 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2698 + difference 4 0) (sourceB2698 + difference 0 4) sourceC2698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 666) := by
    have ha : (tripleCharges (sourceA2698 + difference 4 0) (sourceB2698 + difference 0 4) sourceC2698) = raw37520 := by
      apply Matrix.ext; unfold tripleCharges sourceA2698 sourceB2698 sourceC2698 difference raw37520; decide +kernel
    rw [ha]
    exact (canonical37520 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2698 + difference 5 0) (sourceB2698 + difference 0 5) sourceC2698) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 666) := by
    have ha : (tripleCharges (sourceA2698 + difference 5 0) (sourceB2698 + difference 0 5) sourceC2698) = raw37529 := by
      apply Matrix.ext; unfold tripleCharges sourceA2698 sourceB2698 sourceC2698 difference raw37529; decide +kernel
    rw [ha]
    exact (canonical37529 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2698 + sourceB2698) sourceC2698) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4056) := by
    have ha : (doubleCharges (sourceA2698 + sourceB2698) sourceC2698) = raw37519 := by
      apply Matrix.ext; unfold doubleCharges sourceA2698 sourceB2698 sourceC2698 raw37519; decide +kernel
    rw [ha]
    exact (canonical37519 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2698 sourceB2698 sourceC2698
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2698, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2699 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceB2699 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2699 : Charge := ![-4, -1, 0, 0, 1, 4]
def sourceForm2699 : Integer.Sparse Master := [(Sum.inr 1688, 2), (Sum.inr 1692, 2), (Sum.inr 1695, 2), (Sum.inr 4066, -1)]

theorem sourceEq2699 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2699 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2699 + difference 0 4) (sourceB2699 + difference 4 0) sourceC2699) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA2699 + difference 0 4) (sourceB2699 + difference 4 0) sourceC2699) = raw37530 := by
      apply Matrix.ext; unfold tripleCharges sourceA2699 sourceB2699 sourceC2699 difference raw37530; decide +kernel
    rw [ha]
    exact (canonical37530 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2699 + difference 1 4) (sourceB2699 + difference 4 1) sourceC2699) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1695) := by
    have ha : (tripleCharges (sourceA2699 + difference 1 4) (sourceB2699 + difference 4 1) sourceC2699) = raw37531 := by
      apply Matrix.ext; unfold tripleCharges sourceA2699 sourceB2699 sourceC2699 difference raw37531; decide +kernel
    rw [ha]
    exact (canonical37531 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2699 + difference 2 4) (sourceB2699 + difference 4 2) sourceC2699) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1688) := by
    have ha : (tripleCharges (sourceA2699 + difference 2 4) (sourceB2699 + difference 4 2) sourceC2699) = raw37532 := by
      apply Matrix.ext; unfold tripleCharges sourceA2699 sourceB2699 sourceC2699 difference raw37532; decide +kernel
    rw [ha]
    exact (canonical37532 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2699 + difference 3 4) (sourceB2699 + difference 4 3) sourceC2699) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1688) := by
    have ha : (tripleCharges (sourceA2699 + difference 3 4) (sourceB2699 + difference 4 3) sourceC2699) = raw37533 := by
      apply Matrix.ext; unfold tripleCharges sourceA2699 sourceB2699 sourceC2699 difference raw37533; decide +kernel
    rw [ha]
    exact (canonical37533 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2699 + difference 4 4) (sourceB2699 + difference 4 4) sourceC2699) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1695) := by
    have ha : (tripleCharges (sourceA2699 + difference 4 4) (sourceB2699 + difference 4 4) sourceC2699) = raw37534 := by
      apply Matrix.ext; unfold tripleCharges sourceA2699 sourceB2699 sourceC2699 difference raw37534; decide +kernel
    rw [ha]
    exact (canonical37534 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2699 + difference 5 4) (sourceB2699 + difference 4 5) sourceC2699) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA2699 + difference 5 4) (sourceB2699 + difference 4 5) sourceC2699) = raw37535 := by
      apply Matrix.ext; unfold tripleCharges sourceA2699 sourceB2699 sourceC2699 difference raw37535; decide +kernel
    rw [ha]
    exact (canonical37535 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2699 + sourceB2699) sourceC2699) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (doubleCharges (sourceA2699 + sourceB2699) sourceC2699) = raw37536 := by
      apply Matrix.ext; unfold doubleCharges sourceA2699 sourceB2699 sourceC2699 raw37536; decide +kernel
    rw [ha]
    exact (canonical37536 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2699 sourceB2699 sourceC2699
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2699, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2700 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB2700 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC2700 : Charge := ![-4, -1, 0, 0, 1, 4]
def sourceForm2700 : Integer.Sparse Master := [(Sum.inr 1692, 2), (Sum.inr 3262, 2), (Sum.inr 3275, 2), (Sum.inr 4066, -1)]

theorem sourceEq2700 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2700 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2700 + difference 0 3) (sourceB2700 + difference 3 0) sourceC2700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA2700 + difference 0 3) (sourceB2700 + difference 3 0) sourceC2700) = raw37537 := by
      apply Matrix.ext; unfold tripleCharges sourceA2700 sourceB2700 sourceC2700 difference raw37537; decide +kernel
    rw [ha]
    exact (canonical37537 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2700 + difference 1 3) (sourceB2700 + difference 3 1) sourceC2700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3275) := by
    have ha : (tripleCharges (sourceA2700 + difference 1 3) (sourceB2700 + difference 3 1) sourceC2700) = raw37538 := by
      apply Matrix.ext; unfold tripleCharges sourceA2700 sourceB2700 sourceC2700 difference raw37538; decide +kernel
    rw [ha]
    exact (canonical37538 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2700 + difference 2 3) (sourceB2700 + difference 3 2) sourceC2700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3262) := by
    have ha : (tripleCharges (sourceA2700 + difference 2 3) (sourceB2700 + difference 3 2) sourceC2700) = raw37539 := by
      apply Matrix.ext; unfold tripleCharges sourceA2700 sourceB2700 sourceC2700 difference raw37539; decide +kernel
    rw [ha]
    exact (canonical37539 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2700 + difference 3 3) (sourceB2700 + difference 3 3) sourceC2700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3262) := by
    have ha : (tripleCharges (sourceA2700 + difference 3 3) (sourceB2700 + difference 3 3) sourceC2700) = raw37540 := by
      apply Matrix.ext; unfold tripleCharges sourceA2700 sourceB2700 sourceC2700 difference raw37540; decide +kernel
    rw [ha]
    exact (canonical37540 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2700 + difference 4 3) (sourceB2700 + difference 3 4) sourceC2700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3275) := by
    have ha : (tripleCharges (sourceA2700 + difference 4 3) (sourceB2700 + difference 3 4) sourceC2700) = raw37541 := by
      apply Matrix.ext; unfold tripleCharges sourceA2700 sourceB2700 sourceC2700 difference raw37541; decide +kernel
    rw [ha]
    exact (canonical37541 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2700 + difference 5 3) (sourceB2700 + difference 3 5) sourceC2700) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA2700 + difference 5 3) (sourceB2700 + difference 3 5) sourceC2700) = raw37542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2700 sourceB2700 sourceC2700 difference raw37542; decide +kernel
    rw [ha]
    exact (canonical37542 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2700 + sourceB2700) sourceC2700) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (doubleCharges (sourceA2700 + sourceB2700) sourceC2700) = raw37536 := by
      apply Matrix.ext; unfold doubleCharges sourceA2700 sourceB2700 sourceC2700 raw37536; decide +kernel
    rw [ha]
    exact (canonical37536 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2700 sourceB2700 sourceC2700
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2700, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2701 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2701 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC2701 : Charge := ![-4, -1, 0, 0, 1, 4]
def sourceForm2701 : Integer.Sparse Master := [(Sum.inr 770, 1), (Sum.inr 1555, 2), (Sum.inr 1574, 1), (Sum.inr 1677, 1), (Sum.inr 1692, 1), (Sum.inr 4066, -1)]

theorem sourceEq2701 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2701 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2701 + difference 0 0) (sourceB2701 + difference 0 0) sourceC2701) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA2701 + difference 0 0) (sourceB2701 + difference 0 0) sourceC2701) = raw37542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2701 sourceB2701 sourceC2701 difference raw37542; decide +kernel
    rw [ha]
    exact (canonical37542 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2701 + difference 1 0) (sourceB2701 + difference 0 1) sourceC2701) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1677) := by
    have ha : (tripleCharges (sourceA2701 + difference 1 0) (sourceB2701 + difference 0 1) sourceC2701) = raw37543 := by
      apply Matrix.ext; unfold tripleCharges sourceA2701 sourceB2701 sourceC2701 difference raw37543; decide +kernel
    rw [ha]
    exact (canonical37543 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2701 + difference 2 0) (sourceB2701 + difference 0 2) sourceC2701) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1555) := by
    have ha : (tripleCharges (sourceA2701 + difference 2 0) (sourceB2701 + difference 0 2) sourceC2701) = raw37544 := by
      apply Matrix.ext; unfold tripleCharges sourceA2701 sourceB2701 sourceC2701 difference raw37544; decide +kernel
    rw [ha]
    exact (canonical37544 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2701 + difference 3 0) (sourceB2701 + difference 0 3) sourceC2701) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1555) := by
    have ha : (tripleCharges (sourceA2701 + difference 3 0) (sourceB2701 + difference 0 3) sourceC2701) = raw37545 := by
      apply Matrix.ext; unfold tripleCharges sourceA2701 sourceB2701 sourceC2701 difference raw37545; decide +kernel
    rw [ha]
    exact (canonical37545 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2701 + difference 4 0) (sourceB2701 + difference 0 4) sourceC2701) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1574) := by
    have ha : (tripleCharges (sourceA2701 + difference 4 0) (sourceB2701 + difference 0 4) sourceC2701) = raw37546 := by
      apply Matrix.ext; unfold tripleCharges sourceA2701 sourceB2701 sourceC2701 difference raw37546; decide +kernel
    rw [ha]
    exact (canonical37546 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2701 + difference 5 0) (sourceB2701 + difference 0 5) sourceC2701) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 770) := by
    have ha : (tripleCharges (sourceA2701 + difference 5 0) (sourceB2701 + difference 0 5) sourceC2701) = raw37547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2701 sourceB2701 sourceC2701 difference raw37547; decide +kernel
    rw [ha]
    exact (canonical37547 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2701 + sourceB2701) sourceC2701) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (doubleCharges (sourceA2701 + sourceB2701) sourceC2701) = raw37536 := by
      apply Matrix.ext; unfold doubleCharges sourceA2701 sourceB2701 sourceC2701 raw37536; decide +kernel
    rw [ha]
    exact (canonical37536 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2701 sourceB2701 sourceC2701
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2701, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2702 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2702 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC2702 : Charge := ![-4, -1, 0, 0, 1, 4]
def sourceForm2702 : Integer.Sparse Master := [(Sum.inr 762, 2), (Sum.inr 770, 1), (Sum.inr 774, 1), (Sum.inr 842, 1), (Sum.inr 1692, 1), (Sum.inr 4066, -1)]

theorem sourceEq2702 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2702 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2702 + difference 5 0) (sourceB2702 + difference 0 5) sourceC2702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 770) := by
    have ha : (tripleCharges (sourceA2702 + difference 5 0) (sourceB2702 + difference 0 5) sourceC2702) = raw37547 := by
      apply Matrix.ext; unfold tripleCharges sourceA2702 sourceB2702 sourceC2702 difference raw37547; decide +kernel
    rw [ha]
    exact (canonical37547 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2702 + difference 5 1) (sourceB2702 + difference 1 5) sourceC2702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 774) := by
    have ha : (tripleCharges (sourceA2702 + difference 5 1) (sourceB2702 + difference 1 5) sourceC2702) = raw37548 := by
      apply Matrix.ext; unfold tripleCharges sourceA2702 sourceB2702 sourceC2702 difference raw37548; decide +kernel
    rw [ha]
    exact (canonical37548 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2702 + difference 5 2) (sourceB2702 + difference 2 5) sourceC2702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 762) := by
    have ha : (tripleCharges (sourceA2702 + difference 5 2) (sourceB2702 + difference 2 5) sourceC2702) = raw37549 := by
      apply Matrix.ext; unfold tripleCharges sourceA2702 sourceB2702 sourceC2702 difference raw37549; decide +kernel
    rw [ha]
    exact (canonical37549 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2702 + difference 5 3) (sourceB2702 + difference 3 5) sourceC2702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 762) := by
    have ha : (tripleCharges (sourceA2702 + difference 5 3) (sourceB2702 + difference 3 5) sourceC2702) = raw37550 := by
      apply Matrix.ext; unfold tripleCharges sourceA2702 sourceB2702 sourceC2702 difference raw37550; decide +kernel
    rw [ha]
    exact (canonical37550 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2702 + difference 5 4) (sourceB2702 + difference 4 5) sourceC2702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 842) := by
    have ha : (tripleCharges (sourceA2702 + difference 5 4) (sourceB2702 + difference 4 5) sourceC2702) = raw37551 := by
      apply Matrix.ext; unfold tripleCharges sourceA2702 sourceB2702 sourceC2702 difference raw37551; decide +kernel
    rw [ha]
    exact (canonical37551 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2702 + difference 5 5) (sourceB2702 + difference 5 5) sourceC2702) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1692) := by
    have ha : (tripleCharges (sourceA2702 + difference 5 5) (sourceB2702 + difference 5 5) sourceC2702) = raw37542 := by
      apply Matrix.ext; unfold tripleCharges sourceA2702 sourceB2702 sourceC2702 difference raw37542; decide +kernel
    rw [ha]
    exact (canonical37542 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2702 + sourceB2702) sourceC2702) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4066) := by
    have ha : (doubleCharges (sourceA2702 + sourceB2702) sourceC2702) = raw37536 := by
      apply Matrix.ext; unfold doubleCharges sourceA2702 sourceB2702 sourceC2702 raw37536; decide +kernel
    rw [ha]
    exact (canonical37536 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2702 sourceB2702 sourceC2702
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2702, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2703 : Charge := ![1, 1, 0, 0, 1, -3]
def sourceB2703 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC2703 : Charge := ![-4, -1, 0, 0, 2, 3]
def sourceForm2703 : Integer.Sparse Master := [(Sum.inr 1685, 2), (Sum.inr 1687, 1), (Sum.inr 1694, 1), (Sum.inr 1743, 1), (Sum.inr 2167, 1), (Sum.inr 4067, -1)]

theorem sourceEq2703 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2703 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2703 + difference 0 4) (sourceB2703 + difference 4 0) sourceC2703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2167) := by
    have ha : (tripleCharges (sourceA2703 + difference 0 4) (sourceB2703 + difference 4 0) sourceC2703) = raw37552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2703 sourceB2703 sourceC2703 difference raw37552; decide +kernel
    rw [ha]
    exact (canonical37552 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2703 + difference 1 4) (sourceB2703 + difference 4 1) sourceC2703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1743) := by
    have ha : (tripleCharges (sourceA2703 + difference 1 4) (sourceB2703 + difference 4 1) sourceC2703) = raw37553 := by
      apply Matrix.ext; unfold tripleCharges sourceA2703 sourceB2703 sourceC2703 difference raw37553; decide +kernel
    rw [ha]
    exact (canonical37553 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2703 + difference 2 4) (sourceB2703 + difference 4 2) sourceC2703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1685) := by
    have ha : (tripleCharges (sourceA2703 + difference 2 4) (sourceB2703 + difference 4 2) sourceC2703) = raw37554 := by
      apply Matrix.ext; unfold tripleCharges sourceA2703 sourceB2703 sourceC2703 difference raw37554; decide +kernel
    rw [ha]
    exact (canonical37554 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2703 + difference 3 4) (sourceB2703 + difference 4 3) sourceC2703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1685) := by
    have ha : (tripleCharges (sourceA2703 + difference 3 4) (sourceB2703 + difference 4 3) sourceC2703) = raw37555 := by
      apply Matrix.ext; unfold tripleCharges sourceA2703 sourceB2703 sourceC2703 difference raw37555; decide +kernel
    rw [ha]
    exact (canonical37555 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2703 + difference 4 4) (sourceB2703 + difference 4 4) sourceC2703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1687) := by
    have ha : (tripleCharges (sourceA2703 + difference 4 4) (sourceB2703 + difference 4 4) sourceC2703) = raw37556 := by
      apply Matrix.ext; unfold tripleCharges sourceA2703 sourceB2703 sourceC2703 difference raw37556; decide +kernel
    rw [ha]
    exact (canonical37556 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2703 + difference 5 4) (sourceB2703 + difference 4 5) sourceC2703) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA2703 + difference 5 4) (sourceB2703 + difference 4 5) sourceC2703) = raw37557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2703 sourceB2703 sourceC2703 difference raw37557; decide +kernel
    rw [ha]
    exact (canonical37557 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2703 + sourceB2703) sourceC2703) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2703 + sourceB2703) sourceC2703) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2703 sourceB2703 sourceC2703 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2703 sourceB2703 sourceC2703
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2703, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2704 : Charge := ![1, 1, 0, 1, -2, -1]
def sourceB2704 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceC2704 : Charge := ![-4, -1, 0, 0, 2, 3]
def sourceForm2704 : Integer.Sparse Master := [(Sum.inr 1679, 2), (Sum.inr 1683, 1), (Sum.inr 1693, 1), (Sum.inr 1735, 1), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

theorem sourceEq2704 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2704 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2704 + difference 0 3) (sourceB2704 + difference 3 0) sourceC2704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3277) := by
    have ha : (tripleCharges (sourceA2704 + difference 0 3) (sourceB2704 + difference 3 0) sourceC2704) = raw37559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2704 sourceB2704 sourceC2704 difference raw37559; decide +kernel
    rw [ha]
    exact (canonical37559 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2704 + difference 1 3) (sourceB2704 + difference 3 1) sourceC2704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1735) := by
    have ha : (tripleCharges (sourceA2704 + difference 1 3) (sourceB2704 + difference 3 1) sourceC2704) = raw37560 := by
      apply Matrix.ext; unfold tripleCharges sourceA2704 sourceB2704 sourceC2704 difference raw37560; decide +kernel
    rw [ha]
    exact (canonical37560 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2704 + difference 2 3) (sourceB2704 + difference 3 2) sourceC2704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1679) := by
    have ha : (tripleCharges (sourceA2704 + difference 2 3) (sourceB2704 + difference 3 2) sourceC2704) = raw37561 := by
      apply Matrix.ext; unfold tripleCharges sourceA2704 sourceB2704 sourceC2704 difference raw37561; decide +kernel
    rw [ha]
    exact (canonical37561 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2704 + difference 3 3) (sourceB2704 + difference 3 3) sourceC2704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1679) := by
    have ha : (tripleCharges (sourceA2704 + difference 3 3) (sourceB2704 + difference 3 3) sourceC2704) = raw37562 := by
      apply Matrix.ext; unfold tripleCharges sourceA2704 sourceB2704 sourceC2704 difference raw37562; decide +kernel
    rw [ha]
    exact (canonical37562 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2704 + difference 4 3) (sourceB2704 + difference 3 4) sourceC2704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA2704 + difference 4 3) (sourceB2704 + difference 3 4) sourceC2704) = raw37563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2704 sourceB2704 sourceC2704 difference raw37563; decide +kernel
    rw [ha]
    exact (canonical37563 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2704 + difference 5 3) (sourceB2704 + difference 3 5) sourceC2704) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA2704 + difference 5 3) (sourceB2704 + difference 3 5) sourceC2704) = raw37564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2704 sourceB2704 sourceC2704 difference raw37564; decide +kernel
    rw [ha]
    exact (canonical37564 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2704 + sourceB2704) sourceC2704) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2704 + sourceB2704) sourceC2704) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2704 sourceB2704 sourceC2704 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2704 sourceB2704 sourceC2704
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2704, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2705 : Charge := ![1, 1, 0, 1, -1, -2]
def sourceB2705 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC2705 : Charge := ![-4, -1, 0, 0, 2, 3]
def sourceForm2705 : Integer.Sparse Master := [(Sum.inr 1689, 2), (Sum.inr 1693, 1), (Sum.inr 1694, 1), (Sum.inr 1748, 1), (Sum.inr 3276, 1), (Sum.inr 4067, -1)]

theorem sourceEq2705 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2705 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2705 + difference 0 3) (sourceB2705 + difference 3 0) sourceC2705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA2705 + difference 0 3) (sourceB2705 + difference 3 0) sourceC2705) = raw37565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2705 sourceB2705 sourceC2705 difference raw37565; decide +kernel
    rw [ha]
    exact (canonical37565 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2705 + difference 1 3) (sourceB2705 + difference 3 1) sourceC2705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1748) := by
    have ha : (tripleCharges (sourceA2705 + difference 1 3) (sourceB2705 + difference 3 1) sourceC2705) = raw37566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2705 sourceB2705 sourceC2705 difference raw37566; decide +kernel
    rw [ha]
    exact (canonical37566 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2705 + difference 2 3) (sourceB2705 + difference 3 2) sourceC2705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA2705 + difference 2 3) (sourceB2705 + difference 3 2) sourceC2705) = raw37567 := by
      apply Matrix.ext; unfold tripleCharges sourceA2705 sourceB2705 sourceC2705 difference raw37567; decide +kernel
    rw [ha]
    exact (canonical37567 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2705 + difference 3 3) (sourceB2705 + difference 3 3) sourceC2705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1689) := by
    have ha : (tripleCharges (sourceA2705 + difference 3 3) (sourceB2705 + difference 3 3) sourceC2705) = raw37568 := by
      apply Matrix.ext; unfold tripleCharges sourceA2705 sourceB2705 sourceC2705 difference raw37568; decide +kernel
    rw [ha]
    exact (canonical37568 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2705 + difference 4 3) (sourceB2705 + difference 3 4) sourceC2705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA2705 + difference 4 3) (sourceB2705 + difference 3 4) sourceC2705) = raw37557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2705 sourceB2705 sourceC2705 difference raw37557; decide +kernel
    rw [ha]
    exact (canonical37557 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2705 + difference 5 3) (sourceB2705 + difference 3 5) sourceC2705) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA2705 + difference 5 3) (sourceB2705 + difference 3 5) sourceC2705) = raw37563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2705 sourceB2705 sourceC2705 difference raw37563; decide +kernel
    rw [ha]
    exact (canonical37563 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2705 + sourceB2705) sourceC2705) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2705 + sourceB2705) sourceC2705) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2705 sourceB2705 sourceC2705 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2705 sourceB2705 sourceC2705
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2705, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2706 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2706 : Charge := ![2, 1, 0, 0, -3, 0]
def sourceC2706 : Charge := ![-4, -1, 0, 0, 2, 3]
def sourceForm2706 : Integer.Sparse Master := [(Sum.inr 1683, 1), (Sum.inr 2149, 2), (Sum.inr 2167, 1), (Sum.inr 2258, 1), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

theorem sourceEq2706 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2706 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2706 + difference 0 4) (sourceB2706 + difference 4 0) sourceC2706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA2706 + difference 0 4) (sourceB2706 + difference 4 0) sourceC2706) = raw37569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2706 sourceB2706 sourceC2706 difference raw37569; decide +kernel
    rw [ha]
    exact (canonical37569 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2706 + difference 1 4) (sourceB2706 + difference 4 1) sourceC2706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2167) := by
    have ha : (tripleCharges (sourceA2706 + difference 1 4) (sourceB2706 + difference 4 1) sourceC2706) = raw37552 := by
      apply Matrix.ext; unfold tripleCharges sourceA2706 sourceB2706 sourceC2706 difference raw37552; decide +kernel
    rw [ha]
    exact (canonical37552 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2706 + difference 2 4) (sourceB2706 + difference 4 2) sourceC2706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2149) := by
    have ha : (tripleCharges (sourceA2706 + difference 2 4) (sourceB2706 + difference 4 2) sourceC2706) = raw37570 := by
      apply Matrix.ext; unfold tripleCharges sourceA2706 sourceB2706 sourceC2706 difference raw37570; decide +kernel
    rw [ha]
    exact (canonical37570 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2706 + difference 3 4) (sourceB2706 + difference 4 3) sourceC2706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2149) := by
    have ha : (tripleCharges (sourceA2706 + difference 3 4) (sourceB2706 + difference 4 3) sourceC2706) = raw37571 := by
      apply Matrix.ext; unfold tripleCharges sourceA2706 sourceB2706 sourceC2706 difference raw37571; decide +kernel
    rw [ha]
    exact (canonical37571 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2706 + difference 4 4) (sourceB2706 + difference 4 4) sourceC2706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2258) := by
    have ha : (tripleCharges (sourceA2706 + difference 4 4) (sourceB2706 + difference 4 4) sourceC2706) = raw37572 := by
      apply Matrix.ext; unfold tripleCharges sourceA2706 sourceB2706 sourceC2706 difference raw37572; decide +kernel
    rw [ha]
    exact (canonical37572 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2706 + difference 5 4) (sourceB2706 + difference 4 5) sourceC2706) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3277) := by
    have ha : (tripleCharges (sourceA2706 + difference 5 4) (sourceB2706 + difference 4 5) sourceC2706) = raw37573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2706 sourceB2706 sourceC2706 difference raw37573; decide +kernel
    rw [ha]
    exact (canonical37573 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2706 + sourceB2706) sourceC2706) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2706 + sourceB2706) sourceC2706) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2706 sourceB2706 sourceC2706 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2706 sourceB2706 sourceC2706
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2706, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2707 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB2707 : Charge := ![2, 1, 0, -1, 0, -2]
def sourceC2707 : Charge := ![-4, -1, 0, 0, 2, 3]
def sourceForm2707 : Integer.Sparse Master := [(Sum.inr 1694, 1), (Sum.inr 2167, 1), (Sum.inr 3268, 2), (Sum.inr 3276, 1), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

theorem sourceEq2707 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2707 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2707 + difference 0 3) (sourceB2707 + difference 3 0) sourceC2707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA2707 + difference 0 3) (sourceB2707 + difference 3 0) sourceC2707) = raw37574 := by
      apply Matrix.ext; unfold tripleCharges sourceA2707 sourceB2707 sourceC2707 difference raw37574; decide +kernel
    rw [ha]
    exact (canonical37574 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2707 + difference 1 3) (sourceB2707 + difference 3 1) sourceC2707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3277) := by
    have ha : (tripleCharges (sourceA2707 + difference 1 3) (sourceB2707 + difference 3 1) sourceC2707) = raw37559 := by
      apply Matrix.ext; unfold tripleCharges sourceA2707 sourceB2707 sourceC2707 difference raw37559; decide +kernel
    rw [ha]
    exact (canonical37559 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2707 + difference 2 3) (sourceB2707 + difference 3 2) sourceC2707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3268) := by
    have ha : (tripleCharges (sourceA2707 + difference 2 3) (sourceB2707 + difference 3 2) sourceC2707) = raw37575 := by
      apply Matrix.ext; unfold tripleCharges sourceA2707 sourceB2707 sourceC2707 difference raw37575; decide +kernel
    rw [ha]
    exact (canonical37575 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2707 + difference 3 3) (sourceB2707 + difference 3 3) sourceC2707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3268) := by
    have ha : (tripleCharges (sourceA2707 + difference 3 3) (sourceB2707 + difference 3 3) sourceC2707) = raw37576 := by
      apply Matrix.ext; unfold tripleCharges sourceA2707 sourceB2707 sourceC2707 difference raw37576; decide +kernel
    rw [ha]
    exact (canonical37576 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2707 + difference 4 3) (sourceB2707 + difference 3 4) sourceC2707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA2707 + difference 4 3) (sourceB2707 + difference 3 4) sourceC2707) = raw37577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2707 sourceB2707 sourceC2707 difference raw37577; decide +kernel
    rw [ha]
    exact (canonical37577 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2707 + difference 5 3) (sourceB2707 + difference 3 5) sourceC2707) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2167) := by
    have ha : (tripleCharges (sourceA2707 + difference 5 3) (sourceB2707 + difference 3 5) sourceC2707) = raw37578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2707 sourceB2707 sourceC2707 difference raw37578; decide +kernel
    rw [ha]
    exact (canonical37578 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2707 + sourceB2707) sourceC2707) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2707 + sourceB2707) sourceC2707) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2707 sourceB2707 sourceC2707 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2707 sourceB2707 sourceC2707
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2707, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2708 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB2708 : Charge := ![2, 1, 0, -1, -1, -1]
def sourceC2708 : Charge := ![-4, -1, 0, 0, 2, 3]
def sourceForm2708 : Integer.Sparse Master := [(Sum.inr 1693, 1), (Sum.inr 3272, 2), (Sum.inr 3276, 2), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

theorem sourceEq2708 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2708 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2708 + difference 0 3) (sourceB2708 + difference 3 0) sourceC2708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA2708 + difference 0 3) (sourceB2708 + difference 3 0) sourceC2708) = raw37579 := by
      apply Matrix.ext; unfold tripleCharges sourceA2708 sourceB2708 sourceC2708 difference raw37579; decide +kernel
    rw [ha]
    exact (canonical37579 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2708 + difference 1 3) (sourceB2708 + difference 3 1) sourceC2708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA2708 + difference 1 3) (sourceB2708 + difference 3 1) sourceC2708) = raw37565 := by
      apply Matrix.ext; unfold tripleCharges sourceA2708 sourceB2708 sourceC2708 difference raw37565; decide +kernel
    rw [ha]
    exact (canonical37565 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2708 + difference 2 3) (sourceB2708 + difference 3 2) sourceC2708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA2708 + difference 2 3) (sourceB2708 + difference 3 2) sourceC2708) = raw37580 := by
      apply Matrix.ext; unfold tripleCharges sourceA2708 sourceB2708 sourceC2708 difference raw37580; decide +kernel
    rw [ha]
    exact (canonical37580 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2708 + difference 3 3) (sourceB2708 + difference 3 3) sourceC2708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3272) := by
    have ha : (tripleCharges (sourceA2708 + difference 3 3) (sourceB2708 + difference 3 3) sourceC2708) = raw37581 := by
      apply Matrix.ext; unfold tripleCharges sourceA2708 sourceB2708 sourceC2708 difference raw37581; decide +kernel
    rw [ha]
    exact (canonical37581 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2708 + difference 4 3) (sourceB2708 + difference 3 4) sourceC2708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3277) := by
    have ha : (tripleCharges (sourceA2708 + difference 4 3) (sourceB2708 + difference 3 4) sourceC2708) = raw37573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2708 sourceB2708 sourceC2708 difference raw37573; decide +kernel
    rw [ha]
    exact (canonical37573 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2708 + difference 5 3) (sourceB2708 + difference 3 5) sourceC2708) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA2708 + difference 5 3) (sourceB2708 + difference 3 5) sourceC2708) = raw37577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2708 sourceB2708 sourceC2708 difference raw37577; decide +kernel
    rw [ha]
    exact (canonical37577 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2708 + sourceB2708) sourceC2708) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2708 + sourceB2708) sourceC2708) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2708 sourceB2708 sourceC2708 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2708 sourceB2708 sourceC2708
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2708, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2709 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2709 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC2709 : Charge := ![-4, -1, 0, 0, 2, 3]
def sourceForm2709 : Integer.Sparse Master := [(Sum.inr 1570, 2), (Sum.inr 1577, 1), (Sum.inr 1579, 1), (Sum.inr 1694, 1), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

theorem sourceEq2709 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2709 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2709 + difference 0 0) (sourceB2709 + difference 0 0) sourceC2709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3277) := by
    have ha : (tripleCharges (sourceA2709 + difference 0 0) (sourceB2709 + difference 0 0) sourceC2709) = raw37573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2709 sourceB2709 sourceC2709 difference raw37573; decide +kernel
    rw [ha]
    exact (canonical37573 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2709 + difference 1 0) (sourceB2709 + difference 0 1) sourceC2709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA2709 + difference 1 0) (sourceB2709 + difference 0 1) sourceC2709) = raw37557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2709 sourceB2709 sourceC2709 difference raw37557; decide +kernel
    rw [ha]
    exact (canonical37557 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2709 + difference 2 0) (sourceB2709 + difference 0 2) sourceC2709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1570) := by
    have ha : (tripleCharges (sourceA2709 + difference 2 0) (sourceB2709 + difference 0 2) sourceC2709) = raw37582 := by
      apply Matrix.ext; unfold tripleCharges sourceA2709 sourceB2709 sourceC2709 difference raw37582; decide +kernel
    rw [ha]
    exact (canonical37582 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2709 + difference 3 0) (sourceB2709 + difference 0 3) sourceC2709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1570) := by
    have ha : (tripleCharges (sourceA2709 + difference 3 0) (sourceB2709 + difference 0 3) sourceC2709) = raw37583 := by
      apply Matrix.ext; unfold tripleCharges sourceA2709 sourceB2709 sourceC2709 difference raw37583; decide +kernel
    rw [ha]
    exact (canonical37583 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2709 + difference 4 0) (sourceB2709 + difference 0 4) sourceC2709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1577) := by
    have ha : (tripleCharges (sourceA2709 + difference 4 0) (sourceB2709 + difference 0 4) sourceC2709) = raw37584 := by
      apply Matrix.ext; unfold tripleCharges sourceA2709 sourceB2709 sourceC2709 difference raw37584; decide +kernel
    rw [ha]
    exact (canonical37584 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2709 + difference 5 0) (sourceB2709 + difference 0 5) sourceC2709) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1579) := by
    have ha : (tripleCharges (sourceA2709 + difference 5 0) (sourceB2709 + difference 0 5) sourceC2709) = raw37585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2709 sourceB2709 sourceC2709 difference raw37585; decide +kernel
    rw [ha]
    exact (canonical37585 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2709 + sourceB2709) sourceC2709) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2709 + sourceB2709) sourceC2709) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2709 sourceB2709 sourceC2709 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2709 sourceB2709 sourceC2709
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2709, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2710 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2710 : Charge := ![2, 1, 0, 0, -2, -1]
def sourceC2710 : Charge := ![-4, -1, 0, 0, 2, 3]
def sourceForm2710 : Integer.Sparse Master := [(Sum.inr 1579, 1), (Sum.inr 3237, 1), (Sum.inr 3252, 2), (Sum.inr 3276, 1), (Sum.inr 3277, 1), (Sum.inr 4067, -1)]

theorem sourceEq2710 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2710 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2710 + difference 5 0) (sourceB2710 + difference 0 5) sourceC2710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1579) := by
    have ha : (tripleCharges (sourceA2710 + difference 5 0) (sourceB2710 + difference 0 5) sourceC2710) = raw37585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2710 sourceB2710 sourceC2710 difference raw37585; decide +kernel
    rw [ha]
    exact (canonical37585 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2710 + difference 5 1) (sourceB2710 + difference 1 5) sourceC2710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3237) := by
    have ha : (tripleCharges (sourceA2710 + difference 5 1) (sourceB2710 + difference 1 5) sourceC2710) = raw37586 := by
      apply Matrix.ext; unfold tripleCharges sourceA2710 sourceB2710 sourceC2710 difference raw37586; decide +kernel
    rw [ha]
    exact (canonical37586 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2710 + difference 5 2) (sourceB2710 + difference 2 5) sourceC2710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3252) := by
    have ha : (tripleCharges (sourceA2710 + difference 5 2) (sourceB2710 + difference 2 5) sourceC2710) = raw37587 := by
      apply Matrix.ext; unfold tripleCharges sourceA2710 sourceB2710 sourceC2710 difference raw37587; decide +kernel
    rw [ha]
    exact (canonical37587 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2710 + difference 5 3) (sourceB2710 + difference 3 5) sourceC2710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3252) := by
    have ha : (tripleCharges (sourceA2710 + difference 5 3) (sourceB2710 + difference 3 5) sourceC2710) = raw37588 := by
      apply Matrix.ext; unfold tripleCharges sourceA2710 sourceB2710 sourceC2710 difference raw37588; decide +kernel
    rw [ha]
    exact (canonical37588 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2710 + difference 5 4) (sourceB2710 + difference 4 5) sourceC2710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA2710 + difference 5 4) (sourceB2710 + difference 4 5) sourceC2710) = raw37577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2710 sourceB2710 sourceC2710 difference raw37577; decide +kernel
    rw [ha]
    exact (canonical37577 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2710 + difference 5 5) (sourceB2710 + difference 5 5) sourceC2710) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3277) := by
    have ha : (tripleCharges (sourceA2710 + difference 5 5) (sourceB2710 + difference 5 5) sourceC2710) = raw37573 := by
      apply Matrix.ext; unfold tripleCharges sourceA2710 sourceB2710 sourceC2710 difference raw37573; decide +kernel
    rw [ha]
    exact (canonical37573 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2710 + sourceB2710) sourceC2710) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2710 + sourceB2710) sourceC2710) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2710 sourceB2710 sourceC2710 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2710 sourceB2710 sourceC2710
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2710, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2711 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2711 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC2711 : Charge := ![-4, -1, 0, 0, 2, 3]
def sourceForm2711 : Integer.Sparse Master := [(Sum.inr 1569, 2), (Sum.inr 1576, 1), (Sum.inr 1579, 1), (Sum.inr 1693, 1), (Sum.inr 3276, 1), (Sum.inr 4067, -1)]

theorem sourceEq2711 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2711 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2711 + difference 0 0) (sourceB2711 + difference 0 0) sourceC2711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA2711 + difference 0 0) (sourceB2711 + difference 0 0) sourceC2711) = raw37577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2711 sourceB2711 sourceC2711 difference raw37577; decide +kernel
    rw [ha]
    exact (canonical37577 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2711 + difference 1 0) (sourceB2711 + difference 0 1) sourceC2711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA2711 + difference 1 0) (sourceB2711 + difference 0 1) sourceC2711) = raw37563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2711 sourceB2711 sourceC2711 difference raw37563; decide +kernel
    rw [ha]
    exact (canonical37563 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2711 + difference 2 0) (sourceB2711 + difference 0 2) sourceC2711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1569) := by
    have ha : (tripleCharges (sourceA2711 + difference 2 0) (sourceB2711 + difference 0 2) sourceC2711) = raw37589 := by
      apply Matrix.ext; unfold tripleCharges sourceA2711 sourceB2711 sourceC2711 difference raw37589; decide +kernel
    rw [ha]
    exact (canonical37589 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2711 + difference 3 0) (sourceB2711 + difference 0 3) sourceC2711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1569) := by
    have ha : (tripleCharges (sourceA2711 + difference 3 0) (sourceB2711 + difference 0 3) sourceC2711) = raw37590 := by
      apply Matrix.ext; unfold tripleCharges sourceA2711 sourceB2711 sourceC2711 difference raw37590; decide +kernel
    rw [ha]
    exact (canonical37590 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2711 + difference 4 0) (sourceB2711 + difference 0 4) sourceC2711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1579) := by
    have ha : (tripleCharges (sourceA2711 + difference 4 0) (sourceB2711 + difference 0 4) sourceC2711) = raw37585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2711 sourceB2711 sourceC2711 difference raw37585; decide +kernel
    rw [ha]
    exact (canonical37585 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2711 + difference 5 0) (sourceB2711 + difference 0 5) sourceC2711) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1576) := by
    have ha : (tripleCharges (sourceA2711 + difference 5 0) (sourceB2711 + difference 0 5) sourceC2711) = raw37591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2711 sourceB2711 sourceC2711 difference raw37591; decide +kernel
    rw [ha]
    exact (canonical37591 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2711 + sourceB2711) sourceC2711) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2711 + sourceB2711) sourceC2711) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2711 sourceB2711 sourceC2711 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2711 sourceB2711 sourceC2711
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2711, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2712 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2712 : Charge := ![2, 1, 0, 0, -1, -2]
def sourceC2712 : Charge := ![-4, -1, 0, 0, 2, 3]
def sourceForm2712 : Integer.Sparse Master := [(Sum.inr 1576, 1), (Sum.inr 1849, 2), (Sum.inr 1858, 1), (Sum.inr 2167, 1), (Sum.inr 3276, 1), (Sum.inr 4067, -1)]

theorem sourceEq2712 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2712 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2712 + difference 5 0) (sourceB2712 + difference 0 5) sourceC2712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1576) := by
    have ha : (tripleCharges (sourceA2712 + difference 5 0) (sourceB2712 + difference 0 5) sourceC2712) = raw37591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2712 sourceB2712 sourceC2712 difference raw37591; decide +kernel
    rw [ha]
    exact (canonical37591 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2712 + difference 5 1) (sourceB2712 + difference 1 5) sourceC2712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1858) := by
    have ha : (tripleCharges (sourceA2712 + difference 5 1) (sourceB2712 + difference 1 5) sourceC2712) = raw37592 := by
      apply Matrix.ext; unfold tripleCharges sourceA2712 sourceB2712 sourceC2712 difference raw37592; decide +kernel
    rw [ha]
    exact (canonical37592 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2712 + difference 5 2) (sourceB2712 + difference 2 5) sourceC2712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1849) := by
    have ha : (tripleCharges (sourceA2712 + difference 5 2) (sourceB2712 + difference 2 5) sourceC2712) = raw37593 := by
      apply Matrix.ext; unfold tripleCharges sourceA2712 sourceB2712 sourceC2712 difference raw37593; decide +kernel
    rw [ha]
    exact (canonical37593 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2712 + difference 5 3) (sourceB2712 + difference 3 5) sourceC2712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1849) := by
    have ha : (tripleCharges (sourceA2712 + difference 5 3) (sourceB2712 + difference 3 5) sourceC2712) = raw37594 := by
      apply Matrix.ext; unfold tripleCharges sourceA2712 sourceB2712 sourceC2712 difference raw37594; decide +kernel
    rw [ha]
    exact (canonical37594 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2712 + difference 5 4) (sourceB2712 + difference 4 5) sourceC2712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2167) := by
    have ha : (tripleCharges (sourceA2712 + difference 5 4) (sourceB2712 + difference 4 5) sourceC2712) = raw37578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2712 sourceB2712 sourceC2712 difference raw37578; decide +kernel
    rw [ha]
    exact (canonical37578 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2712 + difference 5 5) (sourceB2712 + difference 5 5) sourceC2712) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3276) := by
    have ha : (tripleCharges (sourceA2712 + difference 5 5) (sourceB2712 + difference 5 5) sourceC2712) = raw37577 := by
      apply Matrix.ext; unfold tripleCharges sourceA2712 sourceB2712 sourceC2712 difference raw37577; decide +kernel
    rw [ha]
    exact (canonical37577 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2712 + sourceB2712) sourceC2712) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2712 + sourceB2712) sourceC2712) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2712 sourceB2712 sourceC2712 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2712 sourceB2712 sourceC2712
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2712, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2713 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB2713 : Charge := ![2, 1, 0, 0, 0, -3]
def sourceC2713 : Charge := ![-4, -1, 0, 0, 2, 3]
def sourceForm2713 : Integer.Sparse Master := [(Sum.inr 961, 1), (Sum.inr 1562, 2), (Sum.inr 1576, 1), (Sum.inr 1683, 1), (Sum.inr 2167, 1), (Sum.inr 4067, -1)]

theorem sourceEq2713 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2713 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2713 + difference 0 0) (sourceB2713 + difference 0 0) sourceC2713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2167) := by
    have ha : (tripleCharges (sourceA2713 + difference 0 0) (sourceB2713 + difference 0 0) sourceC2713) = raw37578 := by
      apply Matrix.ext; unfold tripleCharges sourceA2713 sourceB2713 sourceC2713 difference raw37578; decide +kernel
    rw [ha]
    exact (canonical37578 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2713 + difference 1 0) (sourceB2713 + difference 0 1) sourceC2713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA2713 + difference 1 0) (sourceB2713 + difference 0 1) sourceC2713) = raw37564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2713 sourceB2713 sourceC2713 difference raw37564; decide +kernel
    rw [ha]
    exact (canonical37564 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2713 + difference 2 0) (sourceB2713 + difference 0 2) sourceC2713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1562) := by
    have ha : (tripleCharges (sourceA2713 + difference 2 0) (sourceB2713 + difference 0 2) sourceC2713) = raw37595 := by
      apply Matrix.ext; unfold tripleCharges sourceA2713 sourceB2713 sourceC2713 difference raw37595; decide +kernel
    rw [ha]
    exact (canonical37595 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2713 + difference 3 0) (sourceB2713 + difference 0 3) sourceC2713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1562) := by
    have ha : (tripleCharges (sourceA2713 + difference 3 0) (sourceB2713 + difference 0 3) sourceC2713) = raw37596 := by
      apply Matrix.ext; unfold tripleCharges sourceA2713 sourceB2713 sourceC2713 difference raw37596; decide +kernel
    rw [ha]
    exact (canonical37596 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2713 + difference 4 0) (sourceB2713 + difference 0 4) sourceC2713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1576) := by
    have ha : (tripleCharges (sourceA2713 + difference 4 0) (sourceB2713 + difference 0 4) sourceC2713) = raw37591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2713 sourceB2713 sourceC2713 difference raw37591; decide +kernel
    rw [ha]
    exact (canonical37591 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2713 + difference 5 0) (sourceB2713 + difference 0 5) sourceC2713) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 961) := by
    have ha : (tripleCharges (sourceA2713 + difference 5 0) (sourceB2713 + difference 0 5) sourceC2713) = raw37597 := by
      apply Matrix.ext; unfold tripleCharges sourceA2713 sourceB2713 sourceC2713 difference raw37597; decide +kernel
    rw [ha]
    exact (canonical37597 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2713 + sourceB2713) sourceC2713) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2713 + sourceB2713) sourceC2713) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2713 sourceB2713 sourceC2713 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2713 sourceB2713 sourceC2713
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2713, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2714 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB2714 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2714 : Charge := ![-4, -1, 0, 0, 2, 3]
def sourceForm2714 : Integer.Sparse Master := [(Sum.inr 764, 2), (Sum.inr 773, 1), (Sum.inr 775, 1), (Sum.inr 844, 1), (Sum.inr 1694, 1), (Sum.inr 4067, -1)]

theorem sourceEq2714 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2714 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2714 + difference 0 0) (sourceB2714 + difference 0 0) sourceC2714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA2714 + difference 0 0) (sourceB2714 + difference 0 0) sourceC2714) = raw37557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2714 sourceB2714 sourceC2714 difference raw37557; decide +kernel
    rw [ha]
    exact (canonical37557 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2714 + difference 1 0) (sourceB2714 + difference 0 1) sourceC2714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 844) := by
    have ha : (tripleCharges (sourceA2714 + difference 1 0) (sourceB2714 + difference 0 1) sourceC2714) = raw37598 := by
      apply Matrix.ext; unfold tripleCharges sourceA2714 sourceB2714 sourceC2714 difference raw37598; decide +kernel
    rw [ha]
    exact (canonical37598 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2714 + difference 2 0) (sourceB2714 + difference 0 2) sourceC2714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 764) := by
    have ha : (tripleCharges (sourceA2714 + difference 2 0) (sourceB2714 + difference 0 2) sourceC2714) = raw37599 := by
      apply Matrix.ext; unfold tripleCharges sourceA2714 sourceB2714 sourceC2714 difference raw37599; decide +kernel
    rw [ha]
    exact (canonical37599 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2714 + difference 3 0) (sourceB2714 + difference 0 3) sourceC2714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 764) := by
    have ha : (tripleCharges (sourceA2714 + difference 3 0) (sourceB2714 + difference 0 3) sourceC2714) = raw37600 := by
      apply Matrix.ext; unfold tripleCharges sourceA2714 sourceB2714 sourceC2714 difference raw37600; decide +kernel
    rw [ha]
    exact (canonical37600 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2714 + difference 4 0) (sourceB2714 + difference 0 4) sourceC2714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 773) := by
    have ha : (tripleCharges (sourceA2714 + difference 4 0) (sourceB2714 + difference 0 4) sourceC2714) = raw37601 := by
      apply Matrix.ext; unfold tripleCharges sourceA2714 sourceB2714 sourceC2714 difference raw37601; decide +kernel
    rw [ha]
    exact (canonical37601 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2714 + difference 5 0) (sourceB2714 + difference 0 5) sourceC2714) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 775) := by
    have ha : (tripleCharges (sourceA2714 + difference 5 0) (sourceB2714 + difference 0 5) sourceC2714) = raw37602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2714 sourceB2714 sourceC2714 difference raw37602; decide +kernel
    rw [ha]
    exact (canonical37602 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2714 + sourceB2714) sourceC2714) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2714 + sourceB2714) sourceC2714) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2714 sourceB2714 sourceC2714 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2714 sourceB2714 sourceC2714
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2714, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2715 : Charge := ![1, 1, 0, 0, 0, -2]
def sourceB2715 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2715 : Charge := ![-4, -1, 0, 0, 2, 3]
def sourceForm2715 : Integer.Sparse Master := [(Sum.inr 775, 1), (Sum.inr 1579, 1), (Sum.inr 1591, 2), (Sum.inr 1693, 1), (Sum.inr 1694, 1), (Sum.inr 4067, -1)]

theorem sourceEq2715 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2715 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2715 + difference 5 0) (sourceB2715 + difference 0 5) sourceC2715) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 775) := by
    have ha : (tripleCharges (sourceA2715 + difference 5 0) (sourceB2715 + difference 0 5) sourceC2715) = raw37602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2715 sourceB2715 sourceC2715 difference raw37602; decide +kernel
    rw [ha]
    exact (canonical37602 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2715 + difference 5 1) (sourceB2715 + difference 1 5) sourceC2715) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1579) := by
    have ha : (tripleCharges (sourceA2715 + difference 5 1) (sourceB2715 + difference 1 5) sourceC2715) = raw37585 := by
      apply Matrix.ext; unfold tripleCharges sourceA2715 sourceB2715 sourceC2715 difference raw37585; decide +kernel
    rw [ha]
    exact (canonical37585 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2715 + difference 5 2) (sourceB2715 + difference 2 5) sourceC2715) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1591) := by
    have ha : (tripleCharges (sourceA2715 + difference 5 2) (sourceB2715 + difference 2 5) sourceC2715) = raw37603 := by
      apply Matrix.ext; unfold tripleCharges sourceA2715 sourceB2715 sourceC2715 difference raw37603; decide +kernel
    rw [ha]
    exact (canonical37603 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2715 + difference 5 3) (sourceB2715 + difference 3 5) sourceC2715) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1591) := by
    have ha : (tripleCharges (sourceA2715 + difference 5 3) (sourceB2715 + difference 3 5) sourceC2715) = raw37604 := by
      apply Matrix.ext; unfold tripleCharges sourceA2715 sourceB2715 sourceC2715 difference raw37604; decide +kernel
    rw [ha]
    exact (canonical37604 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2715 + difference 5 4) (sourceB2715 + difference 4 5) sourceC2715) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA2715 + difference 5 4) (sourceB2715 + difference 4 5) sourceC2715) = raw37563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2715 sourceB2715 sourceC2715 difference raw37563; decide +kernel
    rw [ha]
    exact (canonical37563 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2715 + difference 5 5) (sourceB2715 + difference 5 5) sourceC2715) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1694) := by
    have ha : (tripleCharges (sourceA2715 + difference 5 5) (sourceB2715 + difference 5 5) sourceC2715) = raw37557 := by
      apply Matrix.ext; unfold tripleCharges sourceA2715 sourceB2715 sourceC2715 difference raw37557; decide +kernel
    rw [ha]
    exact (canonical37557 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2715 + sourceB2715) sourceC2715) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2715 + sourceB2715) sourceC2715) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2715 sourceB2715 sourceC2715 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2715 sourceB2715 sourceC2715
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2715, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2716 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB2716 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC2716 : Charge := ![-4, -1, 0, 0, 2, 3]
def sourceForm2716 : Integer.Sparse Master := [(Sum.inr 763, 2), (Sum.inr 772, 1), (Sum.inr 775, 1), (Sum.inr 843, 1), (Sum.inr 1693, 1), (Sum.inr 4067, -1)]

theorem sourceEq2716 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2716 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2716 + difference 0 0) (sourceB2716 + difference 0 0) sourceC2716) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA2716 + difference 0 0) (sourceB2716 + difference 0 0) sourceC2716) = raw37563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2716 sourceB2716 sourceC2716 difference raw37563; decide +kernel
    rw [ha]
    exact (canonical37563 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2716 + difference 1 0) (sourceB2716 + difference 0 1) sourceC2716) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 843) := by
    have ha : (tripleCharges (sourceA2716 + difference 1 0) (sourceB2716 + difference 0 1) sourceC2716) = raw37605 := by
      apply Matrix.ext; unfold tripleCharges sourceA2716 sourceB2716 sourceC2716 difference raw37605; decide +kernel
    rw [ha]
    exact (canonical37605 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2716 + difference 2 0) (sourceB2716 + difference 0 2) sourceC2716) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 763) := by
    have ha : (tripleCharges (sourceA2716 + difference 2 0) (sourceB2716 + difference 0 2) sourceC2716) = raw37606 := by
      apply Matrix.ext; unfold tripleCharges sourceA2716 sourceB2716 sourceC2716 difference raw37606; decide +kernel
    rw [ha]
    exact (canonical37606 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2716 + difference 3 0) (sourceB2716 + difference 0 3) sourceC2716) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 763) := by
    have ha : (tripleCharges (sourceA2716 + difference 3 0) (sourceB2716 + difference 0 3) sourceC2716) = raw37607 := by
      apply Matrix.ext; unfold tripleCharges sourceA2716 sourceB2716 sourceC2716 difference raw37607; decide +kernel
    rw [ha]
    exact (canonical37607 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2716 + difference 4 0) (sourceB2716 + difference 0 4) sourceC2716) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 775) := by
    have ha : (tripleCharges (sourceA2716 + difference 4 0) (sourceB2716 + difference 0 4) sourceC2716) = raw37602 := by
      apply Matrix.ext; unfold tripleCharges sourceA2716 sourceB2716 sourceC2716 difference raw37602; decide +kernel
    rw [ha]
    exact (canonical37602 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2716 + difference 5 0) (sourceB2716 + difference 0 5) sourceC2716) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 772) := by
    have ha : (tripleCharges (sourceA2716 + difference 5 0) (sourceB2716 + difference 0 5) sourceC2716) = raw37608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2716 sourceB2716 sourceC2716 difference raw37608; decide +kernel
    rw [ha]
    exact (canonical37608 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2716 + sourceB2716) sourceC2716) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2716 + sourceB2716) sourceC2716) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2716 sourceB2716 sourceC2716 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2716 sourceB2716 sourceC2716
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2716, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2717 : Charge := ![1, 1, 0, 0, -1, -1]
def sourceB2717 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC2717 : Charge := ![-4, -1, 0, 0, 2, 3]
def sourceForm2717 : Integer.Sparse Master := [(Sum.inr 772, 1), (Sum.inr 1576, 1), (Sum.inr 1590, 2), (Sum.inr 1683, 1), (Sum.inr 1693, 1), (Sum.inr 4067, -1)]

theorem sourceEq2717 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2717 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2717 + difference 5 0) (sourceB2717 + difference 0 5) sourceC2717) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 772) := by
    have ha : (tripleCharges (sourceA2717 + difference 5 0) (sourceB2717 + difference 0 5) sourceC2717) = raw37608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2717 sourceB2717 sourceC2717 difference raw37608; decide +kernel
    rw [ha]
    exact (canonical37608 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2717 + difference 5 1) (sourceB2717 + difference 1 5) sourceC2717) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1576) := by
    have ha : (tripleCharges (sourceA2717 + difference 5 1) (sourceB2717 + difference 1 5) sourceC2717) = raw37591 := by
      apply Matrix.ext; unfold tripleCharges sourceA2717 sourceB2717 sourceC2717 difference raw37591; decide +kernel
    rw [ha]
    exact (canonical37591 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2717 + difference 5 2) (sourceB2717 + difference 2 5) sourceC2717) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1590) := by
    have ha : (tripleCharges (sourceA2717 + difference 5 2) (sourceB2717 + difference 2 5) sourceC2717) = raw37609 := by
      apply Matrix.ext; unfold tripleCharges sourceA2717 sourceB2717 sourceC2717 difference raw37609; decide +kernel
    rw [ha]
    exact (canonical37609 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2717 + difference 5 3) (sourceB2717 + difference 3 5) sourceC2717) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1590) := by
    have ha : (tripleCharges (sourceA2717 + difference 5 3) (sourceB2717 + difference 3 5) sourceC2717) = raw37610 := by
      apply Matrix.ext; unfold tripleCharges sourceA2717 sourceB2717 sourceC2717 difference raw37610; decide +kernel
    rw [ha]
    exact (canonical37610 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2717 + difference 5 4) (sourceB2717 + difference 4 5) sourceC2717) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA2717 + difference 5 4) (sourceB2717 + difference 4 5) sourceC2717) = raw37564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2717 sourceB2717 sourceC2717 difference raw37564; decide +kernel
    rw [ha]
    exact (canonical37564 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2717 + difference 5 5) (sourceB2717 + difference 5 5) sourceC2717) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1693) := by
    have ha : (tripleCharges (sourceA2717 + difference 5 5) (sourceB2717 + difference 5 5) sourceC2717) = raw37563 := by
      apply Matrix.ext; unfold tripleCharges sourceA2717 sourceB2717 sourceC2717 difference raw37563; decide +kernel
    rw [ha]
    exact (canonical37563 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2717 + sourceB2717) sourceC2717) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2717 + sourceB2717) sourceC2717) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2717 sourceB2717 sourceC2717 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2717 sourceB2717 sourceC2717
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2717, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2718 : Charge := ![1, 1, 0, 0, -2, 0]
def sourceB2718 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC2718 : Charge := ![-4, -1, 0, 0, 2, 3]
def sourceForm2718 : Integer.Sparse Master := [(Sum.inr 755, 2), (Sum.inr 759, 1), (Sum.inr 772, 1), (Sum.inr 820, 1), (Sum.inr 1683, 1), (Sum.inr 4067, -1)]

theorem sourceEq2718 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2718 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2718 + difference 0 0) (sourceB2718 + difference 0 0) sourceC2718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1683) := by
    have ha : (tripleCharges (sourceA2718 + difference 0 0) (sourceB2718 + difference 0 0) sourceC2718) = raw37564 := by
      apply Matrix.ext; unfold tripleCharges sourceA2718 sourceB2718 sourceC2718 difference raw37564; decide +kernel
    rw [ha]
    exact (canonical37564 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2718 + difference 1 0) (sourceB2718 + difference 0 1) sourceC2718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 820) := by
    have ha : (tripleCharges (sourceA2718 + difference 1 0) (sourceB2718 + difference 0 1) sourceC2718) = raw37611 := by
      apply Matrix.ext; unfold tripleCharges sourceA2718 sourceB2718 sourceC2718 difference raw37611; decide +kernel
    rw [ha]
    exact (canonical37611 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2718 + difference 2 0) (sourceB2718 + difference 0 2) sourceC2718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 755) := by
    have ha : (tripleCharges (sourceA2718 + difference 2 0) (sourceB2718 + difference 0 2) sourceC2718) = raw37612 := by
      apply Matrix.ext; unfold tripleCharges sourceA2718 sourceB2718 sourceC2718 difference raw37612; decide +kernel
    rw [ha]
    exact (canonical37612 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2718 + difference 3 0) (sourceB2718 + difference 0 3) sourceC2718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 755) := by
    have ha : (tripleCharges (sourceA2718 + difference 3 0) (sourceB2718 + difference 0 3) sourceC2718) = raw37613 := by
      apply Matrix.ext; unfold tripleCharges sourceA2718 sourceB2718 sourceC2718 difference raw37613; decide +kernel
    rw [ha]
    exact (canonical37613 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2718 + difference 4 0) (sourceB2718 + difference 0 4) sourceC2718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 772) := by
    have ha : (tripleCharges (sourceA2718 + difference 4 0) (sourceB2718 + difference 0 4) sourceC2718) = raw37608 := by
      apply Matrix.ext; unfold tripleCharges sourceA2718 sourceB2718 sourceC2718 difference raw37608; decide +kernel
    rw [ha]
    exact (canonical37608 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2718 + difference 5 0) (sourceB2718 + difference 0 5) sourceC2718) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 759) := by
    have ha : (tripleCharges (sourceA2718 + difference 5 0) (sourceB2718 + difference 0 5) sourceC2718) = raw37614 := by
      apply Matrix.ext; unfold tripleCharges sourceA2718 sourceB2718 sourceC2718 difference raw37614; decide +kernel
    rw [ha]
    exact (canonical37614 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2718 + sourceB2718) sourceC2718) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4067) := by
    have ha : (doubleCharges (sourceA2718 + sourceB2718) sourceC2718) = raw37558 := by
      apply Matrix.ext; unfold doubleCharges sourceA2718 sourceB2718 sourceC2718 raw37558; decide +kernel
    rw [ha]
    exact (canonical37558 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2718 sourceB2718 sourceC2718
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2718, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2719 : Charge := ![1, 1, 1, -1, 0, -2]
def sourceB2719 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceC2719 : Charge := ![-4, -1, 0, 1, 1, 3]
def sourceForm2719 : Integer.Sparse Master := [(Sum.inr 760, 1), (Sum.inr 1566, 1), (Sum.inr 1670, 2), (Sum.inr 1684, 1), (Sum.inr 1690, 1), (Sum.inr 4064, -1)]

theorem sourceEq2719 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2719 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2719 + difference 3 0) (sourceB2719 + difference 0 3) sourceC2719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 760) := by
    have ha : (tripleCharges (sourceA2719 + difference 3 0) (sourceB2719 + difference 0 3) sourceC2719) = raw37615 := by
      apply Matrix.ext; unfold tripleCharges sourceA2719 sourceB2719 sourceC2719 difference raw37615; decide +kernel
    rw [ha]
    exact (canonical37615 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2719 + difference 3 1) (sourceB2719 + difference 1 3) sourceC2719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1566) := by
    have ha : (tripleCharges (sourceA2719 + difference 3 1) (sourceB2719 + difference 1 3) sourceC2719) = raw37616 := by
      apply Matrix.ext; unfold tripleCharges sourceA2719 sourceB2719 sourceC2719 difference raw37616; decide +kernel
    rw [ha]
    exact (canonical37616 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2719 + difference 3 2) (sourceB2719 + difference 2 3) sourceC2719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1690) := by
    have ha : (tripleCharges (sourceA2719 + difference 3 2) (sourceB2719 + difference 2 3) sourceC2719) = raw37617 := by
      apply Matrix.ext; unfold tripleCharges sourceA2719 sourceB2719 sourceC2719 difference raw37617; decide +kernel
    rw [ha]
    exact (canonical37617 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2719 + difference 3 3) (sourceB2719 + difference 3 3) sourceC2719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1670) := by
    have ha : (tripleCharges (sourceA2719 + difference 3 3) (sourceB2719 + difference 3 3) sourceC2719) = raw37618 := by
      apply Matrix.ext; unfold tripleCharges sourceA2719 sourceB2719 sourceC2719 difference raw37618; decide +kernel
    rw [ha]
    exact (canonical37618 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2719 + difference 3 4) (sourceB2719 + difference 4 3) sourceC2719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1670) := by
    have ha : (tripleCharges (sourceA2719 + difference 3 4) (sourceB2719 + difference 4 3) sourceC2719) = raw37619 := by
      apply Matrix.ext; unfold tripleCharges sourceA2719 sourceB2719 sourceC2719 difference raw37619; decide +kernel
    rw [ha]
    exact (canonical37619 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2719 + difference 3 5) (sourceB2719 + difference 5 3) sourceC2719) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1684) := by
    have ha : (tripleCharges (sourceA2719 + difference 3 5) (sourceB2719 + difference 5 3) sourceC2719) = raw37620 := by
      apply Matrix.ext; unfold tripleCharges sourceA2719 sourceB2719 sourceC2719 difference raw37620; decide +kernel
    rw [ha]
    exact (canonical37620 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2719 + sourceB2719) sourceC2719) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4064) := by
    have ha : (doubleCharges (sourceA2719 + sourceB2719) sourceC2719) = raw37621 := by
      apply Matrix.ext; unfold doubleCharges sourceA2719 sourceB2719 sourceC2719 raw37621; decide +kernel
    rw [ha]
    exact (canonical37621 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2719 sourceB2719 sourceC2719
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2719, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
