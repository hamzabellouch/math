import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical291
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical292

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA2656 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2656 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC2656 : Charge := ![-5, 0, 0, 0, 0, 5]
def sourceForm2656 : Integer.Sparse Master := [(Sum.inr 686, 4), (Sum.inr 697, 1), (Sum.inr 1541, 1), (Sum.inr 4062, -1)]

theorem sourceEq2656 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2656 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2656 + difference 0 0) (sourceB2656 + difference 0 0) sourceC2656) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1541) := by
    have ha : (tripleCharges (sourceA2656 + difference 0 0) (sourceB2656 + difference 0 0) sourceC2656) = raw37335 := by
      apply Matrix.ext; unfold tripleCharges sourceA2656 sourceB2656 sourceC2656 difference raw37335; decide +kernel
    rw [ha]
    exact (canonical37335 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2656 + difference 1 0) (sourceB2656 + difference 0 1) sourceC2656) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 686) := by
    have ha : (tripleCharges (sourceA2656 + difference 1 0) (sourceB2656 + difference 0 1) sourceC2656) = raw37337 := by
      apply Matrix.ext; unfold tripleCharges sourceA2656 sourceB2656 sourceC2656 difference raw37337; decide +kernel
    rw [ha]
    exact (canonical37337 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2656 + difference 2 0) (sourceB2656 + difference 0 2) sourceC2656) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 686) := by
    have ha : (tripleCharges (sourceA2656 + difference 2 0) (sourceB2656 + difference 0 2) sourceC2656) = raw37338 := by
      apply Matrix.ext; unfold tripleCharges sourceA2656 sourceB2656 sourceC2656 difference raw37338; decide +kernel
    rw [ha]
    exact (canonical37338 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2656 + difference 3 0) (sourceB2656 + difference 0 3) sourceC2656) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 686) := by
    have ha : (tripleCharges (sourceA2656 + difference 3 0) (sourceB2656 + difference 0 3) sourceC2656) = raw37339 := by
      apply Matrix.ext; unfold tripleCharges sourceA2656 sourceB2656 sourceC2656 difference raw37339; decide +kernel
    rw [ha]
    exact (canonical37339 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2656 + difference 4 0) (sourceB2656 + difference 0 4) sourceC2656) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 686) := by
    have ha : (tripleCharges (sourceA2656 + difference 4 0) (sourceB2656 + difference 0 4) sourceC2656) = raw37340 := by
      apply Matrix.ext; unfold tripleCharges sourceA2656 sourceB2656 sourceC2656 difference raw37340; decide +kernel
    rw [ha]
    exact (canonical37340 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2656 + difference 5 0) (sourceB2656 + difference 0 5) sourceC2656) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 697) := by
    have ha : (tripleCharges (sourceA2656 + difference 5 0) (sourceB2656 + difference 0 5) sourceC2656) = raw37341 := by
      apply Matrix.ext; unfold tripleCharges sourceA2656 sourceB2656 sourceC2656 difference raw37341; decide +kernel
    rw [ha]
    exact (canonical37341 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2656 + sourceB2656) sourceC2656) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4062) := by
    have ha : (doubleCharges (sourceA2656 + sourceB2656) sourceC2656) = raw37336 := by
      apply Matrix.ext; unfold doubleCharges sourceA2656 sourceB2656 sourceC2656 raw37336; decide +kernel
    rw [ha]
    exact (canonical37336 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2656 sourceB2656 sourceC2656
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2656, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2657 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2657 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2657 : Charge := ![-5, 0, 0, 0, 1, 4]
def sourceForm2657 : Integer.Sparse Master := [(Sum.inr 1521, 1), (Sum.inr 1532, 3), (Sum.inr 1537, 1), (Sum.inr 1540, 1), (Sum.inr 4060, -1)]

theorem sourceEq2657 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2657 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2657 + difference 0 4) (sourceB2657 + difference 4 0) sourceC2657) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA2657 + difference 0 4) (sourceB2657 + difference 4 0) sourceC2657) = raw37342 := by
      apply Matrix.ext; unfold tripleCharges sourceA2657 sourceB2657 sourceC2657 difference raw37342; decide +kernel
    rw [ha]
    exact (canonical37342 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2657 + difference 1 4) (sourceB2657 + difference 4 1) sourceC2657) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1532) := by
    have ha : (tripleCharges (sourceA2657 + difference 1 4) (sourceB2657 + difference 4 1) sourceC2657) = raw37343 := by
      apply Matrix.ext; unfold tripleCharges sourceA2657 sourceB2657 sourceC2657 difference raw37343; decide +kernel
    rw [ha]
    exact (canonical37343 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2657 + difference 2 4) (sourceB2657 + difference 4 2) sourceC2657) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1532) := by
    have ha : (tripleCharges (sourceA2657 + difference 2 4) (sourceB2657 + difference 4 2) sourceC2657) = raw37344 := by
      apply Matrix.ext; unfold tripleCharges sourceA2657 sourceB2657 sourceC2657 difference raw37344; decide +kernel
    rw [ha]
    exact (canonical37344 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2657 + difference 3 4) (sourceB2657 + difference 4 3) sourceC2657) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1532) := by
    have ha : (tripleCharges (sourceA2657 + difference 3 4) (sourceB2657 + difference 4 3) sourceC2657) = raw37345 := by
      apply Matrix.ext; unfold tripleCharges sourceA2657 sourceB2657 sourceC2657 difference raw37345; decide +kernel
    rw [ha]
    exact (canonical37345 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2657 + difference 4 4) (sourceB2657 + difference 4 4) sourceC2657) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1540) := by
    have ha : (tripleCharges (sourceA2657 + difference 4 4) (sourceB2657 + difference 4 4) sourceC2657) = raw37346 := by
      apply Matrix.ext; unfold tripleCharges sourceA2657 sourceB2657 sourceC2657 difference raw37346; decide +kernel
    rw [ha]
    exact (canonical37346 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2657 + difference 5 4) (sourceB2657 + difference 4 5) sourceC2657) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1537) := by
    have ha : (tripleCharges (sourceA2657 + difference 5 4) (sourceB2657 + difference 4 5) sourceC2657) = raw37347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2657 sourceB2657 sourceC2657 difference raw37347; decide +kernel
    rw [ha]
    exact (canonical37347 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2657 + sourceB2657) sourceC2657) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (doubleCharges (sourceA2657 + sourceB2657) sourceC2657) = raw37348 := by
      apply Matrix.ext; unfold doubleCharges sourceA2657 sourceB2657 sourceC2657 raw37348; decide +kernel
    rw [ha]
    exact (canonical37348 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2657 sourceB2657 sourceC2657
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2657, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2658 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB2658 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceC2658 : Charge := ![-5, 0, 0, 0, 1, 4]
def sourceForm2658 : Integer.Sparse Master := [(Sum.inr 1516, 3), (Sum.inr 1521, 1), (Sum.inr 1537, 2), (Sum.inr 4060, -1)]

theorem sourceEq2658 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2658 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2658 + difference 0 3) (sourceB2658 + difference 3 0) sourceC2658) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1537) := by
    have ha : (tripleCharges (sourceA2658 + difference 0 3) (sourceB2658 + difference 3 0) sourceC2658) = raw37349 := by
      apply Matrix.ext; unfold tripleCharges sourceA2658 sourceB2658 sourceC2658 difference raw37349; decide +kernel
    rw [ha]
    exact (canonical37349 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2658 + difference 1 3) (sourceB2658 + difference 3 1) sourceC2658) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1516) := by
    have ha : (tripleCharges (sourceA2658 + difference 1 3) (sourceB2658 + difference 3 1) sourceC2658) = raw37350 := by
      apply Matrix.ext; unfold tripleCharges sourceA2658 sourceB2658 sourceC2658 difference raw37350; decide +kernel
    rw [ha]
    exact (canonical37350 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2658 + difference 2 3) (sourceB2658 + difference 3 2) sourceC2658) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1516) := by
    have ha : (tripleCharges (sourceA2658 + difference 2 3) (sourceB2658 + difference 3 2) sourceC2658) = raw37351 := by
      apply Matrix.ext; unfold tripleCharges sourceA2658 sourceB2658 sourceC2658 difference raw37351; decide +kernel
    rw [ha]
    exact (canonical37351 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2658 + difference 3 3) (sourceB2658 + difference 3 3) sourceC2658) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1516) := by
    have ha : (tripleCharges (sourceA2658 + difference 3 3) (sourceB2658 + difference 3 3) sourceC2658) = raw37352 := by
      apply Matrix.ext; unfold tripleCharges sourceA2658 sourceB2658 sourceC2658 difference raw37352; decide +kernel
    rw [ha]
    exact (canonical37352 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2658 + difference 4 3) (sourceB2658 + difference 3 4) sourceC2658) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1537) := by
    have ha : (tripleCharges (sourceA2658 + difference 4 3) (sourceB2658 + difference 3 4) sourceC2658) = raw37347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2658 sourceB2658 sourceC2658 difference raw37347; decide +kernel
    rw [ha]
    exact (canonical37347 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2658 + difference 5 3) (sourceB2658 + difference 3 5) sourceC2658) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA2658 + difference 5 3) (sourceB2658 + difference 3 5) sourceC2658) = raw37353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2658 sourceB2658 sourceC2658 difference raw37353; decide +kernel
    rw [ha]
    exact (canonical37353 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2658 + sourceB2658) sourceC2658) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (doubleCharges (sourceA2658 + sourceB2658) sourceC2658) = raw37348 := by
      apply Matrix.ext; unfold doubleCharges sourceA2658 sourceB2658 sourceC2658 raw37348; decide +kernel
    rw [ha]
    exact (canonical37348 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2658 sourceB2658 sourceC2658
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2658, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2659 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2659 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC2659 : Charge := ![-5, 0, 0, 0, 1, 4]
def sourceForm2659 : Integer.Sparse Master := [(Sum.inr 683, 3), (Sum.inr 691, 1), (Sum.inr 695, 1), (Sum.inr 1537, 1), (Sum.inr 4060, -1)]

theorem sourceEq2659 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2659 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2659 + difference 0 0) (sourceB2659 + difference 0 0) sourceC2659) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1537) := by
    have ha : (tripleCharges (sourceA2659 + difference 0 0) (sourceB2659 + difference 0 0) sourceC2659) = raw37347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2659 sourceB2659 sourceC2659 difference raw37347; decide +kernel
    rw [ha]
    exact (canonical37347 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2659 + difference 1 0) (sourceB2659 + difference 0 1) sourceC2659) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 683) := by
    have ha : (tripleCharges (sourceA2659 + difference 1 0) (sourceB2659 + difference 0 1) sourceC2659) = raw37354 := by
      apply Matrix.ext; unfold tripleCharges sourceA2659 sourceB2659 sourceC2659 difference raw37354; decide +kernel
    rw [ha]
    exact (canonical37354 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2659 + difference 2 0) (sourceB2659 + difference 0 2) sourceC2659) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 683) := by
    have ha : (tripleCharges (sourceA2659 + difference 2 0) (sourceB2659 + difference 0 2) sourceC2659) = raw37355 := by
      apply Matrix.ext; unfold tripleCharges sourceA2659 sourceB2659 sourceC2659 difference raw37355; decide +kernel
    rw [ha]
    exact (canonical37355 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2659 + difference 3 0) (sourceB2659 + difference 0 3) sourceC2659) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 683) := by
    have ha : (tripleCharges (sourceA2659 + difference 3 0) (sourceB2659 + difference 0 3) sourceC2659) = raw37356 := by
      apply Matrix.ext; unfold tripleCharges sourceA2659 sourceB2659 sourceC2659 difference raw37356; decide +kernel
    rw [ha]
    exact (canonical37356 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2659 + difference 4 0) (sourceB2659 + difference 0 4) sourceC2659) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 695) := by
    have ha : (tripleCharges (sourceA2659 + difference 4 0) (sourceB2659 + difference 0 4) sourceC2659) = raw37357 := by
      apply Matrix.ext; unfold tripleCharges sourceA2659 sourceB2659 sourceC2659 difference raw37357; decide +kernel
    rw [ha]
    exact (canonical37357 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2659 + difference 5 0) (sourceB2659 + difference 0 5) sourceC2659) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 691) := by
    have ha : (tripleCharges (sourceA2659 + difference 5 0) (sourceB2659 + difference 0 5) sourceC2659) = raw37358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2659 sourceB2659 sourceC2659 difference raw37358; decide +kernel
    rw [ha]
    exact (canonical37358 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2659 + sourceB2659) sourceC2659) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (doubleCharges (sourceA2659 + sourceB2659) sourceC2659) = raw37348 := by
      apply Matrix.ext; unfold doubleCharges sourceA2659 sourceB2659 sourceC2659 raw37348; decide +kernel
    rw [ha]
    exact (canonical37348 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2659 sourceB2659 sourceC2659
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2659, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2660 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2660 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC2660 : Charge := ![-5, 0, 0, 0, 1, 4]
def sourceForm2660 : Integer.Sparse Master := [(Sum.inr 691, 1), (Sum.inr 1494, 3), (Sum.inr 1521, 1), (Sum.inr 1537, 1), (Sum.inr 4060, -1)]

theorem sourceEq2660 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2660 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2660 + difference 5 0) (sourceB2660 + difference 0 5) sourceC2660) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 691) := by
    have ha : (tripleCharges (sourceA2660 + difference 5 0) (sourceB2660 + difference 0 5) sourceC2660) = raw37358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2660 sourceB2660 sourceC2660 difference raw37358; decide +kernel
    rw [ha]
    exact (canonical37358 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2660 + difference 5 1) (sourceB2660 + difference 1 5) sourceC2660) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1494) := by
    have ha : (tripleCharges (sourceA2660 + difference 5 1) (sourceB2660 + difference 1 5) sourceC2660) = raw37359 := by
      apply Matrix.ext; unfold tripleCharges sourceA2660 sourceB2660 sourceC2660 difference raw37359; decide +kernel
    rw [ha]
    exact (canonical37359 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2660 + difference 5 2) (sourceB2660 + difference 2 5) sourceC2660) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1494) := by
    have ha : (tripleCharges (sourceA2660 + difference 5 2) (sourceB2660 + difference 2 5) sourceC2660) = raw37360 := by
      apply Matrix.ext; unfold tripleCharges sourceA2660 sourceB2660 sourceC2660 difference raw37360; decide +kernel
    rw [ha]
    exact (canonical37360 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2660 + difference 5 3) (sourceB2660 + difference 3 5) sourceC2660) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1494) := by
    have ha : (tripleCharges (sourceA2660 + difference 5 3) (sourceB2660 + difference 3 5) sourceC2660) = raw37361 := by
      apply Matrix.ext; unfold tripleCharges sourceA2660 sourceB2660 sourceC2660 difference raw37361; decide +kernel
    rw [ha]
    exact (canonical37361 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2660 + difference 5 4) (sourceB2660 + difference 4 5) sourceC2660) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA2660 + difference 5 4) (sourceB2660 + difference 4 5) sourceC2660) = raw37353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2660 sourceB2660 sourceC2660 difference raw37353; decide +kernel
    rw [ha]
    exact (canonical37353 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2660 + difference 5 5) (sourceB2660 + difference 5 5) sourceC2660) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1537) := by
    have ha : (tripleCharges (sourceA2660 + difference 5 5) (sourceB2660 + difference 5 5) sourceC2660) = raw37347 := by
      apply Matrix.ext; unfold tripleCharges sourceA2660 sourceB2660 sourceC2660 difference raw37347; decide +kernel
    rw [ha]
    exact (canonical37347 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2660 + sourceB2660) sourceC2660) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (doubleCharges (sourceA2660 + sourceB2660) sourceC2660) = raw37348 := by
      apply Matrix.ext; unfold doubleCharges sourceA2660 sourceB2660 sourceC2660 raw37348; decide +kernel
    rw [ha]
    exact (canonical37348 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2660 sourceB2660 sourceC2660
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2660, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2661 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2661 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC2661 : Charge := ![-5, 0, 0, 0, 1, 4]
def sourceForm2661 : Integer.Sparse Master := [(Sum.inr 665, 3), (Sum.inr 673, 1), (Sum.inr 691, 1), (Sum.inr 1521, 1), (Sum.inr 4060, -1)]

theorem sourceEq2661 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2661 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2661 + difference 0 0) (sourceB2661 + difference 0 0) sourceC2661) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA2661 + difference 0 0) (sourceB2661 + difference 0 0) sourceC2661) = raw37353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2661 sourceB2661 sourceC2661 difference raw37353; decide +kernel
    rw [ha]
    exact (canonical37353 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2661 + difference 1 0) (sourceB2661 + difference 0 1) sourceC2661) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 665) := by
    have ha : (tripleCharges (sourceA2661 + difference 1 0) (sourceB2661 + difference 0 1) sourceC2661) = raw37362 := by
      apply Matrix.ext; unfold tripleCharges sourceA2661 sourceB2661 sourceC2661 difference raw37362; decide +kernel
    rw [ha]
    exact (canonical37362 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2661 + difference 2 0) (sourceB2661 + difference 0 2) sourceC2661) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 665) := by
    have ha : (tripleCharges (sourceA2661 + difference 2 0) (sourceB2661 + difference 0 2) sourceC2661) = raw37363 := by
      apply Matrix.ext; unfold tripleCharges sourceA2661 sourceB2661 sourceC2661 difference raw37363; decide +kernel
    rw [ha]
    exact (canonical37363 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2661 + difference 3 0) (sourceB2661 + difference 0 3) sourceC2661) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 665) := by
    have ha : (tripleCharges (sourceA2661 + difference 3 0) (sourceB2661 + difference 0 3) sourceC2661) = raw37364 := by
      apply Matrix.ext; unfold tripleCharges sourceA2661 sourceB2661 sourceC2661 difference raw37364; decide +kernel
    rw [ha]
    exact (canonical37364 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2661 + difference 4 0) (sourceB2661 + difference 0 4) sourceC2661) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 691) := by
    have ha : (tripleCharges (sourceA2661 + difference 4 0) (sourceB2661 + difference 0 4) sourceC2661) = raw37358 := by
      apply Matrix.ext; unfold tripleCharges sourceA2661 sourceB2661 sourceC2661 difference raw37358; decide +kernel
    rw [ha]
    exact (canonical37358 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2661 + difference 5 0) (sourceB2661 + difference 0 5) sourceC2661) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 673) := by
    have ha : (tripleCharges (sourceA2661 + difference 5 0) (sourceB2661 + difference 0 5) sourceC2661) = raw37365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2661 sourceB2661 sourceC2661 difference raw37365; decide +kernel
    rw [ha]
    exact (canonical37365 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2661 + sourceB2661) sourceC2661) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (doubleCharges (sourceA2661 + sourceB2661) sourceC2661) = raw37348 := by
      apply Matrix.ext; unfold doubleCharges sourceA2661 sourceB2661 sourceC2661 raw37348; decide +kernel
    rw [ha]
    exact (canonical37348 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2661 sourceB2661 sourceC2661
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2661, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2662 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2662 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC2662 : Charge := ![-5, 0, 0, 0, 1, 4]
def sourceForm2662 : Integer.Sparse Master := [(Sum.inr 673, 1), (Sum.inr 765, 3), (Sum.inr 845, 1), (Sum.inr 1521, 1), (Sum.inr 4060, -1)]

theorem sourceEq2662 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2662 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2662 + difference 5 0) (sourceB2662 + difference 0 5) sourceC2662) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 673) := by
    have ha : (tripleCharges (sourceA2662 + difference 5 0) (sourceB2662 + difference 0 5) sourceC2662) = raw37365 := by
      apply Matrix.ext; unfold tripleCharges sourceA2662 sourceB2662 sourceC2662 difference raw37365; decide +kernel
    rw [ha]
    exact (canonical37365 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2662 + difference 5 1) (sourceB2662 + difference 1 5) sourceC2662) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 765) := by
    have ha : (tripleCharges (sourceA2662 + difference 5 1) (sourceB2662 + difference 1 5) sourceC2662) = raw37366 := by
      apply Matrix.ext; unfold tripleCharges sourceA2662 sourceB2662 sourceC2662 difference raw37366; decide +kernel
    rw [ha]
    exact (canonical37366 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2662 + difference 5 2) (sourceB2662 + difference 2 5) sourceC2662) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 765) := by
    have ha : (tripleCharges (sourceA2662 + difference 5 2) (sourceB2662 + difference 2 5) sourceC2662) = raw37367 := by
      apply Matrix.ext; unfold tripleCharges sourceA2662 sourceB2662 sourceC2662 difference raw37367; decide +kernel
    rw [ha]
    exact (canonical37367 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2662 + difference 5 3) (sourceB2662 + difference 3 5) sourceC2662) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 765) := by
    have ha : (tripleCharges (sourceA2662 + difference 5 3) (sourceB2662 + difference 3 5) sourceC2662) = raw37368 := by
      apply Matrix.ext; unfold tripleCharges sourceA2662 sourceB2662 sourceC2662 difference raw37368; decide +kernel
    rw [ha]
    exact (canonical37368 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2662 + difference 5 4) (sourceB2662 + difference 4 5) sourceC2662) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 845) := by
    have ha : (tripleCharges (sourceA2662 + difference 5 4) (sourceB2662 + difference 4 5) sourceC2662) = raw37369 := by
      apply Matrix.ext; unfold tripleCharges sourceA2662 sourceB2662 sourceC2662 difference raw37369; decide +kernel
    rw [ha]
    exact (canonical37369 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2662 + difference 5 5) (sourceB2662 + difference 5 5) sourceC2662) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1521) := by
    have ha : (tripleCharges (sourceA2662 + difference 5 5) (sourceB2662 + difference 5 5) sourceC2662) = raw37353 := by
      apply Matrix.ext; unfold tripleCharges sourceA2662 sourceB2662 sourceC2662 difference raw37353; decide +kernel
    rw [ha]
    exact (canonical37353 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2662 + sourceB2662) sourceC2662) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4060) := by
    have ha : (doubleCharges (sourceA2662 + sourceB2662) sourceC2662) = raw37348 := by
      apply Matrix.ext; unfold doubleCharges sourceA2662 sourceB2662 sourceC2662 raw37348; decide +kernel
    rw [ha]
    exact (canonical37348 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2662 sourceB2662 sourceC2662
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2662, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2663 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2663 : Charge := ![3, 0, 0, 0, -3, 0]
def sourceC2663 : Charge := ![-5, 0, 0, 0, 2, 3]
def sourceForm2663 : Integer.Sparse Master := [(Sum.inr 1527, 1), (Sum.inr 1529, 3), (Sum.inr 1531, 1), (Sum.inr 1539, 1), (Sum.inr 4061, -1)]

theorem sourceEq2663 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2663 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2663 + difference 0 4) (sourceB2663 + difference 4 0) sourceC2663) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1527) := by
    have ha : (tripleCharges (sourceA2663 + difference 0 4) (sourceB2663 + difference 4 0) sourceC2663) = raw37370 := by
      apply Matrix.ext; unfold tripleCharges sourceA2663 sourceB2663 sourceC2663 difference raw37370; decide +kernel
    rw [ha]
    exact (canonical37370 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2663 + difference 1 4) (sourceB2663 + difference 4 1) sourceC2663) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1529) := by
    have ha : (tripleCharges (sourceA2663 + difference 1 4) (sourceB2663 + difference 4 1) sourceC2663) = raw37371 := by
      apply Matrix.ext; unfold tripleCharges sourceA2663 sourceB2663 sourceC2663 difference raw37371; decide +kernel
    rw [ha]
    exact (canonical37371 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2663 + difference 2 4) (sourceB2663 + difference 4 2) sourceC2663) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1529) := by
    have ha : (tripleCharges (sourceA2663 + difference 2 4) (sourceB2663 + difference 4 2) sourceC2663) = raw37372 := by
      apply Matrix.ext; unfold tripleCharges sourceA2663 sourceB2663 sourceC2663 difference raw37372; decide +kernel
    rw [ha]
    exact (canonical37372 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2663 + difference 3 4) (sourceB2663 + difference 4 3) sourceC2663) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1529) := by
    have ha : (tripleCharges (sourceA2663 + difference 3 4) (sourceB2663 + difference 4 3) sourceC2663) = raw37373 := by
      apply Matrix.ext; unfold tripleCharges sourceA2663 sourceB2663 sourceC2663 difference raw37373; decide +kernel
    rw [ha]
    exact (canonical37373 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2663 + difference 4 4) (sourceB2663 + difference 4 4) sourceC2663) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1531) := by
    have ha : (tripleCharges (sourceA2663 + difference 4 4) (sourceB2663 + difference 4 4) sourceC2663) = raw37374 := by
      apply Matrix.ext; unfold tripleCharges sourceA2663 sourceB2663 sourceC2663 difference raw37374; decide +kernel
    rw [ha]
    exact (canonical37374 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2663 + difference 5 4) (sourceB2663 + difference 4 5) sourceC2663) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1539) := by
    have ha : (tripleCharges (sourceA2663 + difference 5 4) (sourceB2663 + difference 4 5) sourceC2663) = raw37375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2663 sourceB2663 sourceC2663 difference raw37375; decide +kernel
    rw [ha]
    exact (canonical37375 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2663 + sourceB2663) sourceC2663) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (doubleCharges (sourceA2663 + sourceB2663) sourceC2663) = raw37376 := by
      apply Matrix.ext; unfold doubleCharges sourceA2663 sourceB2663 sourceC2663 raw37376; decide +kernel
    rw [ha]
    exact (canonical37376 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2663 sourceB2663 sourceC2663
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2663, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2664 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB2664 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceC2664 : Charge := ![-5, 0, 0, 0, 2, 3]
def sourceForm2664 : Integer.Sparse Master := [(Sum.inr 1523, 3), (Sum.inr 1527, 1), (Sum.inr 1538, 1), (Sum.inr 1539, 1), (Sum.inr 4061, -1)]

theorem sourceEq2664 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2664 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2664 + difference 0 3) (sourceB2664 + difference 3 0) sourceC2664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1539) := by
    have ha : (tripleCharges (sourceA2664 + difference 0 3) (sourceB2664 + difference 3 0) sourceC2664) = raw37377 := by
      apply Matrix.ext; unfold tripleCharges sourceA2664 sourceB2664 sourceC2664 difference raw37377; decide +kernel
    rw [ha]
    exact (canonical37377 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2664 + difference 1 3) (sourceB2664 + difference 3 1) sourceC2664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1523) := by
    have ha : (tripleCharges (sourceA2664 + difference 1 3) (sourceB2664 + difference 3 1) sourceC2664) = raw37378 := by
      apply Matrix.ext; unfold tripleCharges sourceA2664 sourceB2664 sourceC2664 difference raw37378; decide +kernel
    rw [ha]
    exact (canonical37378 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2664 + difference 2 3) (sourceB2664 + difference 3 2) sourceC2664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1523) := by
    have ha : (tripleCharges (sourceA2664 + difference 2 3) (sourceB2664 + difference 3 2) sourceC2664) = raw37379 := by
      apply Matrix.ext; unfold tripleCharges sourceA2664 sourceB2664 sourceC2664 difference raw37379; decide +kernel
    rw [ha]
    exact (canonical37379 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2664 + difference 3 3) (sourceB2664 + difference 3 3) sourceC2664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1523) := by
    have ha : (tripleCharges (sourceA2664 + difference 3 3) (sourceB2664 + difference 3 3) sourceC2664) = raw37380 := by
      apply Matrix.ext; unfold tripleCharges sourceA2664 sourceB2664 sourceC2664 difference raw37380; decide +kernel
    rw [ha]
    exact (canonical37380 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2664 + difference 4 3) (sourceB2664 + difference 3 4) sourceC2664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1538) := by
    have ha : (tripleCharges (sourceA2664 + difference 4 3) (sourceB2664 + difference 3 4) sourceC2664) = raw37381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2664 sourceB2664 sourceC2664 difference raw37381; decide +kernel
    rw [ha]
    exact (canonical37381 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2664 + difference 5 3) (sourceB2664 + difference 3 5) sourceC2664) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1527) := by
    have ha : (tripleCharges (sourceA2664 + difference 5 3) (sourceB2664 + difference 3 5) sourceC2664) = raw37382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2664 sourceB2664 sourceC2664 difference raw37382; decide +kernel
    rw [ha]
    exact (canonical37382 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2664 + sourceB2664) sourceC2664) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (doubleCharges (sourceA2664 + sourceB2664) sourceC2664) = raw37376 := by
      apply Matrix.ext; unfold doubleCharges sourceA2664 sourceB2664 sourceC2664 raw37376; decide +kernel
    rw [ha]
    exact (canonical37376 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2664 sourceB2664 sourceC2664
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2664, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2665 : Charge := ![2, 0, 0, 1, -1, -2]
def sourceB2665 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC2665 : Charge := ![-5, 0, 0, 0, 2, 3]
def sourceForm2665 : Integer.Sparse Master := [(Sum.inr 1533, 3), (Sum.inr 1538, 2), (Sum.inr 1539, 1), (Sum.inr 4061, -1)]

theorem sourceEq2665 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2665 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2665 + difference 0 3) (sourceB2665 + difference 3 0) sourceC2665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1538) := by
    have ha : (tripleCharges (sourceA2665 + difference 0 3) (sourceB2665 + difference 3 0) sourceC2665) = raw37383 := by
      apply Matrix.ext; unfold tripleCharges sourceA2665 sourceB2665 sourceC2665 difference raw37383; decide +kernel
    rw [ha]
    exact (canonical37383 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2665 + difference 1 3) (sourceB2665 + difference 3 1) sourceC2665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1533) := by
    have ha : (tripleCharges (sourceA2665 + difference 1 3) (sourceB2665 + difference 3 1) sourceC2665) = raw37384 := by
      apply Matrix.ext; unfold tripleCharges sourceA2665 sourceB2665 sourceC2665 difference raw37384; decide +kernel
    rw [ha]
    exact (canonical37384 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2665 + difference 2 3) (sourceB2665 + difference 3 2) sourceC2665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1533) := by
    have ha : (tripleCharges (sourceA2665 + difference 2 3) (sourceB2665 + difference 3 2) sourceC2665) = raw37385 := by
      apply Matrix.ext; unfold tripleCharges sourceA2665 sourceB2665 sourceC2665 difference raw37385; decide +kernel
    rw [ha]
    exact (canonical37385 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2665 + difference 3 3) (sourceB2665 + difference 3 3) sourceC2665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1533) := by
    have ha : (tripleCharges (sourceA2665 + difference 3 3) (sourceB2665 + difference 3 3) sourceC2665) = raw37386 := by
      apply Matrix.ext; unfold tripleCharges sourceA2665 sourceB2665 sourceC2665 difference raw37386; decide +kernel
    rw [ha]
    exact (canonical37386 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2665 + difference 4 3) (sourceB2665 + difference 3 4) sourceC2665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1539) := by
    have ha : (tripleCharges (sourceA2665 + difference 4 3) (sourceB2665 + difference 3 4) sourceC2665) = raw37375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2665 sourceB2665 sourceC2665 difference raw37375; decide +kernel
    rw [ha]
    exact (canonical37375 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2665 + difference 5 3) (sourceB2665 + difference 3 5) sourceC2665) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1538) := by
    have ha : (tripleCharges (sourceA2665 + difference 5 3) (sourceB2665 + difference 3 5) sourceC2665) = raw37381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2665 sourceB2665 sourceC2665 difference raw37381; decide +kernel
    rw [ha]
    exact (canonical37381 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2665 + sourceB2665) sourceC2665) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (doubleCharges (sourceA2665 + sourceB2665) sourceC2665) = raw37376 := by
      apply Matrix.ext; unfold doubleCharges sourceA2665 sourceB2665 sourceC2665 raw37376; decide +kernel
    rw [ha]
    exact (canonical37376 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2665 sourceB2665 sourceC2665
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2665, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2666 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2666 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2666 : Charge := ![-5, 0, 0, 0, 2, 3]
def sourceForm2666 : Integer.Sparse Master := [(Sum.inr 685, 3), (Sum.inr 694, 1), (Sum.inr 696, 1), (Sum.inr 1539, 1), (Sum.inr 4061, -1)]

theorem sourceEq2666 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2666 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2666 + difference 0 0) (sourceB2666 + difference 0 0) sourceC2666) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1539) := by
    have ha : (tripleCharges (sourceA2666 + difference 0 0) (sourceB2666 + difference 0 0) sourceC2666) = raw37375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2666 sourceB2666 sourceC2666 difference raw37375; decide +kernel
    rw [ha]
    exact (canonical37375 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2666 + difference 1 0) (sourceB2666 + difference 0 1) sourceC2666) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 685) := by
    have ha : (tripleCharges (sourceA2666 + difference 1 0) (sourceB2666 + difference 0 1) sourceC2666) = raw37387 := by
      apply Matrix.ext; unfold tripleCharges sourceA2666 sourceB2666 sourceC2666 difference raw37387; decide +kernel
    rw [ha]
    exact (canonical37387 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2666 + difference 2 0) (sourceB2666 + difference 0 2) sourceC2666) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 685) := by
    have ha : (tripleCharges (sourceA2666 + difference 2 0) (sourceB2666 + difference 0 2) sourceC2666) = raw37388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2666 sourceB2666 sourceC2666 difference raw37388; decide +kernel
    rw [ha]
    exact (canonical37388 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2666 + difference 3 0) (sourceB2666 + difference 0 3) sourceC2666) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 685) := by
    have ha : (tripleCharges (sourceA2666 + difference 3 0) (sourceB2666 + difference 0 3) sourceC2666) = raw37389 := by
      apply Matrix.ext; unfold tripleCharges sourceA2666 sourceB2666 sourceC2666 difference raw37389; decide +kernel
    rw [ha]
    exact (canonical37389 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2666 + difference 4 0) (sourceB2666 + difference 0 4) sourceC2666) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 694) := by
    have ha : (tripleCharges (sourceA2666 + difference 4 0) (sourceB2666 + difference 0 4) sourceC2666) = raw37390 := by
      apply Matrix.ext; unfold tripleCharges sourceA2666 sourceB2666 sourceC2666 difference raw37390; decide +kernel
    rw [ha]
    exact (canonical37390 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2666 + difference 5 0) (sourceB2666 + difference 0 5) sourceC2666) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 696) := by
    have ha : (tripleCharges (sourceA2666 + difference 5 0) (sourceB2666 + difference 0 5) sourceC2666) = raw37391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2666 sourceB2666 sourceC2666 difference raw37391; decide +kernel
    rw [ha]
    exact (canonical37391 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2666 + sourceB2666) sourceC2666) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (doubleCharges (sourceA2666 + sourceB2666) sourceC2666) = raw37376 := by
      apply Matrix.ext; unfold doubleCharges sourceA2666 sourceB2666 sourceC2666 raw37376; decide +kernel
    rw [ha]
    exact (canonical37376 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2666 sourceB2666 sourceC2666
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2666, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2667 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2667 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2667 : Charge := ![-5, 0, 0, 0, 2, 3]
def sourceForm2667 : Integer.Sparse Master := [(Sum.inr 696, 1), (Sum.inr 1496, 3), (Sum.inr 1538, 1), (Sum.inr 1539, 1), (Sum.inr 4061, -1)]

theorem sourceEq2667 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2667 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2667 + difference 5 0) (sourceB2667 + difference 0 5) sourceC2667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 696) := by
    have ha : (tripleCharges (sourceA2667 + difference 5 0) (sourceB2667 + difference 0 5) sourceC2667) = raw37391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2667 sourceB2667 sourceC2667 difference raw37391; decide +kernel
    rw [ha]
    exact (canonical37391 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2667 + difference 5 1) (sourceB2667 + difference 1 5) sourceC2667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1496) := by
    have ha : (tripleCharges (sourceA2667 + difference 5 1) (sourceB2667 + difference 1 5) sourceC2667) = raw37392 := by
      apply Matrix.ext; unfold tripleCharges sourceA2667 sourceB2667 sourceC2667 difference raw37392; decide +kernel
    rw [ha]
    exact (canonical37392 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2667 + difference 5 2) (sourceB2667 + difference 2 5) sourceC2667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1496) := by
    have ha : (tripleCharges (sourceA2667 + difference 5 2) (sourceB2667 + difference 2 5) sourceC2667) = raw37393 := by
      apply Matrix.ext; unfold tripleCharges sourceA2667 sourceB2667 sourceC2667 difference raw37393; decide +kernel
    rw [ha]
    exact (canonical37393 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2667 + difference 5 3) (sourceB2667 + difference 3 5) sourceC2667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1496) := by
    have ha : (tripleCharges (sourceA2667 + difference 5 3) (sourceB2667 + difference 3 5) sourceC2667) = raw37394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2667 sourceB2667 sourceC2667 difference raw37394; decide +kernel
    rw [ha]
    exact (canonical37394 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2667 + difference 5 4) (sourceB2667 + difference 4 5) sourceC2667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1538) := by
    have ha : (tripleCharges (sourceA2667 + difference 5 4) (sourceB2667 + difference 4 5) sourceC2667) = raw37381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2667 sourceB2667 sourceC2667 difference raw37381; decide +kernel
    rw [ha]
    exact (canonical37381 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2667 + difference 5 5) (sourceB2667 + difference 5 5) sourceC2667) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1539) := by
    have ha : (tripleCharges (sourceA2667 + difference 5 5) (sourceB2667 + difference 5 5) sourceC2667) = raw37375 := by
      apply Matrix.ext; unfold tripleCharges sourceA2667 sourceB2667 sourceC2667 difference raw37375; decide +kernel
    rw [ha]
    exact (canonical37375 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2667 + sourceB2667) sourceC2667) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (doubleCharges (sourceA2667 + sourceB2667) sourceC2667) = raw37376 := by
      apply Matrix.ext; unfold doubleCharges sourceA2667 sourceB2667 sourceC2667 raw37376; decide +kernel
    rw [ha]
    exact (canonical37376 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2667 sourceB2667 sourceC2667
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2667, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2668 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2668 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC2668 : Charge := ![-5, 0, 0, 0, 2, 3]
def sourceForm2668 : Integer.Sparse Master := [(Sum.inr 684, 3), (Sum.inr 693, 1), (Sum.inr 696, 1), (Sum.inr 1538, 1), (Sum.inr 4061, -1)]

theorem sourceEq2668 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2668 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2668 + difference 0 0) (sourceB2668 + difference 0 0) sourceC2668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1538) := by
    have ha : (tripleCharges (sourceA2668 + difference 0 0) (sourceB2668 + difference 0 0) sourceC2668) = raw37381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2668 sourceB2668 sourceC2668 difference raw37381; decide +kernel
    rw [ha]
    exact (canonical37381 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2668 + difference 1 0) (sourceB2668 + difference 0 1) sourceC2668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 684) := by
    have ha : (tripleCharges (sourceA2668 + difference 1 0) (sourceB2668 + difference 0 1) sourceC2668) = raw37395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2668 sourceB2668 sourceC2668 difference raw37395; decide +kernel
    rw [ha]
    exact (canonical37395 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2668 + difference 2 0) (sourceB2668 + difference 0 2) sourceC2668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 684) := by
    have ha : (tripleCharges (sourceA2668 + difference 2 0) (sourceB2668 + difference 0 2) sourceC2668) = raw37396 := by
      apply Matrix.ext; unfold tripleCharges sourceA2668 sourceB2668 sourceC2668 difference raw37396; decide +kernel
    rw [ha]
    exact (canonical37396 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2668 + difference 3 0) (sourceB2668 + difference 0 3) sourceC2668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 684) := by
    have ha : (tripleCharges (sourceA2668 + difference 3 0) (sourceB2668 + difference 0 3) sourceC2668) = raw37397 := by
      apply Matrix.ext; unfold tripleCharges sourceA2668 sourceB2668 sourceC2668 difference raw37397; decide +kernel
    rw [ha]
    exact (canonical37397 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2668 + difference 4 0) (sourceB2668 + difference 0 4) sourceC2668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 696) := by
    have ha : (tripleCharges (sourceA2668 + difference 4 0) (sourceB2668 + difference 0 4) sourceC2668) = raw37391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2668 sourceB2668 sourceC2668 difference raw37391; decide +kernel
    rw [ha]
    exact (canonical37391 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2668 + difference 5 0) (sourceB2668 + difference 0 5) sourceC2668) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 693) := by
    have ha : (tripleCharges (sourceA2668 + difference 5 0) (sourceB2668 + difference 0 5) sourceC2668) = raw37398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2668 sourceB2668 sourceC2668 difference raw37398; decide +kernel
    rw [ha]
    exact (canonical37398 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2668 + sourceB2668) sourceC2668) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (doubleCharges (sourceA2668 + sourceB2668) sourceC2668) = raw37376 := by
      apply Matrix.ext; unfold doubleCharges sourceA2668 sourceB2668 sourceC2668 raw37376; decide +kernel
    rw [ha]
    exact (canonical37376 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2668 sourceB2668 sourceC2668
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2668, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2669 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2669 : Charge := ![3, 0, 0, 0, -1, -2]
def sourceC2669 : Charge := ![-5, 0, 0, 0, 2, 3]
def sourceForm2669 : Integer.Sparse Master := [(Sum.inr 693, 1), (Sum.inr 1495, 3), (Sum.inr 1527, 1), (Sum.inr 1538, 1), (Sum.inr 4061, -1)]

theorem sourceEq2669 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2669 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2669 + difference 5 0) (sourceB2669 + difference 0 5) sourceC2669) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 693) := by
    have ha : (tripleCharges (sourceA2669 + difference 5 0) (sourceB2669 + difference 0 5) sourceC2669) = raw37398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2669 sourceB2669 sourceC2669 difference raw37398; decide +kernel
    rw [ha]
    exact (canonical37398 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2669 + difference 5 1) (sourceB2669 + difference 1 5) sourceC2669) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1495) := by
    have ha : (tripleCharges (sourceA2669 + difference 5 1) (sourceB2669 + difference 1 5) sourceC2669) = raw37399 := by
      apply Matrix.ext; unfold tripleCharges sourceA2669 sourceB2669 sourceC2669 difference raw37399; decide +kernel
    rw [ha]
    exact (canonical37399 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2669 + difference 5 2) (sourceB2669 + difference 2 5) sourceC2669) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1495) := by
    have ha : (tripleCharges (sourceA2669 + difference 5 2) (sourceB2669 + difference 2 5) sourceC2669) = raw37400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2669 sourceB2669 sourceC2669 difference raw37400; decide +kernel
    rw [ha]
    exact (canonical37400 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2669 + difference 5 3) (sourceB2669 + difference 3 5) sourceC2669) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1495) := by
    have ha : (tripleCharges (sourceA2669 + difference 5 3) (sourceB2669 + difference 3 5) sourceC2669) = raw37401 := by
      apply Matrix.ext; unfold tripleCharges sourceA2669 sourceB2669 sourceC2669 difference raw37401; decide +kernel
    rw [ha]
    exact (canonical37401 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2669 + difference 5 4) (sourceB2669 + difference 4 5) sourceC2669) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1527) := by
    have ha : (tripleCharges (sourceA2669 + difference 5 4) (sourceB2669 + difference 4 5) sourceC2669) = raw37382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2669 sourceB2669 sourceC2669 difference raw37382; decide +kernel
    rw [ha]
    exact (canonical37382 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2669 + difference 5 5) (sourceB2669 + difference 5 5) sourceC2669) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1538) := by
    have ha : (tripleCharges (sourceA2669 + difference 5 5) (sourceB2669 + difference 5 5) sourceC2669) = raw37381 := by
      apply Matrix.ext; unfold tripleCharges sourceA2669 sourceB2669 sourceC2669 difference raw37381; decide +kernel
    rw [ha]
    exact (canonical37381 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2669 + sourceB2669) sourceC2669) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (doubleCharges (sourceA2669 + sourceB2669) sourceC2669) = raw37376 := by
      apply Matrix.ext; unfold doubleCharges sourceA2669 sourceB2669 sourceC2669 raw37376; decide +kernel
    rw [ha]
    exact (canonical37376 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2669 sourceB2669 sourceC2669
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2669, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2670 : Charge := ![2, 0, 0, 0, -2, 0]
def sourceB2670 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC2670 : Charge := ![-5, 0, 0, 0, 2, 3]
def sourceForm2670 : Integer.Sparse Master := [(Sum.inr 676, 3), (Sum.inr 680, 1), (Sum.inr 693, 1), (Sum.inr 1527, 1), (Sum.inr 4061, -1)]

theorem sourceEq2670 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2670 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2670 + difference 0 0) (sourceB2670 + difference 0 0) sourceC2670) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1527) := by
    have ha : (tripleCharges (sourceA2670 + difference 0 0) (sourceB2670 + difference 0 0) sourceC2670) = raw37382 := by
      apply Matrix.ext; unfold tripleCharges sourceA2670 sourceB2670 sourceC2670 difference raw37382; decide +kernel
    rw [ha]
    exact (canonical37382 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2670 + difference 1 0) (sourceB2670 + difference 0 1) sourceC2670) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 676) := by
    have ha : (tripleCharges (sourceA2670 + difference 1 0) (sourceB2670 + difference 0 1) sourceC2670) = raw37402 := by
      apply Matrix.ext; unfold tripleCharges sourceA2670 sourceB2670 sourceC2670 difference raw37402; decide +kernel
    rw [ha]
    exact (canonical37402 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2670 + difference 2 0) (sourceB2670 + difference 0 2) sourceC2670) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 676) := by
    have ha : (tripleCharges (sourceA2670 + difference 2 0) (sourceB2670 + difference 0 2) sourceC2670) = raw37403 := by
      apply Matrix.ext; unfold tripleCharges sourceA2670 sourceB2670 sourceC2670 difference raw37403; decide +kernel
    rw [ha]
    exact (canonical37403 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2670 + difference 3 0) (sourceB2670 + difference 0 3) sourceC2670) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 676) := by
    have ha : (tripleCharges (sourceA2670 + difference 3 0) (sourceB2670 + difference 0 3) sourceC2670) = raw37404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2670 sourceB2670 sourceC2670 difference raw37404; decide +kernel
    rw [ha]
    exact (canonical37404 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2670 + difference 4 0) (sourceB2670 + difference 0 4) sourceC2670) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 693) := by
    have ha : (tripleCharges (sourceA2670 + difference 4 0) (sourceB2670 + difference 0 4) sourceC2670) = raw37398 := by
      apply Matrix.ext; unfold tripleCharges sourceA2670 sourceB2670 sourceC2670 difference raw37398; decide +kernel
    rw [ha]
    exact (canonical37398 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2670 + difference 5 0) (sourceB2670 + difference 0 5) sourceC2670) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 680) := by
    have ha : (tripleCharges (sourceA2670 + difference 5 0) (sourceB2670 + difference 0 5) sourceC2670) = raw37405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2670 sourceB2670 sourceC2670 difference raw37405; decide +kernel
    rw [ha]
    exact (canonical37405 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2670 + sourceB2670) sourceC2670) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4061) := by
    have ha : (doubleCharges (sourceA2670 + sourceB2670) sourceC2670) = raw37376 := by
      apply Matrix.ext; unfold doubleCharges sourceA2670 sourceB2670 sourceC2670 raw37376; decide +kernel
    rw [ha]
    exact (canonical37376 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2670 sourceB2670 sourceC2670
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2670, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2671 : Charge := ![2, 0, 0, -1, 1, -2]
def sourceB2671 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2671 : Charge := ![-5, 0, 0, 1, 1, 3]
def sourceForm2671 : Integer.Sparse Master := [(Sum.inr 1514, 2), (Sum.inr 1518, 2), (Sum.inr 1520, 1), (Sum.inr 1535, 1), (Sum.inr 4058, -1)]

theorem sourceEq2671 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2671 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2671 + difference 0 4) (sourceB2671 + difference 4 0) sourceC2671) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA2671 + difference 0 4) (sourceB2671 + difference 4 0) sourceC2671) = raw37406 := by
      apply Matrix.ext; unfold tripleCharges sourceA2671 sourceB2671 sourceC2671 difference raw37406; decide +kernel
    rw [ha]
    exact (canonical37406 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2671 + difference 1 4) (sourceB2671 + difference 4 1) sourceC2671) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1514) := by
    have ha : (tripleCharges (sourceA2671 + difference 1 4) (sourceB2671 + difference 4 1) sourceC2671) = raw37407 := by
      apply Matrix.ext; unfold tripleCharges sourceA2671 sourceB2671 sourceC2671 difference raw37407; decide +kernel
    rw [ha]
    exact (canonical37407 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2671 + difference 2 4) (sourceB2671 + difference 4 2) sourceC2671) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1514) := by
    have ha : (tripleCharges (sourceA2671 + difference 2 4) (sourceB2671 + difference 4 2) sourceC2671) = raw37408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2671 sourceB2671 sourceC2671 difference raw37408; decide +kernel
    rw [ha]
    exact (canonical37408 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2671 + difference 3 4) (sourceB2671 + difference 4 3) sourceC2671) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1535) := by
    have ha : (tripleCharges (sourceA2671 + difference 3 4) (sourceB2671 + difference 4 3) sourceC2671) = raw37409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2671 sourceB2671 sourceC2671 difference raw37409; decide +kernel
    rw [ha]
    exact (canonical37409 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2671 + difference 4 4) (sourceB2671 + difference 4 4) sourceC2671) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1520) := by
    have ha : (tripleCharges (sourceA2671 + difference 4 4) (sourceB2671 + difference 4 4) sourceC2671) = raw37410 := by
      apply Matrix.ext; unfold tripleCharges sourceA2671 sourceB2671 sourceC2671 difference raw37410; decide +kernel
    rw [ha]
    exact (canonical37410 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2671 + difference 5 4) (sourceB2671 + difference 4 5) sourceC2671) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA2671 + difference 5 4) (sourceB2671 + difference 4 5) sourceC2671) = raw37411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2671 sourceB2671 sourceC2671 difference raw37411; decide +kernel
    rw [ha]
    exact (canonical37411 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2671 + sourceB2671) sourceC2671) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (doubleCharges (sourceA2671 + sourceB2671) sourceC2671) = raw37412 := by
      apply Matrix.ext; unfold doubleCharges sourceA2671 sourceB2671 sourceC2671 raw37412; decide +kernel
    rw [ha]
    exact (canonical37412 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2671 sourceB2671 sourceC2671
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2671, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2672 : Charge := ![2, 0, 0, 0, 1, -3]
def sourceB2672 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC2672 : Charge := ![-5, 0, 0, 1, 1, 3]
def sourceForm2672 : Integer.Sparse Master := [(Sum.inr 1509, 1), (Sum.inr 1528, 2), (Sum.inr 1530, 2), (Sum.inr 1535, 1), (Sum.inr 4058, -1)]

theorem sourceEq2672 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2672 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2672 + difference 0 4) (sourceB2672 + difference 4 0) sourceC2672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1509) := by
    have ha : (tripleCharges (sourceA2672 + difference 0 4) (sourceB2672 + difference 4 0) sourceC2672) = raw37413 := by
      apply Matrix.ext; unfold tripleCharges sourceA2672 sourceB2672 sourceC2672 difference raw37413; decide +kernel
    rw [ha]
    exact (canonical37413 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2672 + difference 1 4) (sourceB2672 + difference 4 1) sourceC2672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1528) := by
    have ha : (tripleCharges (sourceA2672 + difference 1 4) (sourceB2672 + difference 4 1) sourceC2672) = raw37414 := by
      apply Matrix.ext; unfold tripleCharges sourceA2672 sourceB2672 sourceC2672 difference raw37414; decide +kernel
    rw [ha]
    exact (canonical37414 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2672 + difference 2 4) (sourceB2672 + difference 4 2) sourceC2672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1528) := by
    have ha : (tripleCharges (sourceA2672 + difference 2 4) (sourceB2672 + difference 4 2) sourceC2672) = raw37415 := by
      apply Matrix.ext; unfold tripleCharges sourceA2672 sourceB2672 sourceC2672 difference raw37415; decide +kernel
    rw [ha]
    exact (canonical37415 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2672 + difference 3 4) (sourceB2672 + difference 4 3) sourceC2672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1530) := by
    have ha : (tripleCharges (sourceA2672 + difference 3 4) (sourceB2672 + difference 4 3) sourceC2672) = raw37416 := by
      apply Matrix.ext; unfold tripleCharges sourceA2672 sourceB2672 sourceC2672 difference raw37416; decide +kernel
    rw [ha]
    exact (canonical37416 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2672 + difference 4 4) (sourceB2672 + difference 4 4) sourceC2672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1530) := by
    have ha : (tripleCharges (sourceA2672 + difference 4 4) (sourceB2672 + difference 4 4) sourceC2672) = raw37417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2672 sourceB2672 sourceC2672 difference raw37417; decide +kernel
    rw [ha]
    exact (canonical37417 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2672 + difference 5 4) (sourceB2672 + difference 4 5) sourceC2672) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1535) := by
    have ha : (tripleCharges (sourceA2672 + difference 5 4) (sourceB2672 + difference 4 5) sourceC2672) = raw37409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2672 sourceB2672 sourceC2672 difference raw37409; decide +kernel
    rw [ha]
    exact (canonical37409 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2672 + sourceB2672) sourceC2672) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (doubleCharges (sourceA2672 + sourceB2672) sourceC2672) = raw37412 := by
      apply Matrix.ext; unfold doubleCharges sourceA2672 sourceB2672 sourceC2672 raw37412; decide +kernel
    rw [ha]
    exact (canonical37412 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2672 sourceB2672 sourceC2672
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2672, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2673 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB2673 : Charge := ![3, 0, -1, 0, 0, -2]
def sourceC2673 : Charge := ![-5, 0, 0, 1, 1, 3]
def sourceForm2673 : Integer.Sparse Master := [(Sum.inr 1505, 2), (Sum.inr 1509, 1), (Sum.inr 1518, 2), (Sum.inr 1535, 1), (Sum.inr 4058, -1)]

theorem sourceEq2673 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2673 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2673 + difference 0 2) (sourceB2673 + difference 2 0) sourceC2673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1535) := by
    have ha : (tripleCharges (sourceA2673 + difference 0 2) (sourceB2673 + difference 2 0) sourceC2673) = raw37418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2673 sourceB2673 sourceC2673 difference raw37418; decide +kernel
    rw [ha]
    exact (canonical37418 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2673 + difference 1 2) (sourceB2673 + difference 2 1) sourceC2673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1505) := by
    have ha : (tripleCharges (sourceA2673 + difference 1 2) (sourceB2673 + difference 2 1) sourceC2673) = raw37419 := by
      apply Matrix.ext; unfold tripleCharges sourceA2673 sourceB2673 sourceC2673 difference raw37419; decide +kernel
    rw [ha]
    exact (canonical37419 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2673 + difference 2 2) (sourceB2673 + difference 2 2) sourceC2673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1505) := by
    have ha : (tripleCharges (sourceA2673 + difference 2 2) (sourceB2673 + difference 2 2) sourceC2673) = raw37420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2673 sourceB2673 sourceC2673 difference raw37420; decide +kernel
    rw [ha]
    exact (canonical37420 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2673 + difference 3 2) (sourceB2673 + difference 2 3) sourceC2673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA2673 + difference 3 2) (sourceB2673 + difference 2 3) sourceC2673) = raw37421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2673 sourceB2673 sourceC2673 difference raw37421; decide +kernel
    rw [ha]
    exact (canonical37421 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2673 + difference 4 2) (sourceB2673 + difference 2 4) sourceC2673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA2673 + difference 4 2) (sourceB2673 + difference 2 4) sourceC2673) = raw37411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2673 sourceB2673 sourceC2673 difference raw37411; decide +kernel
    rw [ha]
    exact (canonical37411 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2673 + difference 5 2) (sourceB2673 + difference 2 5) sourceC2673) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1509) := by
    have ha : (tripleCharges (sourceA2673 + difference 5 2) (sourceB2673 + difference 2 5) sourceC2673) = raw37422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2673 sourceB2673 sourceC2673 difference raw37422; decide +kernel
    rw [ha]
    exact (canonical37422 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2673 + sourceB2673) sourceC2673) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (doubleCharges (sourceA2673 + sourceB2673) sourceC2673) = raw37412 := by
      apply Matrix.ext; unfold doubleCharges sourceA2673 sourceB2673 sourceC2673 raw37412; decide +kernel
    rw [ha]
    exact (canonical37412 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2673 sourceB2673 sourceC2673
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2673, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2674 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2674 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC2674 : Charge := ![-5, 0, 0, 1, 1, 3]
def sourceForm2674 : Integer.Sparse Master := [(Sum.inr 681, 2), (Sum.inr 688, 1), (Sum.inr 690, 2), (Sum.inr 1535, 1), (Sum.inr 4058, -1)]

theorem sourceEq2674 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2674 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2674 + difference 0 0) (sourceB2674 + difference 0 0) sourceC2674) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1535) := by
    have ha : (tripleCharges (sourceA2674 + difference 0 0) (sourceB2674 + difference 0 0) sourceC2674) = raw37409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2674 sourceB2674 sourceC2674 difference raw37409; decide +kernel
    rw [ha]
    exact (canonical37409 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2674 + difference 1 0) (sourceB2674 + difference 0 1) sourceC2674) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 681) := by
    have ha : (tripleCharges (sourceA2674 + difference 1 0) (sourceB2674 + difference 0 1) sourceC2674) = raw37423 := by
      apply Matrix.ext; unfold tripleCharges sourceA2674 sourceB2674 sourceC2674 difference raw37423; decide +kernel
    rw [ha]
    exact (canonical37423 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2674 + difference 2 0) (sourceB2674 + difference 0 2) sourceC2674) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 681) := by
    have ha : (tripleCharges (sourceA2674 + difference 2 0) (sourceB2674 + difference 0 2) sourceC2674) = raw37424 := by
      apply Matrix.ext; unfold tripleCharges sourceA2674 sourceB2674 sourceC2674 difference raw37424; decide +kernel
    rw [ha]
    exact (canonical37424 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2674 + difference 3 0) (sourceB2674 + difference 0 3) sourceC2674) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 690) := by
    have ha : (tripleCharges (sourceA2674 + difference 3 0) (sourceB2674 + difference 0 3) sourceC2674) = raw37425 := by
      apply Matrix.ext; unfold tripleCharges sourceA2674 sourceB2674 sourceC2674 difference raw37425; decide +kernel
    rw [ha]
    exact (canonical37425 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2674 + difference 4 0) (sourceB2674 + difference 0 4) sourceC2674) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 690) := by
    have ha : (tripleCharges (sourceA2674 + difference 4 0) (sourceB2674 + difference 0 4) sourceC2674) = raw37426 := by
      apply Matrix.ext; unfold tripleCharges sourceA2674 sourceB2674 sourceC2674 difference raw37426; decide +kernel
    rw [ha]
    exact (canonical37426 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2674 + difference 5 0) (sourceB2674 + difference 0 5) sourceC2674) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 688) := by
    have ha : (tripleCharges (sourceA2674 + difference 5 0) (sourceB2674 + difference 0 5) sourceC2674) = raw37427 := by
      apply Matrix.ext; unfold tripleCharges sourceA2674 sourceB2674 sourceC2674 difference raw37427; decide +kernel
    rw [ha]
    exact (canonical37427 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2674 + sourceB2674) sourceC2674) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (doubleCharges (sourceA2674 + sourceB2674) sourceC2674) = raw37412 := by
      apply Matrix.ext; unfold doubleCharges sourceA2674 sourceB2674 sourceC2674 raw37412; decide +kernel
    rw [ha]
    exact (canonical37412 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2674 sourceB2674 sourceC2674
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2674, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2675 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2675 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC2675 : Charge := ![-5, 0, 0, 1, 1, 3]
def sourceForm2675 : Integer.Sparse Master := [(Sum.inr 688, 1), (Sum.inr 1492, 2), (Sum.inr 1518, 2), (Sum.inr 1535, 1), (Sum.inr 4058, -1)]

theorem sourceEq2675 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2675 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2675 + difference 5 0) (sourceB2675 + difference 0 5) sourceC2675) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 688) := by
    have ha : (tripleCharges (sourceA2675 + difference 5 0) (sourceB2675 + difference 0 5) sourceC2675) = raw37427 := by
      apply Matrix.ext; unfold tripleCharges sourceA2675 sourceB2675 sourceC2675 difference raw37427; decide +kernel
    rw [ha]
    exact (canonical37427 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2675 + difference 5 1) (sourceB2675 + difference 1 5) sourceC2675) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1492) := by
    have ha : (tripleCharges (sourceA2675 + difference 5 1) (sourceB2675 + difference 1 5) sourceC2675) = raw37428 := by
      apply Matrix.ext; unfold tripleCharges sourceA2675 sourceB2675 sourceC2675 difference raw37428; decide +kernel
    rw [ha]
    exact (canonical37428 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2675 + difference 5 2) (sourceB2675 + difference 2 5) sourceC2675) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1492) := by
    have ha : (tripleCharges (sourceA2675 + difference 5 2) (sourceB2675 + difference 2 5) sourceC2675) = raw37429 := by
      apply Matrix.ext; unfold tripleCharges sourceA2675 sourceB2675 sourceC2675 difference raw37429; decide +kernel
    rw [ha]
    exact (canonical37429 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2675 + difference 5 3) (sourceB2675 + difference 3 5) sourceC2675) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA2675 + difference 5 3) (sourceB2675 + difference 3 5) sourceC2675) = raw37411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2675 sourceB2675 sourceC2675 difference raw37411; decide +kernel
    rw [ha]
    exact (canonical37411 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2675 + difference 5 4) (sourceB2675 + difference 4 5) sourceC2675) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA2675 + difference 5 4) (sourceB2675 + difference 4 5) sourceC2675) = raw37421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2675 sourceB2675 sourceC2675 difference raw37421; decide +kernel
    rw [ha]
    exact (canonical37421 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2675 + difference 5 5) (sourceB2675 + difference 5 5) sourceC2675) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1535) := by
    have ha : (tripleCharges (sourceA2675 + difference 5 5) (sourceB2675 + difference 5 5) sourceC2675) = raw37409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2675 sourceB2675 sourceC2675 difference raw37409; decide +kernel
    rw [ha]
    exact (canonical37409 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2675 + sourceB2675) sourceC2675) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (doubleCharges (sourceA2675 + sourceB2675) sourceC2675) = raw37412 := by
      apply Matrix.ext; unfold doubleCharges sourceA2675 sourceB2675 sourceC2675 raw37412; decide +kernel
    rw [ha]
    exact (canonical37412 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2675 sourceB2675 sourceC2675
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2675, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2676 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2676 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceC2676 : Charge := ![-5, 0, 0, 1, 1, 3]
def sourceForm2676 : Integer.Sparse Master := [(Sum.inr 663, 2), (Sum.inr 669, 1), (Sum.inr 671, 1), (Sum.inr 688, 1), (Sum.inr 1518, 1), (Sum.inr 4058, -1)]

theorem sourceEq2676 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2676 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2676 + difference 0 0) (sourceB2676 + difference 0 0) sourceC2676) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA2676 + difference 0 0) (sourceB2676 + difference 0 0) sourceC2676) = raw37421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2676 sourceB2676 sourceC2676 difference raw37421; decide +kernel
    rw [ha]
    exact (canonical37421 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2676 + difference 1 0) (sourceB2676 + difference 0 1) sourceC2676) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 663) := by
    have ha : (tripleCharges (sourceA2676 + difference 1 0) (sourceB2676 + difference 0 1) sourceC2676) = raw37430 := by
      apply Matrix.ext; unfold tripleCharges sourceA2676 sourceB2676 sourceC2676 difference raw37430; decide +kernel
    rw [ha]
    exact (canonical37430 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2676 + difference 2 0) (sourceB2676 + difference 0 2) sourceC2676) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 663) := by
    have ha : (tripleCharges (sourceA2676 + difference 2 0) (sourceB2676 + difference 0 2) sourceC2676) = raw37431 := by
      apply Matrix.ext; unfold tripleCharges sourceA2676 sourceB2676 sourceC2676 difference raw37431; decide +kernel
    rw [ha]
    exact (canonical37431 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2676 + difference 3 0) (sourceB2676 + difference 0 3) sourceC2676) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 671) := by
    have ha : (tripleCharges (sourceA2676 + difference 3 0) (sourceB2676 + difference 0 3) sourceC2676) = raw37432 := by
      apply Matrix.ext; unfold tripleCharges sourceA2676 sourceB2676 sourceC2676 difference raw37432; decide +kernel
    rw [ha]
    exact (canonical37432 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2676 + difference 4 0) (sourceB2676 + difference 0 4) sourceC2676) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 688) := by
    have ha : (tripleCharges (sourceA2676 + difference 4 0) (sourceB2676 + difference 0 4) sourceC2676) = raw37427 := by
      apply Matrix.ext; unfold tripleCharges sourceA2676 sourceB2676 sourceC2676 difference raw37427; decide +kernel
    rw [ha]
    exact (canonical37427 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2676 + difference 5 0) (sourceB2676 + difference 0 5) sourceC2676) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 669) := by
    have ha : (tripleCharges (sourceA2676 + difference 5 0) (sourceB2676 + difference 0 5) sourceC2676) = raw37433 := by
      apply Matrix.ext; unfold tripleCharges sourceA2676 sourceB2676 sourceC2676 difference raw37433; decide +kernel
    rw [ha]
    exact (canonical37433 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2676 + sourceB2676) sourceC2676) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (doubleCharges (sourceA2676 + sourceB2676) sourceC2676) = raw37412 := by
      apply Matrix.ext; unfold doubleCharges sourceA2676 sourceB2676 sourceC2676 raw37412; decide +kernel
    rw [ha]
    exact (canonical37412 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2676 sourceB2676 sourceC2676
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2676, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2677 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2677 : Charge := ![3, 0, 0, -1, 0, -2]
def sourceC2677 : Charge := ![-5, 0, 0, 1, 1, 3]
def sourceForm2677 : Integer.Sparse Master := [(Sum.inr 669, 1), (Sum.inr 1489, 2), (Sum.inr 1499, 1), (Sum.inr 1509, 1), (Sum.inr 1518, 1), (Sum.inr 4058, -1)]

theorem sourceEq2677 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2677 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2677 + difference 5 0) (sourceB2677 + difference 0 5) sourceC2677) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 669) := by
    have ha : (tripleCharges (sourceA2677 + difference 5 0) (sourceB2677 + difference 0 5) sourceC2677) = raw37433 := by
      apply Matrix.ext; unfold tripleCharges sourceA2677 sourceB2677 sourceC2677 difference raw37433; decide +kernel
    rw [ha]
    exact (canonical37433 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2677 + difference 5 1) (sourceB2677 + difference 1 5) sourceC2677) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1489) := by
    have ha : (tripleCharges (sourceA2677 + difference 5 1) (sourceB2677 + difference 1 5) sourceC2677) = raw37434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2677 sourceB2677 sourceC2677 difference raw37434; decide +kernel
    rw [ha]
    exact (canonical37434 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2677 + difference 5 2) (sourceB2677 + difference 2 5) sourceC2677) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1489) := by
    have ha : (tripleCharges (sourceA2677 + difference 5 2) (sourceB2677 + difference 2 5) sourceC2677) = raw37435 := by
      apply Matrix.ext; unfold tripleCharges sourceA2677 sourceB2677 sourceC2677 difference raw37435; decide +kernel
    rw [ha]
    exact (canonical37435 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2677 + difference 5 3) (sourceB2677 + difference 3 5) sourceC2677) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1509) := by
    have ha : (tripleCharges (sourceA2677 + difference 5 3) (sourceB2677 + difference 3 5) sourceC2677) = raw37422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2677 sourceB2677 sourceC2677 difference raw37422; decide +kernel
    rw [ha]
    exact (canonical37422 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2677 + difference 5 4) (sourceB2677 + difference 4 5) sourceC2677) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1499) := by
    have ha : (tripleCharges (sourceA2677 + difference 5 4) (sourceB2677 + difference 4 5) sourceC2677) = raw37436 := by
      apply Matrix.ext; unfold tripleCharges sourceA2677 sourceB2677 sourceC2677 difference raw37436; decide +kernel
    rw [ha]
    exact (canonical37436 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2677 + difference 5 5) (sourceB2677 + difference 5 5) sourceC2677) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1518) := by
    have ha : (tripleCharges (sourceA2677 + difference 5 5) (sourceB2677 + difference 5 5) sourceC2677) = raw37421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2677 sourceB2677 sourceC2677 difference raw37421; decide +kernel
    rw [ha]
    exact (canonical37421 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2677 + sourceB2677) sourceC2677) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (doubleCharges (sourceA2677 + sourceB2677) sourceC2677) = raw37412 := by
      apply Matrix.ext; unfold doubleCharges sourceA2677 sourceB2677 sourceC2677 raw37412; decide +kernel
    rw [ha]
    exact (canonical37412 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2677 sourceB2677 sourceC2677
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2677, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2678 : Charge := ![2, 0, 0, -1, -1, 0]
def sourceB2678 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC2678 : Charge := ![-5, 0, 0, 1, 1, 3]
def sourceForm2678 : Integer.Sparse Master := [(Sum.inr 657, 2), (Sum.inr 661, 1), (Sum.inr 669, 2), (Sum.inr 1509, 1), (Sum.inr 4058, -1)]

theorem sourceEq2678 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2678 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2678 + difference 0 0) (sourceB2678 + difference 0 0) sourceC2678) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1509) := by
    have ha : (tripleCharges (sourceA2678 + difference 0 0) (sourceB2678 + difference 0 0) sourceC2678) = raw37422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2678 sourceB2678 sourceC2678 difference raw37422; decide +kernel
    rw [ha]
    exact (canonical37422 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2678 + difference 1 0) (sourceB2678 + difference 0 1) sourceC2678) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 657) := by
    have ha : (tripleCharges (sourceA2678 + difference 1 0) (sourceB2678 + difference 0 1) sourceC2678) = raw37437 := by
      apply Matrix.ext; unfold tripleCharges sourceA2678 sourceB2678 sourceC2678 difference raw37437; decide +kernel
    rw [ha]
    exact (canonical37437 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2678 + difference 2 0) (sourceB2678 + difference 0 2) sourceC2678) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 657) := by
    have ha : (tripleCharges (sourceA2678 + difference 2 0) (sourceB2678 + difference 0 2) sourceC2678) = raw37438 := by
      apply Matrix.ext; unfold tripleCharges sourceA2678 sourceB2678 sourceC2678 difference raw37438; decide +kernel
    rw [ha]
    exact (canonical37438 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2678 + difference 3 0) (sourceB2678 + difference 0 3) sourceC2678) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 669) := by
    have ha : (tripleCharges (sourceA2678 + difference 3 0) (sourceB2678 + difference 0 3) sourceC2678) = raw37433 := by
      apply Matrix.ext; unfold tripleCharges sourceA2678 sourceB2678 sourceC2678 difference raw37433; decide +kernel
    rw [ha]
    exact (canonical37433 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2678 + difference 4 0) (sourceB2678 + difference 0 4) sourceC2678) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 669) := by
    have ha : (tripleCharges (sourceA2678 + difference 4 0) (sourceB2678 + difference 0 4) sourceC2678) = raw37439 := by
      apply Matrix.ext; unfold tripleCharges sourceA2678 sourceB2678 sourceC2678 difference raw37439; decide +kernel
    rw [ha]
    exact (canonical37439 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2678 + difference 5 0) (sourceB2678 + difference 0 5) sourceC2678) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 661) := by
    have ha : (tripleCharges (sourceA2678 + difference 5 0) (sourceB2678 + difference 0 5) sourceC2678) = raw37440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2678 sourceB2678 sourceC2678 difference raw37440; decide +kernel
    rw [ha]
    exact (canonical37440 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2678 + sourceB2678) sourceC2678) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4058) := by
    have ha : (doubleCharges (sourceA2678 + sourceB2678) sourceC2678) = raw37412 := by
      apply Matrix.ext; unfold doubleCharges sourceA2678 sourceB2678 sourceC2678 raw37412; decide +kernel
    rw [ha]
    exact (canonical37412 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2678 sourceB2678 sourceC2678
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2678, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2679 : Charge := ![2, 0, 0, -1, -2, 1]
def sourceB2679 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC2679 : Charge := ![-5, 0, 0, 1, 2, 2]
def sourceForm2679 : Integer.Sparse Master := [(Sum.inr 1511, 2), (Sum.inr 1513, 1), (Sum.inr 1519, 1), (Sum.inr 1525, 2), (Sum.inr 4059, -1)]

theorem sourceEq2679 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2679 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2679 + difference 0 5) (sourceB2679 + difference 5 0) sourceC2679) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1525) := by
    have ha : (tripleCharges (sourceA2679 + difference 0 5) (sourceB2679 + difference 5 0) sourceC2679) = raw37441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2679 sourceB2679 sourceC2679 difference raw37441; decide +kernel
    rw [ha]
    exact (canonical37441 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2679 + difference 1 5) (sourceB2679 + difference 5 1) sourceC2679) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1511) := by
    have ha : (tripleCharges (sourceA2679 + difference 1 5) (sourceB2679 + difference 5 1) sourceC2679) = raw37442 := by
      apply Matrix.ext; unfold tripleCharges sourceA2679 sourceB2679 sourceC2679 difference raw37442; decide +kernel
    rw [ha]
    exact (canonical37442 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2679 + difference 2 5) (sourceB2679 + difference 5 2) sourceC2679) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1511) := by
    have ha : (tripleCharges (sourceA2679 + difference 2 5) (sourceB2679 + difference 5 2) sourceC2679) = raw37443 := by
      apply Matrix.ext; unfold tripleCharges sourceA2679 sourceB2679 sourceC2679 difference raw37443; decide +kernel
    rw [ha]
    exact (canonical37443 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2679 + difference 3 5) (sourceB2679 + difference 5 3) sourceC2679) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1525) := by
    have ha : (tripleCharges (sourceA2679 + difference 3 5) (sourceB2679 + difference 5 3) sourceC2679) = raw37444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2679 sourceB2679 sourceC2679 difference raw37444; decide +kernel
    rw [ha]
    exact (canonical37444 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2679 + difference 4 5) (sourceB2679 + difference 5 4) sourceC2679) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA2679 + difference 4 5) (sourceB2679 + difference 5 4) sourceC2679) = raw37445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2679 sourceB2679 sourceC2679 difference raw37445; decide +kernel
    rw [ha]
    exact (canonical37445 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2679 + difference 5 5) (sourceB2679 + difference 5 5) sourceC2679) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1513) := by
    have ha : (tripleCharges (sourceA2679 + difference 5 5) (sourceB2679 + difference 5 5) sourceC2679) = raw37446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2679 sourceB2679 sourceC2679 difference raw37446; decide +kernel
    rw [ha]
    exact (canonical37446 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2679 + sourceB2679) sourceC2679) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (doubleCharges (sourceA2679 + sourceB2679) sourceC2679) = raw37447 := by
      apply Matrix.ext; unfold doubleCharges sourceA2679 sourceB2679 sourceC2679 raw37447; decide +kernel
    rw [ha]
    exact (canonical37447 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2679 sourceB2679 sourceC2679
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2679, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2680 : Charge := ![2, 0, 0, 1, -2, -1]
def sourceB2680 : Charge := ![3, 0, 0, -2, 0, -1]
def sourceC2680 : Charge := ![-5, 0, 0, 1, 2, 2]
def sourceForm2680 : Integer.Sparse Master := [(Sum.inr 1519, 1), (Sum.inr 1522, 2), (Sum.inr 1525, 1), (Sum.inr 1526, 1), (Sum.inr 1536, 1), (Sum.inr 4059, -1)]

theorem sourceEq2680 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2680 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2680 + difference 0 3) (sourceB2680 + difference 3 0) sourceC2680) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA2680 + difference 0 3) (sourceB2680 + difference 3 0) sourceC2680) = raw37448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2680 sourceB2680 sourceC2680 difference raw37448; decide +kernel
    rw [ha]
    exact (canonical37448 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2680 + difference 1 3) (sourceB2680 + difference 3 1) sourceC2680) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1522) := by
    have ha : (tripleCharges (sourceA2680 + difference 1 3) (sourceB2680 + difference 3 1) sourceC2680) = raw37449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2680 sourceB2680 sourceC2680 difference raw37449; decide +kernel
    rw [ha]
    exact (canonical37449 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2680 + difference 2 3) (sourceB2680 + difference 3 2) sourceC2680) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1522) := by
    have ha : (tripleCharges (sourceA2680 + difference 2 3) (sourceB2680 + difference 3 2) sourceC2680) = raw37450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2680 sourceB2680 sourceC2680 difference raw37450; decide +kernel
    rw [ha]
    exact (canonical37450 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2680 + difference 3 3) (sourceB2680 + difference 3 3) sourceC2680) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1526) := by
    have ha : (tripleCharges (sourceA2680 + difference 3 3) (sourceB2680 + difference 3 3) sourceC2680) = raw37451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2680 sourceB2680 sourceC2680 difference raw37451; decide +kernel
    rw [ha]
    exact (canonical37451 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2680 + difference 4 3) (sourceB2680 + difference 3 4) sourceC2680) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1536) := by
    have ha : (tripleCharges (sourceA2680 + difference 4 3) (sourceB2680 + difference 3 4) sourceC2680) = raw37452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2680 sourceB2680 sourceC2680 difference raw37452; decide +kernel
    rw [ha]
    exact (canonical37452 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2680 + difference 5 3) (sourceB2680 + difference 3 5) sourceC2680) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1525) := by
    have ha : (tripleCharges (sourceA2680 + difference 5 3) (sourceB2680 + difference 3 5) sourceC2680) = raw37444 := by
      apply Matrix.ext; unfold tripleCharges sourceA2680 sourceB2680 sourceC2680 difference raw37444; decide +kernel
    rw [ha]
    exact (canonical37444 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2680 + sourceB2680) sourceC2680) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (doubleCharges (sourceA2680 + sourceB2680) sourceC2680) = raw37447 := by
      apply Matrix.ext; unfold doubleCharges sourceA2680 sourceB2680 sourceC2680 raw37447; decide +kernel
    rw [ha]
    exact (canonical37447 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2680 sourceB2680 sourceC2680
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2680, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2681 : Charge := ![2, 0, 1, -1, -1, -1]
def sourceB2681 : Charge := ![3, 0, -1, 0, -1, -1]
def sourceC2681 : Charge := ![-5, 0, 0, 1, 2, 2]
def sourceForm2681 : Integer.Sparse Master := [(Sum.inr 1515, 2), (Sum.inr 1519, 2), (Sum.inr 1536, 2), (Sum.inr 4059, -1)]

theorem sourceEq2681 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2681 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2681 + difference 0 2) (sourceB2681 + difference 2 0) sourceC2681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1536) := by
    have ha : (tripleCharges (sourceA2681 + difference 0 2) (sourceB2681 + difference 2 0) sourceC2681) = raw37453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2681 sourceB2681 sourceC2681 difference raw37453; decide +kernel
    rw [ha]
    exact (canonical37453 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2681 + difference 1 2) (sourceB2681 + difference 2 1) sourceC2681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1515) := by
    have ha : (tripleCharges (sourceA2681 + difference 1 2) (sourceB2681 + difference 2 1) sourceC2681) = raw37454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2681 sourceB2681 sourceC2681 difference raw37454; decide +kernel
    rw [ha]
    exact (canonical37454 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2681 + difference 2 2) (sourceB2681 + difference 2 2) sourceC2681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1515) := by
    have ha : (tripleCharges (sourceA2681 + difference 2 2) (sourceB2681 + difference 2 2) sourceC2681) = raw37455 := by
      apply Matrix.ext; unfold tripleCharges sourceA2681 sourceB2681 sourceC2681 difference raw37455; decide +kernel
    rw [ha]
    exact (canonical37455 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2681 + difference 3 2) (sourceB2681 + difference 2 3) sourceC2681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1536) := by
    have ha : (tripleCharges (sourceA2681 + difference 3 2) (sourceB2681 + difference 2 3) sourceC2681) = raw37452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2681 sourceB2681 sourceC2681 difference raw37452; decide +kernel
    rw [ha]
    exact (canonical37452 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2681 + difference 4 2) (sourceB2681 + difference 2 4) sourceC2681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA2681 + difference 4 2) (sourceB2681 + difference 2 4) sourceC2681) = raw37456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2681 sourceB2681 sourceC2681 difference raw37456; decide +kernel
    rw [ha]
    exact (canonical37456 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2681 + difference 5 2) (sourceB2681 + difference 2 5) sourceC2681) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA2681 + difference 5 2) (sourceB2681 + difference 2 5) sourceC2681) = raw37445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2681 sourceB2681 sourceC2681 difference raw37445; decide +kernel
    rw [ha]
    exact (canonical37445 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2681 + sourceB2681) sourceC2681) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (doubleCharges (sourceA2681 + sourceB2681) sourceC2681) = raw37447 := by
      apply Matrix.ext; unfold doubleCharges sourceA2681 sourceB2681 sourceC2681 raw37447; decide +kernel
    rw [ha]
    exact (canonical37447 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2681 sourceB2681 sourceC2681
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2681, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2682 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2682 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC2682 : Charge := ![-5, 0, 0, 1, 2, 2]
def sourceForm2682 : Integer.Sparse Master := [(Sum.inr 675, 2), (Sum.inr 678, 1), (Sum.inr 679, 1), (Sum.inr 689, 1), (Sum.inr 1525, 1), (Sum.inr 4059, -1)]

theorem sourceEq2682 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2682 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2682 + difference 0 0) (sourceB2682 + difference 0 0) sourceC2682) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1525) := by
    have ha : (tripleCharges (sourceA2682 + difference 0 0) (sourceB2682 + difference 0 0) sourceC2682) = raw37457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2682 sourceB2682 sourceC2682 difference raw37457; decide +kernel
    rw [ha]
    exact (canonical37457 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2682 + difference 1 0) (sourceB2682 + difference 0 1) sourceC2682) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 675) := by
    have ha : (tripleCharges (sourceA2682 + difference 1 0) (sourceB2682 + difference 0 1) sourceC2682) = raw37458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2682 sourceB2682 sourceC2682 difference raw37458; decide +kernel
    rw [ha]
    exact (canonical37458 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2682 + difference 2 0) (sourceB2682 + difference 0 2) sourceC2682) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 675) := by
    have ha : (tripleCharges (sourceA2682 + difference 2 0) (sourceB2682 + difference 0 2) sourceC2682) = raw37459 := by
      apply Matrix.ext; unfold tripleCharges sourceA2682 sourceB2682 sourceC2682 difference raw37459; decide +kernel
    rw [ha]
    exact (canonical37459 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2682 + difference 3 0) (sourceB2682 + difference 0 3) sourceC2682) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 679) := by
    have ha : (tripleCharges (sourceA2682 + difference 3 0) (sourceB2682 + difference 0 3) sourceC2682) = raw37460 := by
      apply Matrix.ext; unfold tripleCharges sourceA2682 sourceB2682 sourceC2682 difference raw37460; decide +kernel
    rw [ha]
    exact (canonical37460 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2682 + difference 4 0) (sourceB2682 + difference 0 4) sourceC2682) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 678) := by
    have ha : (tripleCharges (sourceA2682 + difference 4 0) (sourceB2682 + difference 0 4) sourceC2682) = raw37461 := by
      apply Matrix.ext; unfold tripleCharges sourceA2682 sourceB2682 sourceC2682 difference raw37461; decide +kernel
    rw [ha]
    exact (canonical37461 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2682 + difference 5 0) (sourceB2682 + difference 0 5) sourceC2682) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 689) := by
    have ha : (tripleCharges (sourceA2682 + difference 5 0) (sourceB2682 + difference 0 5) sourceC2682) = raw37462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2682 sourceB2682 sourceC2682 difference raw37462; decide +kernel
    rw [ha]
    exact (canonical37462 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2682 + sourceB2682) sourceC2682) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (doubleCharges (sourceA2682 + sourceB2682) sourceC2682) = raw37447 := by
      apply Matrix.ext; unfold doubleCharges sourceA2682 sourceB2682 sourceC2682 raw37447; decide +kernel
    rw [ha]
    exact (canonical37447 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2682 sourceB2682 sourceC2682
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2682, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2683 : Charge := ![2, 0, 0, 0, 0, -2]
def sourceB2683 : Charge := ![3, 0, 0, -1, -2, 0]
def sourceC2683 : Charge := ![-5, 0, 0, 1, 2, 2]
def sourceForm2683 : Integer.Sparse Master := [(Sum.inr 689, 1), (Sum.inr 1493, 2), (Sum.inr 1519, 1), (Sum.inr 1525, 1), (Sum.inr 1536, 1), (Sum.inr 4059, -1)]

theorem sourceEq2683 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2683 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2683 + difference 5 0) (sourceB2683 + difference 0 5) sourceC2683) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 689) := by
    have ha : (tripleCharges (sourceA2683 + difference 5 0) (sourceB2683 + difference 0 5) sourceC2683) = raw37462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2683 sourceB2683 sourceC2683 difference raw37462; decide +kernel
    rw [ha]
    exact (canonical37462 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2683 + difference 5 1) (sourceB2683 + difference 1 5) sourceC2683) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1493) := by
    have ha : (tripleCharges (sourceA2683 + difference 5 1) (sourceB2683 + difference 1 5) sourceC2683) = raw37463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2683 sourceB2683 sourceC2683 difference raw37463; decide +kernel
    rw [ha]
    exact (canonical37463 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2683 + difference 5 2) (sourceB2683 + difference 2 5) sourceC2683) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1493) := by
    have ha : (tripleCharges (sourceA2683 + difference 5 2) (sourceB2683 + difference 2 5) sourceC2683) = raw37464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2683 sourceB2683 sourceC2683 difference raw37464; decide +kernel
    rw [ha]
    exact (canonical37464 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2683 + difference 5 3) (sourceB2683 + difference 3 5) sourceC2683) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA2683 + difference 5 3) (sourceB2683 + difference 3 5) sourceC2683) = raw37456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2683 sourceB2683 sourceC2683 difference raw37456; decide +kernel
    rw [ha]
    exact (canonical37456 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2683 + difference 5 4) (sourceB2683 + difference 4 5) sourceC2683) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1536) := by
    have ha : (tripleCharges (sourceA2683 + difference 5 4) (sourceB2683 + difference 4 5) sourceC2683) = raw37452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2683 sourceB2683 sourceC2683 difference raw37452; decide +kernel
    rw [ha]
    exact (canonical37452 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2683 + difference 5 5) (sourceB2683 + difference 5 5) sourceC2683) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1525) := by
    have ha : (tripleCharges (sourceA2683 + difference 5 5) (sourceB2683 + difference 5 5) sourceC2683) = raw37457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2683 sourceB2683 sourceC2683 difference raw37457; decide +kernel
    rw [ha]
    exact (canonical37457 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2683 + sourceB2683) sourceC2683) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (doubleCharges (sourceA2683 + sourceB2683) sourceC2683) = raw37447 := by
      apply Matrix.ext; unfold doubleCharges sourceA2683 sourceB2683 sourceC2683 raw37447; decide +kernel
    rw [ha]
    exact (canonical37447 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2683 sourceB2683 sourceC2683
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2683, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2684 : Charge := ![2, 0, 0, 0, -1, -1]
def sourceB2684 : Charge := ![3, 0, 0, -1, -1, -1]
def sourceC2684 : Charge := ![-5, 0, 0, 1, 2, 2]
def sourceForm2684 : Integer.Sparse Master := [(Sum.inr 682, 2), (Sum.inr 689, 2), (Sum.inr 692, 1), (Sum.inr 1536, 1), (Sum.inr 4059, -1)]

theorem sourceEq2684 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2684 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2684 + difference 0 0) (sourceB2684 + difference 0 0) sourceC2684) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1536) := by
    have ha : (tripleCharges (sourceA2684 + difference 0 0) (sourceB2684 + difference 0 0) sourceC2684) = raw37452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2684 sourceB2684 sourceC2684 difference raw37452; decide +kernel
    rw [ha]
    exact (canonical37452 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2684 + difference 1 0) (sourceB2684 + difference 0 1) sourceC2684) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 682) := by
    have ha : (tripleCharges (sourceA2684 + difference 1 0) (sourceB2684 + difference 0 1) sourceC2684) = raw37465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2684 sourceB2684 sourceC2684 difference raw37465; decide +kernel
    rw [ha]
    exact (canonical37465 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2684 + difference 2 0) (sourceB2684 + difference 0 2) sourceC2684) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 682) := by
    have ha : (tripleCharges (sourceA2684 + difference 2 0) (sourceB2684 + difference 0 2) sourceC2684) = raw37466 := by
      apply Matrix.ext; unfold tripleCharges sourceA2684 sourceB2684 sourceC2684 difference raw37466; decide +kernel
    rw [ha]
    exact (canonical37466 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2684 + difference 3 0) (sourceB2684 + difference 0 3) sourceC2684) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 692) := by
    have ha : (tripleCharges (sourceA2684 + difference 3 0) (sourceB2684 + difference 0 3) sourceC2684) = raw37467 := by
      apply Matrix.ext; unfold tripleCharges sourceA2684 sourceB2684 sourceC2684 difference raw37467; decide +kernel
    rw [ha]
    exact (canonical37467 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2684 + difference 4 0) (sourceB2684 + difference 0 4) sourceC2684) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 689) := by
    have ha : (tripleCharges (sourceA2684 + difference 4 0) (sourceB2684 + difference 0 4) sourceC2684) = raw37462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2684 sourceB2684 sourceC2684 difference raw37462; decide +kernel
    rw [ha]
    exact (canonical37462 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2684 + difference 5 0) (sourceB2684 + difference 0 5) sourceC2684) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 689) := by
    have ha : (tripleCharges (sourceA2684 + difference 5 0) (sourceB2684 + difference 0 5) sourceC2684) = raw37468 := by
      apply Matrix.ext; unfold tripleCharges sourceA2684 sourceB2684 sourceC2684 difference raw37468; decide +kernel
    rw [ha]
    exact (canonical37468 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2684 + sourceB2684) sourceC2684) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (doubleCharges (sourceA2684 + sourceB2684) sourceC2684) = raw37447 := by
      apply Matrix.ext; unfold doubleCharges sourceA2684 sourceB2684 sourceC2684 raw37447; decide +kernel
    rw [ha]
    exact (canonical37447 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2684 sourceB2684 sourceC2684
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2684, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2685 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceB2685 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2685 : Charge := ![-5, 0, 0, 1, 2, 2]
def sourceForm2685 : Integer.Sparse Master := [(Sum.inr 664, 2), (Sum.inr 670, 1), (Sum.inr 672, 1), (Sum.inr 689, 1), (Sum.inr 1519, 1), (Sum.inr 4059, -1)]

theorem sourceEq2685 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2685 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2685 + difference 0 0) (sourceB2685 + difference 0 0) sourceC2685) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA2685 + difference 0 0) (sourceB2685 + difference 0 0) sourceC2685) = raw37456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2685 sourceB2685 sourceC2685 difference raw37456; decide +kernel
    rw [ha]
    exact (canonical37456 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2685 + difference 1 0) (sourceB2685 + difference 0 1) sourceC2685) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 664) := by
    have ha : (tripleCharges (sourceA2685 + difference 1 0) (sourceB2685 + difference 0 1) sourceC2685) = raw37469 := by
      apply Matrix.ext; unfold tripleCharges sourceA2685 sourceB2685 sourceC2685 difference raw37469; decide +kernel
    rw [ha]
    exact (canonical37469 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2685 + difference 2 0) (sourceB2685 + difference 0 2) sourceC2685) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 664) := by
    have ha : (tripleCharges (sourceA2685 + difference 2 0) (sourceB2685 + difference 0 2) sourceC2685) = raw37470 := by
      apply Matrix.ext; unfold tripleCharges sourceA2685 sourceB2685 sourceC2685 difference raw37470; decide +kernel
    rw [ha]
    exact (canonical37470 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2685 + difference 3 0) (sourceB2685 + difference 0 3) sourceC2685) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 689) := by
    have ha : (tripleCharges (sourceA2685 + difference 3 0) (sourceB2685 + difference 0 3) sourceC2685) = raw37462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2685 sourceB2685 sourceC2685 difference raw37462; decide +kernel
    rw [ha]
    exact (canonical37462 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2685 + difference 4 0) (sourceB2685 + difference 0 4) sourceC2685) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 670) := by
    have ha : (tripleCharges (sourceA2685 + difference 4 0) (sourceB2685 + difference 0 4) sourceC2685) = raw37471 := by
      apply Matrix.ext; unfold tripleCharges sourceA2685 sourceB2685 sourceC2685 difference raw37471; decide +kernel
    rw [ha]
    exact (canonical37471 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2685 + difference 5 0) (sourceB2685 + difference 0 5) sourceC2685) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 672) := by
    have ha : (tripleCharges (sourceA2685 + difference 5 0) (sourceB2685 + difference 0 5) sourceC2685) = raw37472 := by
      apply Matrix.ext; unfold tripleCharges sourceA2685 sourceB2685 sourceC2685 difference raw37472; decide +kernel
    rw [ha]
    exact (canonical37472 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2685 + sourceB2685) sourceC2685) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (doubleCharges (sourceA2685 + sourceB2685) sourceC2685) = raw37447 := by
      apply Matrix.ext; unfold doubleCharges sourceA2685 sourceB2685 sourceC2685 raw37447; decide +kernel
    rw [ha]
    exact (canonical37447 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2685 sourceB2685 sourceC2685
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2685, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2686 : Charge := ![2, 0, 0, -1, 0, -1]
def sourceB2686 : Charge := ![3, 0, 0, 0, -2, -1]
def sourceC2686 : Charge := ![-5, 0, 0, 1, 2, 2]
def sourceForm2686 : Integer.Sparse Master := [(Sum.inr 672, 1), (Sum.inr 1490, 2), (Sum.inr 1500, 1), (Sum.inr 1519, 2), (Sum.inr 4059, -1)]

theorem sourceEq2686 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2686 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2686 + difference 5 0) (sourceB2686 + difference 0 5) sourceC2686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 672) := by
    have ha : (tripleCharges (sourceA2686 + difference 5 0) (sourceB2686 + difference 0 5) sourceC2686) = raw37472 := by
      apply Matrix.ext; unfold tripleCharges sourceA2686 sourceB2686 sourceC2686 difference raw37472; decide +kernel
    rw [ha]
    exact (canonical37472 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2686 + difference 5 1) (sourceB2686 + difference 1 5) sourceC2686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1490) := by
    have ha : (tripleCharges (sourceA2686 + difference 5 1) (sourceB2686 + difference 1 5) sourceC2686) = raw37473 := by
      apply Matrix.ext; unfold tripleCharges sourceA2686 sourceB2686 sourceC2686 difference raw37473; decide +kernel
    rw [ha]
    exact (canonical37473 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2686 + difference 5 2) (sourceB2686 + difference 2 5) sourceC2686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1490) := by
    have ha : (tripleCharges (sourceA2686 + difference 5 2) (sourceB2686 + difference 2 5) sourceC2686) = raw37474 := by
      apply Matrix.ext; unfold tripleCharges sourceA2686 sourceB2686 sourceC2686 difference raw37474; decide +kernel
    rw [ha]
    exact (canonical37474 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2686 + difference 5 3) (sourceB2686 + difference 3 5) sourceC2686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1500) := by
    have ha : (tripleCharges (sourceA2686 + difference 5 3) (sourceB2686 + difference 3 5) sourceC2686) = raw37475 := by
      apply Matrix.ext; unfold tripleCharges sourceA2686 sourceB2686 sourceC2686 difference raw37475; decide +kernel
    rw [ha]
    exact (canonical37475 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2686 + difference 5 4) (sourceB2686 + difference 4 5) sourceC2686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA2686 + difference 5 4) (sourceB2686 + difference 4 5) sourceC2686) = raw37445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2686 sourceB2686 sourceC2686 difference raw37445; decide +kernel
    rw [ha]
    exact (canonical37445 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2686 + difference 5 5) (sourceB2686 + difference 5 5) sourceC2686) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1519) := by
    have ha : (tripleCharges (sourceA2686 + difference 5 5) (sourceB2686 + difference 5 5) sourceC2686) = raw37456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2686 sourceB2686 sourceC2686 difference raw37456; decide +kernel
    rw [ha]
    exact (canonical37456 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2686 + sourceB2686) sourceC2686) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4059) := by
    have ha : (doubleCharges (sourceA2686 + sourceB2686) sourceC2686) = raw37447 := by
      apply Matrix.ext; unfold doubleCharges sourceA2686 sourceB2686 sourceC2686 raw37447; decide +kernel
    rw [ha]
    exact (canonical37447 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2686 sourceB2686 sourceC2686
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2686, Integer.Sparse.eval]
  linarith only [hs]

def sourceA2687 : Charge := ![2, 0, -1, -1, -1, 1]
def sourceB2687 : Charge := ![3, 0, 0, 0, 0, -3]
def sourceC2687 : Charge := ![-5, 0, 1, 1, 1, 2]
def sourceForm2687 : Integer.Sparse Master := [(Sum.inr 1501, 1), (Sum.inr 1503, 1), (Sum.inr 1507, 3), (Sum.inr 1524, 1), (Sum.inr 4057, -1)]

theorem sourceEq2687 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2687 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2687 + difference 0 5) (sourceB2687 + difference 5 0) sourceC2687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1524) := by
    have ha : (tripleCharges (sourceA2687 + difference 0 5) (sourceB2687 + difference 5 0) sourceC2687) = raw37476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2687 sourceB2687 sourceC2687 difference raw37476; decide +kernel
    rw [ha]
    exact (canonical37476 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2687 + difference 1 5) (sourceB2687 + difference 5 1) sourceC2687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1501) := by
    have ha : (tripleCharges (sourceA2687 + difference 1 5) (sourceB2687 + difference 5 1) sourceC2687) = raw37477 := by
      apply Matrix.ext; unfold tripleCharges sourceA2687 sourceB2687 sourceC2687 difference raw37477; decide +kernel
    rw [ha]
    exact (canonical37477 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2687 + difference 2 5) (sourceB2687 + difference 5 2) sourceC2687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1507) := by
    have ha : (tripleCharges (sourceA2687 + difference 2 5) (sourceB2687 + difference 5 2) sourceC2687) = raw37478 := by
      apply Matrix.ext; unfold tripleCharges sourceA2687 sourceB2687 sourceC2687 difference raw37478; decide +kernel
    rw [ha]
    exact (canonical37478 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2687 + difference 3 5) (sourceB2687 + difference 5 3) sourceC2687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1507) := by
    have ha : (tripleCharges (sourceA2687 + difference 3 5) (sourceB2687 + difference 5 3) sourceC2687) = raw37479 := by
      apply Matrix.ext; unfold tripleCharges sourceA2687 sourceB2687 sourceC2687 difference raw37479; decide +kernel
    rw [ha]
    exact (canonical37479 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2687 + difference 4 5) (sourceB2687 + difference 5 4) sourceC2687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1507) := by
    have ha : (tripleCharges (sourceA2687 + difference 4 5) (sourceB2687 + difference 5 4) sourceC2687) = raw37480 := by
      apply Matrix.ext; unfold tripleCharges sourceA2687 sourceB2687 sourceC2687 difference raw37480; decide +kernel
    rw [ha]
    exact (canonical37480 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2687 + difference 5 5) (sourceB2687 + difference 5 5) sourceC2687) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1503) := by
    have ha : (tripleCharges (sourceA2687 + difference 5 5) (sourceB2687 + difference 5 5) sourceC2687) = raw37481 := by
      apply Matrix.ext; unfold tripleCharges sourceA2687 sourceB2687 sourceC2687 difference raw37481; decide +kernel
    rw [ha]
    exact (canonical37481 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2687 + sourceB2687) sourceC2687) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4057) := by
    have ha : (doubleCharges (sourceA2687 + sourceB2687) sourceC2687) = raw37482 := by
      apply Matrix.ext; unfold doubleCharges sourceA2687 sourceB2687 sourceC2687 raw37482; decide +kernel
    rw [ha]
    exact (canonical37482 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2687 sourceB2687 sourceC2687
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2687, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
