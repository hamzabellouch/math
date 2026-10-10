import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SourceRules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical91
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical93
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical94
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical95
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical96
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical97
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical98
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Canonical99

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

def sourceA736 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB736 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC736 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceForm736 : Integer.Sparse Master := [(Sum.inr 1291, 1), (Sum.inr 2587, 1), (Sum.inr 2739, 1), (Sum.inr 2763, 1), (Sum.inr 2773, 1), (Sum.inr 2782, 1), (Sum.inr 4092, -1)]

theorem sourceEq736 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm736 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA736 + difference 2 0) (sourceB736 + difference 0 2) sourceC736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA736 + difference 2 0) (sourceB736 + difference 0 2) sourceC736) = raw12328 := by
      apply Matrix.ext; unfold tripleCharges sourceA736 sourceB736 sourceC736 difference raw12328; decide +kernel
    rw [ha]
    exact (canonical12328 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA736 + difference 2 1) (sourceB736 + difference 1 2) sourceC736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2587) := by
    have ha : (tripleCharges (sourceA736 + difference 2 1) (sourceB736 + difference 1 2) sourceC736) = raw12332 := by
      apply Matrix.ext; unfold tripleCharges sourceA736 sourceB736 sourceC736 difference raw12332; decide +kernel
    rw [ha]
    exact (canonical12332 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA736 + difference 2 2) (sourceB736 + difference 2 2) sourceC736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA736 + difference 2 2) (sourceB736 + difference 2 2) sourceC736) = raw12320 := by
      apply Matrix.ext; unfold tripleCharges sourceA736 sourceB736 sourceC736 difference raw12320; decide +kernel
    rw [ha]
    exact (canonical12320 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA736 + difference 2 3) (sourceB736 + difference 3 2) sourceC736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA736 + difference 2 3) (sourceB736 + difference 3 2) sourceC736) = raw12336 := by
      apply Matrix.ext; unfold tripleCharges sourceA736 sourceB736 sourceC736 difference raw12336; decide +kernel
    rw [ha]
    exact (canonical12336 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA736 + difference 2 4) (sourceB736 + difference 4 2) sourceC736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA736 + difference 2 4) (sourceB736 + difference 4 2) sourceC736) = raw12337 := by
      apply Matrix.ext; unfold tripleCharges sourceA736 sourceB736 sourceC736 difference raw12337; decide +kernel
    rw [ha]
    exact (canonical12337 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA736 + difference 2 5) (sourceB736 + difference 5 2) sourceC736) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA736 + difference 2 5) (sourceB736 + difference 5 2) sourceC736) = raw12338 := by
      apply Matrix.ext; unfold tripleCharges sourceA736 sourceB736 sourceC736 difference raw12338; decide +kernel
    rw [ha]
    exact (canonical12338 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA736 + sourceB736) sourceC736) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA736 + sourceB736) sourceC736) = raw12326 := by
      apply Matrix.ext; unfold doubleCharges sourceA736 sourceB736 sourceC736 raw12326; decide +kernel
    rw [ha]
    exact (canonical12326 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA736 sourceB736 sourceC736
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm736, Integer.Sparse.eval]
  linarith only [hs]

def sourceA737 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB737 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceC737 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceForm737 : Integer.Sparse Master := [(Sum.inr 2630, 1), (Sum.inr 2632, 1), (Sum.inr 2634, 1), (Sum.inr 2639, 1), (Sum.inr 2763, 1), (Sum.inr 3884, 1), (Sum.inr 4092, -1)]

theorem sourceEq737 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm737 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA737 + difference 0 2) (sourceB737 + difference 2 0) sourceC737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA737 + difference 0 2) (sourceB737 + difference 2 0) sourceC737) = raw12322 := by
      apply Matrix.ext; unfold tripleCharges sourceA737 sourceB737 sourceC737 difference raw12322; decide +kernel
    rw [ha]
    exact (canonical12322 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA737 + difference 1 2) (sourceB737 + difference 2 1) sourceC737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2630) := by
    have ha : (tripleCharges (sourceA737 + difference 1 2) (sourceB737 + difference 2 1) sourceC737) = raw12339 := by
      apply Matrix.ext; unfold tripleCharges sourceA737 sourceB737 sourceC737 difference raw12339; decide +kernel
    rw [ha]
    exact (canonical12339 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA737 + difference 2 2) (sourceB737 + difference 2 2) sourceC737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA737 + difference 2 2) (sourceB737 + difference 2 2) sourceC737) = raw12320 := by
      apply Matrix.ext; unfold tripleCharges sourceA737 sourceB737 sourceC737 difference raw12320; decide +kernel
    rw [ha]
    exact (canonical12320 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA737 + difference 3 2) (sourceB737 + difference 2 3) sourceC737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2639) := by
    have ha : (tripleCharges (sourceA737 + difference 3 2) (sourceB737 + difference 2 3) sourceC737) = raw12340 := by
      apply Matrix.ext; unfold tripleCharges sourceA737 sourceB737 sourceC737 difference raw12340; decide +kernel
    rw [ha]
    exact (canonical12340 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA737 + difference 4 2) (sourceB737 + difference 2 4) sourceC737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2634) := by
    have ha : (tripleCharges (sourceA737 + difference 4 2) (sourceB737 + difference 2 4) sourceC737) = raw12341 := by
      apply Matrix.ext; unfold tripleCharges sourceA737 sourceB737 sourceC737 difference raw12341; decide +kernel
    rw [ha]
    exact (canonical12341 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA737 + difference 5 2) (sourceB737 + difference 2 5) sourceC737) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2632) := by
    have ha : (tripleCharges (sourceA737 + difference 5 2) (sourceB737 + difference 2 5) sourceC737) = raw12342 := by
      apply Matrix.ext; unfold tripleCharges sourceA737 sourceB737 sourceC737 difference raw12342; decide +kernel
    rw [ha]
    exact (canonical12342 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA737 + sourceB737) sourceC737) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA737 + sourceB737) sourceC737) = raw12326 := by
      apply Matrix.ext; unfold doubleCharges sourceA737 sourceB737 sourceC737 raw12326; decide +kernel
    rw [ha]
    exact (canonical12326 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA737 sourceB737 sourceC737
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm737, Integer.Sparse.eval]
  linarith only [hs]

def sourceA738 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB738 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC738 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceForm738 : Integer.Sparse Master := [(Sum.inr 4449, 1), (Sum.inr 4450, 1), (Sum.inr 4453, 1), (Sum.inr 4459, 1), (Sum.inr 4487, 1), (Sum.inr 5069, 1), (Sum.inr 5071, 1), (Sum.inr 5074, 1), (Sum.inr 5092, 1), (Sum.inr 5140, 1), (Sum.inr 5160, 1), (Sum.inr 5161, 2), (Sum.inr 5164, 1), (Sum.inr 5170, 1), (Sum.inr 5226, 1), (Sum.inr 5229, 1), (Sum.inr 5236, 1), (Sum.inr 5255, 1), (Sum.inr 5260, 1), (Sum.inr 5269, 1), (Sum.inr 5281, 1), (Sum.inr 5282, 1), (Sum.inr 5284, 1), (Sum.inr 5289, 1), (Sum.inr 5438, 1), (Sum.inr 5480, 1), (Sum.inr 5484, 2), (Sum.inr 5485, 1)]

theorem sourceEq738 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm738 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA738 + difference 0 1) (sourceB738 + difference 1 0) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5480) := by
    have ha : (tripleCharges (sourceA738 + difference 0 1) (sourceB738 + difference 1 0) sourceC738) = raw12343 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12343; decide +kernel
    rw [ha]
    exact (canonical12343 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA738 + difference 0 2) (sourceB738 + difference 2 0) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA738 + difference 0 2) (sourceB738 + difference 2 0) sourceC738) = raw12344 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12344; decide +kernel
    rw [ha]
    exact (canonical12344 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA738 + difference 0 3) (sourceB738 + difference 3 0) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5438) := by
    have ha : (tripleCharges (sourceA738 + difference 0 3) (sourceB738 + difference 3 0) sourceC738) = raw12345 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12345; decide +kernel
    rw [ha]
    exact (canonical12345 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA738 + difference 0 4) (sourceB738 + difference 4 0) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5484) := by
    have ha : (tripleCharges (sourceA738 + difference 0 4) (sourceB738 + difference 4 0) sourceC738) = raw12346 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12346; decide +kernel
    rw [ha]
    exact (canonical12346 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA738 + difference 0 5) (sourceB738 + difference 5 0) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5485) := by
    have ha : (tripleCharges (sourceA738 + difference 0 5) (sourceB738 + difference 5 0) sourceC738) = raw12347 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12347; decide +kernel
    rw [ha]
    exact (canonical12347 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA738 + difference 1 0) (sourceB738 + difference 0 1) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4449) := by
    have ha : (tripleCharges (sourceA738 + difference 1 0) (sourceB738 + difference 0 1) sourceC738) = raw12348 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12348; decide +kernel
    rw [ha]
    exact (canonical12348 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA738 + difference 1 2) (sourceB738 + difference 2 1) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA738 + difference 1 2) (sourceB738 + difference 2 1) sourceC738) = raw12349 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12349; decide +kernel
    rw [ha]
    exact (canonical12349 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA738 + difference 1 3) (sourceB738 + difference 3 1) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5226) := by
    have ha : (tripleCharges (sourceA738 + difference 1 3) (sourceB738 + difference 3 1) sourceC738) = raw12350 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12350; decide +kernel
    rw [ha]
    exact (canonical12350 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA738 + difference 1 4) (sourceB738 + difference 4 1) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA738 + difference 1 4) (sourceB738 + difference 4 1) sourceC738) = raw12351 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12351; decide +kernel
    rw [ha]
    exact (canonical12351 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA738 + difference 1 5) (sourceB738 + difference 5 1) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA738 + difference 1 5) (sourceB738 + difference 5 1) sourceC738) = raw12352 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12352; decide +kernel
    rw [ha]
    exact (canonical12352 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA738 + difference 2 0) (sourceB738 + difference 0 2) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4487) := by
    have ha : (tripleCharges (sourceA738 + difference 2 0) (sourceB738 + difference 0 2) sourceC738) = raw12353 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12353; decide +kernel
    rw [ha]
    exact (canonical12353 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA738 + difference 2 1) (sourceB738 + difference 1 2) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5092) := by
    have ha : (tripleCharges (sourceA738 + difference 2 1) (sourceB738 + difference 1 2) sourceC738) = raw12354 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12354; decide +kernel
    rw [ha]
    exact (canonical12354 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA738 + difference 2 3) (sourceB738 + difference 3 2) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5236) := by
    have ha : (tripleCharges (sourceA738 + difference 2 3) (sourceB738 + difference 3 2) sourceC738) = raw12355 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12355; decide +kernel
    rw [ha]
    exact (canonical12355 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA738 + difference 2 4) (sourceB738 + difference 4 2) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5269) := by
    have ha : (tripleCharges (sourceA738 + difference 2 4) (sourceB738 + difference 4 2) sourceC738) = raw12356 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12356; decide +kernel
    rw [ha]
    exact (canonical12356 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA738 + difference 2 5) (sourceB738 + difference 5 2) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA738 + difference 2 5) (sourceB738 + difference 5 2) sourceC738) = raw12357 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12357; decide +kernel
    rw [ha]
    exact (canonical12357 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA738 + difference 3 0) (sourceB738 + difference 0 3) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4459) := by
    have ha : (tripleCharges (sourceA738 + difference 3 0) (sourceB738 + difference 0 3) sourceC738) = raw12358 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12358; decide +kernel
    rw [ha]
    exact (canonical12358 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA738 + difference 3 1) (sourceB738 + difference 1 3) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5074) := by
    have ha : (tripleCharges (sourceA738 + difference 3 1) (sourceB738 + difference 1 3) sourceC738) = raw12359 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12359; decide +kernel
    rw [ha]
    exact (canonical12359 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA738 + difference 3 2) (sourceB738 + difference 2 3) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5170) := by
    have ha : (tripleCharges (sourceA738 + difference 3 2) (sourceB738 + difference 2 3) sourceC738) = raw12360 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12360; decide +kernel
    rw [ha]
    exact (canonical12360 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA738 + difference 3 4) (sourceB738 + difference 4 3) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5260) := by
    have ha : (tripleCharges (sourceA738 + difference 3 4) (sourceB738 + difference 4 3) sourceC738) = raw12361 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12361; decide +kernel
    rw [ha]
    exact (canonical12361 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA738 + difference 3 5) (sourceB738 + difference 5 3) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA738 + difference 3 5) (sourceB738 + difference 5 3) sourceC738) = raw12362 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12362; decide +kernel
    rw [ha]
    exact (canonical12362 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA738 + difference 4 0) (sourceB738 + difference 0 4) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4453) := by
    have ha : (tripleCharges (sourceA738 + difference 4 0) (sourceB738 + difference 0 4) sourceC738) = raw12363 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12363; decide +kernel
    rw [ha]
    exact (canonical12363 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA738 + difference 4 1) (sourceB738 + difference 1 4) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5071) := by
    have ha : (tripleCharges (sourceA738 + difference 4 1) (sourceB738 + difference 1 4) sourceC738) = raw12364 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12364; decide +kernel
    rw [ha]
    exact (canonical12364 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA738 + difference 4 2) (sourceB738 + difference 2 4) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5164) := by
    have ha : (tripleCharges (sourceA738 + difference 4 2) (sourceB738 + difference 2 4) sourceC738) = raw12365 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12365; decide +kernel
    rw [ha]
    exact (canonical12365 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA738 + difference 4 3) (sourceB738 + difference 3 4) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5229) := by
    have ha : (tripleCharges (sourceA738 + difference 4 3) (sourceB738 + difference 3 4) sourceC738) = raw12366 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12366; decide +kernel
    rw [ha]
    exact (canonical12366 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA738 + difference 4 5) (sourceB738 + difference 5 4) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5282) := by
    have ha : (tripleCharges (sourceA738 + difference 4 5) (sourceB738 + difference 5 4) sourceC738) = raw12367 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12367; decide +kernel
    rw [ha]
    exact (canonical12367 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA738 + difference 5 0) (sourceB738 + difference 0 5) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4450) := by
    have ha : (tripleCharges (sourceA738 + difference 5 0) (sourceB738 + difference 0 5) sourceC738) = raw12368 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12368; decide +kernel
    rw [ha]
    exact (canonical12368 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA738 + difference 5 1) (sourceB738 + difference 1 5) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5069) := by
    have ha : (tripleCharges (sourceA738 + difference 5 1) (sourceB738 + difference 1 5) sourceC738) = raw12369 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12369; decide +kernel
    rw [ha]
    exact (canonical12369 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA738 + difference 5 2) (sourceB738 + difference 2 5) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA738 + difference 5 2) (sourceB738 + difference 2 5) sourceC738) = raw12370 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12370; decide +kernel
    rw [ha]
    exact (canonical12370 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA738 + difference 5 3) (sourceB738 + difference 3 5) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5140) := by
    have ha : (tripleCharges (sourceA738 + difference 5 3) (sourceB738 + difference 3 5) sourceC738) = raw12371 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12371; decide +kernel
    rw [ha]
    exact (canonical12371 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA738 + difference 5 4) (sourceB738 + difference 4 5) sourceC738) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5161) := by
    have ha : (tripleCharges (sourceA738 + difference 5 4) (sourceB738 + difference 4 5) sourceC738) = raw12372 := by
      apply Matrix.ext; unfold tripleCharges sourceA738 sourceB738 sourceC738 difference raw12372; decide +kernel
    rw [ha]
    exact (canonical12372 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA738 sourceB738 sourceC738
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm738, Integer.Sparse.eval]
  linarith only [hs]

def sourceA739 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB739 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC739 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceForm739 : Integer.Sparse Master := [(Sum.inr 1032, 1), (Sum.inr 1033, 1), (Sum.inr 1036, 1), (Sum.inr 1042, 1), (Sum.inr 1071, 1), (Sum.inr 2476, 1), (Sum.inr 2478, 1), (Sum.inr 2481, 1), (Sum.inr 2501, 1), (Sum.inr 2587, 1), (Sum.inr 2588, 1), (Sum.inr 2591, 1), (Sum.inr 2596, 1), (Sum.inr 2669, 1), (Sum.inr 2670, 1), (Sum.inr 2673, 1), (Sum.inr 2682, 1), (Sum.inr 2718, 1), (Sum.inr 2719, 1), (Sum.inr 2724, 1), (Sum.inr 2736, 1), (Sum.inr 2750, 1), (Sum.inr 2751, 1), (Sum.inr 2753, 1), (Sum.inr 2763, 1), (Sum.inr 3857, 1), (Sum.inr 3978, 1), (Sum.inr 3983, 1), (Sum.inr 3997, 1), (Sum.inr 3998, 1)]

theorem sourceEq739 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm739 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA739 + difference 0 1) (sourceB739 + difference 1 0) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA739 + difference 0 1) (sourceB739 + difference 1 0) sourceC739) = raw12373 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12373; decide +kernel
    rw [ha]
    exact (canonical12373 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA739 + difference 0 2) (sourceB739 + difference 2 0) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3997) := by
    have ha : (tripleCharges (sourceA739 + difference 0 2) (sourceB739 + difference 2 0) sourceC739) = raw12374 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12374; decide +kernel
    rw [ha]
    exact (canonical12374 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA739 + difference 0 3) (sourceB739 + difference 3 0) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA739 + difference 0 3) (sourceB739 + difference 3 0) sourceC739) = raw12375 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12375; decide +kernel
    rw [ha]
    exact (canonical12375 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA739 + difference 0 4) (sourceB739 + difference 4 0) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA739 + difference 0 4) (sourceB739 + difference 4 0) sourceC739) = raw12376 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12376; decide +kernel
    rw [ha]
    exact (canonical12376 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA739 + difference 0 5) (sourceB739 + difference 5 0) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3998) := by
    have ha : (tripleCharges (sourceA739 + difference 0 5) (sourceB739 + difference 5 0) sourceC739) = raw12377 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12377; decide +kernel
    rw [ha]
    exact (canonical12377 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA739 + difference 1 0) (sourceB739 + difference 0 1) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1032) := by
    have ha : (tripleCharges (sourceA739 + difference 1 0) (sourceB739 + difference 0 1) sourceC739) = raw12378 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12378; decide +kernel
    rw [ha]
    exact (canonical12378 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA739 + difference 1 2) (sourceB739 + difference 2 1) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2587) := by
    have ha : (tripleCharges (sourceA739 + difference 1 2) (sourceB739 + difference 2 1) sourceC739) = raw12379 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12379; decide +kernel
    rw [ha]
    exact (canonical12379 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA739 + difference 1 3) (sourceB739 + difference 3 1) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA739 + difference 1 3) (sourceB739 + difference 3 1) sourceC739) = raw12380 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12380; decide +kernel
    rw [ha]
    exact (canonical12380 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA739 + difference 1 4) (sourceB739 + difference 4 1) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA739 + difference 1 4) (sourceB739 + difference 4 1) sourceC739) = raw12381 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12381; decide +kernel
    rw [ha]
    exact (canonical12381 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA739 + difference 1 5) (sourceB739 + difference 5 1) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA739 + difference 1 5) (sourceB739 + difference 5 1) sourceC739) = raw12382 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12382; decide +kernel
    rw [ha]
    exact (canonical12382 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA739 + difference 2 0) (sourceB739 + difference 0 2) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1071) := by
    have ha : (tripleCharges (sourceA739 + difference 2 0) (sourceB739 + difference 0 2) sourceC739) = raw12383 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12383; decide +kernel
    rw [ha]
    exact (canonical12383 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA739 + difference 2 1) (sourceB739 + difference 1 2) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2501) := by
    have ha : (tripleCharges (sourceA739 + difference 2 1) (sourceB739 + difference 1 2) sourceC739) = raw12384 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12384; decide +kernel
    rw [ha]
    exact (canonical12384 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA739 + difference 2 3) (sourceB739 + difference 3 2) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2682) := by
    have ha : (tripleCharges (sourceA739 + difference 2 3) (sourceB739 + difference 3 2) sourceC739) = raw12385 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12385; decide +kernel
    rw [ha]
    exact (canonical12385 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA739 + difference 2 4) (sourceB739 + difference 4 2) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2736) := by
    have ha : (tripleCharges (sourceA739 + difference 2 4) (sourceB739 + difference 4 2) sourceC739) = raw12386 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12386; decide +kernel
    rw [ha]
    exact (canonical12386 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA739 + difference 2 5) (sourceB739 + difference 5 2) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA739 + difference 2 5) (sourceB739 + difference 5 2) sourceC739) = raw12387 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12387; decide +kernel
    rw [ha]
    exact (canonical12387 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA739 + difference 3 0) (sourceB739 + difference 0 3) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA739 + difference 3 0) (sourceB739 + difference 0 3) sourceC739) = raw12388 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12388; decide +kernel
    rw [ha]
    exact (canonical12388 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA739 + difference 3 1) (sourceB739 + difference 1 3) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA739 + difference 3 1) (sourceB739 + difference 1 3) sourceC739) = raw12389 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12389; decide +kernel
    rw [ha]
    exact (canonical12389 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA739 + difference 3 2) (sourceB739 + difference 2 3) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2596) := by
    have ha : (tripleCharges (sourceA739 + difference 3 2) (sourceB739 + difference 2 3) sourceC739) = raw12390 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12390; decide +kernel
    rw [ha]
    exact (canonical12390 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA739 + difference 3 4) (sourceB739 + difference 4 3) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA739 + difference 3 4) (sourceB739 + difference 4 3) sourceC739) = raw12391 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12391; decide +kernel
    rw [ha]
    exact (canonical12391 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA739 + difference 3 5) (sourceB739 + difference 5 3) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2753) := by
    have ha : (tripleCharges (sourceA739 + difference 3 5) (sourceB739 + difference 5 3) sourceC739) = raw12392 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12392; decide +kernel
    rw [ha]
    exact (canonical12392 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA739 + difference 4 0) (sourceB739 + difference 0 4) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1036) := by
    have ha : (tripleCharges (sourceA739 + difference 4 0) (sourceB739 + difference 0 4) sourceC739) = raw12393 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12393; decide +kernel
    rw [ha]
    exact (canonical12393 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA739 + difference 4 1) (sourceB739 + difference 1 4) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2478) := by
    have ha : (tripleCharges (sourceA739 + difference 4 1) (sourceB739 + difference 1 4) sourceC739) = raw12394 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12394; decide +kernel
    rw [ha]
    exact (canonical12394 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA739 + difference 4 2) (sourceB739 + difference 2 4) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2591) := by
    have ha : (tripleCharges (sourceA739 + difference 4 2) (sourceB739 + difference 2 4) sourceC739) = raw12395 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12395; decide +kernel
    rw [ha]
    exact (canonical12395 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA739 + difference 4 3) (sourceB739 + difference 3 4) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2673) := by
    have ha : (tripleCharges (sourceA739 + difference 4 3) (sourceB739 + difference 3 4) sourceC739) = raw12396 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12396; decide +kernel
    rw [ha]
    exact (canonical12396 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA739 + difference 4 5) (sourceB739 + difference 5 4) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA739 + difference 4 5) (sourceB739 + difference 5 4) sourceC739) = raw12397 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12397; decide +kernel
    rw [ha]
    exact (canonical12397 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA739 + difference 5 0) (sourceB739 + difference 0 5) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1033) := by
    have ha : (tripleCharges (sourceA739 + difference 5 0) (sourceB739 + difference 0 5) sourceC739) = raw12398 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12398; decide +kernel
    rw [ha]
    exact (canonical12398 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA739 + difference 5 1) (sourceB739 + difference 1 5) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2476) := by
    have ha : (tripleCharges (sourceA739 + difference 5 1) (sourceB739 + difference 1 5) sourceC739) = raw12399 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12399; decide +kernel
    rw [ha]
    exact (canonical12399 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA739 + difference 5 2) (sourceB739 + difference 2 5) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2588) := by
    have ha : (tripleCharges (sourceA739 + difference 5 2) (sourceB739 + difference 2 5) sourceC739) = raw12400 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12400; decide +kernel
    rw [ha]
    exact (canonical12400 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA739 + difference 5 3) (sourceB739 + difference 3 5) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA739 + difference 5 3) (sourceB739 + difference 3 5) sourceC739) = raw12401 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12401; decide +kernel
    rw [ha]
    exact (canonical12401 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA739 + difference 5 4) (sourceB739 + difference 4 5) sourceC739) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA739 + difference 5 4) (sourceB739 + difference 4 5) sourceC739) = raw12402 := by
      apply Matrix.ext; unfold tripleCharges sourceA739 sourceB739 sourceC739 difference raw12402; decide +kernel
    rw [ha]
    exact (canonical12402 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA739 sourceB739 sourceC739
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm739, Integer.Sparse.eval]
  linarith only [hs]

def sourceA740 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB740 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC740 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceForm740 : Integer.Sparse Master := [(Sum.inr 1636, 1), (Sum.inr 1637, 1), (Sum.inr 1641, 1), (Sum.inr 1646, 1), (Sum.inr 1714, 1), (Sum.inr 2550, 1), (Sum.inr 2560, 1), (Sum.inr 2588, 1), (Sum.inr 2719, 1), (Sum.inr 3376, 1), (Sum.inr 3380, 1), (Sum.inr 3392, 1), (Sum.inr 3442, 1), (Sum.inr 3445, 1), (Sum.inr 3463, 1), (Sum.inr 3503, 1), (Sum.inr 3507, 1), (Sum.inr 3540, 1), (Sum.inr 3558, 1), (Sum.inr 3565, 1), (Sum.inr 3571, 1), (Sum.inr 3572, 1), (Sum.inr 3580, 1), (Sum.inr 3606, 1), (Sum.inr 3625, 1), (Sum.inr 3978, 1), (Sum.inr 3983, 1), (Sum.inr 3984, 1), (Sum.inr 3993, 1), (Sum.inr 3997, 1)]

theorem sourceEq740 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm740 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA740 + difference 0 1) (sourceB740 + difference 1 0) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA740 + difference 0 1) (sourceB740 + difference 1 0) sourceC740) = raw12403 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12403; decide +kernel
    rw [ha]
    exact (canonical12403 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA740 + difference 0 2) (sourceB740 + difference 2 0) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA740 + difference 0 2) (sourceB740 + difference 2 0) sourceC740) = raw12404 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12404; decide +kernel
    rw [ha]
    exact (canonical12404 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA740 + difference 0 3) (sourceB740 + difference 3 0) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3993) := by
    have ha : (tripleCharges (sourceA740 + difference 0 3) (sourceB740 + difference 3 0) sourceC740) = raw12405 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12405; decide +kernel
    rw [ha]
    exact (canonical12405 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA740 + difference 0 4) (sourceB740 + difference 4 0) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3997) := by
    have ha : (tripleCharges (sourceA740 + difference 0 4) (sourceB740 + difference 4 0) sourceC740) = raw12406 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12406; decide +kernel
    rw [ha]
    exact (canonical12406 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA740 + difference 0 5) (sourceB740 + difference 5 0) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3984) := by
    have ha : (tripleCharges (sourceA740 + difference 0 5) (sourceB740 + difference 5 0) sourceC740) = raw12407 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12407; decide +kernel
    rw [ha]
    exact (canonical12407 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA740 + difference 1 0) (sourceB740 + difference 0 1) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1636) := by
    have ha : (tripleCharges (sourceA740 + difference 1 0) (sourceB740 + difference 0 1) sourceC740) = raw12408 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12408; decide +kernel
    rw [ha]
    exact (canonical12408 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA740 + difference 1 2) (sourceB740 + difference 2 1) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA740 + difference 1 2) (sourceB740 + difference 2 1) sourceC740) = raw12409 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12409; decide +kernel
    rw [ha]
    exact (canonical12409 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA740 + difference 1 3) (sourceB740 + difference 3 1) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3376) := by
    have ha : (tripleCharges (sourceA740 + difference 1 3) (sourceB740 + difference 3 1) sourceC740) = raw12410 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12410; decide +kernel
    rw [ha]
    exact (canonical12410 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA740 + difference 1 4) (sourceB740 + difference 4 1) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA740 + difference 1 4) (sourceB740 + difference 4 1) sourceC740) = raw12411 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12411; decide +kernel
    rw [ha]
    exact (canonical12411 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA740 + difference 1 5) (sourceB740 + difference 5 1) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA740 + difference 1 5) (sourceB740 + difference 5 1) sourceC740) = raw12412 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12412; decide +kernel
    rw [ha]
    exact (canonical12412 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA740 + difference 2 0) (sourceB740 + difference 0 2) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1641) := by
    have ha : (tripleCharges (sourceA740 + difference 2 0) (sourceB740 + difference 0 2) sourceC740) = raw12413 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12413; decide +kernel
    rw [ha]
    exact (canonical12413 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA740 + difference 2 1) (sourceB740 + difference 1 2) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3442) := by
    have ha : (tripleCharges (sourceA740 + difference 2 1) (sourceB740 + difference 1 2) sourceC740) = raw12414 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12414; decide +kernel
    rw [ha]
    exact (canonical12414 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA740 + difference 2 3) (sourceB740 + difference 3 2) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3380) := by
    have ha : (tripleCharges (sourceA740 + difference 2 3) (sourceB740 + difference 3 2) sourceC740) = raw12415 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12415; decide +kernel
    rw [ha]
    exact (canonical12415 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA740 + difference 2 4) (sourceB740 + difference 4 2) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3507) := by
    have ha : (tripleCharges (sourceA740 + difference 2 4) (sourceB740 + difference 4 2) sourceC740) = raw12416 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12416; decide +kernel
    rw [ha]
    exact (canonical12416 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA740 + difference 2 5) (sourceB740 + difference 5 2) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA740 + difference 2 5) (sourceB740 + difference 5 2) sourceC740) = raw12417 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12417; decide +kernel
    rw [ha]
    exact (canonical12417 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA740 + difference 3 0) (sourceB740 + difference 0 3) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA740 + difference 3 0) (sourceB740 + difference 0 3) sourceC740) = raw12418 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12418; decide +kernel
    rw [ha]
    exact (canonical12418 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA740 + difference 3 1) (sourceB740 + difference 1 3) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3463) := by
    have ha : (tripleCharges (sourceA740 + difference 3 1) (sourceB740 + difference 1 3) sourceC740) = raw12419 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12419; decide +kernel
    rw [ha]
    exact (canonical12419 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA740 + difference 3 2) (sourceB740 + difference 2 3) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3606) := by
    have ha : (tripleCharges (sourceA740 + difference 3 2) (sourceB740 + difference 2 3) sourceC740) = raw12420 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12420; decide +kernel
    rw [ha]
    exact (canonical12420 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA740 + difference 3 4) (sourceB740 + difference 4 3) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA740 + difference 3 4) (sourceB740 + difference 4 3) sourceC740) = raw12421 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12421; decide +kernel
    rw [ha]
    exact (canonical12421 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA740 + difference 3 5) (sourceB740 + difference 5 3) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA740 + difference 3 5) (sourceB740 + difference 5 3) sourceC740) = raw12422 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12422; decide +kernel
    rw [ha]
    exact (canonical12422 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA740 + difference 4 0) (sourceB740 + difference 0 4) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1646) := by
    have ha : (tripleCharges (sourceA740 + difference 4 0) (sourceB740 + difference 0 4) sourceC740) = raw12423 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12423; decide +kernel
    rw [ha]
    exact (canonical12423 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA740 + difference 4 1) (sourceB740 + difference 1 4) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3445) := by
    have ha : (tripleCharges (sourceA740 + difference 4 1) (sourceB740 + difference 1 4) sourceC740) = raw12424 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12424; decide +kernel
    rw [ha]
    exact (canonical12424 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA740 + difference 4 2) (sourceB740 + difference 2 4) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3565) := by
    have ha : (tripleCharges (sourceA740 + difference 4 2) (sourceB740 + difference 2 4) sourceC740) = raw12425 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12425; decide +kernel
    rw [ha]
    exact (canonical12425 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA740 + difference 4 3) (sourceB740 + difference 3 4) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3392) := by
    have ha : (tripleCharges (sourceA740 + difference 4 3) (sourceB740 + difference 3 4) sourceC740) = raw12426 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12426; decide +kernel
    rw [ha]
    exact (canonical12426 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA740 + difference 4 5) (sourceB740 + difference 5 4) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA740 + difference 4 5) (sourceB740 + difference 5 4) sourceC740) = raw12427 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12427; decide +kernel
    rw [ha]
    exact (canonical12427 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA740 + difference 5 0) (sourceB740 + difference 0 5) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1637) := by
    have ha : (tripleCharges (sourceA740 + difference 5 0) (sourceB740 + difference 0 5) sourceC740) = raw12428 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12428; decide +kernel
    rw [ha]
    exact (canonical12428 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA740 + difference 5 1) (sourceB740 + difference 1 5) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2550) := by
    have ha : (tripleCharges (sourceA740 + difference 5 1) (sourceB740 + difference 1 5) sourceC740) = raw12429 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12429; decide +kernel
    rw [ha]
    exact (canonical12429 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA740 + difference 5 2) (sourceB740 + difference 2 5) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2719) := by
    have ha : (tripleCharges (sourceA740 + difference 5 2) (sourceB740 + difference 2 5) sourceC740) = raw12430 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12430; decide +kernel
    rw [ha]
    exact (canonical12430 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA740 + difference 5 3) (sourceB740 + difference 3 5) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2560) := by
    have ha : (tripleCharges (sourceA740 + difference 5 3) (sourceB740 + difference 3 5) sourceC740) = raw12431 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12431; decide +kernel
    rw [ha]
    exact (canonical12431 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA740 + difference 5 4) (sourceB740 + difference 4 5) sourceC740) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2588) := by
    have ha : (tripleCharges (sourceA740 + difference 5 4) (sourceB740 + difference 4 5) sourceC740) = raw12432 := by
      apply Matrix.ext; unfold tripleCharges sourceA740 sourceB740 sourceC740 difference raw12432; decide +kernel
    rw [ha]
    exact (canonical12432 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA740 sourceB740 sourceC740
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm740, Integer.Sparse.eval]
  linarith only [hs]

def sourceA741 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB741 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC741 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceForm741 : Integer.Sparse Master := [(Sum.inr 3097, 1), (Sum.inr 3876, 1), (Sum.inr 3978, 1), (Sum.inr 3983, 2), (Sum.inr 4010, 1), (Sum.inr 4091, -1)]

theorem sourceEq741 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm741 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA741 + difference 0 0) (sourceB741 + difference 0 0) sourceC741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA741 + difference 0 0) (sourceB741 + difference 0 0) sourceC741) = raw12433 := by
      apply Matrix.ext; unfold tripleCharges sourceA741 sourceB741 sourceC741 difference raw12433; decide +kernel
    rw [ha]
    exact (canonical12433 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA741 + difference 0 1) (sourceB741 + difference 1 0) sourceC741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA741 + difference 0 1) (sourceB741 + difference 1 0) sourceC741) = raw12434 := by
      apply Matrix.ext; unfold tripleCharges sourceA741 sourceB741 sourceC741 difference raw12434; decide +kernel
    rw [ha]
    exact (canonical12434 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA741 + difference 0 2) (sourceB741 + difference 2 0) sourceC741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA741 + difference 0 2) (sourceB741 + difference 2 0) sourceC741) = raw12435 := by
      apply Matrix.ext; unfold tripleCharges sourceA741 sourceB741 sourceC741 difference raw12435; decide +kernel
    rw [ha]
    exact (canonical12435 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA741 + difference 0 3) (sourceB741 + difference 3 0) sourceC741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA741 + difference 0 3) (sourceB741 + difference 3 0) sourceC741) = raw12436 := by
      apply Matrix.ext; unfold tripleCharges sourceA741 sourceB741 sourceC741 difference raw12436; decide +kernel
    rw [ha]
    exact (canonical12436 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA741 + difference 0 4) (sourceB741 + difference 4 0) sourceC741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA741 + difference 0 4) (sourceB741 + difference 4 0) sourceC741) = raw12437 := by
      apply Matrix.ext; unfold tripleCharges sourceA741 sourceB741 sourceC741 difference raw12437; decide +kernel
    rw [ha]
    exact (canonical12437 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA741 + difference 0 5) (sourceB741 + difference 5 0) sourceC741) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4010) := by
    have ha : (tripleCharges (sourceA741 + difference 0 5) (sourceB741 + difference 5 0) sourceC741) = raw12438 := by
      apply Matrix.ext; unfold tripleCharges sourceA741 sourceB741 sourceC741 difference raw12438; decide +kernel
    rw [ha]
    exact (canonical12438 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA741 + sourceB741) sourceC741) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA741 + sourceB741) sourceC741) = raw12439 := by
      apply Matrix.ext; unfold doubleCharges sourceA741 sourceB741 sourceC741 raw12439; decide +kernel
    rw [ha]
    exact (canonical12439 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA741 sourceB741 sourceC741
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm741, Integer.Sparse.eval]
  linarith only [hs]

def sourceA742 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB742 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC742 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceForm742 : Integer.Sparse Master := [(Sum.inr 1403, 1), (Sum.inr 1406, 1), (Sum.inr 1407, 1), (Sum.inr 1415, 1), (Sum.inr 1439, 1), (Sum.inr 3097, 1), (Sum.inr 4091, -1)]

theorem sourceEq742 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm742 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA742 + difference 0 0) (sourceB742 + difference 0 0) sourceC742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA742 + difference 0 0) (sourceB742 + difference 0 0) sourceC742) = raw12433 := by
      apply Matrix.ext; unfold tripleCharges sourceA742 sourceB742 sourceC742 difference raw12433; decide +kernel
    rw [ha]
    exact (canonical12433 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA742 + difference 1 0) (sourceB742 + difference 0 1) sourceC742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1403) := by
    have ha : (tripleCharges (sourceA742 + difference 1 0) (sourceB742 + difference 0 1) sourceC742) = raw12440 := by
      apply Matrix.ext; unfold tripleCharges sourceA742 sourceB742 sourceC742 difference raw12440; decide +kernel
    rw [ha]
    exact (canonical12440 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA742 + difference 2 0) (sourceB742 + difference 0 2) sourceC742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1439) := by
    have ha : (tripleCharges (sourceA742 + difference 2 0) (sourceB742 + difference 0 2) sourceC742) = raw12441 := by
      apply Matrix.ext; unfold tripleCharges sourceA742 sourceB742 sourceC742 difference raw12441; decide +kernel
    rw [ha]
    exact (canonical12441 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA742 + difference 3 0) (sourceB742 + difference 0 3) sourceC742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA742 + difference 3 0) (sourceB742 + difference 0 3) sourceC742) = raw12442 := by
      apply Matrix.ext; unfold tripleCharges sourceA742 sourceB742 sourceC742 difference raw12442; decide +kernel
    rw [ha]
    exact (canonical12442 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA742 + difference 4 0) (sourceB742 + difference 0 4) sourceC742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1407) := by
    have ha : (tripleCharges (sourceA742 + difference 4 0) (sourceB742 + difference 0 4) sourceC742) = raw12443 := by
      apply Matrix.ext; unfold tripleCharges sourceA742 sourceB742 sourceC742 difference raw12443; decide +kernel
    rw [ha]
    exact (canonical12443 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA742 + difference 5 0) (sourceB742 + difference 0 5) sourceC742) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1415) := by
    have ha : (tripleCharges (sourceA742 + difference 5 0) (sourceB742 + difference 0 5) sourceC742) = raw12444 := by
      apply Matrix.ext; unfold tripleCharges sourceA742 sourceB742 sourceC742 difference raw12444; decide +kernel
    rw [ha]
    exact (canonical12444 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA742 + sourceB742) sourceC742) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA742 + sourceB742) sourceC742) = raw12439 := by
      apply Matrix.ext; unfold doubleCharges sourceA742 sourceB742 sourceC742 raw12439; decide +kernel
    rw [ha]
    exact (canonical12439 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA742 sourceB742 sourceC742
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm742, Integer.Sparse.eval]
  linarith only [hs]

def sourceA743 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB743 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC743 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceForm743 : Integer.Sparse Master := [(Sum.inr 1403, 1), (Sum.inr 2951, 1), (Sum.inr 3074, 1), (Sum.inr 3084, 1), (Sum.inr 3091, 1), (Sum.inr 3097, 1), (Sum.inr 4091, -1)]

theorem sourceEq743 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm743 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA743 + difference 1 0) (sourceB743 + difference 0 1) sourceC743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1403) := by
    have ha : (tripleCharges (sourceA743 + difference 1 0) (sourceB743 + difference 0 1) sourceC743) = raw12440 := by
      apply Matrix.ext; unfold tripleCharges sourceA743 sourceB743 sourceC743 difference raw12440; decide +kernel
    rw [ha]
    exact (canonical12440 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA743 + difference 1 1) (sourceB743 + difference 1 1) sourceC743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA743 + difference 1 1) (sourceB743 + difference 1 1) sourceC743) = raw12433 := by
      apply Matrix.ext; unfold tripleCharges sourceA743 sourceB743 sourceC743 difference raw12433; decide +kernel
    rw [ha]
    exact (canonical12433 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA743 + difference 1 2) (sourceB743 + difference 2 1) sourceC743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2951) := by
    have ha : (tripleCharges (sourceA743 + difference 1 2) (sourceB743 + difference 2 1) sourceC743) = raw12445 := by
      apply Matrix.ext; unfold tripleCharges sourceA743 sourceB743 sourceC743 difference raw12445; decide +kernel
    rw [ha]
    exact (canonical12445 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA743 + difference 1 3) (sourceB743 + difference 3 1) sourceC743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA743 + difference 1 3) (sourceB743 + difference 3 1) sourceC743) = raw12446 := by
      apply Matrix.ext; unfold tripleCharges sourceA743 sourceB743 sourceC743 difference raw12446; decide +kernel
    rw [ha]
    exact (canonical12446 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA743 + difference 1 4) (sourceB743 + difference 4 1) sourceC743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3084) := by
    have ha : (tripleCharges (sourceA743 + difference 1 4) (sourceB743 + difference 4 1) sourceC743) = raw12447 := by
      apply Matrix.ext; unfold tripleCharges sourceA743 sourceB743 sourceC743 difference raw12447; decide +kernel
    rw [ha]
    exact (canonical12447 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA743 + difference 1 5) (sourceB743 + difference 5 1) sourceC743) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA743 + difference 1 5) (sourceB743 + difference 5 1) sourceC743) = raw12448 := by
      apply Matrix.ext; unfold tripleCharges sourceA743 sourceB743 sourceC743 difference raw12448; decide +kernel
    rw [ha]
    exact (canonical12448 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA743 + sourceB743) sourceC743) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA743 + sourceB743) sourceC743) = raw12439 := by
      apply Matrix.ext; unfold doubleCharges sourceA743 sourceB743 sourceC743 raw12439; decide +kernel
    rw [ha]
    exact (canonical12439 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA743 sourceB743 sourceC743
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm743, Integer.Sparse.eval]
  linarith only [hs]

def sourceA744 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB744 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC744 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceForm744 : Integer.Sparse Master := [(Sum.inr 2938, 1), (Sum.inr 2984, 1), (Sum.inr 2985, 1), (Sum.inr 2994, 1), (Sum.inr 3097, 1), (Sum.inr 3978, 1), (Sum.inr 4091, -1)]

theorem sourceEq744 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm744 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA744 + difference 0 1) (sourceB744 + difference 1 0) sourceC744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3978) := by
    have ha : (tripleCharges (sourceA744 + difference 0 1) (sourceB744 + difference 1 0) sourceC744) = raw12434 := by
      apply Matrix.ext; unfold tripleCharges sourceA744 sourceB744 sourceC744 difference raw12434; decide +kernel
    rw [ha]
    exact (canonical12434 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA744 + difference 1 1) (sourceB744 + difference 1 1) sourceC744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA744 + difference 1 1) (sourceB744 + difference 1 1) sourceC744) = raw12433 := by
      apply Matrix.ext; unfold tripleCharges sourceA744 sourceB744 sourceC744 difference raw12433; decide +kernel
    rw [ha]
    exact (canonical12433 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA744 + difference 2 1) (sourceB744 + difference 1 2) sourceC744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2994) := by
    have ha : (tripleCharges (sourceA744 + difference 2 1) (sourceB744 + difference 1 2) sourceC744) = raw12449 := by
      apply Matrix.ext; unfold tripleCharges sourceA744 sourceB744 sourceC744 difference raw12449; decide +kernel
    rw [ha]
    exact (canonical12449 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA744 + difference 3 1) (sourceB744 + difference 1 3) sourceC744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA744 + difference 3 1) (sourceB744 + difference 1 3) sourceC744) = raw12450 := by
      apply Matrix.ext; unfold tripleCharges sourceA744 sourceB744 sourceC744 difference raw12450; decide +kernel
    rw [ha]
    exact (canonical12450 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA744 + difference 4 1) (sourceB744 + difference 1 4) sourceC744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2985) := by
    have ha : (tripleCharges (sourceA744 + difference 4 1) (sourceB744 + difference 1 4) sourceC744) = raw12451 := by
      apply Matrix.ext; unfold tripleCharges sourceA744 sourceB744 sourceC744 difference raw12451; decide +kernel
    rw [ha]
    exact (canonical12451 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA744 + difference 5 1) (sourceB744 + difference 1 5) sourceC744) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2938) := by
    have ha : (tripleCharges (sourceA744 + difference 5 1) (sourceB744 + difference 1 5) sourceC744) = raw12452 := by
      apply Matrix.ext; unfold tripleCharges sourceA744 sourceB744 sourceC744 difference raw12452; decide +kernel
    rw [ha]
    exact (canonical12452 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA744 + sourceB744) sourceC744) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA744 + sourceB744) sourceC744) = raw12439 := by
      apply Matrix.ext; unfold doubleCharges sourceA744 sourceB744 sourceC744 raw12439; decide +kernel
    rw [ha]
    exact (canonical12439 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA744 sourceB744 sourceC744
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm744, Integer.Sparse.eval]
  linarith only [hs]

def sourceA745 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB745 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC745 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceForm745 : Integer.Sparse Master := [(Sum.inr 1439, 1), (Sum.inr 2994, 1), (Sum.inr 3097, 2), (Sum.inr 3108, 1), (Sum.inr 3115, 1), (Sum.inr 4091, -1)]

theorem sourceEq745 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm745 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA745 + difference 2 0) (sourceB745 + difference 0 2) sourceC745) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1439) := by
    have ha : (tripleCharges (sourceA745 + difference 2 0) (sourceB745 + difference 0 2) sourceC745) = raw12441 := by
      apply Matrix.ext; unfold tripleCharges sourceA745 sourceB745 sourceC745 difference raw12441; decide +kernel
    rw [ha]
    exact (canonical12441 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA745 + difference 2 1) (sourceB745 + difference 1 2) sourceC745) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2994) := by
    have ha : (tripleCharges (sourceA745 + difference 2 1) (sourceB745 + difference 1 2) sourceC745) = raw12449 := by
      apply Matrix.ext; unfold tripleCharges sourceA745 sourceB745 sourceC745 difference raw12449; decide +kernel
    rw [ha]
    exact (canonical12449 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA745 + difference 2 2) (sourceB745 + difference 2 2) sourceC745) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA745 + difference 2 2) (sourceB745 + difference 2 2) sourceC745) = raw12433 := by
      apply Matrix.ext; unfold tripleCharges sourceA745 sourceB745 sourceC745 difference raw12433; decide +kernel
    rw [ha]
    exact (canonical12433 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA745 + difference 2 3) (sourceB745 + difference 3 2) sourceC745) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3115) := by
    have ha : (tripleCharges (sourceA745 + difference 2 3) (sourceB745 + difference 3 2) sourceC745) = raw12453 := by
      apply Matrix.ext; unfold tripleCharges sourceA745 sourceB745 sourceC745 difference raw12453; decide +kernel
    rw [ha]
    exact (canonical12453 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA745 + difference 2 4) (sourceB745 + difference 4 2) sourceC745) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3108) := by
    have ha : (tripleCharges (sourceA745 + difference 2 4) (sourceB745 + difference 4 2) sourceC745) = raw12454 := by
      apply Matrix.ext; unfold tripleCharges sourceA745 sourceB745 sourceC745 difference raw12454; decide +kernel
    rw [ha]
    exact (canonical12454 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA745 + difference 2 5) (sourceB745 + difference 5 2) sourceC745) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA745 + difference 2 5) (sourceB745 + difference 5 2) sourceC745) = raw12455 := by
      apply Matrix.ext; unfold tripleCharges sourceA745 sourceB745 sourceC745 difference raw12455; decide +kernel
    rw [ha]
    exact (canonical12455 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA745 + sourceB745) sourceC745) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA745 + sourceB745) sourceC745) = raw12439 := by
      apply Matrix.ext; unfold doubleCharges sourceA745 sourceB745 sourceC745 raw12439; decide +kernel
    rw [ha]
    exact (canonical12439 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA745 sourceB745 sourceC745
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm745, Integer.Sparse.eval]
  linarith only [hs]

def sourceA746 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB746 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC746 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceForm746 : Integer.Sparse Master := [(Sum.inr 2951, 1), (Sum.inr 2954, 1), (Sum.inr 2955, 1), (Sum.inr 2964, 1), (Sum.inr 3097, 1), (Sum.inr 3983, 1), (Sum.inr 4091, -1)]

theorem sourceEq746 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm746 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA746 + difference 0 2) (sourceB746 + difference 2 0) sourceC746) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA746 + difference 0 2) (sourceB746 + difference 2 0) sourceC746) = raw12435 := by
      apply Matrix.ext; unfold tripleCharges sourceA746 sourceB746 sourceC746 difference raw12435; decide +kernel
    rw [ha]
    exact (canonical12435 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA746 + difference 1 2) (sourceB746 + difference 2 1) sourceC746) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2951) := by
    have ha : (tripleCharges (sourceA746 + difference 1 2) (sourceB746 + difference 2 1) sourceC746) = raw12445 := by
      apply Matrix.ext; unfold tripleCharges sourceA746 sourceB746 sourceC746 difference raw12445; decide +kernel
    rw [ha]
    exact (canonical12445 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA746 + difference 2 2) (sourceB746 + difference 2 2) sourceC746) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA746 + difference 2 2) (sourceB746 + difference 2 2) sourceC746) = raw12433 := by
      apply Matrix.ext; unfold tripleCharges sourceA746 sourceB746 sourceC746 difference raw12433; decide +kernel
    rw [ha]
    exact (canonical12433 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA746 + difference 3 2) (sourceB746 + difference 2 3) sourceC746) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA746 + difference 3 2) (sourceB746 + difference 2 3) sourceC746) = raw12456 := by
      apply Matrix.ext; unfold tripleCharges sourceA746 sourceB746 sourceC746 difference raw12456; decide +kernel
    rw [ha]
    exact (canonical12456 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA746 + difference 4 2) (sourceB746 + difference 2 4) sourceC746) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA746 + difference 4 2) (sourceB746 + difference 2 4) sourceC746) = raw12457 := by
      apply Matrix.ext; unfold tripleCharges sourceA746 sourceB746 sourceC746 difference raw12457; decide +kernel
    rw [ha]
    exact (canonical12457 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA746 + difference 5 2) (sourceB746 + difference 2 5) sourceC746) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA746 + difference 5 2) (sourceB746 + difference 2 5) sourceC746) = raw12458 := by
      apply Matrix.ext; unfold tripleCharges sourceA746 sourceB746 sourceC746 difference raw12458; decide +kernel
    rw [ha]
    exact (canonical12458 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA746 + sourceB746) sourceC746) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA746 + sourceB746) sourceC746) = raw12439 := by
      apply Matrix.ext; unfold doubleCharges sourceA746 sourceB746 sourceC746 raw12439; decide +kernel
    rw [ha]
    exact (canonical12439 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA746 sourceB746 sourceC746
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm746, Integer.Sparse.eval]
  linarith only [hs]

def sourceA747 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB747 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC747 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceForm747 : Integer.Sparse Master := [(Sum.inr 2942, 1), (Sum.inr 3091, 1), (Sum.inr 3092, 1), (Sum.inr 3097, 1), (Sum.inr 3115, 1), (Sum.inr 3876, 1), (Sum.inr 4091, -1)]

theorem sourceEq747 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm747 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA747 + difference 0 3) (sourceB747 + difference 3 0) sourceC747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA747 + difference 0 3) (sourceB747 + difference 3 0) sourceC747) = raw12436 := by
      apply Matrix.ext; unfold tripleCharges sourceA747 sourceB747 sourceC747 difference raw12436; decide +kernel
    rw [ha]
    exact (canonical12436 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA747 + difference 1 3) (sourceB747 + difference 3 1) sourceC747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3091) := by
    have ha : (tripleCharges (sourceA747 + difference 1 3) (sourceB747 + difference 3 1) sourceC747) = raw12446 := by
      apply Matrix.ext; unfold tripleCharges sourceA747 sourceB747 sourceC747 difference raw12446; decide +kernel
    rw [ha]
    exact (canonical12446 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA747 + difference 2 3) (sourceB747 + difference 3 2) sourceC747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3115) := by
    have ha : (tripleCharges (sourceA747 + difference 2 3) (sourceB747 + difference 3 2) sourceC747) = raw12453 := by
      apply Matrix.ext; unfold tripleCharges sourceA747 sourceB747 sourceC747 difference raw12453; decide +kernel
    rw [ha]
    exact (canonical12453 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA747 + difference 3 3) (sourceB747 + difference 3 3) sourceC747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA747 + difference 3 3) (sourceB747 + difference 3 3) sourceC747) = raw12433 := by
      apply Matrix.ext; unfold tripleCharges sourceA747 sourceB747 sourceC747 difference raw12433; decide +kernel
    rw [ha]
    exact (canonical12433 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA747 + difference 4 3) (sourceB747 + difference 3 4) sourceC747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA747 + difference 4 3) (sourceB747 + difference 3 4) sourceC747) = raw12459 := by
      apply Matrix.ext; unfold tripleCharges sourceA747 sourceB747 sourceC747 difference raw12459; decide +kernel
    rw [ha]
    exact (canonical12459 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA747 + difference 5 3) (sourceB747 + difference 3 5) sourceC747) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2942) := by
    have ha : (tripleCharges (sourceA747 + difference 5 3) (sourceB747 + difference 3 5) sourceC747) = raw12460 := by
      apply Matrix.ext; unfold tripleCharges sourceA747 sourceB747 sourceC747 difference raw12460; decide +kernel
    rw [ha]
    exact (canonical12460 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA747 + sourceB747) sourceC747) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA747 + sourceB747) sourceC747) = raw12439 := by
      apply Matrix.ext; unfold doubleCharges sourceA747 sourceB747 sourceC747 raw12439; decide +kernel
    rw [ha]
    exact (canonical12439 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA747 sourceB747 sourceC747
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm747, Integer.Sparse.eval]
  linarith only [hs]

def sourceA748 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB748 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC748 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm748 : Integer.Sparse Master := [(Sum.inr 4851, 1), (Sum.inr 4853, 1), (Sum.inr 4856, 1), (Sum.inr 4866, 1), (Sum.inr 4888, 1), (Sum.inr 5077, 1), (Sum.inr 5079, 1), (Sum.inr 5108, 1), (Sum.inr 5157, 1), (Sum.inr 5158, 1), (Sum.inr 5173, 1), (Sum.inr 5255, 2), (Sum.inr 5256, 1), (Sum.inr 5262, 1), (Sum.inr 5269, 1), (Sum.inr 5271, 1), (Sum.inr 5280, 1), (Sum.inr 5281, 1), (Sum.inr 5288, 1), (Sum.inr 5289, 2), (Sum.inr 5290, 1), (Sum.inr 5292, 1), (Sum.inr 5295, 1), (Sum.inr 5298, 1), (Sum.inr 5299, 1), (Sum.inr 5304, 2), (Sum.inr 5306, 1)]

theorem sourceEq748 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm748 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA748 + difference 0 1) (sourceB748 + difference 1 0) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA748 + difference 0 1) (sourceB748 + difference 1 0) sourceC748) = raw11662 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw11662; decide +kernel
    rw [ha]
    exact (canonical11662 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA748 + difference 0 2) (sourceB748 + difference 2 0) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA748 + difference 0 2) (sourceB748 + difference 2 0) sourceC748) = raw12184 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12184; decide +kernel
    rw [ha]
    exact (canonical12184 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA748 + difference 0 3) (sourceB748 + difference 3 0) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5173) := by
    have ha : (tripleCharges (sourceA748 + difference 0 3) (sourceB748 + difference 3 0) sourceC748) = raw12461 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12461; decide +kernel
    rw [ha]
    exact (canonical12461 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA748 + difference 0 4) (sourceB748 + difference 4 0) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5269) := by
    have ha : (tripleCharges (sourceA748 + difference 0 4) (sourceB748 + difference 4 0) sourceC748) = raw12462 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12462; decide +kernel
    rw [ha]
    exact (canonical12462 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA748 + difference 0 5) (sourceB748 + difference 5 0) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA748 + difference 0 5) (sourceB748 + difference 5 0) sourceC748) = raw12463 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12463; decide +kernel
    rw [ha]
    exact (canonical12463 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA748 + difference 1 0) (sourceB748 + difference 0 1) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4851) := by
    have ha : (tripleCharges (sourceA748 + difference 1 0) (sourceB748 + difference 0 1) sourceC748) = raw12464 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12464; decide +kernel
    rw [ha]
    exact (canonical12464 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA748 + difference 1 2) (sourceB748 + difference 2 1) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA748 + difference 1 2) (sourceB748 + difference 2 1) sourceC748) = raw12189 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12189; decide +kernel
    rw [ha]
    exact (canonical12189 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA748 + difference 1 3) (sourceB748 + difference 3 1) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5157) := by
    have ha : (tripleCharges (sourceA748 + difference 1 3) (sourceB748 + difference 3 1) sourceC748) = raw12465 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12465; decide +kernel
    rw [ha]
    exact (canonical12465 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA748 + difference 1 4) (sourceB748 + difference 4 1) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5280) := by
    have ha : (tripleCharges (sourceA748 + difference 1 4) (sourceB748 + difference 4 1) sourceC748) = raw12466 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12466; decide +kernel
    rw [ha]
    exact (canonical12466 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA748 + difference 1 5) (sourceB748 + difference 5 1) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA748 + difference 1 5) (sourceB748 + difference 5 1) sourceC748) = raw12467 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12467; decide +kernel
    rw [ha]
    exact (canonical12467 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA748 + difference 2 0) (sourceB748 + difference 0 2) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4856) := by
    have ha : (tripleCharges (sourceA748 + difference 2 0) (sourceB748 + difference 0 2) sourceC748) = raw12468 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12468; decide +kernel
    rw [ha]
    exact (canonical12468 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA748 + difference 2 1) (sourceB748 + difference 1 2) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5262) := by
    have ha : (tripleCharges (sourceA748 + difference 2 1) (sourceB748 + difference 1 2) sourceC748) = raw11672 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw11672; decide +kernel
    rw [ha]
    exact (canonical11672 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA748 + difference 2 3) (sourceB748 + difference 3 2) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5158) := by
    have ha : (tripleCharges (sourceA748 + difference 2 3) (sourceB748 + difference 3 2) sourceC748) = raw12469 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12469; decide +kernel
    rw [ha]
    exact (canonical12469 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA748 + difference 2 4) (sourceB748 + difference 4 2) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5298) := by
    have ha : (tripleCharges (sourceA748 + difference 2 4) (sourceB748 + difference 4 2) sourceC748) = raw12470 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12470; decide +kernel
    rw [ha]
    exact (canonical12470 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA748 + difference 2 5) (sourceB748 + difference 5 2) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA748 + difference 2 5) (sourceB748 + difference 5 2) sourceC748) = raw12003 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12003; decide +kernel
    rw [ha]
    exact (canonical12003 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA748 + difference 3 0) (sourceB748 + difference 0 3) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA748 + difference 3 0) (sourceB748 + difference 0 3) sourceC748) = raw11665 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw11665; decide +kernel
    rw [ha]
    exact (canonical11665 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA748 + difference 3 1) (sourceB748 + difference 1 3) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA748 + difference 3 1) (sourceB748 + difference 1 3) sourceC748) = raw12019 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12019; decide +kernel
    rw [ha]
    exact (canonical12019 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA748 + difference 3 2) (sourceB748 + difference 2 3) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA748 + difference 3 2) (sourceB748 + difference 2 3) sourceC748) = raw11666 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw11666; decide +kernel
    rw [ha]
    exact (canonical11666 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA748 + difference 3 4) (sourceB748 + difference 4 3) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA748 + difference 3 4) (sourceB748 + difference 4 3) sourceC748) = raw11668 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw11668; decide +kernel
    rw [ha]
    exact (canonical11668 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA748 + difference 3 5) (sourceB748 + difference 5 3) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA748 + difference 3 5) (sourceB748 + difference 5 3) sourceC748) = raw11669 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw11669; decide +kernel
    rw [ha]
    exact (canonical11669 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA748 + difference 4 0) (sourceB748 + difference 0 4) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4866) := by
    have ha : (tripleCharges (sourceA748 + difference 4 0) (sourceB748 + difference 0 4) sourceC748) = raw12471 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12471; decide +kernel
    rw [ha]
    exact (canonical12471 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA748 + difference 4 1) (sourceB748 + difference 1 4) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5255) := by
    have ha : (tripleCharges (sourceA748 + difference 4 1) (sourceB748 + difference 1 4) sourceC748) = raw11683 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw11683; decide +kernel
    rw [ha]
    exact (canonical11683 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA748 + difference 4 2) (sourceB748 + difference 2 4) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA748 + difference 4 2) (sourceB748 + difference 2 4) sourceC748) = raw12198 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12198; decide +kernel
    rw [ha]
    exact (canonical12198 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA748 + difference 4 3) (sourceB748 + difference 3 4) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5288) := by
    have ha : (tripleCharges (sourceA748 + difference 4 3) (sourceB748 + difference 3 4) sourceC748) = raw12472 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12472; decide +kernel
    rw [ha]
    exact (canonical12472 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA748 + difference 4 5) (sourceB748 + difference 5 4) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA748 + difference 4 5) (sourceB748 + difference 5 4) sourceC748) = raw12473 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12473; decide +kernel
    rw [ha]
    exact (canonical12473 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA748 + difference 5 0) (sourceB748 + difference 0 5) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA748 + difference 5 0) (sourceB748 + difference 0 5) sourceC748) = raw12474 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12474; decide +kernel
    rw [ha]
    exact (canonical12474 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA748 + difference 5 1) (sourceB748 + difference 1 5) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5077) := by
    have ha : (tripleCharges (sourceA748 + difference 5 1) (sourceB748 + difference 1 5) sourceC748) = raw11688 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw11688; decide +kernel
    rw [ha]
    exact (canonical11688 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA748 + difference 5 2) (sourceB748 + difference 2 5) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5295) := by
    have ha : (tripleCharges (sourceA748 + difference 5 2) (sourceB748 + difference 2 5) sourceC748) = raw12202 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12202; decide +kernel
    rw [ha]
    exact (canonical12202 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA748 + difference 5 3) (sourceB748 + difference 3 5) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5079) := by
    have ha : (tripleCharges (sourceA748 + difference 5 3) (sourceB748 + difference 3 5) sourceC748) = raw12475 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12475; decide +kernel
    rw [ha]
    exact (canonical12475 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA748 + difference 5 4) (sourceB748 + difference 4 5) sourceC748) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5108) := by
    have ha : (tripleCharges (sourceA748 + difference 5 4) (sourceB748 + difference 4 5) sourceC748) = raw12476 := by
      apply Matrix.ext; unfold tripleCharges sourceA748 sourceB748 sourceC748 difference raw12476; decide +kernel
    rw [ha]
    exact (canonical12476 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA748 sourceB748 sourceC748
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm748, Integer.Sparse.eval]
  linarith only [hs]

def sourceA749 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB749 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC749 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm749 : Integer.Sparse Master := [(Sum.inr 2240, 1), (Sum.inr 2259, 1), (Sum.inr 2260, 1), (Sum.inr 2262, 1), (Sum.inr 2274, 1), (Sum.inr 2583, 1), (Sum.inr 2584, 1), (Sum.inr 2585, 1), (Sum.inr 2600, 1), (Sum.inr 2717, 1), (Sum.inr 2718, 1), (Sum.inr 2720, 1), (Sum.inr 2727, 1), (Sum.inr 2749, 1), (Sum.inr 2750, 1), (Sum.inr 2760, 1), (Sum.inr 2762, 1), (Sum.inr 2763, 2), (Sum.inr 2764, 1), (Sum.inr 2766, 1), (Sum.inr 2772, 1), (Sum.inr 2773, 1), (Sum.inr 2781, 1), (Sum.inr 2782, 1), (Sum.inr 2784, 1), (Sum.inr 3084, 1), (Sum.inr 3108, 1), (Sum.inr 3109, 1), (Sum.inr 3119, 1)]

theorem sourceEq749 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm749 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA749 + difference 0 1) (sourceB749 + difference 1 0) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3084) := by
    have ha : (tripleCharges (sourceA749 + difference 0 1) (sourceB749 + difference 1 0) sourceC749) = raw11692 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw11692; decide +kernel
    rw [ha]
    exact (canonical11692 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA749 + difference 0 2) (sourceB749 + difference 2 0) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3119) := by
    have ha : (tripleCharges (sourceA749 + difference 0 2) (sourceB749 + difference 2 0) sourceC749) = raw12477 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12477; decide +kernel
    rw [ha]
    exact (canonical12477 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA749 + difference 0 3) (sourceB749 + difference 3 0) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2600) := by
    have ha : (tripleCharges (sourceA749 + difference 0 3) (sourceB749 + difference 3 0) sourceC749) = raw12478 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12478; decide +kernel
    rw [ha]
    exact (canonical12478 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA749 + difference 0 4) (sourceB749 + difference 4 0) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3108) := by
    have ha : (tripleCharges (sourceA749 + difference 0 4) (sourceB749 + difference 4 0) sourceC749) = raw12479 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12479; decide +kernel
    rw [ha]
    exact (canonical12479 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA749 + difference 0 5) (sourceB749 + difference 5 0) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA749 + difference 0 5) (sourceB749 + difference 5 0) sourceC749) = raw12480 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12480; decide +kernel
    rw [ha]
    exact (canonical12480 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA749 + difference 1 0) (sourceB749 + difference 0 1) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA749 + difference 1 0) (sourceB749 + difference 0 1) sourceC749) = raw12481 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12481; decide +kernel
    rw [ha]
    exact (canonical12481 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA749 + difference 1 2) (sourceB749 + difference 2 1) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA749 + difference 1 2) (sourceB749 + difference 2 1) sourceC749) = raw12482 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12482; decide +kernel
    rw [ha]
    exact (canonical12482 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA749 + difference 1 3) (sourceB749 + difference 3 1) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2583) := by
    have ha : (tripleCharges (sourceA749 + difference 1 3) (sourceB749 + difference 3 1) sourceC749) = raw12483 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12483; decide +kernel
    rw [ha]
    exact (canonical12483 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA749 + difference 1 4) (sourceB749 + difference 4 1) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2749) := by
    have ha : (tripleCharges (sourceA749 + difference 1 4) (sourceB749 + difference 4 1) sourceC749) = raw12484 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12484; decide +kernel
    rw [ha]
    exact (canonical12484 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA749 + difference 1 5) (sourceB749 + difference 5 1) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2750) := by
    have ha : (tripleCharges (sourceA749 + difference 1 5) (sourceB749 + difference 5 1) sourceC749) = raw12485 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12485; decide +kernel
    rw [ha]
    exact (canonical12485 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA749 + difference 2 0) (sourceB749 + difference 0 2) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2274) := by
    have ha : (tripleCharges (sourceA749 + difference 2 0) (sourceB749 + difference 0 2) sourceC749) = raw12486 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12486; decide +kernel
    rw [ha]
    exact (canonical12486 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA749 + difference 2 1) (sourceB749 + difference 1 2) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2727) := by
    have ha : (tripleCharges (sourceA749 + difference 2 1) (sourceB749 + difference 1 2) sourceC749) = raw11702 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw11702; decide +kernel
    rw [ha]
    exact (canonical11702 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA749 + difference 2 3) (sourceB749 + difference 3 2) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2585) := by
    have ha : (tripleCharges (sourceA749 + difference 2 3) (sourceB749 + difference 3 2) sourceC749) = raw12487 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12487; decide +kernel
    rw [ha]
    exact (canonical12487 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA749 + difference 2 4) (sourceB749 + difference 4 2) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2772) := by
    have ha : (tripleCharges (sourceA749 + difference 2 4) (sourceB749 + difference 4 2) sourceC749) = raw12488 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12488; decide +kernel
    rw [ha]
    exact (canonical12488 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA749 + difference 2 5) (sourceB749 + difference 5 2) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA749 + difference 2 5) (sourceB749 + difference 5 2) sourceC749) = raw12025 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12025; decide +kernel
    rw [ha]
    exact (canonical12025 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA749 + difference 3 0) (sourceB749 + difference 0 3) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA749 + difference 3 0) (sourceB749 + difference 0 3) sourceC749) = raw11695 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw11695; decide +kernel
    rw [ha]
    exact (canonical11695 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA749 + difference 3 1) (sourceB749 + difference 1 3) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA749 + difference 3 1) (sourceB749 + difference 1 3) sourceC749) = raw12041 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12041; decide +kernel
    rw [ha]
    exact (canonical12041 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA749 + difference 3 2) (sourceB749 + difference 2 3) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA749 + difference 3 2) (sourceB749 + difference 2 3) sourceC749) = raw11696 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw11696; decide +kernel
    rw [ha]
    exact (canonical11696 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA749 + difference 3 4) (sourceB749 + difference 4 3) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA749 + difference 3 4) (sourceB749 + difference 4 3) sourceC749) = raw11698 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw11698; decide +kernel
    rw [ha]
    exact (canonical11698 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA749 + difference 3 5) (sourceB749 + difference 5 3) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA749 + difference 3 5) (sourceB749 + difference 5 3) sourceC749) = raw11699 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw11699; decide +kernel
    rw [ha]
    exact (canonical11699 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA749 + difference 4 0) (sourceB749 + difference 0 4) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2260) := by
    have ha : (tripleCharges (sourceA749 + difference 4 0) (sourceB749 + difference 0 4) sourceC749) = raw12489 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12489; decide +kernel
    rw [ha]
    exact (canonical12489 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA749 + difference 4 1) (sourceB749 + difference 1 4) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA749 + difference 4 1) (sourceB749 + difference 1 4) sourceC749) = raw11713 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw11713; decide +kernel
    rw [ha]
    exact (canonical11713 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA749 + difference 4 2) (sourceB749 + difference 2 4) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA749 + difference 4 2) (sourceB749 + difference 2 4) sourceC749) = raw12490 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12490; decide +kernel
    rw [ha]
    exact (canonical12490 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA749 + difference 4 3) (sourceB749 + difference 3 4) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2760) := by
    have ha : (tripleCharges (sourceA749 + difference 4 3) (sourceB749 + difference 3 4) sourceC749) = raw12491 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12491; decide +kernel
    rw [ha]
    exact (canonical12491 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA749 + difference 4 5) (sourceB749 + difference 5 4) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2764) := by
    have ha : (tripleCharges (sourceA749 + difference 4 5) (sourceB749 + difference 5 4) sourceC749) = raw12492 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12492; decide +kernel
    rw [ha]
    exact (canonical12492 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA749 + difference 5 0) (sourceB749 + difference 0 5) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2259) := by
    have ha : (tripleCharges (sourceA749 + difference 5 0) (sourceB749 + difference 0 5) sourceC749) = raw12493 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12493; decide +kernel
    rw [ha]
    exact (canonical12493 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA749 + difference 5 1) (sourceB749 + difference 1 5) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2717) := by
    have ha : (tripleCharges (sourceA749 + difference 5 1) (sourceB749 + difference 1 5) sourceC749) = raw11718 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw11718; decide +kernel
    rw [ha]
    exact (canonical11718 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA749 + difference 5 2) (sourceB749 + difference 2 5) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA749 + difference 5 2) (sourceB749 + difference 2 5) sourceC749) = raw12494 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12494; decide +kernel
    rw [ha]
    exact (canonical12494 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA749 + difference 5 3) (sourceB749 + difference 3 5) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2584) := by
    have ha : (tripleCharges (sourceA749 + difference 5 3) (sourceB749 + difference 3 5) sourceC749) = raw12495 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12495; decide +kernel
    rw [ha]
    exact (canonical12495 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA749 + difference 5 4) (sourceB749 + difference 4 5) sourceC749) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2762) := by
    have ha : (tripleCharges (sourceA749 + difference 5 4) (sourceB749 + difference 4 5) sourceC749) = raw12496 := by
      apply Matrix.ext; unfold tripleCharges sourceA749 sourceB749 sourceC749 difference raw12496; decide +kernel
    rw [ha]
    exact (canonical12496 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA749 sourceB749 sourceC749
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm749, Integer.Sparse.eval]
  linarith only [hs]

def sourceA750 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB750 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC750 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm750 : Integer.Sparse Master := [(Sum.inr 2484, 1), (Sum.inr 2486, 1), (Sum.inr 2487, 1), (Sum.inr 2518, 1), (Sum.inr 2718, 1), (Sum.inr 2735, 1), (Sum.inr 2736, 1), (Sum.inr 2739, 1), (Sum.inr 2769, 1), (Sum.inr 2782, 1), (Sum.inr 3034, 1), (Sum.inr 3047, 1), (Sum.inr 3048, 1), (Sum.inr 3051, 1), (Sum.inr 3070, 1), (Sum.inr 3071, 1), (Sum.inr 3074, 1), (Sum.inr 3084, 1), (Sum.inr 3085, 1), (Sum.inr 3096, 1), (Sum.inr 3097, 2), (Sum.inr 3099, 1), (Sum.inr 3100, 1), (Sum.inr 3119, 1), (Sum.inr 3120, 1), (Sum.inr 3172, 1), (Sum.inr 3174, 1), (Sum.inr 3184, 1), (Sum.inr 3227, 1)]

theorem sourceEq750 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm750 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA750 + difference 0 1) (sourceB750 + difference 1 0) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA750 + difference 0 1) (sourceB750 + difference 1 0) sourceC750) = raw11722 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw11722; decide +kernel
    rw [ha]
    exact (canonical11722 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA750 + difference 0 2) (sourceB750 + difference 2 0) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA750 + difference 0 2) (sourceB750 + difference 2 0) sourceC750) = raw12205 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12205; decide +kernel
    rw [ha]
    exact (canonical12205 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA750 + difference 0 3) (sourceB750 + difference 3 0) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA750 + difference 0 3) (sourceB750 + difference 3 0) sourceC750) = raw12497 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12497; decide +kernel
    rw [ha]
    exact (canonical12497 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA750 + difference 0 4) (sourceB750 + difference 4 0) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2736) := by
    have ha : (tripleCharges (sourceA750 + difference 0 4) (sourceB750 + difference 4 0) sourceC750) = raw12498 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12498; decide +kernel
    rw [ha]
    exact (canonical12498 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA750 + difference 0 5) (sourceB750 + difference 5 0) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA750 + difference 0 5) (sourceB750 + difference 5 0) sourceC750) = raw12499 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12499; decide +kernel
    rw [ha]
    exact (canonical12499 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA750 + difference 1 0) (sourceB750 + difference 0 1) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3172) := by
    have ha : (tripleCharges (sourceA750 + difference 1 0) (sourceB750 + difference 0 1) sourceC750) = raw12500 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12500; decide +kernel
    rw [ha]
    exact (canonical12500 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA750 + difference 1 2) (sourceB750 + difference 2 1) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA750 + difference 1 2) (sourceB750 + difference 2 1) sourceC750) = raw12210 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12210; decide +kernel
    rw [ha]
    exact (canonical12210 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA750 + difference 1 3) (sourceB750 + difference 3 1) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3070) := by
    have ha : (tripleCharges (sourceA750 + difference 1 3) (sourceB750 + difference 3 1) sourceC750) = raw12501 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12501; decide +kernel
    rw [ha]
    exact (canonical12501 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA750 + difference 1 4) (sourceB750 + difference 4 1) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3071) := by
    have ha : (tripleCharges (sourceA750 + difference 1 4) (sourceB750 + difference 4 1) sourceC750) = raw12502 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12502; decide +kernel
    rw [ha]
    exact (canonical12502 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA750 + difference 1 5) (sourceB750 + difference 5 1) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3074) := by
    have ha : (tripleCharges (sourceA750 + difference 1 5) (sourceB750 + difference 5 1) sourceC750) = raw12503 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12503; decide +kernel
    rw [ha]
    exact (canonical12503 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA750 + difference 2 0) (sourceB750 + difference 0 2) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3174) := by
    have ha : (tripleCharges (sourceA750 + difference 2 0) (sourceB750 + difference 0 2) sourceC750) = raw12504 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12504; decide +kernel
    rw [ha]
    exact (canonical12504 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA750 + difference 2 1) (sourceB750 + difference 1 2) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3034) := by
    have ha : (tripleCharges (sourceA750 + difference 2 1) (sourceB750 + difference 1 2) sourceC750) = raw11732 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw11732; decide +kernel
    rw [ha]
    exact (canonical11732 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA750 + difference 2 3) (sourceB750 + difference 3 2) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3047) := by
    have ha : (tripleCharges (sourceA750 + difference 2 3) (sourceB750 + difference 3 2) sourceC750) = raw12505 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12505; decide +kernel
    rw [ha]
    exact (canonical12505 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA750 + difference 2 4) (sourceB750 + difference 4 2) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3048) := by
    have ha : (tripleCharges (sourceA750 + difference 2 4) (sourceB750 + difference 4 2) sourceC750) = raw12506 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12506; decide +kernel
    rw [ha]
    exact (canonical12506 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA750 + difference 2 5) (sourceB750 + difference 5 2) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA750 + difference 2 5) (sourceB750 + difference 5 2) sourceC750) = raw12047 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12047; decide +kernel
    rw [ha]
    exact (canonical12047 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA750 + difference 3 0) (sourceB750 + difference 0 3) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3227) := by
    have ha : (tripleCharges (sourceA750 + difference 3 0) (sourceB750 + difference 0 3) sourceC750) = raw11725 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw11725; decide +kernel
    rw [ha]
    exact (canonical11725 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA750 + difference 3 1) (sourceB750 + difference 1 3) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3085) := by
    have ha : (tripleCharges (sourceA750 + difference 3 1) (sourceB750 + difference 1 3) sourceC750) = raw12063 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12063; decide +kernel
    rw [ha]
    exact (canonical12063 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA750 + difference 3 2) (sourceB750 + difference 2 3) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3120) := by
    have ha : (tripleCharges (sourceA750 + difference 3 2) (sourceB750 + difference 2 3) sourceC750) = raw11726 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw11726; decide +kernel
    rw [ha]
    exact (canonical11726 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA750 + difference 3 4) (sourceB750 + difference 4 3) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA750 + difference 3 4) (sourceB750 + difference 4 3) sourceC750) = raw11728 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw11728; decide +kernel
    rw [ha]
    exact (canonical11728 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA750 + difference 3 5) (sourceB750 + difference 5 3) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA750 + difference 3 5) (sourceB750 + difference 5 3) sourceC750) = raw11729 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw11729; decide +kernel
    rw [ha]
    exact (canonical11729 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA750 + difference 4 0) (sourceB750 + difference 0 4) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3184) := by
    have ha : (tripleCharges (sourceA750 + difference 4 0) (sourceB750 + difference 0 4) sourceC750) = raw12507 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12507; decide +kernel
    rw [ha]
    exact (canonical12507 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA750 + difference 4 1) (sourceB750 + difference 1 4) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3084) := by
    have ha : (tripleCharges (sourceA750 + difference 4 1) (sourceB750 + difference 1 4) sourceC750) = raw11743 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw11743; decide +kernel
    rw [ha]
    exact (canonical11743 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA750 + difference 4 2) (sourceB750 + difference 2 4) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3119) := by
    have ha : (tripleCharges (sourceA750 + difference 4 2) (sourceB750 + difference 2 4) sourceC750) = raw12219 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12219; decide +kernel
    rw [ha]
    exact (canonical12219 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA750 + difference 4 3) (sourceB750 + difference 3 4) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3096) := by
    have ha : (tripleCharges (sourceA750 + difference 4 3) (sourceB750 + difference 3 4) sourceC750) = raw12508 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12508; decide +kernel
    rw [ha]
    exact (canonical12508 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA750 + difference 4 5) (sourceB750 + difference 5 4) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3099) := by
    have ha : (tripleCharges (sourceA750 + difference 4 5) (sourceB750 + difference 5 4) sourceC750) = raw12509 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12509; decide +kernel
    rw [ha]
    exact (canonical12509 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA750 + difference 5 0) (sourceB750 + difference 0 5) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA750 + difference 5 0) (sourceB750 + difference 0 5) sourceC750) = raw12510 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12510; decide +kernel
    rw [ha]
    exact (canonical12510 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA750 + difference 5 1) (sourceB750 + difference 1 5) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2484) := by
    have ha : (tripleCharges (sourceA750 + difference 5 1) (sourceB750 + difference 1 5) sourceC750) = raw11748 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw11748; decide +kernel
    rw [ha]
    exact (canonical11748 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA750 + difference 5 2) (sourceB750 + difference 2 5) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2769) := by
    have ha : (tripleCharges (sourceA750 + difference 5 2) (sourceB750 + difference 2 5) sourceC750) = raw12223 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12223; decide +kernel
    rw [ha]
    exact (canonical12223 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA750 + difference 5 3) (sourceB750 + difference 3 5) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2487) := by
    have ha : (tripleCharges (sourceA750 + difference 5 3) (sourceB750 + difference 3 5) sourceC750) = raw12511 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12511; decide +kernel
    rw [ha]
    exact (canonical12511 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA750 + difference 5 4) (sourceB750 + difference 4 5) sourceC750) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2518) := by
    have ha : (tripleCharges (sourceA750 + difference 5 4) (sourceB750 + difference 4 5) sourceC750) = raw12512 := by
      apply Matrix.ext; unfold tripleCharges sourceA750 sourceB750 sourceC750 difference raw12512; decide +kernel
    rw [ha]
    exact (canonical12512 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA750 sourceB750 sourceC750
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm750, Integer.Sparse.eval]
  linarith only [hs]

def sourceA751 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB751 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC751 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm751 : Integer.Sparse Master := [(Sum.inr 2952, 1), (Sum.inr 3503, 1), (Sum.inr 3507, 1), (Sum.inr 3534, 1), (Sum.inr 3572, 1), (Sum.inr 3583, 1), (Sum.inr 4083, -1)]

theorem sourceEq751 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm751 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA751 + difference 0 0) (sourceB751 + difference 0 0) sourceC751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA751 + difference 0 0) (sourceB751 + difference 0 0) sourceC751) = raw11769 := by
      apply Matrix.ext; unfold tripleCharges sourceA751 sourceB751 sourceC751 difference raw11769; decide +kernel
    rw [ha]
    exact (canonical11769 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA751 + difference 0 1) (sourceB751 + difference 1 0) sourceC751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA751 + difference 0 1) (sourceB751 + difference 1 0) sourceC751) = raw11753 := by
      apply Matrix.ext; unfold tripleCharges sourceA751 sourceB751 sourceC751 difference raw11753; decide +kernel
    rw [ha]
    exact (canonical11753 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA751 + difference 0 2) (sourceB751 + difference 2 0) sourceC751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA751 + difference 0 2) (sourceB751 + difference 2 0) sourceC751) = raw12227 := by
      apply Matrix.ext; unfold tripleCharges sourceA751 sourceB751 sourceC751 difference raw12227; decide +kernel
    rw [ha]
    exact (canonical12227 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA751 + difference 0 3) (sourceB751 + difference 3 0) sourceC751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA751 + difference 0 3) (sourceB751 + difference 3 0) sourceC751) = raw12513 := by
      apply Matrix.ext; unfold tripleCharges sourceA751 sourceB751 sourceC751 difference raw12513; decide +kernel
    rw [ha]
    exact (canonical12513 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA751 + difference 0 4) (sourceB751 + difference 4 0) sourceC751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3507) := by
    have ha : (tripleCharges (sourceA751 + difference 0 4) (sourceB751 + difference 4 0) sourceC751) = raw12514 := by
      apply Matrix.ext; unfold tripleCharges sourceA751 sourceB751 sourceC751 difference raw12514; decide +kernel
    rw [ha]
    exact (canonical12514 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA751 + difference 0 5) (sourceB751 + difference 5 0) sourceC751) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA751 + difference 0 5) (sourceB751 + difference 5 0) sourceC751) = raw12515 := by
      apply Matrix.ext; unfold tripleCharges sourceA751 sourceB751 sourceC751 difference raw12515; decide +kernel
    rw [ha]
    exact (canonical12515 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA751 + sourceB751) sourceC751) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA751 + sourceB751) sourceC751) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA751 sourceB751 sourceC751 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA751 sourceB751 sourceC751
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm751, Integer.Sparse.eval]
  linarith only [hs]

def sourceA752 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB752 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC752 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm752 : Integer.Sparse Master := [(Sum.inr 2088, 1), (Sum.inr 2950, 1), (Sum.inr 3550, 1), (Sum.inr 3571, 1), (Sum.inr 3572, 2), (Sum.inr 4083, -1)]

theorem sourceEq752 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm752 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA752 + difference 1 0) (sourceB752 + difference 0 1) sourceC752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2088) := by
    have ha : (tripleCharges (sourceA752 + difference 1 0) (sourceB752 + difference 0 1) sourceC752) = raw12516 := by
      apply Matrix.ext; unfold tripleCharges sourceA752 sourceB752 sourceC752 difference raw12516; decide +kernel
    rw [ha]
    exact (canonical12516 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA752 + difference 1 1) (sourceB752 + difference 1 1) sourceC752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA752 + difference 1 1) (sourceB752 + difference 1 1) sourceC752) = raw11769 := by
      apply Matrix.ext; unfold tripleCharges sourceA752 sourceB752 sourceC752 difference raw11769; decide +kernel
    rw [ha]
    exact (canonical11769 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA752 + difference 1 2) (sourceB752 + difference 2 1) sourceC752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA752 + difference 1 2) (sourceB752 + difference 2 1) sourceC752) = raw12517 := by
      apply Matrix.ext; unfold tripleCharges sourceA752 sourceB752 sourceC752 difference raw12517; decide +kernel
    rw [ha]
    exact (canonical12517 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA752 + difference 1 3) (sourceB752 + difference 3 1) sourceC752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2950) := by
    have ha : (tripleCharges (sourceA752 + difference 1 3) (sourceB752 + difference 3 1) sourceC752) = raw12518 := by
      apply Matrix.ext; unfold tripleCharges sourceA752 sourceB752 sourceC752 difference raw12518; decide +kernel
    rw [ha]
    exact (canonical12518 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA752 + difference 1 4) (sourceB752 + difference 4 1) sourceC752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3550) := by
    have ha : (tripleCharges (sourceA752 + difference 1 4) (sourceB752 + difference 4 1) sourceC752) = raw12519 := by
      apply Matrix.ext; unfold tripleCharges sourceA752 sourceB752 sourceC752 difference raw12519; decide +kernel
    rw [ha]
    exact (canonical12519 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA752 + difference 1 5) (sourceB752 + difference 5 1) sourceC752) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA752 + difference 1 5) (sourceB752 + difference 5 1) sourceC752) = raw12520 := by
      apply Matrix.ext; unfold tripleCharges sourceA752 sourceB752 sourceC752 difference raw12520; decide +kernel
    rw [ha]
    exact (canonical12520 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA752 + sourceB752) sourceC752) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA752 + sourceB752) sourceC752) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA752 sourceB752 sourceC752 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA752 sourceB752 sourceC752
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm752, Integer.Sparse.eval]
  linarith only [hs]

def sourceA753 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB753 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC753 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm753 : Integer.Sparse Master := [(Sum.inr 2094, 1), (Sum.inr 2956, 1), (Sum.inr 3500, 1), (Sum.inr 3552, 1), (Sum.inr 3572, 1), (Sum.inr 3573, 1), (Sum.inr 4083, -1)]

theorem sourceEq753 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm753 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA753 + difference 2 0) (sourceB753 + difference 0 2) sourceC753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2094) := by
    have ha : (tripleCharges (sourceA753 + difference 2 0) (sourceB753 + difference 0 2) sourceC753) = raw12521 := by
      apply Matrix.ext; unfold tripleCharges sourceA753 sourceB753 sourceC753 difference raw12521; decide +kernel
    rw [ha]
    exact (canonical12521 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA753 + difference 2 1) (sourceB753 + difference 1 2) sourceC753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3500) := by
    have ha : (tripleCharges (sourceA753 + difference 2 1) (sourceB753 + difference 1 2) sourceC753) = raw11762 := by
      apply Matrix.ext; unfold tripleCharges sourceA753 sourceB753 sourceC753 difference raw11762; decide +kernel
    rw [ha]
    exact (canonical11762 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA753 + difference 2 2) (sourceB753 + difference 2 2) sourceC753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA753 + difference 2 2) (sourceB753 + difference 2 2) sourceC753) = raw11769 := by
      apply Matrix.ext; unfold tripleCharges sourceA753 sourceB753 sourceC753 difference raw11769; decide +kernel
    rw [ha]
    exact (canonical11769 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA753 + difference 2 3) (sourceB753 + difference 3 2) sourceC753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2956) := by
    have ha : (tripleCharges (sourceA753 + difference 2 3) (sourceB753 + difference 3 2) sourceC753) = raw12522 := by
      apply Matrix.ext; unfold tripleCharges sourceA753 sourceB753 sourceC753 difference raw12522; decide +kernel
    rw [ha]
    exact (canonical12522 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA753 + difference 2 4) (sourceB753 + difference 4 2) sourceC753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3552) := by
    have ha : (tripleCharges (sourceA753 + difference 2 4) (sourceB753 + difference 4 2) sourceC753) = raw12523 := by
      apply Matrix.ext; unfold tripleCharges sourceA753 sourceB753 sourceC753 difference raw12523; decide +kernel
    rw [ha]
    exact (canonical12523 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA753 + difference 2 5) (sourceB753 + difference 5 2) sourceC753) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA753 + difference 2 5) (sourceB753 + difference 5 2) sourceC753) = raw12078 := by
      apply Matrix.ext; unfold tripleCharges sourceA753 sourceB753 sourceC753 difference raw12078; decide +kernel
    rw [ha]
    exact (canonical12078 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA753 + sourceB753) sourceC753) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA753 + sourceB753) sourceC753) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA753 sourceB753 sourceC753 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA753 sourceB753 sourceC753
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm753, Integer.Sparse.eval]
  linarith only [hs]

def sourceA754 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB754 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC754 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm754 : Integer.Sparse Master := [(Sum.inr 2950, 1), (Sum.inr 2952, 1), (Sum.inr 2956, 1), (Sum.inr 2962, 1), (Sum.inr 3096, 1), (Sum.inr 3572, 1), (Sum.inr 4083, -1)]

theorem sourceEq754 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm754 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA754 + difference 0 3) (sourceB754 + difference 3 0) sourceC754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA754 + difference 0 3) (sourceB754 + difference 3 0) sourceC754) = raw12513 := by
      apply Matrix.ext; unfold tripleCharges sourceA754 sourceB754 sourceC754 difference raw12513; decide +kernel
    rw [ha]
    exact (canonical12513 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA754 + difference 1 3) (sourceB754 + difference 3 1) sourceC754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2950) := by
    have ha : (tripleCharges (sourceA754 + difference 1 3) (sourceB754 + difference 3 1) sourceC754) = raw12518 := by
      apply Matrix.ext; unfold tripleCharges sourceA754 sourceB754 sourceC754 difference raw12518; decide +kernel
    rw [ha]
    exact (canonical12518 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA754 + difference 2 3) (sourceB754 + difference 3 2) sourceC754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2956) := by
    have ha : (tripleCharges (sourceA754 + difference 2 3) (sourceB754 + difference 3 2) sourceC754) = raw12522 := by
      apply Matrix.ext; unfold tripleCharges sourceA754 sourceB754 sourceC754 difference raw12522; decide +kernel
    rw [ha]
    exact (canonical12522 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA754 + difference 3 3) (sourceB754 + difference 3 3) sourceC754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA754 + difference 3 3) (sourceB754 + difference 3 3) sourceC754) = raw11769 := by
      apply Matrix.ext; unfold tripleCharges sourceA754 sourceB754 sourceC754 difference raw11769; decide +kernel
    rw [ha]
    exact (canonical11769 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA754 + difference 4 3) (sourceB754 + difference 3 4) sourceC754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3096) := by
    have ha : (tripleCharges (sourceA754 + difference 4 3) (sourceB754 + difference 3 4) sourceC754) = raw12524 := by
      apply Matrix.ext; unfold tripleCharges sourceA754 sourceB754 sourceC754 difference raw12524; decide +kernel
    rw [ha]
    exact (canonical12524 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA754 + difference 5 3) (sourceB754 + difference 3 5) sourceC754) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2962) := by
    have ha : (tripleCharges (sourceA754 + difference 5 3) (sourceB754 + difference 3 5) sourceC754) = raw12525 := by
      apply Matrix.ext; unfold tripleCharges sourceA754 sourceB754 sourceC754 difference raw12525; decide +kernel
    rw [ha]
    exact (canonical12525 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA754 + sourceB754) sourceC754) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA754 + sourceB754) sourceC754) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA754 sourceB754 sourceC754 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA754 sourceB754 sourceC754
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm754, Integer.Sparse.eval]
  linarith only [hs]

def sourceA755 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB755 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC755 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm755 : Integer.Sparse Master := [(Sum.inr 2107, 1), (Sum.inr 3096, 1), (Sum.inr 3503, 1), (Sum.inr 3572, 1), (Sum.inr 3581, 1), (Sum.inr 3583, 1), (Sum.inr 4083, -1)]

theorem sourceEq755 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm755 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA755 + difference 4 0) (sourceB755 + difference 0 4) sourceC755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA755 + difference 4 0) (sourceB755 + difference 0 4) sourceC755) = raw12526 := by
      apply Matrix.ext; unfold tripleCharges sourceA755 sourceB755 sourceC755 difference raw12526; decide +kernel
    rw [ha]
    exact (canonical12526 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA755 + difference 4 1) (sourceB755 + difference 1 4) sourceC755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3503) := by
    have ha : (tripleCharges (sourceA755 + difference 4 1) (sourceB755 + difference 1 4) sourceC755) = raw11770 := by
      apply Matrix.ext; unfold tripleCharges sourceA755 sourceB755 sourceC755 difference raw11770; decide +kernel
    rw [ha]
    exact (canonical11770 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA755 + difference 4 2) (sourceB755 + difference 2 4) sourceC755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA755 + difference 4 2) (sourceB755 + difference 2 4) sourceC755) = raw12527 := by
      apply Matrix.ext; unfold tripleCharges sourceA755 sourceB755 sourceC755 difference raw12527; decide +kernel
    rw [ha]
    exact (canonical12527 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA755 + difference 4 3) (sourceB755 + difference 3 4) sourceC755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3096) := by
    have ha : (tripleCharges (sourceA755 + difference 4 3) (sourceB755 + difference 3 4) sourceC755) = raw12524 := by
      apply Matrix.ext; unfold tripleCharges sourceA755 sourceB755 sourceC755 difference raw12524; decide +kernel
    rw [ha]
    exact (canonical12524 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA755 + difference 4 4) (sourceB755 + difference 4 4) sourceC755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA755 + difference 4 4) (sourceB755 + difference 4 4) sourceC755) = raw11769 := by
      apply Matrix.ext; unfold tripleCharges sourceA755 sourceB755 sourceC755 difference raw11769; decide +kernel
    rw [ha]
    exact (canonical11769 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA755 + difference 4 5) (sourceB755 + difference 5 4) sourceC755) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3581) := by
    have ha : (tripleCharges (sourceA755 + difference 4 5) (sourceB755 + difference 5 4) sourceC755) = raw12528 := by
      apply Matrix.ext; unfold tripleCharges sourceA755 sourceB755 sourceC755 difference raw12528; decide +kernel
    rw [ha]
    exact (canonical12528 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA755 + sourceB755) sourceC755) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA755 + sourceB755) sourceC755) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA755 sourceB755 sourceC755 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA755 sourceB755 sourceC755
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm755, Integer.Sparse.eval]
  linarith only [hs]

def sourceA756 : Charge := ![1, 0, 1, -2, -1, 1]
def sourceB756 : Charge := ![2, 0, -1, 1, 0, -2]
def sourceC756 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm756 : Integer.Sparse Master := [(Sum.inr 2995, 1), (Sum.inr 3507, 1), (Sum.inr 3550, 1), (Sum.inr 3552, 1), (Sum.inr 3572, 2), (Sum.inr 4083, -1)]

theorem sourceEq756 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm756 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA756 + difference 0 4) (sourceB756 + difference 4 0) sourceC756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3507) := by
    have ha : (tripleCharges (sourceA756 + difference 0 4) (sourceB756 + difference 4 0) sourceC756) = raw12514 := by
      apply Matrix.ext; unfold tripleCharges sourceA756 sourceB756 sourceC756 difference raw12514; decide +kernel
    rw [ha]
    exact (canonical12514 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA756 + difference 1 4) (sourceB756 + difference 4 1) sourceC756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3550) := by
    have ha : (tripleCharges (sourceA756 + difference 1 4) (sourceB756 + difference 4 1) sourceC756) = raw12519 := by
      apply Matrix.ext; unfold tripleCharges sourceA756 sourceB756 sourceC756 difference raw12519; decide +kernel
    rw [ha]
    exact (canonical12519 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA756 + difference 2 4) (sourceB756 + difference 4 2) sourceC756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3552) := by
    have ha : (tripleCharges (sourceA756 + difference 2 4) (sourceB756 + difference 4 2) sourceC756) = raw12523 := by
      apply Matrix.ext; unfold tripleCharges sourceA756 sourceB756 sourceC756 difference raw12523; decide +kernel
    rw [ha]
    exact (canonical12523 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA756 + difference 3 4) (sourceB756 + difference 4 3) sourceC756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA756 + difference 3 4) (sourceB756 + difference 4 3) sourceC756) = raw12529 := by
      apply Matrix.ext; unfold tripleCharges sourceA756 sourceB756 sourceC756 difference raw12529; decide +kernel
    rw [ha]
    exact (canonical12529 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA756 + difference 4 4) (sourceB756 + difference 4 4) sourceC756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA756 + difference 4 4) (sourceB756 + difference 4 4) sourceC756) = raw11769 := by
      apply Matrix.ext; unfold tripleCharges sourceA756 sourceB756 sourceC756 difference raw11769; decide +kernel
    rw [ha]
    exact (canonical11769 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA756 + difference 5 4) (sourceB756 + difference 4 5) sourceC756) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2995) := by
    have ha : (tripleCharges (sourceA756 + difference 5 4) (sourceB756 + difference 4 5) sourceC756) = raw12530 := by
      apply Matrix.ext; unfold tripleCharges sourceA756 sourceB756 sourceC756 difference raw12530; decide +kernel
    rw [ha]
    exact (canonical12530 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA756 + sourceB756) sourceC756) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA756 + sourceB756) sourceC756) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA756 sourceB756 sourceC756 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA756 sourceB756 sourceC756
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm756, Integer.Sparse.eval]
  linarith only [hs]

def sourceA757 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB757 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC757 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceForm757 : Integer.Sparse Master := [(Sum.inr 4601, 1), (Sum.inr 4602, 2), (Sum.inr 4606, 1), (Sum.inr 4622, 1), (Sum.inr 5148, 1), (Sum.inr 5149, 2), (Sum.inr 5167, 1), (Sum.inr 5202, 1), (Sum.inr 5203, 1), (Sum.inr 5204, 2), (Sum.inr 5283, 1), (Sum.inr 5284, 2), (Sum.inr 5292, 3), (Sum.inr 5293, 2), (Sum.inr 5294, 2), (Sum.inr 5307, 2), (Sum.inr 5433, 1), (Sum.inr 5450, 1), (Sum.inr 5452, 1), (Sum.inr 5454, 2)]

theorem sourceEq757 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm757 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA757 + difference 0 1) (sourceB757 + difference 1 0) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5433) := by
    have ha : (tripleCharges (sourceA757 + difference 0 1) (sourceB757 + difference 1 0) sourceC757) = raw12531 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12531; decide +kernel
    rw [ha]
    exact (canonical12531 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA757 + difference 0 2) (sourceB757 + difference 2 0) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5450) := by
    have ha : (tripleCharges (sourceA757 + difference 0 2) (sourceB757 + difference 2 0) sourceC757) = raw12532 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12532; decide +kernel
    rw [ha]
    exact (canonical12532 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA757 + difference 0 3) (sourceB757 + difference 3 0) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA757 + difference 0 3) (sourceB757 + difference 3 0) sourceC757) = raw12533 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12533; decide +kernel
    rw [ha]
    exact (canonical12533 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA757 + difference 0 4) (sourceB757 + difference 4 0) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5454) := by
    have ha : (tripleCharges (sourceA757 + difference 0 4) (sourceB757 + difference 4 0) sourceC757) = raw12534 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12534; decide +kernel
    rw [ha]
    exact (canonical12534 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA757 + difference 0 5) (sourceB757 + difference 5 0) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5452) := by
    have ha : (tripleCharges (sourceA757 + difference 0 5) (sourceB757 + difference 5 0) sourceC757) = raw12535 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12535; decide +kernel
    rw [ha]
    exact (canonical12535 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA757 + difference 1 0) (sourceB757 + difference 0 1) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4601) := by
    have ha : (tripleCharges (sourceA757 + difference 1 0) (sourceB757 + difference 0 1) sourceC757) = raw12536 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12536; decide +kernel
    rw [ha]
    exact (canonical12536 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA757 + difference 1 2) (sourceB757 + difference 2 1) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5202) := by
    have ha : (tripleCharges (sourceA757 + difference 1 2) (sourceB757 + difference 2 1) sourceC757) = raw12537 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12537; decide +kernel
    rw [ha]
    exact (canonical12537 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA757 + difference 1 3) (sourceB757 + difference 3 1) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA757 + difference 1 3) (sourceB757 + difference 3 1) sourceC757) = raw12538 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12538; decide +kernel
    rw [ha]
    exact (canonical12538 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA757 + difference 1 4) (sourceB757 + difference 4 1) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA757 + difference 1 4) (sourceB757 + difference 4 1) sourceC757) = raw12539 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12539; decide +kernel
    rw [ha]
    exact (canonical12539 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA757 + difference 1 5) (sourceB757 + difference 5 1) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5283) := by
    have ha : (tripleCharges (sourceA757 + difference 1 5) (sourceB757 + difference 5 1) sourceC757) = raw12540 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12540; decide +kernel
    rw [ha]
    exact (canonical12540 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA757 + difference 2 0) (sourceB757 + difference 0 2) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4622) := by
    have ha : (tripleCharges (sourceA757 + difference 2 0) (sourceB757 + difference 0 2) sourceC757) = raw12541 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12541; decide +kernel
    rw [ha]
    exact (canonical12541 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA757 + difference 2 1) (sourceB757 + difference 1 2) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA757 + difference 2 1) (sourceB757 + difference 1 2) sourceC757) = raw12542 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12542; decide +kernel
    rw [ha]
    exact (canonical12542 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA757 + difference 2 3) (sourceB757 + difference 3 2) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA757 + difference 2 3) (sourceB757 + difference 3 2) sourceC757) = raw12543 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12543; decide +kernel
    rw [ha]
    exact (canonical12543 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA757 + difference 2 4) (sourceB757 + difference 4 2) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA757 + difference 2 4) (sourceB757 + difference 4 2) sourceC757) = raw12544 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12544; decide +kernel
    rw [ha]
    exact (canonical12544 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA757 + difference 2 5) (sourceB757 + difference 5 2) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA757 + difference 2 5) (sourceB757 + difference 5 2) sourceC757) = raw12545 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12545; decide +kernel
    rw [ha]
    exact (canonical12545 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA757 + difference 3 0) (sourceB757 + difference 0 3) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA757 + difference 3 0) (sourceB757 + difference 0 3) sourceC757) = raw12546 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12546; decide +kernel
    rw [ha]
    exact (canonical12546 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA757 + difference 3 1) (sourceB757 + difference 1 3) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA757 + difference 3 1) (sourceB757 + difference 1 3) sourceC757) = raw12547 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12547; decide +kernel
    rw [ha]
    exact (canonical12547 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA757 + difference 3 2) (sourceB757 + difference 2 3) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA757 + difference 3 2) (sourceB757 + difference 2 3) sourceC757) = raw12548 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12548; decide +kernel
    rw [ha]
    exact (canonical12548 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA757 + difference 3 4) (sourceB757 + difference 4 3) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA757 + difference 3 4) (sourceB757 + difference 4 3) sourceC757) = raw12549 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12549; decide +kernel
    rw [ha]
    exact (canonical12549 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA757 + difference 3 5) (sourceB757 + difference 5 3) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA757 + difference 3 5) (sourceB757 + difference 5 3) sourceC757) = raw12550 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12550; decide +kernel
    rw [ha]
    exact (canonical12550 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA757 + difference 4 0) (sourceB757 + difference 0 4) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4602) := by
    have ha : (tripleCharges (sourceA757 + difference 4 0) (sourceB757 + difference 0 4) sourceC757) = raw12551 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12551; decide +kernel
    rw [ha]
    exact (canonical12551 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA757 + difference 4 1) (sourceB757 + difference 1 4) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5149) := by
    have ha : (tripleCharges (sourceA757 + difference 4 1) (sourceB757 + difference 1 4) sourceC757) = raw12552 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12552; decide +kernel
    rw [ha]
    exact (canonical12552 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA757 + difference 4 2) (sourceB757 + difference 2 4) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5204) := by
    have ha : (tripleCharges (sourceA757 + difference 4 2) (sourceB757 + difference 2 4) sourceC757) = raw12553 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12553; decide +kernel
    rw [ha]
    exact (canonical12553 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA757 + difference 4 3) (sourceB757 + difference 3 4) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA757 + difference 4 3) (sourceB757 + difference 3 4) sourceC757) = raw12554 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12554; decide +kernel
    rw [ha]
    exact (canonical12554 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA757 + difference 4 5) (sourceB757 + difference 5 4) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5284) := by
    have ha : (tripleCharges (sourceA757 + difference 4 5) (sourceB757 + difference 5 4) sourceC757) = raw12555 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12555; decide +kernel
    rw [ha]
    exact (canonical12555 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA757 + difference 5 0) (sourceB757 + difference 0 5) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4606) := by
    have ha : (tripleCharges (sourceA757 + difference 5 0) (sourceB757 + difference 0 5) sourceC757) = raw12556 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12556; decide +kernel
    rw [ha]
    exact (canonical12556 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA757 + difference 5 1) (sourceB757 + difference 1 5) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5148) := by
    have ha : (tripleCharges (sourceA757 + difference 5 1) (sourceB757 + difference 1 5) sourceC757) = raw12557 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12557; decide +kernel
    rw [ha]
    exact (canonical12557 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA757 + difference 5 2) (sourceB757 + difference 2 5) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5203) := by
    have ha : (tripleCharges (sourceA757 + difference 5 2) (sourceB757 + difference 2 5) sourceC757) = raw12558 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12558; decide +kernel
    rw [ha]
    exact (canonical12558 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA757 + difference 5 3) (sourceB757 + difference 3 5) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA757 + difference 5 3) (sourceB757 + difference 3 5) sourceC757) = raw12559 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12559; decide +kernel
    rw [ha]
    exact (canonical12559 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA757 + difference 5 4) (sourceB757 + difference 4 5) sourceC757) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA757 + difference 5 4) (sourceB757 + difference 4 5) sourceC757) = raw12560 := by
      apply Matrix.ext; unfold tripleCharges sourceA757 sourceB757 sourceC757 difference raw12560; decide +kernel
    rw [ha]
    exact (canonical12560 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA757 sourceB757 sourceC757
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm757, Integer.Sparse.eval]
  linarith only [hs]

def sourceA758 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB758 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceC758 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceForm758 : Integer.Sparse Master := [(Sum.inr 1235, 1), (Sum.inr 1236, 2), (Sum.inr 1240, 1), (Sum.inr 1299, 1), (Sum.inr 2880, 1), (Sum.inr 2881, 2), (Sum.inr 2884, 1), (Sum.inr 2924, 2), (Sum.inr 2927, 1), (Sum.inr 2958, 1), (Sum.inr 3076, 1), (Sum.inr 3077, 2), (Sum.inr 3100, 3), (Sum.inr 3101, 2), (Sum.inr 3102, 2), (Sum.inr 3122, 2), (Sum.inr 4029, 1), (Sum.inr 4033, 1), (Sum.inr 4039, 1), (Sum.inr 4040, 2)]

theorem sourceEq758 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm758 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA758 + difference 0 1) (sourceB758 + difference 1 0) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4033) := by
    have ha : (tripleCharges (sourceA758 + difference 0 1) (sourceB758 + difference 1 0) sourceC758) = raw12561 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12561; decide +kernel
    rw [ha]
    exact (canonical12561 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA758 + difference 0 2) (sourceB758 + difference 2 0) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4029) := by
    have ha : (tripleCharges (sourceA758 + difference 0 2) (sourceB758 + difference 2 0) sourceC758) = raw12562 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12562; decide +kernel
    rw [ha]
    exact (canonical12562 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA758 + difference 0 3) (sourceB758 + difference 3 0) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4040) := by
    have ha : (tripleCharges (sourceA758 + difference 0 3) (sourceB758 + difference 3 0) sourceC758) = raw12563 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12563; decide +kernel
    rw [ha]
    exact (canonical12563 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA758 + difference 0 4) (sourceB758 + difference 4 0) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4040) := by
    have ha : (tripleCharges (sourceA758 + difference 0 4) (sourceB758 + difference 4 0) sourceC758) = raw12564 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12564; decide +kernel
    rw [ha]
    exact (canonical12564 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA758 + difference 0 5) (sourceB758 + difference 5 0) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4039) := by
    have ha : (tripleCharges (sourceA758 + difference 0 5) (sourceB758 + difference 5 0) sourceC758) = raw12565 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12565; decide +kernel
    rw [ha]
    exact (canonical12565 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA758 + difference 1 0) (sourceB758 + difference 0 1) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA758 + difference 1 0) (sourceB758 + difference 0 1) sourceC758) = raw12566 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12566; decide +kernel
    rw [ha]
    exact (canonical12566 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA758 + difference 1 2) (sourceB758 + difference 2 1) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2880) := by
    have ha : (tripleCharges (sourceA758 + difference 1 2) (sourceB758 + difference 2 1) sourceC758) = raw12567 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12567; decide +kernel
    rw [ha]
    exact (canonical12567 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA758 + difference 1 3) (sourceB758 + difference 3 1) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA758 + difference 1 3) (sourceB758 + difference 3 1) sourceC758) = raw12568 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12568; decide +kernel
    rw [ha]
    exact (canonical12568 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA758 + difference 1 4) (sourceB758 + difference 4 1) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA758 + difference 1 4) (sourceB758 + difference 4 1) sourceC758) = raw12569 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12569; decide +kernel
    rw [ha]
    exact (canonical12569 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA758 + difference 1 5) (sourceB758 + difference 5 1) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3076) := by
    have ha : (tripleCharges (sourceA758 + difference 1 5) (sourceB758 + difference 5 1) sourceC758) = raw12570 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12570; decide +kernel
    rw [ha]
    exact (canonical12570 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA758 + difference 2 0) (sourceB758 + difference 0 2) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1299) := by
    have ha : (tripleCharges (sourceA758 + difference 2 0) (sourceB758 + difference 0 2) sourceC758) = raw12571 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12571; decide +kernel
    rw [ha]
    exact (canonical12571 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA758 + difference 2 1) (sourceB758 + difference 1 2) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2958) := by
    have ha : (tripleCharges (sourceA758 + difference 2 1) (sourceB758 + difference 1 2) sourceC758) = raw12572 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12572; decide +kernel
    rw [ha]
    exact (canonical12572 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA758 + difference 2 3) (sourceB758 + difference 3 2) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3122) := by
    have ha : (tripleCharges (sourceA758 + difference 2 3) (sourceB758 + difference 3 2) sourceC758) = raw12573 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12573; decide +kernel
    rw [ha]
    exact (canonical12573 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA758 + difference 2 4) (sourceB758 + difference 4 2) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3122) := by
    have ha : (tripleCharges (sourceA758 + difference 2 4) (sourceB758 + difference 4 2) sourceC758) = raw12574 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12574; decide +kernel
    rw [ha]
    exact (canonical12574 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA758 + difference 2 5) (sourceB758 + difference 5 2) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3100) := by
    have ha : (tripleCharges (sourceA758 + difference 2 5) (sourceB758 + difference 5 2) sourceC758) = raw12575 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12575; decide +kernel
    rw [ha]
    exact (canonical12575 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA758 + difference 3 0) (sourceB758 + difference 0 3) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA758 + difference 3 0) (sourceB758 + difference 0 3) sourceC758) = raw12576 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12576; decide +kernel
    rw [ha]
    exact (canonical12576 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA758 + difference 3 1) (sourceB758 + difference 1 3) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA758 + difference 3 1) (sourceB758 + difference 1 3) sourceC758) = raw12577 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12577; decide +kernel
    rw [ha]
    exact (canonical12577 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA758 + difference 3 2) (sourceB758 + difference 2 3) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA758 + difference 3 2) (sourceB758 + difference 2 3) sourceC758) = raw12578 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12578; decide +kernel
    rw [ha]
    exact (canonical12578 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA758 + difference 3 4) (sourceB758 + difference 4 3) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA758 + difference 3 4) (sourceB758 + difference 4 3) sourceC758) = raw12579 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12579; decide +kernel
    rw [ha]
    exact (canonical12579 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA758 + difference 3 5) (sourceB758 + difference 5 3) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA758 + difference 3 5) (sourceB758 + difference 5 3) sourceC758) = raw12580 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12580; decide +kernel
    rw [ha]
    exact (canonical12580 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA758 + difference 4 0) (sourceB758 + difference 0 4) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA758 + difference 4 0) (sourceB758 + difference 0 4) sourceC758) = raw12581 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12581; decide +kernel
    rw [ha]
    exact (canonical12581 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA758 + difference 4 1) (sourceB758 + difference 1 4) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA758 + difference 4 1) (sourceB758 + difference 1 4) sourceC758) = raw12582 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12582; decide +kernel
    rw [ha]
    exact (canonical12582 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA758 + difference 4 2) (sourceB758 + difference 2 4) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA758 + difference 4 2) (sourceB758 + difference 2 4) sourceC758) = raw12583 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12583; decide +kernel
    rw [ha]
    exact (canonical12583 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA758 + difference 4 3) (sourceB758 + difference 3 4) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3101) := by
    have ha : (tripleCharges (sourceA758 + difference 4 3) (sourceB758 + difference 3 4) sourceC758) = raw12584 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12584; decide +kernel
    rw [ha]
    exact (canonical12584 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA758 + difference 4 5) (sourceB758 + difference 5 4) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA758 + difference 4 5) (sourceB758 + difference 5 4) sourceC758) = raw12585 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12585; decide +kernel
    rw [ha]
    exact (canonical12585 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA758 + difference 5 0) (sourceB758 + difference 0 5) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA758 + difference 5 0) (sourceB758 + difference 0 5) sourceC758) = raw12586 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12586; decide +kernel
    rw [ha]
    exact (canonical12586 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA758 + difference 5 1) (sourceB758 + difference 1 5) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2927) := by
    have ha : (tripleCharges (sourceA758 + difference 5 1) (sourceB758 + difference 1 5) sourceC758) = raw12587 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12587; decide +kernel
    rw [ha]
    exact (canonical12587 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA758 + difference 5 2) (sourceB758 + difference 2 5) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA758 + difference 5 2) (sourceB758 + difference 2 5) sourceC758) = raw12588 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12588; decide +kernel
    rw [ha]
    exact (canonical12588 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA758 + difference 5 3) (sourceB758 + difference 3 5) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA758 + difference 5 3) (sourceB758 + difference 3 5) sourceC758) = raw12589 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12589; decide +kernel
    rw [ha]
    exact (canonical12589 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA758 + difference 5 4) (sourceB758 + difference 4 5) sourceC758) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3102) := by
    have ha : (tripleCharges (sourceA758 + difference 5 4) (sourceB758 + difference 4 5) sourceC758) = raw12590 := by
      apply Matrix.ext; unfold tripleCharges sourceA758 sourceB758 sourceC758 difference raw12590; decide +kernel
    rw [ha]
    exact (canonical12590 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA758 sourceB758 sourceC758
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm758, Integer.Sparse.eval]
  linarith only [hs]

def sourceA759 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB759 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC759 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceForm759 : Integer.Sparse Master := [(Sum.inr 4456, 1), (Sum.inr 4457, 1), (Sum.inr 4458, 2), (Sum.inr 4495, 1), (Sum.inr 5072, 1), (Sum.inr 5073, 2), (Sum.inr 5098, 1), (Sum.inr 5167, 1), (Sum.inr 5168, 1), (Sum.inr 5169, 2), (Sum.inr 5257, 2), (Sum.inr 5258, 2), (Sum.inr 5259, 2), (Sum.inr 5271, 2), (Sum.inr 5292, 1), (Sum.inr 5293, 2), (Sum.inr 5306, 1), (Sum.inr 5482, 1), (Sum.inr 5486, 1), (Sum.inr 5490, 2), (Sum.inr 5493, 1)]

theorem sourceEq759 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm759 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA759 + difference 0 1) (sourceB759 + difference 1 0) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5482) := by
    have ha : (tripleCharges (sourceA759 + difference 0 1) (sourceB759 + difference 1 0) sourceC759) = raw12591 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12591; decide +kernel
    rw [ha]
    exact (canonical12591 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA759 + difference 0 2) (sourceB759 + difference 2 0) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5486) := by
    have ha : (tripleCharges (sourceA759 + difference 0 2) (sourceB759 + difference 2 0) sourceC759) = raw12592 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12592; decide +kernel
    rw [ha]
    exact (canonical12592 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA759 + difference 0 3) (sourceB759 + difference 3 0) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA759 + difference 0 3) (sourceB759 + difference 3 0) sourceC759) = raw12593 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12593; decide +kernel
    rw [ha]
    exact (canonical12593 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA759 + difference 0 4) (sourceB759 + difference 4 0) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5490) := by
    have ha : (tripleCharges (sourceA759 + difference 0 4) (sourceB759 + difference 4 0) sourceC759) = raw12594 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12594; decide +kernel
    rw [ha]
    exact (canonical12594 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA759 + difference 0 5) (sourceB759 + difference 5 0) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5493) := by
    have ha : (tripleCharges (sourceA759 + difference 0 5) (sourceB759 + difference 5 0) sourceC759) = raw12595 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12595; decide +kernel
    rw [ha]
    exact (canonical12595 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA759 + difference 1 0) (sourceB759 + difference 0 1) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4456) := by
    have ha : (tripleCharges (sourceA759 + difference 1 0) (sourceB759 + difference 0 1) sourceC759) = raw12596 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12596; decide +kernel
    rw [ha]
    exact (canonical12596 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA759 + difference 1 2) (sourceB759 + difference 2 1) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5167) := by
    have ha : (tripleCharges (sourceA759 + difference 1 2) (sourceB759 + difference 2 1) sourceC759) = raw12597 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12597; decide +kernel
    rw [ha]
    exact (canonical12597 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA759 + difference 1 3) (sourceB759 + difference 3 1) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA759 + difference 1 3) (sourceB759 + difference 3 1) sourceC759) = raw12598 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12598; decide +kernel
    rw [ha]
    exact (canonical12598 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA759 + difference 1 4) (sourceB759 + difference 4 1) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA759 + difference 1 4) (sourceB759 + difference 4 1) sourceC759) = raw12599 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12599; decide +kernel
    rw [ha]
    exact (canonical12599 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA759 + difference 1 5) (sourceB759 + difference 5 1) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA759 + difference 1 5) (sourceB759 + difference 5 1) sourceC759) = raw12600 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12600; decide +kernel
    rw [ha]
    exact (canonical12600 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA759 + difference 2 0) (sourceB759 + difference 0 2) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4495) := by
    have ha : (tripleCharges (sourceA759 + difference 2 0) (sourceB759 + difference 0 2) sourceC759) = raw12601 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12601; decide +kernel
    rw [ha]
    exact (canonical12601 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA759 + difference 2 1) (sourceB759 + difference 1 2) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5098) := by
    have ha : (tripleCharges (sourceA759 + difference 2 1) (sourceB759 + difference 1 2) sourceC759) = raw12602 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12602; decide +kernel
    rw [ha]
    exact (canonical12602 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA759 + difference 2 3) (sourceB759 + difference 3 2) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA759 + difference 2 3) (sourceB759 + difference 3 2) sourceC759) = raw12603 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12603; decide +kernel
    rw [ha]
    exact (canonical12603 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA759 + difference 2 4) (sourceB759 + difference 4 2) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA759 + difference 2 4) (sourceB759 + difference 4 2) sourceC759) = raw12604 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12604; decide +kernel
    rw [ha]
    exact (canonical12604 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA759 + difference 2 5) (sourceB759 + difference 5 2) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA759 + difference 2 5) (sourceB759 + difference 5 2) sourceC759) = raw12605 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12605; decide +kernel
    rw [ha]
    exact (canonical12605 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA759 + difference 3 0) (sourceB759 + difference 0 3) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA759 + difference 3 0) (sourceB759 + difference 0 3) sourceC759) = raw12606 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12606; decide +kernel
    rw [ha]
    exact (canonical12606 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA759 + difference 3 1) (sourceB759 + difference 1 3) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA759 + difference 3 1) (sourceB759 + difference 1 3) sourceC759) = raw12607 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12607; decide +kernel
    rw [ha]
    exact (canonical12607 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA759 + difference 3 2) (sourceB759 + difference 2 3) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA759 + difference 3 2) (sourceB759 + difference 2 3) sourceC759) = raw12608 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12608; decide +kernel
    rw [ha]
    exact (canonical12608 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA759 + difference 3 4) (sourceB759 + difference 4 3) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA759 + difference 3 4) (sourceB759 + difference 4 3) sourceC759) = raw12609 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12609; decide +kernel
    rw [ha]
    exact (canonical12609 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA759 + difference 3 5) (sourceB759 + difference 5 3) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA759 + difference 3 5) (sourceB759 + difference 5 3) sourceC759) = raw12610 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12610; decide +kernel
    rw [ha]
    exact (canonical12610 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA759 + difference 4 0) (sourceB759 + difference 0 4) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4458) := by
    have ha : (tripleCharges (sourceA759 + difference 4 0) (sourceB759 + difference 0 4) sourceC759) = raw12611 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12611; decide +kernel
    rw [ha]
    exact (canonical12611 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA759 + difference 4 1) (sourceB759 + difference 1 4) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5073) := by
    have ha : (tripleCharges (sourceA759 + difference 4 1) (sourceB759 + difference 1 4) sourceC759) = raw12612 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12612; decide +kernel
    rw [ha]
    exact (canonical12612 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA759 + difference 4 2) (sourceB759 + difference 2 4) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5169) := by
    have ha : (tripleCharges (sourceA759 + difference 4 2) (sourceB759 + difference 2 4) sourceC759) = raw12613 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12613; decide +kernel
    rw [ha]
    exact (canonical12613 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA759 + difference 4 3) (sourceB759 + difference 3 4) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5259) := by
    have ha : (tripleCharges (sourceA759 + difference 4 3) (sourceB759 + difference 3 4) sourceC759) = raw12614 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12614; decide +kernel
    rw [ha]
    exact (canonical12614 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA759 + difference 4 5) (sourceB759 + difference 5 4) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5293) := by
    have ha : (tripleCharges (sourceA759 + difference 4 5) (sourceB759 + difference 5 4) sourceC759) = raw12615 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12615; decide +kernel
    rw [ha]
    exact (canonical12615 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA759 + difference 5 0) (sourceB759 + difference 0 5) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4457) := by
    have ha : (tripleCharges (sourceA759 + difference 5 0) (sourceB759 + difference 0 5) sourceC759) = raw12616 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12616; decide +kernel
    rw [ha]
    exact (canonical12616 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA759 + difference 5 1) (sourceB759 + difference 1 5) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5072) := by
    have ha : (tripleCharges (sourceA759 + difference 5 1) (sourceB759 + difference 1 5) sourceC759) = raw12617 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12617; decide +kernel
    rw [ha]
    exact (canonical12617 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA759 + difference 5 2) (sourceB759 + difference 2 5) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5168) := by
    have ha : (tripleCharges (sourceA759 + difference 5 2) (sourceB759 + difference 2 5) sourceC759) = raw12618 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12618; decide +kernel
    rw [ha]
    exact (canonical12618 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA759 + difference 5 3) (sourceB759 + difference 3 5) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA759 + difference 5 3) (sourceB759 + difference 3 5) sourceC759) = raw12619 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12619; decide +kernel
    rw [ha]
    exact (canonical12619 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA759 + difference 5 4) (sourceB759 + difference 4 5) sourceC759) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5258) := by
    have ha : (tripleCharges (sourceA759 + difference 5 4) (sourceB759 + difference 4 5) sourceC759) = raw12620 := by
      apply Matrix.ext; unfold tripleCharges sourceA759 sourceB759 sourceC759 difference raw12620; decide +kernel
    rw [ha]
    exact (canonical12620 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA759 sourceB759 sourceC759
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm759, Integer.Sparse.eval]
  linarith only [hs]

def sourceA760 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB760 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC760 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceForm760 : Integer.Sparse Master := [(Sum.inr 1039, 1), (Sum.inr 1040, 1), (Sum.inr 1041, 2), (Sum.inr 1079, 1), (Sum.inr 2479, 1), (Sum.inr 2480, 2), (Sum.inr 2508, 1), (Sum.inr 2593, 1), (Sum.inr 2594, 1), (Sum.inr 2595, 2), (Sum.inr 2721, 2), (Sum.inr 2722, 2), (Sum.inr 2723, 2), (Sum.inr 2739, 2), (Sum.inr 2766, 1), (Sum.inr 2767, 2), (Sum.inr 2784, 1), (Sum.inr 3980, 1), (Sum.inr 3999, 1), (Sum.inr 4013, 2), (Sum.inr 4018, 1)]

theorem sourceEq760 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm760 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA760 + difference 0 1) (sourceB760 + difference 1 0) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3980) := by
    have ha : (tripleCharges (sourceA760 + difference 0 1) (sourceB760 + difference 1 0) sourceC760) = raw12621 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12621; decide +kernel
    rw [ha]
    exact (canonical12621 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA760 + difference 0 2) (sourceB760 + difference 2 0) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3999) := by
    have ha : (tripleCharges (sourceA760 + difference 0 2) (sourceB760 + difference 2 0) sourceC760) = raw12622 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12622; decide +kernel
    rw [ha]
    exact (canonical12622 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA760 + difference 0 3) (sourceB760 + difference 3 0) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA760 + difference 0 3) (sourceB760 + difference 3 0) sourceC760) = raw12623 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12623; decide +kernel
    rw [ha]
    exact (canonical12623 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA760 + difference 0 4) (sourceB760 + difference 4 0) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4013) := by
    have ha : (tripleCharges (sourceA760 + difference 0 4) (sourceB760 + difference 4 0) sourceC760) = raw12624 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12624; decide +kernel
    rw [ha]
    exact (canonical12624 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA760 + difference 0 5) (sourceB760 + difference 5 0) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4018) := by
    have ha : (tripleCharges (sourceA760 + difference 0 5) (sourceB760 + difference 5 0) sourceC760) = raw12625 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12625; decide +kernel
    rw [ha]
    exact (canonical12625 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA760 + difference 1 0) (sourceB760 + difference 0 1) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1039) := by
    have ha : (tripleCharges (sourceA760 + difference 1 0) (sourceB760 + difference 0 1) sourceC760) = raw12626 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12626; decide +kernel
    rw [ha]
    exact (canonical12626 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA760 + difference 1 2) (sourceB760 + difference 2 1) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2593) := by
    have ha : (tripleCharges (sourceA760 + difference 1 2) (sourceB760 + difference 2 1) sourceC760) = raw12627 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12627; decide +kernel
    rw [ha]
    exact (canonical12627 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA760 + difference 1 3) (sourceB760 + difference 3 1) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA760 + difference 1 3) (sourceB760 + difference 3 1) sourceC760) = raw12628 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12628; decide +kernel
    rw [ha]
    exact (canonical12628 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA760 + difference 1 4) (sourceB760 + difference 4 1) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2721) := by
    have ha : (tripleCharges (sourceA760 + difference 1 4) (sourceB760 + difference 4 1) sourceC760) = raw12629 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12629; decide +kernel
    rw [ha]
    exact (canonical12629 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA760 + difference 1 5) (sourceB760 + difference 5 1) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2766) := by
    have ha : (tripleCharges (sourceA760 + difference 1 5) (sourceB760 + difference 5 1) sourceC760) = raw12630 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12630; decide +kernel
    rw [ha]
    exact (canonical12630 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA760 + difference 2 0) (sourceB760 + difference 0 2) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA760 + difference 2 0) (sourceB760 + difference 0 2) sourceC760) = raw12631 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12631; decide +kernel
    rw [ha]
    exact (canonical12631 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA760 + difference 2 1) (sourceB760 + difference 1 2) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA760 + difference 2 1) (sourceB760 + difference 1 2) sourceC760) = raw12632 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12632; decide +kernel
    rw [ha]
    exact (canonical12632 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA760 + difference 2 3) (sourceB760 + difference 3 2) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA760 + difference 2 3) (sourceB760 + difference 3 2) sourceC760) = raw12633 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12633; decide +kernel
    rw [ha]
    exact (canonical12633 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA760 + difference 2 4) (sourceB760 + difference 4 2) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA760 + difference 2 4) (sourceB760 + difference 4 2) sourceC760) = raw12634 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12634; decide +kernel
    rw [ha]
    exact (canonical12634 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA760 + difference 2 5) (sourceB760 + difference 5 2) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2784) := by
    have ha : (tripleCharges (sourceA760 + difference 2 5) (sourceB760 + difference 5 2) sourceC760) = raw12635 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12635; decide +kernel
    rw [ha]
    exact (canonical12635 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA760 + difference 3 0) (sourceB760 + difference 0 3) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA760 + difference 3 0) (sourceB760 + difference 0 3) sourceC760) = raw12636 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12636; decide +kernel
    rw [ha]
    exact (canonical12636 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA760 + difference 3 1) (sourceB760 + difference 1 3) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA760 + difference 3 1) (sourceB760 + difference 1 3) sourceC760) = raw12637 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12637; decide +kernel
    rw [ha]
    exact (canonical12637 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA760 + difference 3 2) (sourceB760 + difference 2 3) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA760 + difference 3 2) (sourceB760 + difference 2 3) sourceC760) = raw12638 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12638; decide +kernel
    rw [ha]
    exact (canonical12638 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA760 + difference 3 4) (sourceB760 + difference 4 3) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA760 + difference 3 4) (sourceB760 + difference 4 3) sourceC760) = raw12639 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12639; decide +kernel
    rw [ha]
    exact (canonical12639 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA760 + difference 3 5) (sourceB760 + difference 5 3) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA760 + difference 3 5) (sourceB760 + difference 5 3) sourceC760) = raw12640 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12640; decide +kernel
    rw [ha]
    exact (canonical12640 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA760 + difference 4 0) (sourceB760 + difference 0 4) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA760 + difference 4 0) (sourceB760 + difference 0 4) sourceC760) = raw12641 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12641; decide +kernel
    rw [ha]
    exact (canonical12641 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA760 + difference 4 1) (sourceB760 + difference 1 4) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA760 + difference 4 1) (sourceB760 + difference 1 4) sourceC760) = raw12642 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12642; decide +kernel
    rw [ha]
    exact (canonical12642 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA760 + difference 4 2) (sourceB760 + difference 2 4) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2595) := by
    have ha : (tripleCharges (sourceA760 + difference 4 2) (sourceB760 + difference 2 4) sourceC760) = raw12643 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12643; decide +kernel
    rw [ha]
    exact (canonical12643 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA760 + difference 4 3) (sourceB760 + difference 3 4) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2723) := by
    have ha : (tripleCharges (sourceA760 + difference 4 3) (sourceB760 + difference 3 4) sourceC760) = raw12644 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12644; decide +kernel
    rw [ha]
    exact (canonical12644 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA760 + difference 4 5) (sourceB760 + difference 5 4) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2767) := by
    have ha : (tripleCharges (sourceA760 + difference 4 5) (sourceB760 + difference 5 4) sourceC760) = raw12645 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12645; decide +kernel
    rw [ha]
    exact (canonical12645 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA760 + difference 5 0) (sourceB760 + difference 0 5) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1040) := by
    have ha : (tripleCharges (sourceA760 + difference 5 0) (sourceB760 + difference 0 5) sourceC760) = raw12646 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12646; decide +kernel
    rw [ha]
    exact (canonical12646 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA760 + difference 5 1) (sourceB760 + difference 1 5) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2479) := by
    have ha : (tripleCharges (sourceA760 + difference 5 1) (sourceB760 + difference 1 5) sourceC760) = raw12647 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12647; decide +kernel
    rw [ha]
    exact (canonical12647 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA760 + difference 5 2) (sourceB760 + difference 2 5) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2594) := by
    have ha : (tripleCharges (sourceA760 + difference 5 2) (sourceB760 + difference 2 5) sourceC760) = raw12648 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12648; decide +kernel
    rw [ha]
    exact (canonical12648 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA760 + difference 5 3) (sourceB760 + difference 3 5) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA760 + difference 5 3) (sourceB760 + difference 3 5) sourceC760) = raw12649 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12649; decide +kernel
    rw [ha]
    exact (canonical12649 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA760 + difference 5 4) (sourceB760 + difference 4 5) sourceC760) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA760 + difference 5 4) (sourceB760 + difference 4 5) sourceC760) = raw12650 := by
      apply Matrix.ext; unfold tripleCharges sourceA760 sourceB760 sourceC760 difference raw12650; decide +kernel
    rw [ha]
    exact (canonical12650 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA760 sourceB760 sourceC760
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm760, Integer.Sparse.eval]
  linarith only [hs]

def sourceA761 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceB761 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC761 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm761 : Integer.Sparse Master := [(Sum.inr 4887, 1), (Sum.inr 4888, 1), (Sum.inr 4889, 1), (Sum.inr 4893, 2), (Sum.inr 5256, 1), (Sum.inr 5257, 3), (Sum.inr 5265, 1), (Sum.inr 5271, 2), (Sum.inr 5273, 1), (Sum.inr 5281, 2), (Sum.inr 5283, 1), (Sum.inr 5289, 2), (Sum.inr 5290, 2), (Sum.inr 5292, 3), (Sum.inr 5299, 2), (Sum.inr 5301, 1), (Sum.inr 5306, 1), (Sum.inr 5307, 3)]

theorem sourceEq761 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm761 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA761 + difference 0 1) (sourceB761 + difference 1 0) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA761 + difference 0 1) (sourceB761 + difference 1 0) sourceC761) = raw11664 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw11664; decide +kernel
    rw [ha]
    exact (canonical11664 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA761 + difference 0 2) (sourceB761 + difference 2 0) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA761 + difference 0 2) (sourceB761 + difference 2 0) sourceC761) = raw12186 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12186; decide +kernel
    rw [ha]
    exact (canonical12186 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA761 + difference 0 3) (sourceB761 + difference 3 0) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA761 + difference 0 3) (sourceB761 + difference 3 0) sourceC761) = raw12463 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12463; decide +kernel
    rw [ha]
    exact (canonical12463 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA761 + difference 0 4) (sourceB761 + difference 4 0) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA761 + difference 0 4) (sourceB761 + difference 4 0) sourceC761) = raw12651 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12651; decide +kernel
    rw [ha]
    exact (canonical12651 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA761 + difference 0 5) (sourceB761 + difference 5 0) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5273) := by
    have ha : (tripleCharges (sourceA761 + difference 0 5) (sourceB761 + difference 5 0) sourceC761) = raw12652 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12652; decide +kernel
    rw [ha]
    exact (canonical12652 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA761 + difference 1 0) (sourceB761 + difference 0 1) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4887) := by
    have ha : (tripleCharges (sourceA761 + difference 1 0) (sourceB761 + difference 0 1) sourceC761) = raw12653 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12653; decide +kernel
    rw [ha]
    exact (canonical12653 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA761 + difference 1 2) (sourceB761 + difference 2 1) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA761 + difference 1 2) (sourceB761 + difference 2 1) sourceC761) = raw12191 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12191; decide +kernel
    rw [ha]
    exact (canonical12191 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA761 + difference 1 3) (sourceB761 + difference 3 1) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA761 + difference 1 3) (sourceB761 + difference 3 1) sourceC761) = raw12467 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12467; decide +kernel
    rw [ha]
    exact (canonical12467 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA761 + difference 1 4) (sourceB761 + difference 4 1) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5281) := by
    have ha : (tripleCharges (sourceA761 + difference 1 4) (sourceB761 + difference 4 1) sourceC761) = raw12654 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12654; decide +kernel
    rw [ha]
    exact (canonical12654 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA761 + difference 1 5) (sourceB761 + difference 5 1) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5283) := by
    have ha : (tripleCharges (sourceA761 + difference 1 5) (sourceB761 + difference 5 1) sourceC761) = raw12655 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12655; decide +kernel
    rw [ha]
    exact (canonical12655 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA761 + difference 2 0) (sourceB761 + difference 0 2) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4889) := by
    have ha : (tripleCharges (sourceA761 + difference 2 0) (sourceB761 + difference 0 2) sourceC761) = raw12002 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12002; decide +kernel
    rw [ha]
    exact (canonical12002 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA761 + difference 2 1) (sourceB761 + difference 1 2) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA761 + difference 2 1) (sourceB761 + difference 1 2) sourceC761) = raw11674 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw11674; decide +kernel
    rw [ha]
    exact (canonical11674 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA761 + difference 2 3) (sourceB761 + difference 3 2) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA761 + difference 2 3) (sourceB761 + difference 3 2) sourceC761) = raw12003 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12003; decide +kernel
    rw [ha]
    exact (canonical12003 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA761 + difference 2 4) (sourceB761 + difference 4 2) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA761 + difference 2 4) (sourceB761 + difference 4 2) sourceC761) = raw12004 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12004; decide +kernel
    rw [ha]
    exact (canonical12004 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA761 + difference 2 5) (sourceB761 + difference 5 2) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5301) := by
    have ha : (tripleCharges (sourceA761 + difference 2 5) (sourceB761 + difference 5 2) sourceC761) = raw12005 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12005; decide +kernel
    rw [ha]
    exact (canonical12005 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA761 + difference 3 0) (sourceB761 + difference 0 3) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA761 + difference 3 0) (sourceB761 + difference 0 3) sourceC761) = raw12656 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12656; decide +kernel
    rw [ha]
    exact (canonical12656 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA761 + difference 3 1) (sourceB761 + difference 1 3) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA761 + difference 3 1) (sourceB761 + difference 1 3) sourceC761) = raw11679 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw11679; decide +kernel
    rw [ha]
    exact (canonical11679 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA761 + difference 3 2) (sourceB761 + difference 2 3) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA761 + difference 3 2) (sourceB761 + difference 2 3) sourceC761) = raw12195 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12195; decide +kernel
    rw [ha]
    exact (canonical12195 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA761 + difference 3 4) (sourceB761 + difference 4 3) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA761 + difference 3 4) (sourceB761 + difference 4 3) sourceC761) = raw12657 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12657; decide +kernel
    rw [ha]
    exact (canonical12657 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA761 + difference 3 5) (sourceB761 + difference 5 3) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA761 + difference 3 5) (sourceB761 + difference 5 3) sourceC761) = raw12658 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12658; decide +kernel
    rw [ha]
    exact (canonical12658 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA761 + difference 4 0) (sourceB761 + difference 0 4) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4893) := by
    have ha : (tripleCharges (sourceA761 + difference 4 0) (sourceB761 + difference 0 4) sourceC761) = raw12659 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12659; decide +kernel
    rw [ha]
    exact (canonical12659 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA761 + difference 4 1) (sourceB761 + difference 1 4) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5257) := by
    have ha : (tripleCharges (sourceA761 + difference 4 1) (sourceB761 + difference 1 4) sourceC761) = raw11684 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw11684; decide +kernel
    rw [ha]
    exact (canonical11684 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA761 + difference 4 2) (sourceB761 + difference 2 4) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5307) := by
    have ha : (tripleCharges (sourceA761 + difference 4 2) (sourceB761 + difference 2 4) sourceC761) = raw12199 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12199; decide +kernel
    rw [ha]
    exact (canonical12199 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA761 + difference 4 3) (sourceB761 + difference 3 4) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA761 + difference 4 3) (sourceB761 + difference 3 4) sourceC761) = raw12473 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12473; decide +kernel
    rw [ha]
    exact (canonical12473 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA761 + difference 4 5) (sourceB761 + difference 5 4) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5292) := by
    have ha : (tripleCharges (sourceA761 + difference 4 5) (sourceB761 + difference 5 4) sourceC761) = raw12660 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12660; decide +kernel
    rw [ha]
    exact (canonical12660 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA761 + difference 5 0) (sourceB761 + difference 0 5) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4888) := by
    have ha : (tripleCharges (sourceA761 + difference 5 0) (sourceB761 + difference 0 5) sourceC761) = raw11665 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw11665; decide +kernel
    rw [ha]
    exact (canonical11665 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA761 + difference 5 1) (sourceB761 + difference 1 5) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5256) := by
    have ha : (tripleCharges (sourceA761 + difference 5 1) (sourceB761 + difference 1 5) sourceC761) = raw12019 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw12019; decide +kernel
    rw [ha]
    exact (canonical12019 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA761 + difference 5 2) (sourceB761 + difference 2 5) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5306) := by
    have ha : (tripleCharges (sourceA761 + difference 5 2) (sourceB761 + difference 2 5) sourceC761) = raw11666 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw11666; decide +kernel
    rw [ha]
    exact (canonical11666 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA761 + difference 5 3) (sourceB761 + difference 3 5) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA761 + difference 5 3) (sourceB761 + difference 3 5) sourceC761) = raw11667 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw11667; decide +kernel
    rw [ha]
    exact (canonical11667 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA761 + difference 5 4) (sourceB761 + difference 4 5) sourceC761) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA761 + difference 5 4) (sourceB761 + difference 4 5) sourceC761) = raw11668 := by
      apply Matrix.ext; unfold tripleCharges sourceA761 sourceB761 sourceC761 difference raw11668; decide +kernel
    rw [ha]
    exact (canonical11668 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA761 sourceB761 sourceC761
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm761, Integer.Sparse.eval]
  linarith only [hs]

def sourceA762 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceB762 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC762 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm762 : Integer.Sparse Master := [(Sum.inr 3532, 1), (Sum.inr 3534, 2), (Sum.inr 3546, 1), (Sum.inr 3622, 1), (Sum.inr 3628, 1), (Sum.inr 4083, -1)]

theorem sourceEq762 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm762 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA762 + difference 0 0) (sourceB762 + difference 0 0) sourceC762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3622) := by
    have ha : (tripleCharges (sourceA762 + difference 0 0) (sourceB762 + difference 0 0) sourceC762) = raw12661 := by
      apply Matrix.ext; unfold tripleCharges sourceA762 sourceB762 sourceC762 difference raw12661; decide +kernel
    rw [ha]
    exact (canonical12661 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA762 + difference 0 1) (sourceB762 + difference 1 0) sourceC762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3532) := by
    have ha : (tripleCharges (sourceA762 + difference 0 1) (sourceB762 + difference 1 0) sourceC762) = raw11755 := by
      apply Matrix.ext; unfold tripleCharges sourceA762 sourceB762 sourceC762 difference raw11755; decide +kernel
    rw [ha]
    exact (canonical11755 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA762 + difference 0 2) (sourceB762 + difference 2 0) sourceC762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3628) := by
    have ha : (tripleCharges (sourceA762 + difference 0 2) (sourceB762 + difference 2 0) sourceC762) = raw12229 := by
      apply Matrix.ext; unfold tripleCharges sourceA762 sourceB762 sourceC762 difference raw12229; decide +kernel
    rw [ha]
    exact (canonical12229 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA762 + difference 0 3) (sourceB762 + difference 3 0) sourceC762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA762 + difference 0 3) (sourceB762 + difference 3 0) sourceC762) = raw12515 := by
      apply Matrix.ext; unfold tripleCharges sourceA762 sourceB762 sourceC762 difference raw12515; decide +kernel
    rw [ha]
    exact (canonical12515 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA762 + difference 0 4) (sourceB762 + difference 4 0) sourceC762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA762 + difference 0 4) (sourceB762 + difference 4 0) sourceC762) = raw12662 := by
      apply Matrix.ext; unfold tripleCharges sourceA762 sourceB762 sourceC762 difference raw12662; decide +kernel
    rw [ha]
    exact (canonical12662 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA762 + difference 0 5) (sourceB762 + difference 5 0) sourceC762) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3546) := by
    have ha : (tripleCharges (sourceA762 + difference 0 5) (sourceB762 + difference 5 0) sourceC762) = raw12663 := by
      apply Matrix.ext; unfold tripleCharges sourceA762 sourceB762 sourceC762 difference raw12663; decide +kernel
    rw [ha]
    exact (canonical12663 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA762 + sourceB762) sourceC762) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA762 + sourceB762) sourceC762) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA762 sourceB762 sourceC762 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA762 sourceB762 sourceC762
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm762, Integer.Sparse.eval]
  linarith only [hs]

def sourceA763 : Charge := ![1, 0, 1, -1, -1, 0]
def sourceB763 : Charge := ![2, 0, -1, 0, 0, -1]
def sourceC763 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceForm763 : Integer.Sparse Master := [(Sum.inr 2243, 1), (Sum.inr 3571, 2), (Sum.inr 3618, 1), (Sum.inr 3622, 2), (Sum.inr 4083, -1)]

theorem sourceEq763 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm763 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA763 + difference 1 0) (sourceB763 + difference 0 1) sourceC763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2243) := by
    have ha : (tripleCharges (sourceA763 + difference 1 0) (sourceB763 + difference 0 1) sourceC763) = raw12664 := by
      apply Matrix.ext; unfold tripleCharges sourceA763 sourceB763 sourceC763 difference raw12664; decide +kernel
    rw [ha]
    exact (canonical12664 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA763 + difference 1 1) (sourceB763 + difference 1 1) sourceC763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3622) := by
    have ha : (tripleCharges (sourceA763 + difference 1 1) (sourceB763 + difference 1 1) sourceC763) = raw12661 := by
      apply Matrix.ext; unfold tripleCharges sourceA763 sourceB763 sourceC763 difference raw12661; decide +kernel
    rw [ha]
    exact (canonical12661 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA763 + difference 1 2) (sourceB763 + difference 2 1) sourceC763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3622) := by
    have ha : (tripleCharges (sourceA763 + difference 1 2) (sourceB763 + difference 2 1) sourceC763) = raw12665 := by
      apply Matrix.ext; unfold tripleCharges sourceA763 sourceB763 sourceC763 difference raw12665; decide +kernel
    rw [ha]
    exact (canonical12665 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA763 + difference 1 3) (sourceB763 + difference 3 1) sourceC763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA763 + difference 1 3) (sourceB763 + difference 3 1) sourceC763) = raw12520 := by
      apply Matrix.ext; unfold tripleCharges sourceA763 sourceB763 sourceC763 difference raw12520; decide +kernel
    rw [ha]
    exact (canonical12520 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA763 + difference 1 4) (sourceB763 + difference 4 1) sourceC763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3571) := by
    have ha : (tripleCharges (sourceA763 + difference 1 4) (sourceB763 + difference 4 1) sourceC763) = raw12666 := by
      apply Matrix.ext; unfold tripleCharges sourceA763 sourceB763 sourceC763 difference raw12666; decide +kernel
    rw [ha]
    exact (canonical12666 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA763 + difference 1 5) (sourceB763 + difference 5 1) sourceC763) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3618) := by
    have ha : (tripleCharges (sourceA763 + difference 1 5) (sourceB763 + difference 5 1) sourceC763) = raw12667 := by
      apply Matrix.ext; unfold tripleCharges sourceA763 sourceB763 sourceC763 difference raw12667; decide +kernel
    rw [ha]
    exact (canonical12667 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA763 + sourceB763) sourceC763) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA763 + sourceB763) sourceC763) = raw11756 := by
      apply Matrix.ext; unfold doubleCharges sourceA763 sourceB763 sourceC763 raw11756; decide +kernel
    rw [ha]
    exact (canonical11756 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA763 sourceB763 sourceC763
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm763, Integer.Sparse.eval]
  linarith only [hs]

def sourceA764 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB764 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceC764 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceForm764 : Integer.Sparse Master := [(Sum.inr 4566, 1), (Sum.inr 4567, 1), (Sum.inr 4568, 1), (Sum.inr 4571, 1), (Sum.inr 4616, 1), (Sum.inr 5060, 1), (Sum.inr 5062, 1), (Sum.inr 5103, 1), (Sum.inr 5153, 1), (Sum.inr 5154, 1), (Sum.inr 5160, 1), (Sum.inr 5208, 1), (Sum.inr 5210, 1), (Sum.inr 5211, 1), (Sum.inr 5265, 1), (Sum.inr 5266, 2), (Sum.inr 5267, 1), (Sum.inr 5271, 1), (Sum.inr 5276, 1), (Sum.inr 5286, 1), (Sum.inr 5287, 1), (Sum.inr 5289, 1), (Sum.inr 5299, 1), (Sum.inr 5300, 1), (Sum.inr 5304, 1), (Sum.inr 5411, 1), (Sum.inr 5425, 1), (Sum.inr 5435, 1), (Sum.inr 5443, 1)]

theorem sourceEq764 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm764 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA764 + difference 0 1) (sourceB764 + difference 1 0) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5425) := by
    have ha : (tripleCharges (sourceA764 + difference 0 1) (sourceB764 + difference 1 0) sourceC764) = raw12668 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12668; decide +kernel
    rw [ha]
    exact (canonical12668 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA764 + difference 0 2) (sourceB764 + difference 2 0) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA764 + difference 0 2) (sourceB764 + difference 2 0) sourceC764) = raw12669 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12669; decide +kernel
    rw [ha]
    exact (canonical12669 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA764 + difference 0 3) (sourceB764 + difference 3 0) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5435) := by
    have ha : (tripleCharges (sourceA764 + difference 0 3) (sourceB764 + difference 3 0) sourceC764) = raw12670 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12670; decide +kernel
    rw [ha]
    exact (canonical12670 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA764 + difference 0 4) (sourceB764 + difference 4 0) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5443) := by
    have ha : (tripleCharges (sourceA764 + difference 0 4) (sourceB764 + difference 4 0) sourceC764) = raw12671 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12671; decide +kernel
    rw [ha]
    exact (canonical12671 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA764 + difference 0 5) (sourceB764 + difference 5 0) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5411) := by
    have ha : (tripleCharges (sourceA764 + difference 0 5) (sourceB764 + difference 5 0) sourceC764) = raw12672 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12672; decide +kernel
    rw [ha]
    exact (canonical12672 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA764 + difference 1 0) (sourceB764 + difference 0 1) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4566) := by
    have ha : (tripleCharges (sourceA764 + difference 1 0) (sourceB764 + difference 0 1) sourceC764) = raw12673 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12673; decide +kernel
    rw [ha]
    exact (canonical12673 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA764 + difference 1 2) (sourceB764 + difference 2 1) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5208) := by
    have ha : (tripleCharges (sourceA764 + difference 1 2) (sourceB764 + difference 2 1) sourceC764) = raw12674 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12674; decide +kernel
    rw [ha]
    exact (canonical12674 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA764 + difference 1 3) (sourceB764 + difference 3 1) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5265) := by
    have ha : (tripleCharges (sourceA764 + difference 1 3) (sourceB764 + difference 3 1) sourceC764) = raw12675 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12675; decide +kernel
    rw [ha]
    exact (canonical12675 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA764 + difference 1 4) (sourceB764 + difference 4 1) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5299) := by
    have ha : (tripleCharges (sourceA764 + difference 1 4) (sourceB764 + difference 4 1) sourceC764) = raw12676 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12676; decide +kernel
    rw [ha]
    exact (canonical12676 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA764 + difference 1 5) (sourceB764 + difference 5 1) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5286) := by
    have ha : (tripleCharges (sourceA764 + difference 1 5) (sourceB764 + difference 5 1) sourceC764) = raw12677 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12677; decide +kernel
    rw [ha]
    exact (canonical12677 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA764 + difference 2 0) (sourceB764 + difference 0 2) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4616) := by
    have ha : (tripleCharges (sourceA764 + difference 2 0) (sourceB764 + difference 0 2) sourceC764) = raw12678 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12678; decide +kernel
    rw [ha]
    exact (canonical12678 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA764 + difference 2 1) (sourceB764 + difference 1 2) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5160) := by
    have ha : (tripleCharges (sourceA764 + difference 2 1) (sourceB764 + difference 1 2) sourceC764) = raw12679 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12679; decide +kernel
    rw [ha]
    exact (canonical12679 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA764 + difference 2 3) (sourceB764 + difference 3 2) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5271) := by
    have ha : (tripleCharges (sourceA764 + difference 2 3) (sourceB764 + difference 3 2) sourceC764) = raw12680 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12680; decide +kernel
    rw [ha]
    exact (canonical12680 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA764 + difference 2 4) (sourceB764 + difference 4 2) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA764 + difference 2 4) (sourceB764 + difference 4 2) sourceC764) = raw12681 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12681; decide +kernel
    rw [ha]
    exact (canonical12681 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA764 + difference 2 5) (sourceB764 + difference 5 2) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5289) := by
    have ha : (tripleCharges (sourceA764 + difference 2 5) (sourceB764 + difference 5 2) sourceC764) = raw12682 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12682; decide +kernel
    rw [ha]
    exact (canonical12682 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA764 + difference 3 0) (sourceB764 + difference 0 3) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4567) := by
    have ha : (tripleCharges (sourceA764 + difference 3 0) (sourceB764 + difference 0 3) sourceC764) = raw12683 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12683; decide +kernel
    rw [ha]
    exact (canonical12683 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA764 + difference 3 1) (sourceB764 + difference 1 3) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5060) := by
    have ha : (tripleCharges (sourceA764 + difference 3 1) (sourceB764 + difference 1 3) sourceC764) = raw12684 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12684; decide +kernel
    rw [ha]
    exact (canonical12684 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA764 + difference 3 2) (sourceB764 + difference 2 3) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5062) := by
    have ha : (tripleCharges (sourceA764 + difference 3 2) (sourceB764 + difference 2 3) sourceC764) = raw12685 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12685; decide +kernel
    rw [ha]
    exact (canonical12685 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA764 + difference 3 4) (sourceB764 + difference 4 3) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5276) := by
    have ha : (tripleCharges (sourceA764 + difference 3 4) (sourceB764 + difference 4 3) sourceC764) = raw12686 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12686; decide +kernel
    rw [ha]
    exact (canonical12686 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA764 + difference 3 5) (sourceB764 + difference 5 3) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5103) := by
    have ha : (tripleCharges (sourceA764 + difference 3 5) (sourceB764 + difference 5 3) sourceC764) = raw12687 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12687; decide +kernel
    rw [ha]
    exact (canonical12687 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA764 + difference 4 0) (sourceB764 + difference 0 4) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4568) := by
    have ha : (tripleCharges (sourceA764 + difference 4 0) (sourceB764 + difference 0 4) sourceC764) = raw12688 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12688; decide +kernel
    rw [ha]
    exact (canonical12688 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA764 + difference 4 1) (sourceB764 + difference 1 4) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5154) := by
    have ha : (tripleCharges (sourceA764 + difference 4 1) (sourceB764 + difference 1 4) sourceC764) = raw12689 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12689; decide +kernel
    rw [ha]
    exact (canonical12689 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA764 + difference 4 2) (sourceB764 + difference 2 4) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5210) := by
    have ha : (tripleCharges (sourceA764 + difference 4 2) (sourceB764 + difference 2 4) sourceC764) = raw12690 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12690; decide +kernel
    rw [ha]
    exact (canonical12690 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA764 + difference 4 3) (sourceB764 + difference 3 4) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5267) := by
    have ha : (tripleCharges (sourceA764 + difference 4 3) (sourceB764 + difference 3 4) sourceC764) = raw12691 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12691; decide +kernel
    rw [ha]
    exact (canonical12691 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA764 + difference 4 5) (sourceB764 + difference 5 4) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5287) := by
    have ha : (tripleCharges (sourceA764 + difference 4 5) (sourceB764 + difference 5 4) sourceC764) = raw12692 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12692; decide +kernel
    rw [ha]
    exact (canonical12692 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA764 + difference 5 0) (sourceB764 + difference 0 5) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4571) := by
    have ha : (tripleCharges (sourceA764 + difference 5 0) (sourceB764 + difference 0 5) sourceC764) = raw12693 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12693; decide +kernel
    rw [ha]
    exact (canonical12693 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA764 + difference 5 1) (sourceB764 + difference 1 5) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5153) := by
    have ha : (tripleCharges (sourceA764 + difference 5 1) (sourceB764 + difference 1 5) sourceC764) = raw12694 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12694; decide +kernel
    rw [ha]
    exact (canonical12694 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA764 + difference 5 2) (sourceB764 + difference 2 5) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5211) := by
    have ha : (tripleCharges (sourceA764 + difference 5 2) (sourceB764 + difference 2 5) sourceC764) = raw12695 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12695; decide +kernel
    rw [ha]
    exact (canonical12695 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA764 + difference 5 3) (sourceB764 + difference 3 5) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5266) := by
    have ha : (tripleCharges (sourceA764 + difference 5 3) (sourceB764 + difference 3 5) sourceC764) = raw12696 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12696; decide +kernel
    rw [ha]
    exact (canonical12696 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA764 + difference 5 4) (sourceB764 + difference 4 5) sourceC764) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5300) := by
    have ha : (tripleCharges (sourceA764 + difference 5 4) (sourceB764 + difference 4 5) sourceC764) = raw12697 := by
      apply Matrix.ext; unfold tripleCharges sourceA764 sourceB764 sourceC764 difference raw12697; decide +kernel
    rw [ha]
    exact (canonical12697 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA764 sourceB764 sourceC764
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm764, Integer.Sparse.eval]
  linarith only [hs]

def sourceA765 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB765 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceC765 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceForm765 : Integer.Sparse Master := [(Sum.inr 1183, 1), (Sum.inr 1184, 1), (Sum.inr 1185, 1), (Sum.inr 1189, 1), (Sum.inr 1291, 1), (Sum.inr 2836, 1), (Sum.inr 2837, 1), (Sum.inr 2838, 1), (Sum.inr 2841, 1), (Sum.inr 2906, 1), (Sum.inr 2907, 1), (Sum.inr 2909, 1), (Sum.inr 2951, 1), (Sum.inr 3023, 1), (Sum.inr 3024, 1), (Sum.inr 3025, 1), (Sum.inr 3037, 1), (Sum.inr 3038, 1), (Sum.inr 3039, 1), (Sum.inr 3051, 1), (Sum.inr 3052, 1), (Sum.inr 3055, 1), (Sum.inr 3097, 1), (Sum.inr 3109, 1), (Sum.inr 3119, 1), (Sum.inr 3535, 1), (Sum.inr 3809, 1), (Sum.inr 3839, 1), (Sum.inr 3853, 1), (Sum.inr 3862, 1)]

theorem sourceEq765 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm765 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA765 + difference 0 1) (sourceB765 + difference 1 0) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA765 + difference 0 1) (sourceB765 + difference 1 0) sourceC765) = raw12698 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12698; decide +kernel
    rw [ha]
    exact (canonical12698 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA765 + difference 0 2) (sourceB765 + difference 2 0) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA765 + difference 0 2) (sourceB765 + difference 2 0) sourceC765) = raw12699 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12699; decide +kernel
    rw [ha]
    exact (canonical12699 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA765 + difference 0 3) (sourceB765 + difference 3 0) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA765 + difference 0 3) (sourceB765 + difference 3 0) sourceC765) = raw12700 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12700; decide +kernel
    rw [ha]
    exact (canonical12700 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA765 + difference 0 4) (sourceB765 + difference 4 0) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3862) := by
    have ha : (tripleCharges (sourceA765 + difference 0 4) (sourceB765 + difference 4 0) sourceC765) = raw12701 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12701; decide +kernel
    rw [ha]
    exact (canonical12701 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA765 + difference 0 5) (sourceB765 + difference 5 0) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA765 + difference 0 5) (sourceB765 + difference 5 0) sourceC765) = raw12702 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12702; decide +kernel
    rw [ha]
    exact (canonical12702 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA765 + difference 1 0) (sourceB765 + difference 0 1) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1183) := by
    have ha : (tripleCharges (sourceA765 + difference 1 0) (sourceB765 + difference 0 1) sourceC765) = raw12703 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12703; decide +kernel
    rw [ha]
    exact (canonical12703 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA765 + difference 1 2) (sourceB765 + difference 2 1) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2836) := by
    have ha : (tripleCharges (sourceA765 + difference 1 2) (sourceB765 + difference 2 1) sourceC765) = raw12704 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12704; decide +kernel
    rw [ha]
    exact (canonical12704 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA765 + difference 1 3) (sourceB765 + difference 3 1) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3037) := by
    have ha : (tripleCharges (sourceA765 + difference 1 3) (sourceB765 + difference 3 1) sourceC765) = raw12705 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12705; decide +kernel
    rw [ha]
    exact (canonical12705 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA765 + difference 1 4) (sourceB765 + difference 4 1) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA765 + difference 1 4) (sourceB765 + difference 4 1) sourceC765) = raw12706 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12706; decide +kernel
    rw [ha]
    exact (canonical12706 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA765 + difference 1 5) (sourceB765 + difference 5 1) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3023) := by
    have ha : (tripleCharges (sourceA765 + difference 1 5) (sourceB765 + difference 5 1) sourceC765) = raw12707 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12707; decide +kernel
    rw [ha]
    exact (canonical12707 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA765 + difference 2 0) (sourceB765 + difference 0 2) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA765 + difference 2 0) (sourceB765 + difference 0 2) sourceC765) = raw12708 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12708; decide +kernel
    rw [ha]
    exact (canonical12708 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA765 + difference 2 1) (sourceB765 + difference 1 2) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2951) := by
    have ha : (tripleCharges (sourceA765 + difference 2 1) (sourceB765 + difference 1 2) sourceC765) = raw12709 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12709; decide +kernel
    rw [ha]
    exact (canonical12709 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA765 + difference 2 3) (sourceB765 + difference 3 2) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3109) := by
    have ha : (tripleCharges (sourceA765 + difference 2 3) (sourceB765 + difference 3 2) sourceC765) = raw12710 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12710; decide +kernel
    rw [ha]
    exact (canonical12710 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA765 + difference 2 4) (sourceB765 + difference 4 2) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3119) := by
    have ha : (tripleCharges (sourceA765 + difference 2 4) (sourceB765 + difference 4 2) sourceC765) = raw12711 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12711; decide +kernel
    rw [ha]
    exact (canonical12711 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA765 + difference 2 5) (sourceB765 + difference 5 2) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA765 + difference 2 5) (sourceB765 + difference 5 2) sourceC765) = raw12712 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12712; decide +kernel
    rw [ha]
    exact (canonical12712 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA765 + difference 3 0) (sourceB765 + difference 0 3) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1184) := by
    have ha : (tripleCharges (sourceA765 + difference 3 0) (sourceB765 + difference 0 3) sourceC765) = raw12713 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12713; decide +kernel
    rw [ha]
    exact (canonical12713 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA765 + difference 3 1) (sourceB765 + difference 1 3) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2906) := by
    have ha : (tripleCharges (sourceA765 + difference 3 1) (sourceB765 + difference 1 3) sourceC765) = raw12714 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12714; decide +kernel
    rw [ha]
    exact (canonical12714 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA765 + difference 3 2) (sourceB765 + difference 2 3) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2837) := by
    have ha : (tripleCharges (sourceA765 + difference 3 2) (sourceB765 + difference 2 3) sourceC765) = raw12715 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12715; decide +kernel
    rw [ha]
    exact (canonical12715 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA765 + difference 3 4) (sourceB765 + difference 4 3) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA765 + difference 3 4) (sourceB765 + difference 4 3) sourceC765) = raw12716 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12716; decide +kernel
    rw [ha]
    exact (canonical12716 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA765 + difference 3 5) (sourceB765 + difference 5 3) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA765 + difference 3 5) (sourceB765 + difference 5 3) sourceC765) = raw12717 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12717; decide +kernel
    rw [ha]
    exact (canonical12717 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA765 + difference 4 0) (sourceB765 + difference 0 4) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1185) := by
    have ha : (tripleCharges (sourceA765 + difference 4 0) (sourceB765 + difference 0 4) sourceC765) = raw12718 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12718; decide +kernel
    rw [ha]
    exact (canonical12718 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA765 + difference 4 1) (sourceB765 + difference 1 4) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2907) := by
    have ha : (tripleCharges (sourceA765 + difference 4 1) (sourceB765 + difference 1 4) sourceC765) = raw12719 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12719; decide +kernel
    rw [ha]
    exact (canonical12719 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA765 + difference 4 2) (sourceB765 + difference 2 4) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2838) := by
    have ha : (tripleCharges (sourceA765 + difference 4 2) (sourceB765 + difference 2 4) sourceC765) = raw12720 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12720; decide +kernel
    rw [ha]
    exact (canonical12720 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA765 + difference 4 3) (sourceB765 + difference 3 4) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA765 + difference 4 3) (sourceB765 + difference 3 4) sourceC765) = raw12721 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12721; decide +kernel
    rw [ha]
    exact (canonical12721 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA765 + difference 4 5) (sourceB765 + difference 5 4) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3025) := by
    have ha : (tripleCharges (sourceA765 + difference 4 5) (sourceB765 + difference 5 4) sourceC765) = raw12722 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12722; decide +kernel
    rw [ha]
    exact (canonical12722 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA765 + difference 5 0) (sourceB765 + difference 0 5) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1189) := by
    have ha : (tripleCharges (sourceA765 + difference 5 0) (sourceB765 + difference 0 5) sourceC765) = raw12723 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12723; decide +kernel
    rw [ha]
    exact (canonical12723 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA765 + difference 5 1) (sourceB765 + difference 1 5) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2909) := by
    have ha : (tripleCharges (sourceA765 + difference 5 1) (sourceB765 + difference 1 5) sourceC765) = raw12724 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12724; decide +kernel
    rw [ha]
    exact (canonical12724 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA765 + difference 5 2) (sourceB765 + difference 2 5) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2841) := by
    have ha : (tripleCharges (sourceA765 + difference 5 2) (sourceB765 + difference 2 5) sourceC765) = raw12725 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12725; decide +kernel
    rw [ha]
    exact (canonical12725 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA765 + difference 5 3) (sourceB765 + difference 3 5) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA765 + difference 5 3) (sourceB765 + difference 3 5) sourceC765) = raw12726 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12726; decide +kernel
    rw [ha]
    exact (canonical12726 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA765 + difference 5 4) (sourceB765 + difference 4 5) sourceC765) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA765 + difference 5 4) (sourceB765 + difference 4 5) sourceC765) = raw12727 := by
      apply Matrix.ext; unfold tripleCharges sourceA765 sourceB765 sourceC765 difference raw12727; decide +kernel
    rw [ha]
    exact (canonical12727 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA765 sourceB765 sourceC765
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm765, Integer.Sparse.eval]
  linarith only [hs]

def sourceA766 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB766 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceC766 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceForm766 : Integer.Sparse Master := [(Sum.inr 2463, 1), (Sum.inr 2465, 1), (Sum.inr 2466, 1), (Sum.inr 2513, 1), (Sum.inr 2744, 1), (Sum.inr 2834, 1), (Sum.inr 2835, 1), (Sum.inr 2841, 1), (Sum.inr 3039, 1), (Sum.inr 3239, 1), (Sum.inr 3240, 1), (Sum.inr 3246, 1), (Sum.inr 3303, 1), (Sum.inr 3526, 1), (Sum.inr 3534, 1), (Sum.inr 3535, 1), (Sum.inr 3541, 1), (Sum.inr 3558, 1), (Sum.inr 3559, 1), (Sum.inr 3561, 1), (Sum.inr 3567, 1), (Sum.inr 3572, 1), (Sum.inr 3573, 1), (Sum.inr 3577, 1), (Sum.inr 3583, 1), (Sum.inr 3584, 1), (Sum.inr 3853, 1), (Sum.inr 3872, 1), (Sum.inr 3883, 1), (Sum.inr 3889, 1)]

theorem sourceEq766 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm766 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA766 + difference 0 1) (sourceB766 + difference 1 0) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA766 + difference 0 1) (sourceB766 + difference 1 0) sourceC766) = raw12728 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12728; decide +kernel
    rw [ha]
    exact (canonical12728 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA766 + difference 0 2) (sourceB766 + difference 2 0) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3039) := by
    have ha : (tripleCharges (sourceA766 + difference 0 2) (sourceB766 + difference 2 0) sourceC766) = raw12729 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12729; decide +kernel
    rw [ha]
    exact (canonical12729 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA766 + difference 0 3) (sourceB766 + difference 3 0) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3853) := by
    have ha : (tripleCharges (sourceA766 + difference 0 3) (sourceB766 + difference 3 0) sourceC766) = raw12730 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12730; decide +kernel
    rw [ha]
    exact (canonical12730 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA766 + difference 0 4) (sourceB766 + difference 4 0) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3889) := by
    have ha : (tripleCharges (sourceA766 + difference 0 4) (sourceB766 + difference 4 0) sourceC766) = raw12731 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12731; decide +kernel
    rw [ha]
    exact (canonical12731 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA766 + difference 0 5) (sourceB766 + difference 5 0) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3883) := by
    have ha : (tripleCharges (sourceA766 + difference 0 5) (sourceB766 + difference 5 0) sourceC766) = raw12732 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12732; decide +kernel
    rw [ha]
    exact (canonical12732 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA766 + difference 1 0) (sourceB766 + difference 0 1) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3239) := by
    have ha : (tripleCharges (sourceA766 + difference 1 0) (sourceB766 + difference 0 1) sourceC766) = raw12733 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12733; decide +kernel
    rw [ha]
    exact (canonical12733 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA766 + difference 1 2) (sourceB766 + difference 2 1) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2834) := by
    have ha : (tripleCharges (sourceA766 + difference 1 2) (sourceB766 + difference 2 1) sourceC766) = raw12734 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12734; decide +kernel
    rw [ha]
    exact (canonical12734 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA766 + difference 1 3) (sourceB766 + difference 3 1) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3526) := by
    have ha : (tripleCharges (sourceA766 + difference 1 3) (sourceB766 + difference 3 1) sourceC766) = raw12735 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12735; decide +kernel
    rw [ha]
    exact (canonical12735 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA766 + difference 1 4) (sourceB766 + difference 4 1) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3573) := by
    have ha : (tripleCharges (sourceA766 + difference 1 4) (sourceB766 + difference 4 1) sourceC766) = raw12736 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12736; decide +kernel
    rw [ha]
    exact (canonical12736 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA766 + difference 1 5) (sourceB766 + difference 5 1) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3567) := by
    have ha : (tripleCharges (sourceA766 + difference 1 5) (sourceB766 + difference 5 1) sourceC766) = raw12737 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12737; decide +kernel
    rw [ha]
    exact (canonical12737 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA766 + difference 2 0) (sourceB766 + difference 0 2) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3303) := by
    have ha : (tripleCharges (sourceA766 + difference 2 0) (sourceB766 + difference 0 2) sourceC766) = raw12738 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12738; decide +kernel
    rw [ha]
    exact (canonical12738 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA766 + difference 2 1) (sourceB766 + difference 1 2) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA766 + difference 2 1) (sourceB766 + difference 1 2) sourceC766) = raw12739 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12739; decide +kernel
    rw [ha]
    exact (canonical12739 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA766 + difference 2 3) (sourceB766 + difference 3 2) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3534) := by
    have ha : (tripleCharges (sourceA766 + difference 2 3) (sourceB766 + difference 3 2) sourceC766) = raw12740 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12740; decide +kernel
    rw [ha]
    exact (canonical12740 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA766 + difference 2 4) (sourceB766 + difference 4 2) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA766 + difference 2 4) (sourceB766 + difference 4 2) sourceC766) = raw12741 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12741; decide +kernel
    rw [ha]
    exact (canonical12741 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA766 + difference 2 5) (sourceB766 + difference 5 2) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA766 + difference 2 5) (sourceB766 + difference 5 2) sourceC766) = raw12742 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12742; decide +kernel
    rw [ha]
    exact (canonical12742 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA766 + difference 3 0) (sourceB766 + difference 0 3) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2466) := by
    have ha : (tripleCharges (sourceA766 + difference 3 0) (sourceB766 + difference 0 3) sourceC766) = raw12743 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12743; decide +kernel
    rw [ha]
    exact (canonical12743 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA766 + difference 3 1) (sourceB766 + difference 1 3) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2463) := by
    have ha : (tripleCharges (sourceA766 + difference 3 1) (sourceB766 + difference 1 3) sourceC766) = raw12744 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12744; decide +kernel
    rw [ha]
    exact (canonical12744 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA766 + difference 3 2) (sourceB766 + difference 2 3) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2465) := by
    have ha : (tripleCharges (sourceA766 + difference 3 2) (sourceB766 + difference 2 3) sourceC766) = raw12745 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12745; decide +kernel
    rw [ha]
    exact (canonical12745 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA766 + difference 3 4) (sourceB766 + difference 4 3) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA766 + difference 3 4) (sourceB766 + difference 4 3) sourceC766) = raw12746 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12746; decide +kernel
    rw [ha]
    exact (canonical12746 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA766 + difference 3 5) (sourceB766 + difference 5 3) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2513) := by
    have ha : (tripleCharges (sourceA766 + difference 3 5) (sourceB766 + difference 5 3) sourceC766) = raw12747 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12747; decide +kernel
    rw [ha]
    exact (canonical12747 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA766 + difference 4 0) (sourceB766 + difference 0 4) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3240) := by
    have ha : (tripleCharges (sourceA766 + difference 4 0) (sourceB766 + difference 0 4) sourceC766) = raw12748 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12748; decide +kernel
    rw [ha]
    exact (canonical12748 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA766 + difference 4 1) (sourceB766 + difference 1 4) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3561) := by
    have ha : (tripleCharges (sourceA766 + difference 4 1) (sourceB766 + difference 1 4) sourceC766) = raw12749 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12749; decide +kernel
    rw [ha]
    exact (canonical12749 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA766 + difference 4 2) (sourceB766 + difference 2 4) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2835) := by
    have ha : (tripleCharges (sourceA766 + difference 4 2) (sourceB766 + difference 2 4) sourceC766) = raw12750 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12750; decide +kernel
    rw [ha]
    exact (canonical12750 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA766 + difference 4 3) (sourceB766 + difference 3 4) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA766 + difference 4 3) (sourceB766 + difference 3 4) sourceC766) = raw12751 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12751; decide +kernel
    rw [ha]
    exact (canonical12751 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA766 + difference 4 5) (sourceB766 + difference 5 4) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3577) := by
    have ha : (tripleCharges (sourceA766 + difference 4 5) (sourceB766 + difference 5 4) sourceC766) = raw12752 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12752; decide +kernel
    rw [ha]
    exact (canonical12752 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA766 + difference 5 0) (sourceB766 + difference 0 5) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3246) := by
    have ha : (tripleCharges (sourceA766 + difference 5 0) (sourceB766 + difference 0 5) sourceC766) = raw12753 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12753; decide +kernel
    rw [ha]
    exact (canonical12753 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA766 + difference 5 1) (sourceB766 + difference 1 5) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3559) := by
    have ha : (tripleCharges (sourceA766 + difference 5 1) (sourceB766 + difference 1 5) sourceC766) = raw12754 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12754; decide +kernel
    rw [ha]
    exact (canonical12754 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA766 + difference 5 2) (sourceB766 + difference 2 5) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2841) := by
    have ha : (tripleCharges (sourceA766 + difference 5 2) (sourceB766 + difference 2 5) sourceC766) = raw12755 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12755; decide +kernel
    rw [ha]
    exact (canonical12755 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA766 + difference 5 3) (sourceB766 + difference 3 5) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA766 + difference 5 3) (sourceB766 + difference 3 5) sourceC766) = raw12756 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12756; decide +kernel
    rw [ha]
    exact (canonical12756 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA766 + difference 5 4) (sourceB766 + difference 4 5) sourceC766) (![0, 1, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA766 + difference 5 4) (sourceB766 + difference 4 5) sourceC766) = raw12757 := by
      apply Matrix.ext; unfold tripleCharges sourceA766 sourceB766 sourceC766 difference raw12757; decide +kernel
    rw [ha]
    exact (canonical12757 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA766 sourceB766 sourceC766
    (0 : Fin 2) 1 1 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm766, Integer.Sparse.eval]
  linarith only [hs]

def sourceA767 : Charge := ![-3, 0, 0, 1, 1, 1]
def sourceB767 : Charge := ![1, 0, 2, -2, -1, 0]
def sourceC767 : Charge := ![2, 0, -2, 1, 0, -1]
def sourceForm767 : Integer.Sparse Master := [(Sum.inr 1276, 1), (Sum.inr 1277, 1), (Sum.inr 1278, 1), (Sum.inr 1280, 1), (Sum.inr 1291, 1), (Sum.inr 2773, 1), (Sum.inr 4092, -1)]

theorem sourceEq767 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm767 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA767 + difference 0 0) (sourceB767 + difference 0 0) sourceC767) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA767 + difference 0 0) (sourceB767 + difference 0 0) sourceC767) = raw12758 := by
      apply Matrix.ext; unfold tripleCharges sourceA767 sourceB767 sourceC767 difference raw12758; decide +kernel
    rw [ha]
    exact (canonical12758 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA767 + difference 1 0) (sourceB767 + difference 0 1) sourceC767) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1276) := by
    have ha : (tripleCharges (sourceA767 + difference 1 0) (sourceB767 + difference 0 1) sourceC767) = raw12759 := by
      apply Matrix.ext; unfold tripleCharges sourceA767 sourceB767 sourceC767 difference raw12759; decide +kernel
    rw [ha]
    exact (canonical12759 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA767 + difference 2 0) (sourceB767 + difference 0 2) sourceC767) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA767 + difference 2 0) (sourceB767 + difference 0 2) sourceC767) = raw12760 := by
      apply Matrix.ext; unfold tripleCharges sourceA767 sourceB767 sourceC767 difference raw12760; decide +kernel
    rw [ha]
    exact (canonical12760 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA767 + difference 3 0) (sourceB767 + difference 0 3) sourceC767) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1280) := by
    have ha : (tripleCharges (sourceA767 + difference 3 0) (sourceB767 + difference 0 3) sourceC767) = raw12761 := by
      apply Matrix.ext; unfold tripleCharges sourceA767 sourceB767 sourceC767 difference raw12761; decide +kernel
    rw [ha]
    exact (canonical12761 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA767 + difference 4 0) (sourceB767 + difference 0 4) sourceC767) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1278) := by
    have ha : (tripleCharges (sourceA767 + difference 4 0) (sourceB767 + difference 0 4) sourceC767) = raw12762 := by
      apply Matrix.ext; unfold tripleCharges sourceA767 sourceB767 sourceC767 difference raw12762; decide +kernel
    rw [ha]
    exact (canonical12762 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA767 + difference 5 0) (sourceB767 + difference 0 5) sourceC767) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1277) := by
    have ha : (tripleCharges (sourceA767 + difference 5 0) (sourceB767 + difference 0 5) sourceC767) = raw12763 := by
      apply Matrix.ext; unfold tripleCharges sourceA767 sourceB767 sourceC767 difference raw12763; decide +kernel
    rw [ha]
    exact (canonical12763 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA767 + sourceB767) sourceC767) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA767 + sourceB767) sourceC767) = raw12764 := by
      apply Matrix.ext; unfold doubleCharges sourceA767 sourceB767 sourceC767 raw12764; decide +kernel
    rw [ha]
    exact (canonical12764 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA767 sourceB767 sourceC767
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm767, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
