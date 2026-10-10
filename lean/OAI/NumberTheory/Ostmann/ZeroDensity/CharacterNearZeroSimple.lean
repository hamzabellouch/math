import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterNearZeroUnique
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroPartialSums

namespace OAI

/-! # Unique near-one indices have analytic multiplicity one -/

namespace Ostmann

open scoped Classical

theorem actual_character_zero_simple (χ : PrimitiveComplexCharacter) (i : ℕ)
    (hunique : ∀ j : ℕ, (actualCharacterZeros χ).zeros j = (actualCharacterZeros χ).zeros i → j = i) :
    analyticOrderNatAt χ.L ((actualCharacterZeros χ).zeros i) = 1 := by
  let Z := actualCharacterZeros χ
  let z := Z.zeros i
  let T := |z.im|
  have hz : z ∈ criticalZerosUpTo χ T := by
    apply mem_criticalZerosUpTo.mpr
    exact ⟨⟨(Z.in_strip i).1, (Z.in_strip i).2, Z.actual_zero i⟩, le_rfl⟩
  have hf := characterZeroEnumeration_fiber_card χ (faithfulCharacterZeroEquiv χ) T z hz
  change ((Z.heightIndices T).filter (fun j => Z.zeros j = z)).card = analyticOrderNatAt χ.L z at hf
  have hsingle : (Z.heightIndices T).filter (fun j => Z.zeros j = z) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hj
      exact hunique j hj.2
    · intro hj
      subst j
      exact ⟨(Z.mem_heightIndices T i).mpr le_rfl, rfl⟩
  rw [hsingle, Finset.card_singleton] at hf
  exact hf.symm

theorem character_near_zero_simple : ∃ c : ℝ, 0 < c ∧
    ∀ (χ : PrimitiveComplexCharacter) (T : ℝ), 2 ≤ T →
      let H := Real.log χ.modulus + Real.log (T + 2) + 1
      (∀ i : ℕ, |((actualCharacterZeros χ).zeros i).im| ≤ T →
        1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re →
          χ.character ^ 2 = 1 ∧ ((actualCharacterZeros χ).zeros i).im = 0 ∧
            analyticOrderNatAt χ.L ((actualCharacterZeros χ).zeros i) = 1) ∧
      (∀ i j : ℕ, |((actualCharacterZeros χ).zeros i).im| ≤ T →
        |((actualCharacterZeros χ).zeros j).im| ≤ T →
        1 - c / H ≤ ((actualCharacterZeros χ).zeros i).re →
        1 - c / H ≤ ((actualCharacterZeros χ).zeros j).re → i = j) := by
  obtain ⟨c, hc, hdata⟩ := character_near_zero_unique
  refine ⟨c, hc, ?_⟩
  intro χ T hT
  obtain ⟨hreal, huniq⟩ := hdata χ T hT
  refine ⟨?_, huniq⟩
  intro i hi hnear
  obtain ⟨hsq, him⟩ := hreal i hi hnear
  refine ⟨hsq, him, actual_character_zero_simple χ i ?_⟩
  intro j hj
  apply huniq j i _ hi _ hnear
  · simpa only [hj] using hi
  · simpa only [hj] using hnear

end Ostmann

end OAI
