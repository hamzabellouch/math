import OAI.NumberTheory.Ostmann.ZeroDensity.InverseSquareZeroSum
import OAI.NumberTheory.Ostmann.Characters.CharacterFaithfulEnumeration

namespace OAI

/-! # Square-decaying sums over the actual character zeros -/

namespace Ostmann

open scoped Classical BigOperators

theorem character_zero_inverse_square_summable (χ : PrimitiveComplexCharacter) :
    Summable (fun i => ((1 + |((actualCharacterZeros χ).zeros i).im|) ^ 2)⁻¹) := by
  let Z := actualCharacterZeros χ
  let K : ℝ := 32 / Real.log (14 / 13)
  have hK : 0 ≤ K := div_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  apply inverse_square_weights_summable (fun i => |(Z.zeros i).im|) χ.modulus K hq hK
    (fun _ => abs_nonneg _)
  intro S t ht
  have hsub : S.filter (fun i => |(Z.zeros i).im| ≤ t) ⊆ Z.heightIndices t := by
    intro i hi
    exact (Z.mem_heightIndices t i).mpr (Finset.mem_filter.mp hi).2
  have hc := Z.count_bound_of_multiplicity (actualCharacterZeros_respectsMultiplicity χ) t ht
  rw [Z.count_zero_eq_card] at hc
  exact (show (((S.filter (fun i => |(Z.zeros i).im| ≤ t)).card : ℝ)) ≤
    (Z.heightIndices t).card from by exact_mod_cast Finset.card_le_card hsub).trans hc

end Ostmann

end OAI
