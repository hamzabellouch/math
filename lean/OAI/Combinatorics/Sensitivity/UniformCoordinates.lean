import OAI.Combinatorics.Sensitivity.FixedCoordinates
import Mathlib.Probability.Distributions.Uniform

namespace OAI

/-! The exact probability of prescribed values under uniform independent labels. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem uniform_fixedCoordinates_probability {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [Nonempty β] (s : Finset α) (v : α → β) :
    ((PMF.uniformOfFintype (α → β)).toOuterMeasure
      {f | ∀ i ∈ s, f i = v i}).toReal = 1 / (Fintype.card β : ℝ)^s.card := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  rw [Fintype.card_subtype]
  simp only [Set.mem_ofPred_eq]
  rw [card_fixedCoordinates, Fintype.card_fun]
  simp only [Nat.cast_pow]
  have hp : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := β)
  rw [div_eq_div_iff (pow_ne_zero _ hp) (pow_ne_zero _ hp), one_mul,
    ← pow_add, Nat.sub_add_cancel (Finset.card_le_univ s)]

end Paper320

end

end OAI
