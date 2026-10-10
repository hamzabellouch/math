import OAI.NumberTheory.Ostmann.Characters.CharacterLogDerivativeLocal

namespace OAI

/-! # Actual logarithmic-derivative control away from the nearby zeros -/

namespace Ostmann

open Complex Metric
open scoped BigOperators

theorem character_logDeriv_separated_bound (χ : PrimitiveComplexCharacter) (t M δ : ℝ)
    (hM : 1 ≤ M) (hδ : 0 < δ)
    (hbound : ∀ z ∈ closedBall (characterZeroCenter t) (11 / 4 : ℝ), ‖χ.L z‖ ≤ M)
    (s : ℂ) (hs : ‖s - characterZeroCenter t‖ ≤ 5 / 2)
    (hsep : ∀ z ∈ characterContourZeros χ t, δ ≤ ‖s - z‖) :
    ‖logDeriv χ.L s‖ ≤
      1312 * (Real.log (3 * M) +
        (∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℝ)) * Real.log 21 + 1) +
      (∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℝ)) / δ := by
  have hsnot : s ∉ characterContourZeros χ t := by
    intro h
    have hh := hsep s h
    simp only [sub_self, norm_zero] at hh
    linarith
  have he := character_logDeriv_local_error χ t M hM hbound s hs hsnot
  have hsum : ‖∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℂ) / (s - z)‖ ≤
      (∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℝ)) / δ := by
    apply (norm_sum_le _ _).trans
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro z hz
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (hsep z hz)
  have ht := norm_le_norm_sub_add (logDeriv χ.L s)
    (∑ z ∈ characterContourZeros χ t, (analyticOrderNatAt χ.L z : ℂ) / (s - z))
  exact ht.trans (add_le_add he hsum)

end Ostmann

end OAI
