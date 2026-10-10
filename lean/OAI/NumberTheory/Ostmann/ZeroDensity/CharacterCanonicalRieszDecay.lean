import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterCanonicalRieszComparison

namespace OAI

/-! # Uniform character Riesz decay with the canonical Page correction -/

namespace Ostmann

open Filter

theorem character_riesz_canonical_decay : ∃ d : ℝ, 0 < d ∧
    ∀ᶠ y : ℝ in atTop, ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.exp y →
      ∀ χ : PrimitiveComplexCharacter, χ.modulus ∣ q →
        ‖characterRieszMean χ (Real.exp (y ^ 2)) -
            canonicalCharacterRieszTerm χ q (Real.exp (y ^ 2))‖ ≤
          3 * Real.exp (y ^ 2 - d * y) := by
  obtain ⟨c, A, B, E, hc, hc4, hA, hB, hE, hbound⟩ := character_riesz_canonical_bound
  refine ⟨c / 6, by positivity, ?_⟩
  filter_upwards [riesz_exponential_error c A B E hc hc4 hA.le hB.le hE.le,
    eventually_ge_atTop (5 : ℝ)] with y hy hy5
  intro q hq hqy χ hdvd
  have hy0 : 0 < y := by linarith
  have hT : 2 ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hb1 : 1 < 1 + 1 / y ^ 2 := by
    have hh : 0 < 1 / y ^ 2 := by positivity
    linarith
  have hb2 : 1 + 1 / y ^ 2 ≤ 2 := by
    have hys : 1 ≤ y ^ 2 := by nlinarith
    have hh : 1 / y ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hys
    linarith
  have hr := hbound q χ (Real.exp y) (Real.exp (y ^ 2)) (1 + 1 / y ^ 2)
    hq hdvd hqy hT (Real.one_le_exp (sq_nonneg y)) hb1 hb2
  have hχq : (χ.modulus : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (by omega : 0 < q) hdvd
  have hχ : (χ.modulus : ℝ) ≤ Real.exp y := hχq.trans hqy
  obtain ⟨hH, hHy⟩ := character_riesz_height_log_bound χ y hy5 hχ
  exact hr.trans (hy _ hH hHy)

theorem character_riesz_canonical_sqrt_decay : ∃ d : ℝ, 0 < d ∧
    ∀ᶠ X : ℝ in atTop, ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ Real.exp (Real.sqrt (Real.log X)) →
      ∀ χ : PrimitiveComplexCharacter, χ.modulus ∣ q →
        ‖characterRieszMean χ X - canonicalCharacterRieszTerm χ q X‖ ≤
          3 * X * Real.exp (-d * Real.sqrt (Real.log X)) := by
  obtain ⟨d, hd, h⟩ := character_riesz_canonical_decay
  refine ⟨d, hd, ?_⟩
  have ht := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually h, eventually_ge_atTop (1 : ℝ)] with X hX hX1
  have hx : 0 < X := by linarith
  have heq : Real.exp ((Real.sqrt (Real.log X)) ^ 2) = X := by
    rw [Real.sq_sqrt (Real.log_nonneg hX1), Real.exp_log hx]
  intro q hq hqX χ hχ
  have hh := hX q hq hqX χ hχ
  dsimp only [Function.comp_apply] at hh
  rw [heq, Real.exp_sub, Real.sq_sqrt (Real.log_nonneg hX1), Real.exp_log hx] at hh
  simpa only [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, neg_mul] using hh

end Ostmann

end OAI
