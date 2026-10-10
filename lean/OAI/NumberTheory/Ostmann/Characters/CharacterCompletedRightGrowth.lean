import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterGammaFactorialGrowth

namespace OAI

/-! # Actual completed L-function growth in the right half-plane -/

namespace Ostmann

open Complex

theorem PrimitiveComplexCharacter.completed_eq_L_mul_gamma
    (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 0 < s.re) :
    χ.completed s = χ.L s * DirichletCharacter.gammaFactor χ.character s := by
  have hgne : DirichletCharacter.gammaFactor χ.character s ≠ 0 := by
    intro h
    have hh := χ.gammaInverse_ne_zero s hs
    apply hh
    change (DirichletCharacter.gammaFactor χ.character s)⁻¹ = 0
    rw [h, inv_zero]
  have hL := congrFun χ.L_eq_completed_mul_all s
  change χ.L s = χ.completed s / DirichletCharacter.gammaFactor χ.character s at hL
  exact ((eq_div_iff hgne).mp hL).symm

theorem character_completed_right_growth : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (N : ℕ) (s : ℂ),
      (1 / 2 : ℝ) ≤ s.re → ‖s‖ ≤ (N : ℝ) + 1 →
      ‖χ.completed s‖ ≤ 2 * ((N : ℝ) + 1) * ((χ.modulus : ℝ) + 1) *
        (C + ((N + 1).factorial : ℝ)) := by
  obtain ⟨C, hC, hgamma⟩ := characterGamma_factorial_growth
  refine ⟨C, hC, ?_⟩
  intro χ N s hs hn
  have hspos : 0 < s.re := by linarith
  have hl : ‖χ.L s‖ ≤ 2 * ((N : ℝ) + 1) * ((χ.modulus : ℝ) + 1) := by
    apply (χ.L_norm_bound_positive s hspos).trans
    apply (div_le_iff₀ hspos).mpr
    have hb := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ (χ.modulus : ℝ) + 1)
    have hc := mul_le_mul_of_nonneg_left hs (by positivity :
      0 ≤ 2 * ((N : ℝ) + 1) * ((χ.modulus : ℝ) + 1))
    nlinarith
  have hg := hgamma χ N s hs ((le_abs_self s.re).trans ((abs_re_le_norm s).trans hn))
  rw [χ.completed_eq_L_mul_gamma s hspos, norm_mul]
  exact mul_le_mul hl hg (norm_nonneg _) (by positivity)

end Ostmann

end OAI
