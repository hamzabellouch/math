import OAI.NumberTheory.Ostmann.ZeroDensity.GammaRealLogDerivative

namespace OAI

/-! # Bounds for the real-place Gamma factor on the shifted contour -/

namespace Ostmann

open Complex

theorem gammaReal_differentiableAt (s : ℂ) (hs : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact (((differentiableAt_id.neg).div_const 2).const_cpow (.inl hpi)).mul
    ((Complex.differentiableAt_Gamma _ hs).comp s (differentiableAt_id.div_const 2))

theorem gammaReal_contour_regular (s : ℂ)
    (hs : s.re = -(1 / 2 : ℝ) ∨ s.re = 1 / 2 ∨ s.re = 3 / 2 ∨ s.re = 5 / 2) :
    ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
  apply gamma_not_pole_of_re
  · simp only [div_ofNat_re]
    rcases hs with h | h | h | h <;> linarith
  · simp only [div_ofNat_re]
    rcases hs with h | h | h | h <;> rw [h] <;> norm_num

theorem gammaReal_contour_logDeriv_bound : ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ,
    (s.re = -(1 / 2 : ℝ) ∨ s.re = 1 / 2 ∨ s.re = 3 / 2 ∨ s.re = 5 / 2) →
      ‖logDeriv Complex.Gammaℝ s‖ ≤ B * (1 + |s.im|) := by
  obtain ⟨B, hB, hbound⟩ := gamma_logDeriv_contour_bound
  refine ⟨B + |Real.log Real.pi| + 1, by positivity, ?_⟩
  intro s hs
  have hhalf : (s / 2).re = -(1 / 4 : ℝ) ∨ (s / 2).re = 1 / 4 ∨
      (s / 2).re = 3 / 4 ∨ (s / 2).re = 5 / 4 := by
    simp only [div_ofNat_re]
    rcases hs with h | h | h | h
    · left; linarith
    · right; left; linarith
    · right; right; left; linarith
    · right; right; right; linarith
  have hb := hbound (s / 2) hhalf
  change ‖Complex.digamma (s / 2)‖ ≤ _ at hb
  have him : |(s / 2).im| = |s.im| / 2 := by simp [abs_div]
  have hnorm : ‖Complex.log (Real.pi : ℂ)‖ = |Real.log Real.pi| := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs]
  rw [gammaReal_logDeriv s (gammaReal_contour_regular s hs), norm_div, norm_ofNat]
  have hh := (norm_sub_le (Complex.digamma (s / 2)) (Complex.log (Real.pi : ℂ))).trans
    (add_le_add hb (le_refl ‖Complex.log (Real.pi : ℂ)‖))
  rw [him, hnorm] at hh
  change ‖Complex.digamma (s / 2) - Complex.log (Real.pi : ℂ)‖ / 2 ≤ _
  nlinarith [abs_nonneg s.im, abs_nonneg (Real.log Real.pi)]

end Ostmann

end OAI
