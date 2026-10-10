import OAI.NumberTheory.Ostmann.Characters.CharacterCompletedLogDerivative

namespace OAI

/-! # The logarithmic derivative on the left side of the explicit-formula contour -/

namespace Ostmann

open Complex

/-- A uniform polynomial bound, derived from the functional equation and the
absolutely convergent right-hand line. -/
theorem character_logDeriv_left_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), s.re = -(1 / 2 : ℝ) →
      ‖logDeriv χ.L s‖ ≤ C * (1 + Real.log (χ.modulus : ℝ) + |s.im|) := by
  obtain ⟨A, hA, hright⟩ := character_logDeriv_right_bound
  obtain ⟨B, hB, hgamma⟩ := characterGammaInverse_contour_bound
  refine ⟨1 + A + 2 * B, by positivity, ?_⟩
  intro χ s hs
  have hr : (1 - s).re = (3 / 2 : ℝ) := by simp; linarith
  have hne : s ≠ 0 := by intro he; subst s; norm_num at hs
  have hL := χ.logDeriv_L_eq_completed_add s
    (χ.L_ne_zero_left_ne_origin s hs.ge (by linarith) hne)
  have hLi := χ.inverse.logDeriv_L_eq_completed_add (1 - s)
    (χ.inverse.L_ne_zero_one_le_re _ (by rw [hr]; norm_num))
  have hCi : logDeriv χ.inverse.completed (1 - s) =
      logDeriv χ.inverse.L (1 - s) - logDeriv χ.inverse.gammaInverse (1 - s) := by
    linear_combination -hLi
  have hR := χ.completed_logDeriv_reflection (1 - s) (by rw [hr]; norm_num)
  have hcomp : 1 - (1 - s) = s := by ring
  rw [hcomp] at hR
  rw [hL, hR, hCi]
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hlogq : 0 ≤ Real.log (χ.modulus : ℝ) := Real.log_nonneg hq
  have hnlog : ‖Complex.log (χ.modulus : ℂ)‖ = Real.log (χ.modulus : ℝ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity), norm_real,
      Real.norm_eq_abs, abs_of_nonneg hlogq]
  have hri := hright χ.inverse (1 - s) hr
  have hgi := hgamma χ.inverse (1 - s) (.inr hr)
  have hgc := hgamma χ s (.inl hs)
  simp only [sub_im, one_im, zero_sub, abs_neg] at hgi
  calc
    _ ≤ ‖-Complex.log (χ.modulus : ℂ)‖ +
        ‖logDeriv χ.inverse.L (1 - s) - logDeriv χ.inverse.gammaInverse (1 - s)‖ +
          ‖logDeriv χ.gammaInverse s‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (le_refl _))
    _ ≤ Real.log (χ.modulus : ℝ) + (A + B * (1 + |s.im|)) + B * (1 + |s.im|) := by
      rw [norm_neg, hnlog]
      exact add_le_add (add_le_add (le_refl _) ((norm_sub_le _ _).trans (add_le_add hri hgi))) hgc
    _ ≤ _ := by
      nlinarith [abs_nonneg s.im, mul_nonneg hA.le hlogq,
        mul_nonneg hA.le (abs_nonneg s.im), mul_nonneg hB.le hlogq]

end Ostmann

end OAI
