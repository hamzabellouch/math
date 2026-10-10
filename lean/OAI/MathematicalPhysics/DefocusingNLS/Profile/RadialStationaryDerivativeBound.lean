import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexFlux

namespace OAI

/-! The regular-origin flux formula bounds the profile derivative directly
by its source, uniformly in the large odd power. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radialStationary_derivative_bound (m : ℕ) (a b R S : ℝ) (_hS : 0 ≤ S)
    (Q : ℝ → ℂ) (hQ : ContDiff ℝ 2 Q)
    (he : ∀ r ∈ Ioo 0 R, deriv (deriv Q) r+(11/r : ℝ)*deriv Q r+
      Complex.I*((r/2 : ℝ)*deriv Q r+(a : ℂ)*Q r)+(b : ℂ)*Q r=oddPowerNonlinearity m (Q r))
    (hsource : ∀ r ∈ Icc 0 R, ‖radialComplexSource m a b (Q r)‖ ≤ S)
    (r : ℝ) (hr : r ∈ Ioc 0 R) : ‖deriv Q r‖ ≤ S*r/12 := by
  have hflux := radialComplexFlux_integral m a b r hr.1 Q hQ.continuous.continuousOn
    (hQ.continuous_deriv (by norm_num)).continuousOn
    (fun t _ => (hQ.deriv' (n := 1)).differentiable (by norm_num) t)
    (fun t ht => he t ⟨ht.1,ht.2.trans_le hr.2⟩)
  have hexp (t : ℝ) : ‖Complex.exp (Complex.I*(t^2/4 : ℝ))‖ = 1 := by
    simp only [Complex.norm_exp,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,Real.exp_zero]
  have hn : ‖radialComplexFlux Q r‖ = r^11*‖deriv Q r‖ := by
    simp only [radialComplexFlux,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hr.1,hexp,mul_one]
  have hi : ‖∫ t in (0 : ℝ)..r, (t : ℂ)^11*Complex.exp (Complex.I*(t^2/4 : ℝ))*
      radialComplexSource m a b (Q t)‖ ≤ ∫ t in (0 : ℝ)..r, S*t^11 := by
    apply intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hr.1.le
    · apply Filter.Eventually.of_forall
      intro t ht
      simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg ht.1.le,hexp,mul_one]
      exact (mul_le_mul_of_nonneg_left (hsource t ⟨ht.1.le,ht.2.trans hr.2⟩)
        (pow_nonneg ht.1.le _)).trans_eq (mul_comm _ _)
    · exact (continuous_const.mul (continuous_id.pow 11)).intervalIntegrable 0 r
  rw [intervalIntegral.integral_const_mul,integral_pow] at hi
  norm_num only [Nat.reduceAdd,zero_pow (by norm_num : 12 ≠ 0),sub_zero] at hi
  rw [← hflux,hn] at hi
  apply (mul_le_mul_iff_right₀ (pow_pos hr.1 11)).mp
  calc
    _ = r^11*‖deriv Q r‖ := by ring
    _ ≤ S*(r^12/12) := hi
    _ = _ := by ring

end DefocusingNLS

end OAI
