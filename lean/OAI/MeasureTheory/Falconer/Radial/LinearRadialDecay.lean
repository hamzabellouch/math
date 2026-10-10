import OAI.MeasureTheory.Falconer.Estimates.LinearNonstationary

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

noncomputable def radialPhaseIntegral (f : ℝ → ℂ) (xi : ℝ) : ℂ :=
  ∫ s : ℝ, Complex.exp (Complex.I*(xi:ℂ)*(s:ℂ))*f s

theorem radialPhaseIntegral_bound {f : ℝ → ℂ} {a b C xi : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc a b) (hab : a ≤ b)
    (hb : ∀ s, ‖f s‖ ≤ C) : ‖radialPhaseIntegral f xi‖ ≤ C*(b-a) := by
  obtain ⟨φ,hφ⟩ := compact_smooth_to_schwartz hs hf
  have hh := compact_derivative_integral_bound φ hab (by simpa [hφ] using hs) 0
    (by simpa only [iteratedDeriv_zero,hφ] using hb)
  simp only [iteratedDeriv_zero,hφ] at hh
  apply (norm_integral_le_integral_norm _).trans
  simpa only [norm_mul,Complex.norm_exp,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,sub_self,
    Real.exp_zero,one_mul] using hh

theorem radialPhaseIntegral_nonzero {f : ℝ → ℂ} {a b C xi : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc a b) (hab : a ≤ b)
    (hxi : xi ≠ 0) (n : ℕ) (hb : ∀ s, ‖iteratedDeriv n f s‖ ≤ C) :
    ‖radialPhaseIntegral f xi‖ ≤ C*(b-a)/|xi|^n := by
  have hp : (2:ℝ)*Real.pi ≠ 0 := by positivity
  have hh := compact_linear_phase_bound (ξ := -xi/(2*Real.pi)) (C := C) (D := 1)
    hf hs hab (div_ne_zero (neg_ne_zero.mpr hxi) hp) n (by simpa using hb)
  have he (s : ℝ) : -(2:ℂ)*(Real.pi:ℂ)*Complex.I*(s:ℂ)*((-xi/(2*Real.pi):ℝ):ℂ) =
      Complex.I*(xi:ℂ)*(s:ℂ) := by
    push_cast
    have hpc : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  simp_rw [he] at hh
  have hd : (2*Real.pi)^n*‖-xi/(2*Real.pi)‖^n = |xi|^n := by
    rw [Real.norm_eq_abs,abs_div,abs_neg,abs_of_pos (by positivity : 0 < 2*Real.pi),div_pow]
    field_simp
  simpa only [radialPhaseIntegral,one_pow,mul_one,hd] using hh

theorem radialPhaseIntegral_two_derivatives {f : ℝ → ℂ} {a b C xi : ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Icc a b) (hab : a ≤ b) (hC : 0 ≤ C)
    (h0 : ∀ s, ‖f s‖ ≤ C) (h2 : ∀ s, ‖iteratedDeriv 2 f s‖ ≤ C) :
    ‖radialPhaseIntegral f xi‖ ≤ 4*C*(b-a)/(1+|xi|)^2 := by
  have hbase := radialPhaseIntegral_bound hf hs hab h0 (xi := xi)
  have ht : 0 ≤ C*(b-a) := mul_nonneg hC (sub_nonneg.mpr hab)
  have hden : 0 < (1+|xi|)^2 := by positivity
  apply (le_div_iff₀ hden).mpr
  by_cases hsmall : |xi| ≤ 1
  · have hsquare : (1+|xi|)^2 ≤ 4 := by nlinarith [abs_nonneg xi]
    nlinarith [mul_le_mul_of_nonneg_left hsquare (norm_nonneg (radialPhaseIntegral f xi))]
  · have hbig : 1 < |xi| := lt_of_not_ge hsmall
    have hxi : xi ≠ 0 := by intro hz; norm_num [hz] at hbig
    have hh := (le_div_iff₀ (pow_pos (abs_pos.mpr hxi) 2)).mp
      (radialPhaseIntegral_nonzero hf hs hab hxi 2 h2)
    have hsquare : (1+|xi|)^2 ≤ 4*|xi|^2 := by nlinarith [sq_nonneg (|xi|-1)]
    nlinarith [mul_le_mul_of_nonneg_left hsquare (norm_nonneg (radialPhaseIntegral f xi))]

end PlanarFalconer

end OAI
