import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Fourier.SchwartzIteratedDerivIntegrable

namespace OAI

/-! Measures and the conditional distance-set completion. -/

section
section
namespace Attempt4FullFar
open Set MeasureTheory
open scoped ContDiff SchwartzMap FourierTransform RealInnerProductSpace
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

end Attempt4FullFar
end
end

end OAI
