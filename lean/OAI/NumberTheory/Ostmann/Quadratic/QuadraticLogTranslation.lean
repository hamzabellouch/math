import OAI.NumberTheory.Ostmann.Quadratic.QuadraticLogKernel

namespace OAI

/-! # Translating the logarithmic cutoff preserves its Fourier L1 cost -/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform

 theorem quadratic_fourier_phase_integral (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    𝓕 f u = ∫ x : ℝ, realAdditivePhase (-(x * u)) * f x := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with x
  change Complex.exp _ * f x = Complex.exp _ * f x
  congr 2
  push_cast
  ring

 theorem quadratic_fourier_translate (f : 𝓢(ℝ, ℂ)) (a u : ℝ) :
    𝓕 (f.compSubConstCLM ℂ a) u = realAdditivePhase (-(a * u)) * 𝓕 f u := by
  rw [quadratic_fourier_phase_integral, quadratic_fourier_phase_integral]
  have ht := integral_add_right_eq_self (μ := volume)
    (fun x : ℝ => realAdditivePhase (-(x * u)) * f (x - a)) a
  change (∫ x : ℝ, realAdditivePhase (-(x * u)) * f (x - a)) = _
  rw [← ht, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [add_sub_cancel_right]
  have he : -((x + a) * u) = -(a * u) + -(x * u) := by ring
  rw [he, realAdditivePhase_add]
  ring

 theorem quadratic_fourier_translate_norm (f : 𝓢(ℝ, ℂ)) (a u : ℝ) :
    ‖𝓕 (f.compSubConstCLM ℂ a) u‖ = ‖𝓕 f u‖ := by
  rw [quadratic_fourier_translate, norm_mul, norm_realAdditivePhase, one_mul]

 theorem quadraticLogKernel_fourier_cost (ρ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ) :
    (∫ u : ℝ, ‖𝓕 (quadraticLogKernel ρ X N) u‖) =
      ∫ u : ℝ, ‖𝓕 (quadraticLogWindow ρ (X / (N : ℝ) ^ 2)) u‖ := by
  apply integral_congr_ae
  filter_upwards with u
  exact quadratic_fourier_translate_norm _ _ _

end Ostmann

end OAI
