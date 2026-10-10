import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSquareCompose

namespace OAI

/-! # Gaussian regularization of the quadratic Fourier integral -/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap FourierTransform

noncomputable def quadraticGaussianDamping (ε x : ℝ) : ℂ :=
  Complex.exp (-((Real.pi * ε : ℝ) : ℂ) * (x : ℂ) ^ 2)

 theorem quadraticGaussianDamping_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (quadraticGaussianDamping ε) :=
  integrable_cexp_neg_mul_sq (by simpa using mul_pos Real.pi_pos hε)

 theorem quadratic_gaussian_phase_identity (ε a t x : ℝ) :
    quadraticGaussianDamping ε x * realAdditivePhase (-(t * (a * x ^ 2))) =
      Complex.exp (-((Real.pi : ℂ) * ((ε : ℂ) + 2 * Complex.I * (a * t : ℝ))) *
        (x : ℂ) ^ 2) := by
  unfold quadraticGaussianDamping realAdditivePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

 theorem quadratic_damped_fresnel_integrable (ρ : 𝓢(ℝ, ℂ))
    {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    Integrable (fun p : ℝ × ℝ => quadraticGaussianDamping ε p.1 *
      realAdditivePhase (-(p.2 * (a * p.1 ^ 2))) * ρ p.2) := by
  have hi : Integrable (fun p : ℝ × ℝ => ‖quadraticGaussianDamping ε p.1‖ * ‖ρ p.2‖)
      (volume.prod volume) :=
    (quadraticGaussianDamping_integrable hε).norm.mul_prod ρ.integrable.norm
  apply hi.mono'
  · apply Continuous.aestronglyMeasurable
    unfold quadraticGaussianDamping realAdditivePhase
    fun_prop
  · filter_upwards with p
    simp only [norm_mul, norm_realAdditivePhase, mul_one]
    rfl

 theorem quadratic_damped_fresnel (ρ : 𝓢(ℝ, ℂ)) {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    (∫ x : ℝ, quadraticGaussianDamping ε x * 𝓕 ρ (a * x ^ 2)) =
      ∫ t : ℝ, ((1 : ℂ) / ((ε : ℂ) + 2 * Complex.I * (a * t : ℝ))) ^ (1 / 2 : ℂ) * ρ t := by
  have hprod := quadratic_damped_fresnel_integrable ρ hε a
  calc
    _ = ∫ x : ℝ, ∫ t : ℝ, quadraticGaussianDamping ε x *
        realAdditivePhase (-(t * (a * x ^ 2))) * ρ t := by
      apply integral_congr_ae
      filter_upwards with x
      rw [quadratic_fourier_phase_integral, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      ring
    _ = ∫ t : ℝ, ∫ x : ℝ, quadraticGaussianDamping ε x *
        realAdditivePhase (-(t * (a * x ^ 2))) * ρ t := integral_integral_swap hprod
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      simp_rw [quadratic_gaussian_phase_identity]
      rw [integral_mul_const]
      have hp : 0 < (((Real.pi : ℂ) * ((ε : ℂ) + 2 * Complex.I * (a * t : ℝ)))).re := by
        simpa using mul_pos Real.pi_pos hε
      rw [integral_gaussian_complex hp]
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have he : (Real.pi : ℂ) /
          ((Real.pi : ℂ) * ((ε : ℂ) + 2 * Complex.I * (a * t : ℝ))) =
          1 / ((ε : ℂ) + 2 * Complex.I * (a * t : ℝ)) := by
        rw [div_mul_eq_div_div, div_self hpi]
      rw [he]

end Ostmann

end OAI
