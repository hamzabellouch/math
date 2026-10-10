import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFourierDerivative

namespace OAI

/-! # A concrete Fourier L1 bound from two physical-space derivatives -/

namespace Ostmann

open MeasureTheory LineDeriv
open scoped SchwartzMap FourierTransform

 theorem quadratic_fourier_norm_le_integral (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    ‖𝓕 f u‖ ≤ ∫ x : ℝ, ‖f x‖ := by
  rw [quadratic_fourier_phase_integral]
  simpa only [norm_mul, norm_realAdditivePhase, one_mul] using
    norm_integral_le_integral_norm (fun x : ℝ => realAdditivePhase (-(x * u)) * f x)

 theorem quadratic_fourier_frequency_bound (f : 𝓢(ℝ, ℂ)) (u : ℝ) :
    u ^ 2 * ‖𝓕 f u‖ ≤
      (∫ x : ℝ, ‖(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f)) x‖) / (2 * Real.pi) ^ 2 := by
  have hp : 0 < (2 * Real.pi) ^ 2 := by positivity
  apply (le_div_iff₀ hp).mpr
  have hh := quadratic_fourier_norm_le_integral (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f)) u
  rw [quadratic_fourier_second_derivative_norm] at hh
  convert hh using 1
  ring

 theorem quadratic_fourier_l1_bound (f : 𝓢(ℝ, ℂ)) :
    (∫ u : ℝ, ‖𝓕 f u‖) ≤
      2 * ((∫ x : ℝ, ‖f x‖) +
        (∫ x : ℝ, ‖(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f)) x‖) / (2 * Real.pi) ^ 2) *
      ∫ u : ℝ, (1 + ‖u‖) ^ (-(2 : ℝ)) := by
  let A := ∫ x : ℝ, ‖f x‖
  let B := (∫ x : ℝ, ‖(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} f)) x‖) / (2 * Real.pi) ^ 2
  have hb (u : ℝ) : ‖𝓕 f u‖ ≤ 2 * (A + B) * (1 + ‖u‖) ^ (-(2 : ℝ)) := by
    have h₀ := quadratic_fourier_norm_le_integral f u
    have h₂ := quadratic_fourier_frequency_bound f u
    have he : (1 + ‖u‖) ^ 2 ≤ 2 * (1 + u ^ 2) := by
      rw [Real.norm_eq_abs]
      nlinarith [sq_nonneg (|u| - 1), sq_abs u]
    have hm := mul_le_mul_of_nonneg_right he (norm_nonneg (𝓕 f u))
    have hw : (1 + ‖u‖) ^ 2 * ‖𝓕 f u‖ ≤ 2 * (A + B) := by
      calc
        _ ≤ 2 * (1 + u ^ 2) * ‖𝓕 f u‖ := hm
        _ = 2 * (‖𝓕 f u‖ + u ^ 2 * ‖𝓕 f u‖) := by ring
        _ ≤ 2 * (A + B) := mul_le_mul_of_nonneg_left (add_le_add h₀ h₂) (by norm_num)
    rw [Real.rpow_neg (by positivity : 0 ≤ 1 + ‖u‖), Real.rpow_two,
      ← div_eq_mul_inv]
    exact (le_div_iff₀ (by positivity : 0 < (1 + ‖u‖) ^ 2)).mpr (by nlinarith [hw])
  have hi : Integrable (fun u : ℝ => (1 + ‖u‖) ^ (-(2 : ℝ))) :=
    integrable_one_add_norm (E := ℝ) (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2)
  calc
    _ ≤ ∫ u : ℝ, 2 * (A + B) * (1 + ‖u‖) ^ (-(2 : ℝ)) :=
      integral_mono (𝓕 f : 𝓢(ℝ, ℂ)).integrable.norm (hi.const_mul _) hb
    _ = _ := integral_const_mul _ _

end Ostmann

end OAI
