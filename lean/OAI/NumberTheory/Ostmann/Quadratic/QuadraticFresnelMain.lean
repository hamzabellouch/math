import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFresnelEvaluation
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSqrtIntegral

namespace OAI

/-! # The exact main term of the second quadratic Poisson transform -/

namespace Ostmann

open MeasureTheory Set
open scoped SchwartzMap FourierTransform

noncomputable def quadraticFresnelPhase (a : ℝ) : ℂ :=
  if 0 < a then 1 - Complex.I else 1 + Complex.I

theorem quadratic_fresnel_coefficient_factor {a t : ℝ} (ha : a ≠ 0) (ht : 0 < t) :
    quadraticFresnelCoefficient 0 a t =
      (quadraticFresnelPhase a / (2 * (Real.sqrt |a| : ℂ))) *
        ((Real.sqrt t)⁻¹ : ℝ) := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hat : a * t < 0 := mul_neg_of_neg_of_pos ha ht
    rw [quadratic_fresnel_coefficient_negative hat, quadraticFresnelPhase,
      ite_eq_right (not_lt_of_ge ha.le), abs_of_neg ha,
      show -(a * t) = (-a) * t by ring, Real.sqrt_mul (neg_pos.mpr ha).le]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · rw [quadratic_fresnel_coefficient_positive (mul_pos ha ht), quadraticFresnelPhase,
      ite_eq_left ha, abs_of_pos ha, Real.sqrt_mul ha.le]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

theorem quadratic_fresnel_main (ρ : 𝓢(ℝ, ℂ)) (a : ℝ)
    (ha : 1 ≤ |a|) (hρ : ∀ t < 1 / 2, ρ t = 0) :
    (∫ x : ℝ, 𝓕 ρ (a * x ^ 2)) =
      (quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
        ∫ x in Ioi (0 : ℝ), ρ (x ^ 2) := by
  have ha₀ : a ≠ 0 := by
    intro hz
    simp only [hz, abs_zero] at ha
    linarith
  rw [quadratic_fresnel_integral ρ a ha hρ]
  calc
    _ = ∫ t : ℝ, (quadraticFresnelPhase a / (2 * (Real.sqrt |a| : ℂ))) *
        ((Real.sqrt t)⁻¹ • ρ t) := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t < 1 / 2
      · simp [hρ t ht]
      · rw [quadratic_fresnel_coefficient_factor ha₀ (by linarith)]
        simp only [Complex.real_smul]
        ring
    _ = (quadraticFresnelPhase a / (2 * (Real.sqrt |a| : ℂ))) *
        ((2 : ℝ) • ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) := by
      rw [integral_const_mul, quadratic_sqrt_integral]
    _ = _ := by
      simp only [Complex.real_smul, Complex.ofReal_ofNat]
      ring

end Ostmann

end OAI
