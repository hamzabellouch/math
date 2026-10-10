import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFresnelLimit

namespace OAI

/-! # The square-root Jacobian in the quadratic Poisson main term -/

namespace Ostmann

open MeasureTheory Set
open scoped SchwartzMap

theorem quadratic_sqrt_integral (ρ : ℝ → ℂ) :
    (∫ t : ℝ, (Real.sqrt t)⁻¹ • ρ t) =
      (2 : ℝ) • ∫ x in Ioi (0 : ℝ), ρ (x ^ 2) := by
  have hsupport : (∫ t in Ioi (0 : ℝ), (Real.sqrt t)⁻¹ • ρ t) =
      ∫ t : ℝ, (Real.sqrt t)⁻¹ • ρ t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have ht' : t ≤ 0 := le_of_not_gt ht
    simp [Real.sqrt_eq_zero_of_nonpos ht']
  rw [← hsupport, ← integral_comp_rpow_Ioi (fun t : ℝ => (Real.sqrt t)⁻¹ • ρ t)
    (by norm_num : (2 : ℝ) ≠ 0)]
  calc
    _ = ∫ x in Ioi (0 : ℝ), (2 : ℝ) • ρ (x ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx₀ : x ≠ 0 := ne_of_gt hx
      simp only [abs_of_pos (by norm_num : (0 : ℝ) < 2),
        show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
        Real.sqrt_sq (le_of_lt hx), smul_smul]
      congr 1
      field_simp
    _ = _ := integral_smul _ _

end Ostmann

end OAI
