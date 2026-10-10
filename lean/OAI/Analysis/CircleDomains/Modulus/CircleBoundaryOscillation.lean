import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace OAI

/-! The two offset-circle contributions in the Stokes estimate: zero
period costs radius times oscillation, and the distinguished constant
weight costs only that constant times the period. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem zero_period_weighted_integral_bound
    (φ dφ u du : ℝ → ℝ) {T K A : ℝ} (hT : 0 ≤ T)
    (hφ : ∀ x ∈ uIcc (0 : ℝ) T, HasDerivAt φ (dφ x) x)
    (hu : ∀ x ∈ uIcc (0 : ℝ) T, HasDerivAt u (du x) x)
    (hdφ : IntervalIntegrable dφ volume 0 T) (hdu : IntervalIntegrable du volume 0 T)
    (hperiod : u T = u 0)
    (hK : ∀ x ∈ Icc (0 : ℝ) T, |dφ x| ≤ K)
    (hA : ∀ x ∈ Icc (0 : ℝ) T, |u x - u 0| ≤ A) :
    |∫ x in (0 : ℝ)..T, φ x * du x| ≤ T * K * A := by
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hφ
    (fun x hx => (hu x hx).sub_const (u 0)) hdφ hdu
  have he : (∫ x in (0 : ℝ)..T, φ x * du x) =
      -(∫ x in (0 : ℝ)..T, dφ x * (u x - u 0)) := by
    simpa only [hperiod, sub_self, mul_zero, zero_sub] using hparts
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ⟨le_rfl, hT⟩)
  have hb : ‖∫ x in (0 : ℝ)..T, dφ x * (u x - u 0)‖ ≤
      ∫ _x in (0 : ℝ)..T, K * A := by
    apply intervalIntegral.norm_integral_le_of_norm_le hT _ (intervalIntegrable_const)
    apply Eventually.of_forall
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) T := ⟨hx.1.le, hx.2⟩
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hK x hx') (hA x hx') (abs_nonneg _) hK0
  rw [he, abs_neg]
  simpa only [Real.norm_eq_abs, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    mul_assoc] using hb

 theorem circle_zero_period_integral_bound
    (φ : ℂ → ℝ) (hφ : LipschitzWith 1 φ) (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (dφ u du : ℝ → ℝ)
    (hderiv : ∀ x ∈ uIcc (0 : ℝ) (2 * Real.pi),
      HasDerivAt (φ ∘ circleMap c r) (dφ x) x)
    (hu : ∀ x ∈ uIcc (0 : ℝ) (2 * Real.pi), HasDerivAt u (du x) x)
    (hdφ : IntervalIntegrable dφ volume 0 (2 * Real.pi))
    (hdu : IntervalIntegrable du volume 0 (2 * Real.pi))
    (hperiod : u (2 * Real.pi) = u 0) (A : ℝ)
    (hA : ∀ x ∈ Icc (0 : ℝ) (2 * Real.pi), |u x - u 0| ≤ A) :
    |∫ x in (0 : ℝ)..(2 * Real.pi), φ (circleMap c r x) * du x| ≤
      2 * Real.pi * r * A := by
  apply zero_period_weighted_integral_bound (φ ∘ circleMap c r) dφ u du
    (by positivity) hderiv hu hdφ hdu hperiod ?_ hA
  intro x hx
  have hlip := hφ.comp (lipschitzWith_circleMap c r)
  have hb := (hderiv x (by simpa only [uIcc_of_le (show 0 ≤ 2 * Real.pi by positivity)] using hx)).le_of_lipschitz hlip
  simpa only [NNReal.coe_mul, NNReal.coe_one, one_mul, Real.coe_nnabs,
    abs_of_nonneg hr, Real.norm_eq_abs] using hb

 theorem constant_weight_integral_eq_period
    (u du : ℝ → ℝ) (T ρ : ℝ)
    (hu : ∀ x ∈ uIcc (0 : ℝ) T, HasDerivAt u (du x) x)
    (hdu : IntervalIntegrable du volume 0 T) :
    (∫ x in (0 : ℝ)..T, ρ * du x) = ρ * (u T - u 0) := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hu hdu]

end CircleDomainRigidity

end

end OAI
