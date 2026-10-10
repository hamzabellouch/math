import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-! The nonsingular radial Green kernel in dimension twelve. -/

open MeasureTheory Set intervalIntegral
namespace DefocusingNLS

noncomputable def radialAverage (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, f (t*s)*s^11

/-- This is the regular form of
`∫ t in r..R, t⁻¹¹ * ∫ s in 0..t, s¹¹*f s`. -/
noncomputable def radialDirichletKernel (R : ℝ) (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ t in r..R, t*radialAverage f t

theorem radialAverage_nonneg (f : ℝ → ℝ) (t : ℝ)
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ f (t*s)) : 0 ≤ radialAverage f t := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro s hs
  exact mul_nonneg (hf s hs) (pow_nonneg hs.1 _)

theorem radialAverage_norm_le (f : ℝ → ℝ) (R C t : ℝ)
    (ht : 0 ≤ t) (htR : t ≤ R) (hf : ∀ u ∈ Icc 0 R, ‖f u‖ ≤ C) :
    ‖radialAverage f t‖ ≤ C/12 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun s : ℝ => f (t*s)*s^11) (g := fun s : ℝ => C*s^11)
    (by norm_num : (0 : ℝ) ≤ 1) (Filter.Eventually.of_forall fun s hs => ?_)
    ((continuous_const.mul (continuous_id.pow 11)).intervalIntegrable 0 1)
  · have hv : (∫ s in (0 : ℝ)..1, C*s^11)=C/12 := by
      rw [intervalIntegral.integral_const_mul,integral_pow]
      norm_num
      ring
    rw [hv] at h
    exact h
  · have hs0 : 0 ≤ s := hs.1.le
    have hts : t*s ∈ Icc 0 R :=
      ⟨mul_nonneg ht hs0,(mul_le_of_le_one_right ht hs.2).trans htR⟩
    simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hs0 _)]
    exact mul_le_mul_of_nonneg_right (hf _ hts) (pow_nonneg hs0 _)

theorem radialDirichletKernel_norm_le (f : ℝ → ℝ) (R C r : ℝ)
    (hr : 0 ≤ r) (hrR : r ≤ R) (hf : ∀ u ∈ Icc 0 R, ‖f u‖ ≤ C) :
    ‖radialDirichletKernel R f r‖ ≤ C*(R^2-r^2)/24 := by
  have hbound : IntervalIntegrable (fun t : ℝ => (C/12)*t) volume r R :=
    (continuous_const.mul continuous_id).intervalIntegrable r R
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun t : ℝ => t*radialAverage f t) (g := fun t : ℝ => (C/12)*t)
    hrR (Filter.Eventually.of_forall fun t ht => ?_) hbound
  · calc
      ‖radialDirichletKernel R f r‖ ≤ ∫ t in r..R, (C/12)*t := h
      _ = C*(R^2-r^2)/24 := by
        rw [intervalIntegral.integral_const_mul,integral_id]
        ring
  · have ht0 : 0 ≤ t := hr.trans ht.1.le
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg ht0]
    calc
      t*‖radialAverage f t‖ ≤ t*(C/12) :=
        mul_le_mul_of_nonneg_left (radialAverage_norm_le f R C t ht0 ht.2 hf) ht0
      _ = (C/12)*t := mul_comm _ _

theorem radialDirichletKernel_boundary (R : ℝ) (f : ℝ → ℝ) :
    radialDirichletKernel R f R=0 := by simp [radialDirichletKernel]

end DefocusingNLS

end OAI
