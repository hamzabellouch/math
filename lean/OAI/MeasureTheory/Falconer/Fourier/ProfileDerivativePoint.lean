import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic

namespace OAI

/-! # An interior profile derivative exceeds any smaller secant slope -/

namespace Falconer
open Set MeasureTheory
open scoped NNReal

theorem lipschitz_unit_interval_derivative_point {f : ℝ → ℝ} {K : ℝ≥0} {r : ℝ}
    (hf : LipschitzOnWith K f (Icc 0 1)) (hinc : r < f 1-f 0) :
    ∃ A ∈ Ioo 0 1, ∃ l : ℝ, HasDerivAt f l A ∧ r < l := by
  have hfu : LipschitzOnWith K f (uIcc 0 1) := by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hf
  have hac : AbsolutelyContinuousOnInterval f 0 1 := hfu.absolutelyContinuousOnInterval
  by_contra hn
  push Not at hn
  have hbound : (fun x => deriv f x) ≤ᵐ[volume.restrict (Icc 0 1)] fun _ => r := by
    change ∀ᵐ x ∂volume.restrict (Icc (0:ℝ) 1), deriv f x ≤ r
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hac.ae_differentiableAt,volume.ae_ne (0:ℝ),volume.ae_ne (1:ℝ)] with x hd hx0 hx1 hx
    have hi : x ∈ Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0),lt_of_le_of_ne hx.2 hx1⟩
    have hdx : DifferentiableAt ℝ f x := hd (by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx)
    exact hn x hi (deriv f x) hdx.hasDerivAt
  have hh := intervalIntegral.integral_mono_ae_restrict (by norm_num : (0:ℝ) ≤ 1)
    hac.intervalIntegrable_deriv (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => r) volume 0 1) hbound
  rw [hac.integral_deriv_eq_sub,intervalIntegral.integral_const] at hh
  norm_num at hh
  linarith

end Falconer

end OAI
