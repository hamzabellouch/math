import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! # The squared Cauchy kernel has zero integral around a polygon -/

open Set MeasureTheory
namespace DefocusingNLS

theorem integral_segment_inv_sq (u v a : ℂ) (l r : ℝ)
    (hn : ∀ t ∈ uIcc l r, u + (t : ℂ) * v - a ≠ 0) :
    (∫ t : ℝ in l..r, v / (u + (t : ℂ) * v - a) ^ 2) =
      (u + (l : ℂ) * v - a)⁻¹ - (u + (r : ℂ) * v - a)⁻¹ := by
  have hd (t : ℝ) (ht : t ∈ uIcc l r) :
      HasDerivAt (fun s : ℝ => -(u + (s : ℂ) * v - a)⁻¹)
        (v / (u + (t : ℂ) * v - a) ^ 2) t := by
    have h := (((((hasDerivAt_id t).ofReal_comp.mul_const v).const_add u).sub_const a).inv
      (hn t ht)).neg
    simpa only [neg_div, neg_neg, id_eq, Complex.ofReal_one, one_mul] using! h
  have hi : IntervalIntegrable (fun t : ℝ => v / (u + (t : ℂ) * v - a) ^ 2) volume l r := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div (by fun_prop) (fun t ht => pow_ne_zero 2 (hn t ht))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  simpa only [neg_sub_neg] using h

end DefocusingNLS

end OAI
