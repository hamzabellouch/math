import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatSymbol

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessianFunctional
lemma exp_neg_quadratic_bound {r : ℝ} (hr : 0 ≤ r) :
    Real.exp (-r) ≤ 1-r+r^2/2 := by
  let f : ℝ → ℝ := fun x => 1-x+x^2/2-Real.exp (-x)
  have hd (x : ℝ) : HasDerivAt f (-1+x+Real.exp (-x)) x := by
    have h := (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).add
      (((hasDerivAt_id x).pow 2).div_const 2)).sub
      (Real.hasDerivAt_exp (-x) |>.comp x (hasDerivAt_id x).neg)
    convert h using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hm : Monotone f := monotone_of_hasDerivAt_nonneg hd (by
    intro x
    have h := Real.add_one_le_exp (-x)
    change 0 ≤ -1+x+Real.exp (-x)
    linarith)
  have h := hm hr
  simp only [f, sub_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_div,
    add_zero, neg_zero, Real.exp_zero, sub_self] at h
  linarith

lemma heatSymbol_second_error {t s : ℝ} (ht : 0 ≤ t) (hs : s ∈ Icc (0:ℝ) 1) :
    |(heatSymbol t s-1)*s^2-t*(s^2-s)| ≤ t^2/2 := by
  rcases hs.1.eq_or_lt with hsz | hsz
  · simp only [← hsz, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, sub_self, abs_zero]
    positivity
  let r := t/s-t
  have hr : 0 ≤ r := by
    dsimp [r]
    have h : t ≤ t/s := (le_div_iff₀ hsz).mpr (by nlinarith [hs.2])
    linarith
  have he : heatSymbol t s = Real.exp (-r) := by
    rw [heatSymbol_of_pos ht hsz]
    congr 1
    dsimp [r]
    ring
  have hrs : r*s = t*(1-s) := by
    dsimp [r]
    field_simp
  have hlow := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-r)) (sq_nonneg s)
  have hupp := mul_le_mul_of_nonneg_right (exp_neg_quadratic_bound hr) (sq_nonneg s)
  have her : (heatSymbol t s-1)*s^2-t*(s^2-s) =
      (Real.exp (-r)-1+r)*s^2 := by
    rw [he]
    nlinarith [congrArg (fun x : ℝ => x*s) hrs]
  rw [her, abs_of_nonneg (by nlinarith : 0 ≤ (Real.exp (-r)-1+r)*s^2)]
  have hs1 : (1-s)^2 ≤ 1 := by nlinarith [hs.1,hs.2]
  have hsq := congrArg (fun x : ℝ => x^2) hrs
  have hmul := mul_le_mul_of_nonneg_left hs1 (sq_nonneg t)
  nlinarith

end WeakHessianFunctional

end
end InlinedFile0

end OAI
