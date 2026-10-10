import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory InformationTheory
open Set Filter
open scoped Topology

namespace WeakHessian

lemma hasDerivAt_sin_sub_mul_cos (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin y-y*Real.cos y) (x*Real.sin x) x := by
  convert (Real.hasDerivAt_sin x).sub ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x)) using 1 <;> first | rfl | (dsimp; ring)

lemma hasDerivAt_sin_cubic (x : ℝ) :
    HasDerivAt (fun y : ℝ => (1-y^2/3)*Real.sin y-y*Real.cos y)
      (x*(Real.sin x-x*Real.cos x)/3) x := by
  convert (((hasDerivAt_const x (1:ℝ)).sub
    (((hasDerivAt_id x).pow 2).div_const 3)).mul (Real.hasDerivAt_sin x)).sub
    ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x)) using 1 <;> first | rfl | (dsimp; ring)

lemma hasDerivAt_mul_cosh_sub_sinh (x : ℝ) :
    HasDerivAt (fun y : ℝ => y*Real.cosh y-Real.sinh y) (x*Real.sinh x) x := by
  convert ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub (Real.hasDerivAt_sinh x) using 1 <;> first | rfl | (dsimp; ring)

lemma hasDerivAt_sinh_cubic (x : ℝ) :
    HasDerivAt (fun y : ℝ => (1+y^2/3)*Real.sinh y-y*Real.cosh y)
      (x*(x*Real.cosh x-Real.sinh x)/3) x := by
  convert (((hasDerivAt_const x (1:ℝ)).add
    (((hasDerivAt_id x).pow 2).div_const 3)).mul (Real.hasDerivAt_sinh x)).sub
    ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)) using 1 <;> first | rfl | (dsimp; ring)

lemma hasDerivAt_log_sin_correction {x : ℝ} (hx : 0 < x) (hpi : x < Real.pi) :
    HasDerivAt (fun y : ℝ => Real.log (Real.sin y)-Real.log y+y^2/6)
      (Real.cos x/Real.sin x-1/x+x/3) x := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hx hpi
  convert (((Real.hasDerivAt_sin x).log hs.ne').sub
    ((hasDerivAt_id x).log hx.ne')).add (((hasDerivAt_id x).pow 2).div_const 6) using 1 <;> first | rfl | (dsimp; ring)

lemma hasDerivAt_log_sinh_correction {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.log (Real.sinh y)-Real.log y-y^2/6)
      (Real.cosh x/Real.sinh x-1/x-x/3) x := by
  have hs := Real.sinh_pos_iff.mpr hx
  convert (((Real.hasDerivAt_sinh x).log hs.ne').sub
    ((hasDerivAt_id x).log hx.ne')).sub (((hasDerivAt_id x).pow 2).div_const 6) using 1 <;> first | rfl | (dsimp; ring)

lemma sin_sub_mul_cos_nonneg {x : ℝ} (hx : 0 ≤ x) (hpi : x ≤ Real.pi) :
    0 ≤ Real.sin x - x * Real.cos x := by
  have hm : MonotoneOn (fun y : ℝ => Real.sin y - y * Real.cos y) (Icc 0 Real.pi) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by fun_prop)
    · intro y hy
      exact (hasDerivAt_sin_sub_mul_cos y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hasDerivAt_sin_sub_mul_cos y).deriv]
      have hy' : y ∈ Icc 0 Real.pi := interior_subset hy
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi hy'.1 hy'.2
      exact mul_nonneg hy'.1 hs
  simpa using hm (by simp [Real.pi_pos.le]) ⟨hx,hpi⟩ hx

lemma sin_cubic_cot_bound {x : ℝ} (hx : 0 ≤ x) (hpi : x ≤ Real.pi) :
    x * Real.cos x ≤ (1-x^2/3) * Real.sin x := by
  have hm : MonotoneOn (fun y : ℝ => (1-y^2/3)*Real.sin y-y*Real.cos y)
      (Icc 0 Real.pi) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by fun_prop)
    · intro y hy
      exact (hasDerivAt_sin_cubic y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hasDerivAt_sin_cubic y).deriv]
      have hy' : y ∈ Icc 0 Real.pi := interior_subset hy
      exact div_nonneg (mul_nonneg hy'.1 (sin_sub_mul_cos_nonneg hy'.1 hy'.2)) (by norm_num)
  have H := hm (by simp [Real.pi_pos.le]) ⟨hx,hpi⟩ hx
  simp only [sub_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, Real.sin_zero,
    Real.cos_zero, zero_mul, mul_zero] at H
  linarith

lemma mul_cosh_sub_sinh_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x * Real.cosh x - Real.sinh x := by
  have hm : MonotoneOn (fun y : ℝ => y*Real.cosh y-Real.sinh y) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) (by fun_prop)
    · intro y hy
      exact (hasDerivAt_mul_cosh_sub_sinh y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hasDerivAt_mul_cosh_sub_sinh y).deriv]
      have hy' : 0 ≤ y := interior_subset hy
      exact mul_nonneg hy' (Real.sinh_nonneg_iff.mpr hy')
  simpa using hm (by simp) hx hx

lemma sinh_cubic_coth_bound {x : ℝ} (hx : 0 ≤ x) :
    x * Real.cosh x ≤ (1+x^2/3)*Real.sinh x := by
  have hm : MonotoneOn (fun y : ℝ => (1+y^2/3)*Real.sinh y-y*Real.cosh y) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) (by fun_prop)
    · intro y hy
      exact (hasDerivAt_sinh_cubic y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hasDerivAt_sinh_cubic y).deriv]
      have hy' : 0 ≤ y := interior_subset hy
      exact div_nonneg (mul_nonneg hy' (mul_cosh_sub_sinh_nonneg hy')) (by norm_num)
  have H := hm (by simp) hx hx
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_div, Real.sinh_zero,
    Real.cosh_zero, zero_mul, mul_zero, sub_zero, add_zero] at H
  linarith

lemma antitone_log_sin_correction :
    AntitoneOn (fun x : ℝ => Real.log (Real.sin x)-Real.log x+x^2/6) (Ioo 0 Real.pi) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo _ _) ?_ ?_ ?_
  · intro x hx
    exact (hasDerivAt_log_sin_correction hx.1 hx.2).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Ioo 0 Real.pi := interior_subset hx
    exact (hasDerivAt_log_sin_correction hx'.1 hx'.2).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Ioo 0 Real.pi := interior_subset hx
    have hs := Real.sin_pos_of_pos_of_lt_pi hx'.1 hx'.2
    rw [(hasDerivAt_log_sin_correction hx'.1 hx'.2).deriv]
    have hc := sin_cubic_cot_bound hx'.1.le hx'.2.le
    have hp := mul_pos hx'.1 hs
    apply (mul_le_mul_iff_of_pos_right hp).mp
    rw [zero_mul]
    calc
      _ = x * Real.cos x - Real.sin x + x^2 * Real.sin x / 3 := by
        field_simp [hx'.1.ne', hs.ne']
      _ ≤ 0 := by nlinarith

lemma antitone_log_sinh_correction :
    AntitoneOn (fun x : ℝ => Real.log (Real.sinh x)-Real.log x-x^2/6) (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi _) ?_ ?_ ?_
  · intro x hx
    exact (hasDerivAt_log_sinh_correction hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 0 < x := interior_subset hx
    exact (hasDerivAt_log_sinh_correction hx').differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 0 < x := interior_subset hx
    have hs := Real.sinh_pos_iff.mpr hx'
    rw [(hasDerivAt_log_sinh_correction hx').deriv]
    have hc := sinh_cubic_coth_bound hx'.le
    have hp := mul_pos hx' hs
    apply (mul_le_mul_iff_of_pos_right hp).mp
    field_simp [hx'.ne', hs.ne']
    nlinarith

lemma sin_ratio_exp_lower {t x : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hx : 0 < x) (hpi : x < Real.pi) :
    t*Real.exp ((1-t^2)*x^2/6) ≤ Real.sin (t*x)/Real.sin x := by
  have htx := mul_pos ht hx
  have htxl : t*x ≤ x := by nlinarith
  have hs := Real.sin_pos_of_pos_of_lt_pi hx hpi
  have hst := Real.sin_pos_of_pos_of_lt_pi htx (htxl.trans_lt hpi)
  have H := antitone_log_sin_correction ⟨htx,htxl.trans_lt hpi⟩ ⟨hx,hpi⟩ htxl
  dsimp only at H
  rw [Real.log_mul ht.ne' hx.ne'] at H
  have H' : Real.log t + ((1-t^2)*x^2/6) ≤ Real.log (Real.sin (t*x))-Real.log (Real.sin x) := by
    nlinarith
  rw [← Real.log_div hst.ne' hs.ne'] at H'
  have HH := Real.exp_le_exp.mpr H'
  simpa only [Real.exp_add,Real.exp_log ht,Real.exp_log (div_pos hst hs)] using HH

lemma sinh_ratio_exp_lower {t x : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hx : 0 < x) :
    t*Real.exp (-((1-t^2)*x^2/6)) ≤ Real.sinh (t*x)/Real.sinh x := by
  have htx := mul_pos ht hx
  have htxl : t*x ≤ x := by nlinarith
  have hs := Real.sinh_pos_iff.mpr hx
  have hst := Real.sinh_pos_iff.mpr htx
  have H := antitone_log_sinh_correction htx hx htxl
  dsimp only at H
  rw [Real.log_mul ht.ne' hx.ne'] at H
  have H' : Real.log t - ((1-t^2)*x^2/6) ≤ Real.log (Real.sinh (t*x))-Real.log (Real.sinh x) := by
    nlinarith
  rw [← Real.log_div hst.ne' hs.ne'] at H'
  have HH := Real.exp_le_exp.mpr H'
  simpa only [sub_eq_add_neg,Real.exp_add,Real.exp_log ht,Real.exp_log (div_pos hst hs)] using HH
end WeakHessian

end
end InlinedFile0

end OAI
