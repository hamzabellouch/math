import Mathlib

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
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open scoped ENNReal NNReal

namespace WeakHessianTransport

def joinControl (u v : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r ≤ 1/2 then 2*u (2*r) else 2*v (2*r-1)

lemma measurable_joinControl {u v : ℝ → ℝ} (hu : Measurable u) (hv : Measurable v) :
    Measurable (joinControl u v) := by
  exact Measurable.ite measurableSet_Iic
    (measurable_const.mul (hu.comp (measurable_const.mul measurable_id)))
    (measurable_const.mul (hv.comp ((measurable_const.mul measurable_id).sub measurable_const)))

lemma intervalIntegrable_joinControl_left {u v : ℝ → ℝ}
    (hu : IntervalIntegrable u volume 0 1) :
    IntervalIntegrable (joinControl u v) volume 0 (1/2) := by
  have H : IntervalIntegrable (fun r => 2*u (2*r)) volume 0 (1/2) := by
    simpa using (hu.comp_mul_left (c := 2)).const_mul 2
  apply H.congr
  intro r hr
  simp only [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/2), mem_Ioc] at hr
  simp only [joinControl, ite_eq_left hr.2]

lemma intervalIntegrable_joinControl_right {u v : ℝ → ℝ}
    (hv : IntervalIntegrable v volume 0 1) :
    IntervalIntegrable (joinControl u v) volume (1/2) 1 := by
  have H : IntervalIntegrable (fun r => 2*v (2*r-1)) volume (1/2) 1 := by
    convert ((hv.comp_sub_right 1).comp_mul_left (c := 2)).const_mul 2 using 1 <;> norm_num
  apply H.congr
  intro r hr
  simp only [uIoc_of_le (by norm_num : (1/2:ℝ) ≤ 1), mem_Ioc] at hr
  simp only [joinControl, ite_eq_right (not_le.mpr hr.1)]

lemma intervalIntegrable_joinControl {u v : ℝ → ℝ}
    (hu : IntervalIntegrable u volume 0 1) (hv : IntervalIntegrable v volume 0 1) :
    IntervalIntegrable (joinControl u v) volume 0 1 :=
  (intervalIntegrable_joinControl_left hu).trans (intervalIntegrable_joinControl_right hv)

lemma joinControl_sq (u v : ℝ → ℝ) :
    (fun r => (joinControl u v r)^2) = fun r => 2*joinControl (fun s => (u s)^2) (fun s => (v s)^2) r := by
  funext r
  simp only [joinControl]
  split_ifs <;> ring

lemma intervalIntegrable_joinControl_sq {u v : ℝ → ℝ}
    (hu : IntervalIntegrable (fun r => (u r)^2) volume 0 1)
    (hv : IntervalIntegrable (fun r => (v r)^2) volume 0 1) :
    IntervalIntegrable (fun r => (joinControl u v r)^2) volume 0 1 := by
  rw [joinControl_sq]
  exact (intervalIntegrable_joinControl hu hv).const_mul 2

lemma integral_joinControl_left (u v : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (hb : b ≤ 1/2) :
    (∫ r in a..b, joinControl u v r) = ∫ r in (2*a)..(2*b), u r := by
  calc
    (∫ r in a..b, joinControl u v r) = ∫ r in a..b, 2*u (2*r) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le hab] at hr
      simp only [joinControl, ite_eq_left (hr.2.trans hb)]
    _ = ∫ r in (2*a)..(2*b), u r := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left u (by norm_num : (2:ℝ) ≠ 0)]
      simp

lemma integral_joinControl_right (u v : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) (ha : 1/2 ≤ a) :
    (∫ r in a..b, joinControl u v r) = ∫ r in (2*a-1)..(2*b-1), v r := by
  calc
    (∫ r in a..b, joinControl u v r) = ∫ r in a..b, 2*v (2*r-1) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab
      intro r hr
      simp only [joinControl, ite_eq_right (not_le.mpr (ha.trans_lt hr.1))]
    _ = ∫ r in (2*a-1)..(2*b-1), v r := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_sub v (by norm_num : (2:ℝ) ≠ 0)]
      simp

lemma integral_joinControl {u v : ℝ → ℝ}
    (hu : IntervalIntegrable u volume 0 1) (hv : IntervalIntegrable v volume 0 1) :
    (∫ r in (0:ℝ)..1, joinControl u v r) = (∫ r in (0:ℝ)..1, u r)+(∫ r in (0:ℝ)..1, v r) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_joinControl_left hu)
    (intervalIntegrable_joinControl_right hv), integral_joinControl_left u v (by norm_num) le_rfl,
    integral_joinControl_right u v (by norm_num) le_rfl]
  norm_num

lemma integral_joinControl_sq {u v : ℝ → ℝ}
    (hu : IntervalIntegrable (fun r => (u r)^2) volume 0 1)
    (hv : IntervalIntegrable (fun r => (v r)^2) volume 0 1) :
    (∫ r in (0:ℝ)..1, (joinControl u v r)^2) =
      2*((∫ r in (0:ℝ)..1, (u r)^2)+(∫ r in (0:ℝ)..1, (v r)^2)) := by
  rw [joinControl_sq, intervalIntegral.integral_const_mul, integral_joinControl hu hv]

end WeakHessianTransport

end
end InlinedFile0

end OAI
