import Mathlib
import OAI.Geometry.WeakHessian.Entropy.ReducedEntropy

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
open Set Filter
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
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

lemma log_one_add_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1+x) ≤ 2*Real.sqrt x := by
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  have H := Real.add_one_le_exp (Real.sqrt x)
  have hp := Real.exp_pos (Real.sqrt x)
  have hs := Real.sq_sqrt hx
  have hn := Real.sqrt_nonneg x
  rw [show 2*Real.sqrt x = Real.sqrt x+Real.sqrt x by ring,Real.exp_add]
  nlinarith [sq_nonneg (Real.exp (Real.sqrt x)-(Real.sqrt x+1))]

lemma renormalizedEntropy_error {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    |renormalizedEntropy a x-reducedEntropy x| ≤ 4*Real.sqrt a*Real.sqrt x := by
  by_cases hz : x = 0
  · simp [hz,renormalizedEntropy,regularizedEntropy_zero,reducedEntropy]
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
  have he : renormalizedEntropy a x-reducedEntropy x =
      x*Real.log (1+a/x)+a*Real.log (1+x/a) := by
    rw [renormalizedEntropy_eq ha hx,reducedEntropy,
      show 1+a/x = (x+a)/x by field_simp,
      show 1+x/a = (x+a)/a by field_simp; ring,
      Real.log_div (by positivity) hxp.ne',Real.log_div (by positivity) ha.ne']
    ring
  have hp : 0 ≤ x*Real.log (1+a/x)+a*Real.log (1+x/a) :=
    add_nonneg (mul_nonneg hx (Real.log_nonneg (by linarith [div_nonneg ha.le hx])))
      (mul_nonneg ha.le (Real.log_nonneg (by linarith [div_nonneg hx ha.le])))
  rw [he,abs_of_nonneg hp]
  have H1 := mul_le_mul_of_nonneg_left (log_one_add_le_two_sqrt (div_nonneg ha.le hx)) hx
  have H2 := mul_le_mul_of_nonneg_left (log_one_add_le_two_sqrt (div_nonneg hx ha.le)) ha.le
  have h1 : x*Real.sqrt (a/x) = Real.sqrt a*Real.sqrt x := by
    rw [Real.sqrt_div ha.le,← mul_div_assoc]
    apply (div_eq_iff (Real.sqrt_ne_zero'.mpr hxp)).mpr
    rw [mul_assoc,Real.mul_self_sqrt hx,mul_comm]
  have h2 : a*Real.sqrt (x/a) = Real.sqrt a*Real.sqrt x := by
    rw [Real.sqrt_div hx,← mul_div_assoc]
    apply (div_eq_iff (Real.sqrt_ne_zero'.mpr ha)).mpr
    calc
      a*Real.sqrt x = (Real.sqrt a*Real.sqrt a)*Real.sqrt x := by rw [Real.mul_self_sqrt ha.le]
      _ = _ := by ring
  nlinarith
end WeakHessian
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma integrable_reducedEntropy_of_sqrt (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hs : Integrable (fun x => Real.sqrt (u x)) m) :
    Integrable (fun x => reducedEntropy (u x)) m := by
  apply ((regularizedEntropy_integrable (a := 1) zero_lt_one u).norm.add (hs.const_mul 4)).mono'
    ((Real.continuous_mul_log.sub continuous_id).comp_aestronglyMeasurable (Lp.aestronglyMeasurable u))
  filter_upwards [hun] with x hx
  have H := renormalizedEntropy_error (a := 1) zero_lt_one hx
  simp only [Real.sqrt_one,mul_one,renormalizedEntropy,Real.log_one,zero_mul,add_zero] at H
  have H' := abs_sub_comm (regularizedEntropy 1 (u x)) (reducedEntropy (u x))
  simp only [Real.norm_eq_abs,Pi.add_apply]
  calc
    |reducedEntropy (u x)| ≤ |reducedEntropy (u x)-regularizedEntropy 1 (u x)|+
        |regularizedEntropy 1 (u x)| := by simpa only [sub_zero] using abs_sub_le (reducedEntropy (u x)) (regularizedEntropy 1 (u x)) 0
    _ ≤ _ := by rw [← H']; linarith

lemma integral_renormalizedEntropy_error {a : ℝ} (ha : 0 < a) (u : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    (hs : Integrable (fun x => Real.sqrt (u x)) m) :
    |(∫ x,renormalizedEntropy a (u x) ∂m)-(∫ x,reducedEntropy (u x) ∂m)| ≤
      4*Real.sqrt a*(∫ x,Real.sqrt (u x) ∂m) := by
  rw [← integral_sub (renormalizedEntropy_integrable ha u hi) (integrable_reducedEntropy_of_sqrt u hun hs)]
  calc
    _ ≤ ∫ x,|renormalizedEntropy a (u x)-reducedEntropy (u x)| ∂m := abs_integral_le_integral_abs
    _ ≤ ∫ x,4*Real.sqrt a*Real.sqrt (u x) ∂m := by
      apply integral_mono_ae
        ((renormalizedEntropy_integrable ha u hi).sub (integrable_reducedEntropy_of_sqrt u hun hs)).abs
        (hs.const_mul _)
      exact hun.mono (fun x hx => renormalizedEntropy_error ha hx)
    _ = _ := integral_const_mul _ _

lemma tendsto_integral_renormalizedEntropy_Lp {a : ℝ} (ha : 0 < a)
    {us : ℕ → Lp ℝ 2 m} {u : Lp ℝ 2 m} (hu : Tendsto us atTop (𝓝 u))
    (hi : Integrable u m) (his : ∀ n,Integrable (us n) m)
    (hm : ∀ n,(∫ x,us n x ∂m) = ∫ x,u x ∂m) :
    Tendsto (fun n => ∫ x,renormalizedEntropy a (us n x) ∂m) atTop
      (𝓝 (∫ x,renormalizedEntropy a (u x) ∂m)) := by
  have H := ((regularizedEntropy_hasFDeriv ha u).continuousAt.tendsto.comp hu).add_const
    (Real.log a*(∫ x,u x ∂m))
  have he (v : Lp ℝ 2 m) (hv : Integrable v m) :
      (∫ x,renormalizedEntropy a (v x) ∂m) =
        (∫ x,regularizedEntropy a (v x) ∂m)+Real.log a*(∫ x,v x ∂m) := by
    simp only [renormalizedEntropy]
    rw [integral_add (regularizedEntropy_integrable ha v) (hv.const_mul _),integral_const_mul]
  simpa only [he u hi,he _ (his _),hm,Function.comp_apply] using H

lemma tendsto_integral_reducedEntropy_of_sqrt_bound
    {us : ℕ → Lp ℝ 2 m} {u : Lp ℝ 2 m} (hu : Tendsto us atTop (𝓝 u))
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hns : ∀ n,∀ᵐ x ∂m,0 ≤ us n x)
    (hi : Integrable u m) (his : ∀ n,Integrable (us n) m)
    (hm : ∀ n,(∫ x,us n x ∂m) = ∫ x,u x ∂m)
    (hs : Integrable (fun x => Real.sqrt (u x)) m)
    (hss : ∀ n,Integrable (fun x => Real.sqrt (us n x)) m)
    {C : ℝ} (hsC : (∫ x,Real.sqrt (u x) ∂m) ≤ C)
    (hssC : ∀ n,(∫ x,Real.sqrt (us n x) ∂m) ≤ C) :
    Tendsto (fun n => ∫ x,reducedEntropy (us n x) ∂m) atTop
      (𝓝 (∫ x,reducedEntropy (u x) ∂m)) := by
  have hlim : Tendsto (fun k => 4*Real.sqrt (fisherEpsilon k)*C) atTop (𝓝 0) := by
    simpa using ((fisherEpsilon_tendsto.sqrt.const_mul 4).mul_const C)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k,hk⟩ := (hlim.eventually_lt_const (by linarith : 0 < ε/3)).exists
  have H := tendsto_integral_renormalizedEntropy_Lp (fisherEpsilon_pos k) hu hi his hm
  obtain ⟨n,hn⟩ := Metric.tendsto_atTop.mp H (ε/3) (by linarith)
  refine ⟨n,fun j hj => ?_⟩
  have he0 := (integral_renormalizedEntropy_error (fisherEpsilon_pos k) u hun hi hs).trans
    (mul_le_mul_of_nonneg_left hsC (by positivity))
  have hej := (integral_renormalizedEntropy_error (fisherEpsilon_pos k) (us j) (hns j) (his j) (hss j)).trans
    (mul_le_mul_of_nonneg_left (hssC j) (by positivity))
  have hh := hn j hj
  rw [Real.dist_eq] at hh ⊢
  have he := abs_sub_le (∫ x,reducedEntropy (us j x) ∂m)
    (∫ x,renormalizedEntropy (fisherEpsilon k) (us j x) ∂m)
    (∫ x,reducedEntropy (u x) ∂m)
  have he' := abs_sub_le (∫ x,renormalizedEntropy (fisherEpsilon k) (us j x) ∂m)
    (∫ x,renormalizedEntropy (fisherEpsilon k) (u x) ∂m)
    (∫ x,reducedEntropy (u x) ∂m)
  rw [abs_sub_comm (∫ x,renormalizedEntropy (fisherEpsilon k) (us j x) ∂m)] at hej
  linarith
end WeakHessian

end
end InlinedFile0

end OAI
