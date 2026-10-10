import Mathlib
import OAI.Probability.Perceptron.Cascade.WeightedCDF
import OAI.Probability.Perceptron.Variational.MarkedVariance

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BoundedContinuousFunction ContDiff
namespace SphericalPerceptronFreeEnergy

lemma sphereTail_measurable (ν : Measure Time) [IsProbabilityMeasure ν] :
    Measurable (sphereTail ν) := by
  have hm : Measurable (fun p : Time×Time=>1-max (p.1:ℝ) (p.2:ℝ)) := by fun_prop
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma sphereKernel_integral_measurable (ν : Measure Time) [IsProbabilityMeasure ν]
    (a : Time→ℝ) (ha : Measurable a) :
    Measurable (fun x=>∫ y,sphereKernel x y*a y ∂ν) := by
  have hm : Measurable (fun p : Time×Time=>sphereKernel p.1 p.2*a p.2) := by
    unfold sphereKernel
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma sphereKernel_integral_abs_bound (ν : Measure Time) [IsProbabilityMeasure ν]
    (a : Time→ℝ) {A : ℝ} (_hA : 0≤A) (hab : ∀ x,|a x|≤A) (r : Time) :
    |∫ y,sphereKernel r y*a y ∂ν|≤A := by
  have hb (y : Time) : ‖sphereKernel r y*a y‖≤A := by
    rw [Real.norm_eq_abs,abs_mul]
    simpa only [one_mul] using mul_le_mul (sphereKernel_abs_le_one r y) (hab y) (abs_nonneg _) zero_le_one
  simpa [Real.norm_eq_abs,Measure.real] using
    norm_integral_le_of_norm_le_const (ae_of_all ν hb)

lemma tangent_wronskian_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure Time) [IsProbabilityMeasure ν]
    (r s t : Ω→Time) (hr : Measurable r) (hs : Measurable s) (ht : Measurable t)
    (hmarg : P.map r=ν)
    (hlaws : P.map (fun x=>(r x,s x))=(1/2:ℝ≥0) • (ν.prod ν)+(1/2:ℝ≥0) • (ν.map fun x=>(x,x)))
    (hlawt : P.map (fun x=>(r x,t x))=(1/2:ℝ≥0) • (ν.prod ν)+(1/2:ℝ≥0) • (ν.map fun x=>(x,x)))
    (htri : ∀ᵐ x ∂P,UltrametricTriangle (r x:ℝ) (s x:ℝ) (t x:ℝ))
    (a : Time→ℝ) (ha : Measurable a) {A : ℝ} (hA : 0≤A) (hab : ∀ x,|a x|≤A)
    (hT : ∀ G : ℝ→ᵇℝ,ContDiff ℝ 1 (G : ℝ→ℝ)→
      (∫ x,G (r x)*((r x:ℝ)-a (r x)*(1-(r x:ℝ)^2)+2*a (s x)*((t x:ℝ)-(r x:ℝ)*(s x:ℝ))) ∂P)=0) :
    ∀ᵐ x ∂ν,a x*sphereTail ν x=(x:ℝ)+∫ y,sphereKernel x y*a y ∂ν := by
  let Z : Time→ℝ := fun x=>(x:ℝ)-a x*sphereTail ν x+∫ y,sphereKernel x y*a y ∂ν
  have hZm : Measurable Z := (measurable_subtype_coe.sub (ha.mul (sphereTail_measurable ν))).add
    (sphereKernel_integral_measurable ν a ha)
  have hZb (x : Time) : |Z x|≤1+2*A := by
    have htail : |sphereTail ν x|≤1 := by
      rw [abs_of_nonneg (sphereTail_nonneg ν x)]
      exact (sphereTail_upper ν x).trans (by linarith [x.property.1])
    have hx : |a x*sphereTail ν x|≤A := by
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul (hab x) htail (abs_nonneg _) hA
    have hg := (abs_sub (x:ℝ) (a x*sphereTail ν x)).trans (add_le_add (time_abs_le_one x) hx)
    exact (abs_add_le _ _).trans ((add_le_add hg (sphereKernel_integral_abs_bound ν a hA hab x)).trans (by ring_nf; exact le_rfl))
  have hz : ∀ G : ℝ→ᵇℝ,ContDiff ℝ 1 (G : ℝ→ℝ)→(∫ x,G x*Z x ∂ν)=0 := by
    intro G hG
    rw [←tangent_wronskian_test P ν r s t hr hs ht hmarg hlaws hlawt htri a ha hA hab G]
    exact hT G hG
  have hz' (F : Time→ᵇℝ) : (∫ x,F x*Z x ∂ν)=0 :=
    smooth_compact_test_extend ν zero_le_one id measurable_id Z hZm (by linarith) hZb hz F
  have hz2 := bounded_continuous_test_extend ν id measurable_id Z hZm (by linarith) hZb hz' Z hZm (by linarith) hZb
  have hi : Integrable (fun x=>Z x*Z x) ν := boundedAbs_integrable ν _ (hZm.mul hZm) ((1+2*A)^2) (fun x=>by
    rw [abs_mul,←pow_two]
    exact pow_le_pow_left₀ (abs_nonneg _) (hZb x) 2)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x=>mul_self_nonneg (Z x)) hi).mp hz2
  filter_upwards [hae] with x hx
  have h := mul_self_eq_zero.mp hx
  change (x:ℝ)-a x*sphereTail ν x+∫ y,sphereKernel x y*a y ∂ν=0 at h
  linarith

theorem tangent_sphere_self_consistency {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure Time) [IsProbabilityMeasure ν]
    (r s t : Ω→Time) (hr : Measurable r) (hs : Measurable s) (ht : Measurable t)
    (hmarg : P.map r=ν)
    (hlaws : P.map (fun x=>(r x,s x))=(1/2:ℝ≥0) • (ν.prod ν)+(1/2:ℝ≥0) • (ν.map fun x=>(x,x)))
    (hlawt : P.map (fun x=>(r x,t x))=(1/2:ℝ≥0) • (ν.prod ν)+(1/2:ℝ≥0) • (ν.map fun x=>(x,x)))
    (htri : ∀ᵐ x ∂P,UltrametricTriangle (r x:ℝ) (s x:ℝ) (t x:ℝ))
    (a : Time→ℝ) (ha : Measurable a) {A : ℝ} (hA : 0≤A) (hab : ∀ x,0≤a x ∧ a x≤A)
    (hT : ∀ G : ℝ→ᵇℝ,ContDiff ℝ 1 (G : ℝ→ℝ)→
      (∫ x,G (r x)*((r x:ℝ)-a (r x)*(1-(r x:ℝ)^2)+2*a (s x)*((t x:ℝ)-(r x:ℝ)*(s x:ℝ))) ∂P)=0) :
    (∀ᵐ x ∂ν,a x=∫ y in 0..(x:ℝ),(realTail ν y)⁻¹^2) ∧
      ∀ᵐ x : Time ∂ν,(x:ℝ)≤A/(1+A) := by
  apply sphere_self_consistency ν hA ha.aestronglyMeasurable
    (ae_of_all _ fun x=>(hab x).1) (ae_of_all _ fun x=>(hab x).2)
  exact tangent_wronskian_ae P ν r s t hr hs ht hmarg hlaws hlawt htri a ha hA
    (fun x=>by rw [abs_of_nonneg (hab x).1]; exact (hab x).2) hT

end SphericalPerceptronFreeEnergy
end

end OAI
