import OAI.Probability.PosteriorReplicas.Information.ObservableLikelihood

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma normalized_log_likelihood {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {g : X → ℝ≥0∞} (hg : Measurable g) (hpos : ∀ᵐ x ∂ν, 0 < g x)
    (hmean : (∫⁻ x, g x ∂ν) = 1) :
    Integrable (fun x => Real.exp (Real.log (g x).toReal)) ν ∧
      (∫ x, Real.exp (Real.log (g x).toReal) ∂ν) = 1 := by
  have ht : ∀ᵐ x ∂ν, g x < ∞ := ae_lt_top hg (by rw [hmean]; exact ENNReal.one_ne_top)
  have he : (fun x => Real.exp (Real.log (g x).toReal)) =ᵐ[ν] (fun x => (g x).toReal) := by
    filter_upwards [hpos,ht] with x hx hxt
    exact Real.exp_log (ENNReal.toReal_pos hx.ne' hxt.ne)
  refine ⟨(integrable_toReal_of_lintegral_ne_top hg.aemeasurable (by rw [hmean]; exact ENNReal.one_ne_top)).congr he.symm,?_⟩
  rw [integral_congr_ae he,integral_toReal hg.aemeasurable ht,hmean,ENNReal.toReal_one]

lemma observableLikelihood_pos {d ℓ k m : ℕ} (hk : 1 ≤ k) (hkm : k+m ≤ ℓ)
    {f : Vec d → ℝ≥0∞} {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    (z : Observation d ℓ k m) : 0 < observableLikelihood f z := by
  unfold observableLikelihood
  apply ENNReal.mul_pos_iff.mpr
  constructor
  · apply ENNReal.mul_pos_iff.mpr
    constructor
    · exact ENNReal.mul_pos_iff.mpr ⟨equalConstant_pos _ _, ENNReal.inv_pos.mpr (wishartMoment_ne_top hk hkm)⟩
    · exact ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top) _
  · exact ENNReal.pow_pos (ENNReal.inv_pos.mpr (projectedDensity_ne_top .spherical hLt hfL _ _)) _

def observableLog {d ℓ k m : ℕ} (f : Vec d → ℝ≥0∞) (z : Observation d ℓ k m) : ℝ :=
  Real.log (observableLikelihood f z).toReal

@[fun_prop] lemma measurable_observableLog {d ℓ k m : ℕ} {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) : Measurable (@observableLog d ℓ k m f) := by unfold observableLog; fun_prop

lemma observableLog_normalized {d ℓ k m : ℕ} (hd : k+m+2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hkm : k+m ≤ ℓ)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)] :
    Integrable (fun z => Real.exp (observableLog f z))
      (((equalReference (k := k) (m := m) ((sphereLaw d).withDensity f)).prod (auxLaw d ℓ k)).map observe) ∧
    (∫ z, Real.exp (observableLog f z)
      ∂(((equalReference (k := k) (m := m) ((sphereLaw d).withDensity f)).prod (auxLaw d ℓ k)).map observe)) = 1 := by
  apply normalized_log_likelihood _ (measurable_observableLikelihood hf)
    (ae_of_all _ (observableLikelihood_pos hk hkm hLt hfL))
  rw [lintegral_map (by fun_prop) measurable_observe]
  exact observableLikelihood_lintegral hd hk hm hkm hf hLt hfL

end PosteriorReplicas
end

end OAI
