import OAI.Analysis.LpDimension.DyadicRamps

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset
open scoped BigOperators Topology Matrix ENNReal NNReal
universe u uE uΩ uι

namespace SubpolynomialLp

variable {ι : Type uι} {Ω : Type uΩ} [Fintype ι] [MeasurableSpace Ω]

def averageLaw (μ : ι → Measure Ω) : Measure Ω :=
  (Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, μ i

instance averageLaw_probability [Nonempty ι] (μ : ι → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)] : IsProbabilityMeasure (averageLaw μ) := by
  constructor
  simp [averageLaw,Measure.smul_apply,Measure.finsetSum_apply,ENNReal.inv_mul_cancel,
    Fintype.card_ne_zero]

lemma averageLaw_integrable (μ : ι → Measure Ω) (f : Ω → ℝ)
    (hf : ∀ i, Integrable f (μ i)) : Integrable f (averageLaw μ) := by
  by_cases h : IsEmpty ι
  · let _ := h
    simp [averageLaw]
  · have : Nonempty ι := not_isEmpty_iff.mp h
    exact (integrable_finsetSum_measure.mpr (fun i _ => hf i)).smul_measure (by simp)

lemma averageLaw_integral (μ : ι → Measure Ω) (f : Ω → ℝ)
    (hf : ∀ i, Integrable f (μ i)) :
    (∫ x, f x ∂averageLaw μ) = (∑ i, ∫ x, f x ∂μ i)/(Fintype.card ι : ℝ) := by
  rw [averageLaw,integral_smul_measure,integral_finsetSum_measure (fun i _ => hf i)]
  simp [smul_eq_mul,div_eq_mul_inv,mul_comm]

lemma averageLaw_ae [Nonempty ι] (μ : ι → Measure Ω) (P : Ω → Prop)
    (hP : ∀ i, ∀ᵐ x ∂μ i, P x) : ∀ᵐ x ∂averageLaw μ, P x := by
  exact Measure.ae_smul_measure (ae_finsetSum_measure_iff.mpr (fun i _ => hP i)) _

section Symmetric
variable {E : Type uE} [AddCommGroup E] [MeasurableSpace E] [MeasurableNeg E]

def symmetricLaw (μ : Measure E) : Measure E := (1/2 : ℝ≥0∞) • μ +
  (1/2 : ℝ≥0∞) • μ.map (fun x => -x)

instance symmetricLaw_probability (μ : Measure E) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (symmetricLaw μ) := by
  have : IsProbabilityMeasure (μ.map (fun x=>-x)) := inferInstance
  constructor
  norm_num [symmetricLaw,Measure.add_apply,Measure.smul_apply,ENNReal.inv_two_add_inv_two]

lemma symmetricLaw_symmetry (μ : Measure E) :
    (symmetricLaw μ).map (fun x=>-x) = symmetricLaw μ := by
  rw [symmetricLaw,Measure.map_add _ _ measurable_neg,
    Measure.map_smul _ measurable_neg.aemeasurable,
    Measure.map_smul _ measurable_neg.aemeasurable,
    Measure.map_map measurable_neg measurable_neg]
  simp only [Function.comp_def,neg_neg,Measure.map_id']
  exact add_comm _ _

lemma symmetricLaw_ae (μ : Measure E) (P : E → Prop)
    (hP : ∀ᵐ x ∂μ, P x) (hN : ∀ x, P x → P (-x)) :
    ∀ᵐ x ∂symmetricLaw μ, P x := by
  apply ae_add_measure_iff.mpr
  constructor
  · exact Measure.ae_smul_measure hP _
  · apply Measure.ae_smul_measure
    exact (measurableEmbedding_neg.ae_map_iff).mpr (hP.mono hN)


lemma symmetricLaw_even_integral (μ : Measure E) (f : E → ℝ) (hf : Measurable f)
    (hi : Integrable f μ) (hn : ∀ x, f (-x) = f x) :
    (∫ x, f x ∂symmetricLaw μ) = ∫ x, f x ∂μ := by
  have hi' : Integrable f (μ.map (fun x=>-x)) := by
    rw [integrable_map_measure hf.aestronglyMeasurable measurable_neg.aemeasurable]
    simpa only [Function.comp_def,hn] using hi
  rw [symmetricLaw,integral_add_measure (hi.smul_measure (by norm_num))
    (hi'.smul_measure (by norm_num)),integral_smul_measure,integral_smul_measure,
    integral_map measurable_neg.aemeasurable hf.aestronglyMeasurable]
  simp only [hn,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat,smul_eq_mul]
  ring
end Symmetric

end SubpolynomialLp

end

end OAI
