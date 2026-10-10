import OAI.Probability.CriticalPercolation.ProductMeasure.BernoulliSingleton

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma force_closed_after_singleton (e : E) (σ ω : Set E) :
    forceOn {e} ∅ (forceOn {e} σ ω) = forceOn {e} ∅ ω := by
  ext f
  by_cases hf : f = e <;> simp [hf]

lemma lintegral_singleton_decomposition (q : E → unitInterval) (e : E)
    (f : Set E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f ω ∂law q) =
      bitMeasure (q e) {True} * (∫⁻ ω, f (forceOn {e} Set.univ ω) ∂law q) +
      bitMeasure (q e) {False} * (∫⁻ ω, f (forceOn {e} ∅ ω) ∂law q) := by
  conv_lhs => rw [law_singleton_decomposition q e]
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_map hf (measurable_forceOn _ _), lintegral_map hf (measurable_forceOn _ _)]
  rfl

lemma lintegral_open_closed_observable (q : E → unitInterval) (e : E)
    (F : Set E → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, if e ∈ ω then F (forceOn {e} ∅ ω) else 0 ∂law q) =
      bitMeasure (q e) {True} * ∫⁻ ω, F (forceOn {e} ∅ ω) ∂law q := by
  have hm : Measurable (fun ω => if e ∈ ω then F (forceOn {e} ∅ ω) else 0) :=
    (hF.comp (measurable_forceOn _ _)).ite (measurable_set_mem e).setOf measurable_const
  rw [lintegral_singleton_decomposition q e _ hm]
  simp only [mem_forceOn, Set.mem_singleton, ite_true, Set.mem_univ,
    Set.mem_empty_iff_false, ite_false, force_closed_after_singleton,
    lintegral_zero, mul_zero, add_zero]

lemma lintegral_closed_observable (q : E → unitInterval) (e : E)
    (F : Set E → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, if e ∉ ω then F ω else 0 ∂law q) =
      bitMeasure (q e) {False} * ∫⁻ ω, F (forceOn {e} ∅ ω) ∂law q := by
  have hm : Measurable (fun ω => if e ∉ ω then F ω else 0) :=
    hF.ite (measurable_set_mem e).setOf.compl measurable_const
  rw [lintegral_singleton_decomposition q e _ hm]
  simp only [mem_forceOn, Set.mem_singleton, ite_true, Set.mem_univ,
    Set.mem_empty_iff_false, not_true_eq_false, not_false_eq_true,
    ite_false, ite_true, lintegral_zero, mul_zero, zero_add]

theorem lintegral_edge_closing (q : E → unitInterval) (e : E)
    (he : (q e : ℝ) < 1) (F : Set E → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, if e ∈ ω then F (forceOn {e} ∅ ω) else 0 ∂law q) =
      (ENNReal.ofReal (q e : ℝ) / ENNReal.ofReal (1 - (q e : ℝ))) *
        (∫⁻ ω, if e ∉ ω then F ω else 0 ∂law q) := by
  have hbit (b : Prop) : bitMeasure (q e) {b} = ENNReal.ofReal (bitWeight (q e) b) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    congr 1
    exact bitMeasure_real_singleton (q e) b
  have hne : ENNReal.ofReal (1 - (q e : ℝ)) ≠ 0 := (ENNReal.ofReal_pos.mpr (sub_pos.mpr he)).ne'
  rw [lintegral_open_closed_observable q e F hF, lintegral_closed_observable q e F hF,
    hbit True, hbit False]
  simp only [bitWeight, ite_true, ite_false]
  rw [← mul_assoc, ENNReal.div_mul_cancel hne ENNReal.ofReal_ne_top]

end CriticalPercolation.BernoulliProduct

end

end OAI
