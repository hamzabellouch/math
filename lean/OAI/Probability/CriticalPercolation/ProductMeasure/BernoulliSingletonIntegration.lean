import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.BernoulliSingleton

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma integral_singleton_decomposition (q : E → unitInterval) (e : E)
    (f : Set E → ℝ) (hm : Measurable f) (C : ℝ) (hb : ∀ ω, ‖f ω‖≤C) :
    (∫ ω, f ω ∂law q) = (q e : ℝ)*(∫ ω, f (forceOn {e} Set.univ ω) ∂law q)+
      (1-(q e : ℝ))*(∫ ω, f (forceOn {e} ∅ ω) ∂law q) := by
  have hi (σ : Set E) : Integrable f ((law q).map (forceOn {e} σ)) := by
    exact Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hb)
  conv_lhs => rw [law_singleton_decomposition q e]
  rw [integral_add_measure ((hi _).smul_measure (measure_ne_top _ _))
    ((hi _).smul_measure (measure_ne_top _ _)),integral_smul_measure,integral_smul_measure,
    integral_map (measurable_forceOn _ _).aemeasurable hm.aestronglyMeasurable,
    integral_map (measurable_forceOn _ _).aemeasurable hm.aestronglyMeasurable]
  have ht := bitMeasure_real_singleton (q e) True
  have hf := bitMeasure_real_singleton (q e) False
  simp only [measureReal_def,bitWeight,ite_true,ite_false] at ht hf
  simp only [smul_eq_mul,ht,hf]

lemma integral_centered_singleton (q : E → unitInterval) (e : E)
    (f : Set E → ℝ) (hm : Measurable f) (C : ℝ) (hC : 0≤C) (hb : ∀ ω, ‖f ω‖≤C) :
    (∫ ω, (if e∈ω then 1-(q e : ℝ) else -(q e : ℝ))*f ω ∂law q) =
      (q e : ℝ)*(1-(q e : ℝ))*
        ((∫ ω, f (forceOn {e} Set.univ ω) ∂law q) - (∫ ω, f (forceOn {e} ∅ ω) ∂law q)) := by
  have hm' : Measurable (fun ω => (if e∈ω then 1-(q e : ℝ) else -(q e : ℝ))*f ω) :=
    (measurable_const.ite (measurable_set_mem e).setOf measurable_const).mul hm
  have hb' (ω : Set E) : ‖(if e∈ω then 1-(q e : ℝ) else -(q e : ℝ))*f ω‖≤C := by
    rw [norm_mul]
    have hc : ‖(if e∈ω then 1-(q e : ℝ) else -(q e : ℝ))‖≤1 := by
      split_ifs <;> simp only [Real.norm_eq_abs]
      · rw [abs_of_nonneg (sub_nonneg.mpr (q e).property.2)]
        linarith [(q e).property.1]
      · rw [abs_neg,abs_of_nonneg (q e).property.1]
        exact (q e).property.2
    exact (mul_le_mul_of_nonneg_left (hb ω) (norm_nonneg _)).trans
      ((mul_le_mul_of_nonneg_right hc hC).trans_eq (one_mul C))
  rw [integral_singleton_decomposition q e _ hm' C hb']
  have ht (ω : Set E) : e∈forceOn {e} Set.univ ω := by simp
  have hf (ω : Set E) : e∉forceOn {e} ∅ ω := by simp
  simp only [ite_eq_left (ht _),ite_eq_right (hf _),integral_const_mul]
  ring

end CriticalPercolation.BernoulliProduct
end
end

end OAI
