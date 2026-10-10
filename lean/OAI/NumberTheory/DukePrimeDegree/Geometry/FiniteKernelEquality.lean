import OAI.NumberTheory.DukePrimeDegree.Entropy.PrefixRootConditionals

namespace OAI

/-! # One null set for equality of finite kernels -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace DukePrimeDegree

lemma finiteKernels_ae_eq_of_apply
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace B]
    (κ η : Kernel A B) [IsFiniteKernel κ] [IsFiniteKernel η] (μ : Measure A)
    (h : ∀ U, MeasurableSet U → ∀ᵐ a ∂μ, κ a U = η a U) :
    ∀ᵐ a ∂μ, κ a = η a := by
  let f := embeddingReal B
  have hf := measurableEmbedding_embeddingReal B
  let κ' := κ.map f
  let η' := η.map f
  have ht (U : Set ℝ) (hU : MeasurableSet U) : ∀ᵐ a ∂μ, κ' a U = η' a U := by
    filter_upwards [h (f ⁻¹' U) (hf.measurable hU)] with a ha
    change (κ.map f) a U = (η.map f) a U
    rw [Kernel.map_apply' κ hf.measurable _ hU,Kernel.map_apply' η hf.measurable _ hU]
    exact ha
  have Hall : ∀ᵐ a ∂μ, ∀ ⦃U⦄, MeasurableSet U → κ' a U = η' a U := by
    apply MeasurableSpace.ae_induction_on_inter Real.borel_eq_generateFrom_Iic_rat
      Real.isPiSystem_Iic_rat
    · simp
    · simp only [iUnion_singleton_eq_range,mem_range,forall_exists_index,forall_apply_eq_imp_iff]
      exact ae_all_iff.mpr fun q => ht _ measurableSet_Iic
    · filter_upwards [ht univ MeasurableSet.univ] with a ha U hU heq
      rw [measure_compl hU (measure_ne_top _ _),measure_compl hU (measure_ne_top _ _),ha,heq]
    · exact ae_of_all _ fun a F hdisj hF heq => by
        rw [measure_iUnion hdisj hF,measure_iUnion hdisj hF]
        exact tsum_congr heq
  filter_upwards [Hall] with a ha
  apply hf.map_injective
  have he : κ' a = η' a := Measure.ext fun U hU => ha hU
  change (κ.map f) a = (η.map f) a at he
  rw [Kernel.map_apply κ hf.measurable,Kernel.map_apply η hf.measurable] at he
  exact he

end DukePrimeDegree

end

end OAI
