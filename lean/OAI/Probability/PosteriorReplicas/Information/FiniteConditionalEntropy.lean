import OAI.Probability.PosteriorReplicas.Information.FiniteEntropyBounds

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma neg_mul_log_product {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    -(p*q)*Real.log (p*q) = q*(-p*Real.log p)+p*(-q*Real.log q) := by
  rcases hp.eq_or_lt with hp0 | hp0
  · simp [← hp0]
  rcases hq.eq_or_lt with hq0 | hq0
  · simp [← hq0]
  rw [Real.log_mul (ne_of_gt hp0) (ne_of_gt hq0)]
  ring

section
variable {V W : Type*} [Fintype V] [Fintype W] [MeasurableSpace V] [MeasurableSpace W]
    [MeasurableSingletonClass V] [MeasurableSingletonClass W]
    (μ : Measure V) [IsProbabilityMeasure μ] (κ : Kernel V W) [IsMarkovKernel κ]

omit [Fintype W] [IsProbabilityMeasure μ] in
lemma compProd_real_singleton (v : V) (w : W) :
    (μ ⊗ₘ κ).real {(v,w)} = μ.real {v} * (κ v).real {w} := by
  rw [measureReal_def,← singleton_prod_singleton,
    Measure.compProd_apply_prod (measurableSet_singleton v) (measurableSet_singleton w),
    lintegral_singleton,ENNReal.toReal_mul]
  exact mul_comm _ _

omit [IsProbabilityMeasure μ] in
lemma finiteEntropy_compProd :
    finiteEntropy (μ ⊗ₘ κ) = finiteEntropy μ + ∑ v, μ.real {v} * finiteEntropy (κ v) := by
  unfold finiteEntropy
  rw [Fintype.sum_prod_type]
  simp_rw [compProd_real_singleton,neg_mul_log_product measureReal_nonneg measureReal_nonneg]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum,
    sum_probability_atoms (κ v),one_mul]

omit [IsProbabilityMeasure μ] in
lemma finiteEntropy_compProd_conditional :
    finiteEntropy (μ ⊗ₘ κ) - finiteEntropy μ = ∑ v, μ.real {v} * finiteEntropy (κ v) := by
  rw [finiteEntropy_compProd]
  ring

end
end PosteriorReplicas
end

end OAI
