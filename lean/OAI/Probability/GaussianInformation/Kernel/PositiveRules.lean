import Mathlib
import OAI.Probability.GaussianInformation.Kernel.NoisyRules

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference

structure PositiveRule (k d N : ℕ) where
  prob : ((Mat k d) × (Fin k → ℝ)) → Fin N → ℝ
  measurable_prob : Measurable (Function.uncurry prob)
  sum_prob : ∀ t,∑ w,prob t w=1
  lower : ℝ
  lower_pos : 0 < lower
  lower_prob : ∀ t w,lower ≤ prob t w

namespace PositiveRule
variable {k d N : ℕ} (rule : PositiveRule k d N)
lemma nonneg (t) (w) : 0 ≤ rule.prob t w := rule.lower_pos.le.trans (rule.lower_prob t w)
lemma le_one (t) (w) : rule.prob t w ≤ 1 := by
  rw [← rule.sum_prob t]
  exact Finset.single_le_sum (fun v _ => rule.nonneg t v) (Finset.mem_univ w)
lemma measurable (w) : Measurable (fun t => rule.prob t w) :=
  rule.measurable_prob.comp (measurable_id.prodMk measurable_const)
noncomputable def kernel (z : Observation k d) (w : Fin N) : ℝ≥0∞ :=
  ENNReal.ofReal (rule.prob (z.1.1,z.2.1) w)
lemma measurable_kernel : Measurable (Function.uncurry rule.kernel) := by
  unfold kernel
  exact (rule.measurable_prob.comp ((measurable_fst.fst.fst.prodMk measurable_fst.snd.fst).prodMk measurable_snd)).ennreal_ofReal
lemma sum_kernel (z) : ∑ w,rule.kernel z w=1 := by
  unfold kernel
  rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => rule.nonneg _ w),rule.sum_prob,ENNReal.ofReal_one]
lemma kernel_le_one (z) (w) : rule.kernel z w ≤ 1 :=
  ENNReal.ofReal_le_one.mpr (rule.le_one _ _)
lemma lower_kernel (z) (w) : ENNReal.ofReal rule.lower ≤ rule.kernel z w :=
  ENNReal.ofReal_le_ofReal (rule.lower_prob _ _)
noncomputable def response (η : ℝ) (w : Fin N) (s : Ambient d) : ℝ :=
  likelihood (observationBase k d) (observationKernel η) rule.kernel s w
lemma measurable_response (η : ℝ) (w : Fin N) : Measurable (rule.response η w) := by
  have hK : Measurable (Function.uncurry (observationKernel (k := k) (d := d) η)) := observationKernel_measurable η
  have hκ : Measurable (fun z : Observation k d => rule.kernel z w) :=
    rule.measurable_kernel.comp (measurable_id.prodMk measurable_const)
  have hm : Measurable (fun a : Ambient d × Observation k d => observationKernel η a.2 a.1*rule.kernel a.2 w) :=
    (hK.comp measurable_swap).mul (hκ.comp measurable_snd)
  unfold response likelihood
  exact hm.lintegral_prod_right.ennreal_toReal
lemma response_bounds {η : ℝ} (hη : 0 < η) (w) (s) :
    rule.lower ≤ rule.response η w s ∧ rule.response η w s ≤ 1 :=
  likelihood_real_bounds (observationBase k d) (observationKernel η) rule.kernel
    (observationKernel_measurable η) (observationKernel_probability hη) rule.lower_pos.le
    rule.lower_kernel rule.kernel_le_one s w
lemma response_sum {η : ℝ} (hη : 0 < η) (s) : ∑ w,rule.response η w s=1 :=
  likelihood_sum (observationBase k d) (observationKernel η) rule.kernel
    (observationKernel_measurable η) rule.measurable_kernel (observationKernel_probability hη)
    rule.sum_kernel s
lemma response_average {η : ℝ} (hη : 0 < η) (w) (s) :
    rule.response η w s=∫ X,∫ e,rule.prob (X,projectVector X s+e) w ∂noiseLaw k η ∂gaussianRows k d :=
  likelihood_first hη _ (rule.measurable w) (fun t => rule.nonneg t w) (fun t => rule.le_one t w) s
lemma mass_pos {η : ℝ} (hη : 0 < η) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] (w) :
    0 < mass ν (rule.response η w) :=
  rule.lower_pos.trans_le (mass_bounds ν _ (rule.measurable_response η w) rule.lower_pos
    (fun s => (rule.response_bounds hη w s).1) (fun s => (rule.response_bounds hη w s).2)).1
lemma mass_le_one {η : ℝ} (hη : 0 < η) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] (w) :
    mass ν (rule.response η w) ≤ 1 :=
  (mass_bounds ν _ (rule.measurable_response η w) rule.lower_pos
    (fun s => (rule.response_bounds hη w s).1) (fun s => (rule.response_bounds hη w s).2)).2
lemma mass_sum {η : ℝ} (hη : 0 < η) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] :
    ∑ w,mass ν (rule.response η w)=1 := by
  unfold mass
  rw [← integral_finsetSum _ (fun w _ => integrable_rule ν _ (rule.measurable_response η w)
    (fun s => rule.lower_pos.le.trans (rule.response_bounds hη w s).1) (fun s => (rule.response_bounds hη w s).2))]
  simp_rw [rule.response_sum hη]
  simp
lemma post_prob {η : ℝ} (hη : 0 < η) (ν : Measure (Ambient d)) [IsProbabilityMeasure ν] (w) :
    IsProbabilityMeasure (post ν (rule.response η w)) :=
  post_probability ν _ (rule.measurable_response η w)
    (fun s => rule.lower_pos.le.trans (rule.response_bounds hη w s).1)
    (fun s => (rule.response_bounds hη w s).2) (rule.mass_pos hη ν w)
end PositiveRule
end KernelPotential.NoisyDrift

end OAI
