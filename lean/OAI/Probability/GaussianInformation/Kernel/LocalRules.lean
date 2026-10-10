import Mathlib
import OAI.Probability.GaussianInformation.Kernel.NoiseContinuity

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.NoisyDrift
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference
structure LocalRule (k d N : ℕ) where
  prob : ((Mat k d) × (Fin k → ℝ)) → Fin N → ℝ
  measurable : ∀ w,Measurable (fun t => prob t w)
  nonneg : ∀ t w,0 ≤ prob t w
  sum : ∀ t,∑ w,prob t w=1
namespace LocalRule
variable {k d N : ℕ} (rule : LocalRule k d N)
lemma le_one (t) (w) : rule.prob t w ≤ 1 := by
  rw [← rule.sum t]
  exact Finset.single_le_sum (fun v _ => rule.nonneg t v) (Finset.mem_univ w)
noncomputable def response (w : Fin N) (s : Ambient d) : ℝ :=
  ∫ X,rule.prob (X,projectVector X s) w ∂gaussianRows k d
lemma integrable_eval (w : Fin N) (s : Ambient d) :
    Integrable (fun X => rule.prob (X,projectVector X s) w) (gaussianRows k d) := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  apply Integrable.of_bound ((rule.measurable w).comp (measurable_id.prodMk
    ((continuous_projectVector.comp (continuous_id.prodMk continuous_const)).measurable))).aestronglyMeasurable 1
  filter_upwards [] with X
  change ‖rule.prob (X,projectVector X s) w‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (rule.nonneg _ _)]
  exact rule.le_one _ _
lemma measurable_response (w : Fin N) : Measurable (rule.response w) := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have hm : Measurable (fun t : Ambient d × Mat k d => rule.prob (t.2,projectVector t.2 t.1) w) :=
    (rule.measurable w).comp (measurable_snd.prodMk ((continuous_projectVector.comp (continuous_snd.prodMk continuous_fst)).measurable))
  exact hm.stronglyMeasurable.integral_prod_right.measurable
lemma response_bounds (w : Fin N) (s : Ambient d) : 0 ≤ rule.response w s ∧ rule.response w s ≤ 1 := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  exact ⟨integral_nonneg (fun _ => rule.nonneg _ _),by
    simpa [response] using integral_mono (rule.integrable_eval w s) (integrable_const (1:ℝ)) (fun _ => rule.le_one _ _)⟩
lemma response_sum (s : Ambient d) : ∑ w,rule.response w s=1 := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  unfold response
  rw [← integral_finsetSum _ (fun w _ => rule.integrable_eval w s)]
  simp only [rule.sum,integral_const,probReal_univ,one_smul]
noncomputable def positive (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) : PositiveRule k d N where
  prob := fun t w => (1-ε)*rule.prob t w+ε/(N:ℝ)
  measurable_prob := by
    apply measurable_from_prod_countable_left
    intro w
    exact ((rule.measurable w).const_mul _).add_const _
  sum_prob := by
    intro t
    rw [Finset.sum_add_distrib,← Finset.mul_sum,rule.sum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
    ring
  lower := ε/(N:ℝ)
  lower_pos := div_pos hε (by exact_mod_cast hN)
  lower_prob := fun t w => le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hε1) (rule.nonneg t w))
lemma positive_response (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (w : Fin N) (s : Ambient d) :
    (rule.positive hN ε hε hε1).exactResponse w s=(1-ε)*rule.response w s+ε/(N:ℝ) := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  change (∫ X,(1-ε)*rule.prob (X,projectVector X s) w+ε/(N:ℝ) ∂gaussianRows k d)=_
  rw [integral_add ((rule.integrable_eval w s).const_mul _) (integrable_const _),integral_const_mul]
  simp [response]
end LocalRule
end KernelPotential.NoisyDrift

end OAI
