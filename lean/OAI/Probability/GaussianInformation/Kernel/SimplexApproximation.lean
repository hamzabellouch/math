import Mathlib
import OAI.Probability.GaussianInformation.Kernel.EnergyBayes

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

lemma continuous_ae_approx {k d N : ℕ}
    (μ : Measure ((Mat k d) × (Fin k → ℝ))) [IsFiniteMeasure μ]
    (f : ((Mat k d) × (Fin k → ℝ)) → (Fin N → ℝ)) (hf : Integrable f μ) :
    ∃ g : ℕ → BoundedContinuousFunction ((Mat k d) × (Fin k → ℝ)) (Fin N → ℝ),
      ∀ᵐ t ∂μ,Tendsto (fun n => g n t) atTop (𝓝 (f t)) := by
  have he (n : ℕ) : ENNReal.ofReal (1/((n:ℝ)+1)) ≠ 0 := by positivity
  choose g hg _hgi using fun n => hf.exists_boundedContinuous_lintegral_sub_le (he n)
  have ht : Tendsto (fun n => eLpNorm ((g n : _ → _)-f) 1 μ) atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => ENNReal.ofReal (1/((n:ℝ)+1))) atTop (𝓝 0) := by
      simpa only [Function.comp_def,ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hp (fun _ => bot_le)
    intro n
    simpa only [eLpNorm_one_eq_lintegral_enorm
      ((g n).continuous.measurable.aestronglyMeasurable.sub hf.aestronglyMeasurable),
      Pi.sub_apply,enorm_sub_rev] using hg n
  obtain ⟨ns,_hns,hconv⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (p := (1:ℝ≥0∞)) (by norm_num)
    ht).exists_seq_tendsto_ae
  exact ⟨fun n => g (ns n),hconv⟩

end KernelPotential.NoisyDrift
namespace KernelPotential.NoisyDrift.Simplex
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
noncomputable def clip (ε : ℝ) (x : ℝ) : ℝ := max ε (min 1 x)
noncomputable def total {N : ℕ} (ε : ℝ) (x : Fin N → ℝ) : ℝ := ∑ w,clip ε (x w)
noncomputable def normalize {N : ℕ} (ε : ℝ) (x : Fin N → ℝ) (w : Fin N) : ℝ := clip ε (x w)/total ε x
lemma clip_lower (ε x : ℝ) : ε ≤ clip ε x := le_max_left _ _
lemma clip_upper {ε : ℝ} (hε : ε ≤ 1) (x : ℝ) : clip ε x ≤ 1 := max_le hε (min_le_left _ _)
lemma total_pos {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (x : Fin N → ℝ) : 0 < total ε x := by
  have h : (N:ℝ)*ε ≤ total ε x := by
    simpa [total] using Finset.sum_le_sum (s := Finset.univ) (fun w _ => clip_lower ε (x w))
  exact (mul_pos (by exact_mod_cast hN) hε).trans_le h
lemma total_upper {N : ℕ} {ε : ℝ} (hε : ε ≤ 1) (x : Fin N → ℝ) : total ε x ≤ (N:ℝ) := by
  simpa [total] using Finset.sum_le_sum (s := Finset.univ) (fun w _ => clip_upper hε (x w))
lemma normalize_lower {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x : Fin N → ℝ) (w : Fin N) :
    ε/(N:ℝ) ≤ normalize ε x w := by
  exact (div_le_div_of_nonneg_left hε.le (total_pos hN hε x) (total_upper hε1 x)).trans
    (div_le_div_of_nonneg_right (clip_lower ε (x w)) (total_pos hN hε x).le)
lemma normalize_sum {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) (x : Fin N → ℝ) :
    ∑ w,normalize ε x w=1 := by
  unfold normalize
  rw [← Finset.sum_div]
  exact div_self (total_pos hN hε x).ne'
lemma continuous_normalize {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) : Continuous (normalize (N := N) ε) := by
  have hc (w : Fin N) : Continuous (fun x : Fin N → ℝ => clip ε (x w)) := continuous_const.max (continuous_const.min (continuous_apply w))
  have ht : Continuous (fun x : Fin N → ℝ => total ε x) := continuous_finsetSum _ (fun w _ => hc w)
  exact continuous_pi (fun w => (hc w).div ht (fun x => (total_pos hN hε x).ne'))
lemma normalize_eq {N : ℕ} {ε : ℝ} (x : Fin N → ℝ) (hl : ∀ w,ε ≤ x w) (hu : ∀ w,x w ≤ 1) (hs : ∑ w,x w=1) :
    normalize ε x=x := by
  have he (w) : clip ε (x w)=x w := by rw [clip,min_eq_right (hu w),max_eq_right (hl w)]
  ext w
  simp only [normalize,total,he,hs,div_one]
end KernelPotential.NoisyDrift.Simplex

namespace KernelPotential.NoisyDrift.PositiveRule
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference
variable {k d N : ℕ} (rule : PositiveRule k d N)
lemma lower_le_one (hN : 0 < N) : rule.lower ≤ 1 :=
  (rule.lower_prob (0,0) ⟨0,hN⟩).trans (rule.le_one _ _)
lemma exists_continuous_approx (hN : 0 < N) (μ : Measure ((Mat k d) × (Fin k → ℝ))) [IsFiniteMeasure μ] :
    ∃ R : ℕ → PositiveRule k d N,
      (∀ n w,Continuous (fun t => (R n).prob t w)) ∧
      (∀ n,(R n).lower=rule.lower/(N:ℝ)) ∧
      (∀ᵐ t ∂μ,∀ w,Tendsto (fun n => (R n).prob t w) atTop (𝓝 (rule.prob t w))) := by
  have hm : Measurable rule.prob := Measurable.of_eval (fun message => rule.measurable message)
  have hi : Integrable rule.prob μ := by
    refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
    filter_upwards [] with t
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro w
    rw [Real.norm_eq_abs,abs_of_nonneg (rule.nonneg _ _)]
    exact rule.le_one _ _
  obtain ⟨g,hg⟩ := continuous_ae_approx μ rule.prob hi
  let R : ℕ → PositiveRule k d N := fun n => {
    prob := fun t => Simplex.normalize rule.lower (g n t)
    measurable_prob := by
      apply measurable_from_prod_countable_left
      intro w
      exact ((continuous_apply w).comp ((Simplex.continuous_normalize hN rule.lower_pos).comp (g n).continuous)).measurable
    sum_prob := fun _ => Simplex.normalize_sum hN rule.lower_pos _
    lower := rule.lower/(N:ℝ)
    lower_pos := div_pos rule.lower_pos (by exact_mod_cast hN)
    lower_prob := fun _ _ => Simplex.normalize_lower hN rule.lower_pos (rule.lower_le_one hN) _ _ }
  refine ⟨R,?_,fun _ => rfl,?_⟩
  · intro n w
    exact (continuous_apply w).comp ((Simplex.continuous_normalize hN rule.lower_pos).comp (g n).continuous)
  · filter_upwards [hg] with t ht
    have hh := ((Simplex.continuous_normalize hN rule.lower_pos).tendsto _).comp ht
    rw [Simplex.normalize_eq _ (rule.lower_prob t) (rule.le_one t) (rule.sum_prob t)] at hh
    intro w
    exact (continuous_apply w).tendsto _ |>.comp hh
end KernelPotential.NoisyDrift.PositiveRule

end OAI
