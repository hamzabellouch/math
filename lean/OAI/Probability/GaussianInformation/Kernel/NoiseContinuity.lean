import Mathlib
import OAI.Probability.GaussianInformation.Kernel.PositiveRules

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal

namespace KernelPotential.Noise
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open Projection Projection.Support GaussianTools ReferenceGaussian

lemma noise_norm_le {k : ℕ} {η : ℝ} (hη : 0 ≤ η) :
    ∀ᵐ e ∂noiseLaw k η, ‖e‖ ≤ η := by
  filter_upwards [noise_support k η] with e he
  apply (pi_norm_le_iff_of_nonneg hη).mpr
  intro i
  simpa [closedBox,Real.norm_eq_abs] using he i

lemma tendsto_noise_average {k : ℕ} (φ : (Fin k → ℝ) → ℝ) (hφ : Continuous φ)
    (hφ0 : ∀ e,0 ≤ φ e) (hφ1 : ∀ e,φ e ≤ 1) (y : Fin k → ℝ)
    (η : ℕ → ℝ) (hη : ∀ n,0 < η n) (hlim : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun n => ∫ e,φ (y+e) ∂noiseLaw k (η n)) atTop (𝓝 (φ y)) := by
  have hi (n) : Integrable (fun e => φ (y+e)) (noiseLaw k (η n)) := by
    have := noise_probability k (hη n)
    refine Integrable.of_bound (hφ.comp (continuous_const.add continuous_id)).measurable.aestronglyMeasurable 1 ?_
    filter_upwards [] with e
    rw [Real.norm_eq_abs,abs_of_nonneg (hφ0 _)]
    exact hφ1 _
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hh⟩ := Metric.continuousAt_iff.mp (hφ.continuousAt (x := y)) (ε/2) (half_pos hε)
  filter_upwards [hlim.eventually (eventually_lt_nhds hδ)] with n hn
  have := noise_probability k (hη n)
  have hb : ∀ᵐ e ∂noiseLaw k (η n),‖φ (y+e)-φ y‖ ≤ ε/2 := by
    filter_upwards [noise_norm_le (hη n).le] with e he
    have hdist : dist (y+e) y < δ := by
      simpa only [dist_eq_norm,add_sub_cancel_left] using he.trans_lt hn
    simpa only [dist_eq_norm] using (hh hdist).le
  have hb' := norm_integral_le_of_norm_le_const hb
  rw [integral_sub (hi n) (integrable_const _)] at hb'
  simp only [integral_const,probReal_univ,one_smul,mul_one] at hb'
  rw [dist_eq_norm]
  exact hb'.trans_lt (half_lt_self hε)

end KernelPotential.Noise
namespace KernelPotential.NoisyDrift.PositiveRule
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open Projection Projection.Support GaussianTools ReferenceGaussian Noise Bayes DriftTools.FiniteReference
variable {k d N : ℕ} (rule : PositiveRule k d N)
noncomputable def exactResponse (w : Fin N) (s : Ambient d) : ℝ :=
  ∫ X,rule.prob (X,projectVector X s) w ∂gaussianRows k d
lemma measurable_exactResponse (w : Fin N) : Measurable (rule.exactResponse w) := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have hm : Measurable (fun t : Ambient d × Mat k d => rule.prob (t.2,projectVector t.2 t.1) w) := by
    apply (rule.measurable w).comp
    exact measurable_snd.prodMk ((continuous_projectVector.comp (continuous_snd.prodMk continuous_fst)).measurable)
  exact hm.stronglyMeasurable.integral_prod_right.measurable
lemma exactResponse_bounds (w : Fin N) (s : Ambient d) :
    rule.lower ≤ rule.exactResponse w s ∧ rule.exactResponse w s ≤ 1 := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have hi : Integrable (fun X => rule.prob (X,projectVector X s) w) (gaussianRows k d) := by
    refine Integrable.of_bound ((rule.measurable w).comp (measurable_id.prodMk ((continuous_projectVector.comp (continuous_id.prodMk continuous_const)).measurable))).aestronglyMeasurable 1 ?_
    filter_upwards [] with X
    rw [Real.norm_eq_abs,abs_of_nonneg (rule.nonneg _ _)]
    exact rule.le_one _ _
  constructor
  · have h := integral_mono (integrable_const rule.lower) hi (fun X => rule.lower_prob _ w)
    simpa [exactResponse] using h
  · have h := integral_mono hi (integrable_const (1:ℝ)) (fun X => rule.le_one _ w)
    simpa [exactResponse] using h
lemma tendsto_response (hc : ∀ w,Continuous (fun t => rule.prob t w)) (w : Fin N) (s : Ambient d)
    (η : ℕ → ℝ) (hη : ∀ n,0 < η n) (hlim : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun n => rule.response (η n) w s) atTop (𝓝 (rule.exactResponse w s)) := by
  have : IsProbabilityMeasure (gaussianRows k d) := by unfold gaussianRows; infer_instance
  have he (n) : rule.response (η n) w s = ∫ X,∫ e,rule.prob (X,projectVector X s+e) w ∂noiseLaw k (η n) ∂gaussianRows k d :=
    likelihood_first (hη n) _ (rule.measurable w) (fun t => rule.nonneg t w) (fun t => rule.le_one t w) s
  simp_rw [he]
  apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
    (fun n => (noiseAverage_measurable (hη n) _ (rule.measurable w) s).aestronglyMeasurable)
    (integrable_const 1)
  · intro n
    have := noise_probability k (hη n)
    filter_upwards [] with X
    have hb := norm_integral_le_of_norm_le_const (μ := noiseLaw k (η n)) (f := fun e => rule.prob (X,projectVector X s+e) w)
      (ae_of_all _ (fun e => by rw [Real.norm_eq_abs,abs_of_nonneg (rule.nonneg _ _)]; exact rule.le_one _ _))
    simpa using hb
  · filter_upwards [] with X
    exact tendsto_noise_average _ ((hc w).comp (continuous_const.prodMk continuous_id))
      (fun e => rule.nonneg _ _) (fun e => rule.le_one _ _) _ η hη hlim
end KernelPotential.NoisyDrift.PositiveRule

end OAI
