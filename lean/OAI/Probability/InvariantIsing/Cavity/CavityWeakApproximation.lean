import OAI.Probability.InvariantIsing.Cavity.CavitySoftCutoff

namespace OAI

/-! Bounded measurable tests can be passed through a weak limit when
continuous error envelopes have vanishing integral in the limiting law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_continuous_approximation_error {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ProbabilityMeasure E) (f : E → ℝ) (hf : Measurable f)
    {C : ℝ} (hb : ∀ x, |f x| ≤ C) (F G : E →ᵇ ℝ)
    (herror : ∀ x, |f x-F x| ≤ G x) :
    |(∫ x, f x ∂(μ : Measure E)) - ∫ x, F x ∂(μ : Measure E)| ≤
      ∫ x, G x ∂(μ : Measure E) := by
  have hfi : Integrable f (μ : Measure E) := Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x))
  have hF : Integrable (fun x => F x) (μ : Measure E) := F.integrable (μ := (μ : Measure E))
  have hG : Integrable (fun x => G x) (μ : Measure E) := G.integrable (μ := (μ : Measure E))
  rw [← integral_sub hfi hF]
  exact (abs_integral_le_integral_abs).trans
    (integral_mono (hfi.sub hF).abs hG herror)

theorem cavity_weak_integral_of_continuous_approximation {E : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (μ : ℕ → ProbabilityMeasure E) (ν : ProbabilityMeasure E)
    (hμ : Tendsto μ atTop (𝓝 ν))
    (f : E → ℝ) (hf : Measurable f) {C : ℝ} (hb : ∀ x, |f x| ≤ C)
    (F G : ℕ → E →ᵇ ℝ) (herror : ∀ j x, |f x-F j x| ≤ G j x)
    (hG : Tendsto (fun j => ∫ x, G j x ∂(ν : Measure E)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f x ∂(μ n : Measure E)) atTop
      (𝓝 (∫ x, f x ∂(ν : Measure E))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j,hj⟩ := (hG.eventually (gt_mem_nhds (show (0 : ℝ) < ε/8 by positivity))).exists
  have hFj := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ (F j)
  have hGj := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ (G j)
  have hFclose := hFj.eventually (Metric.ball_mem_nhds
    (∫ x, F j x ∂(ν : Measure E)) (show 0 < ε/4 by positivity))
  have hGclose := hGj.eventually (Metric.ball_mem_nhds
    (∫ x, G j x ∂(ν : Measure E)) (show 0 < ε/4 by positivity))
  filter_upwards [hFclose,hGclose] with n hnF hnG
  rw [Real.dist_eq] at hnF hnG ⊢
  have heμ := cavity_continuous_approximation_error (μ n) f hf hb (F j) (G j) (herror j)
  have heν := cavity_continuous_approximation_error ν f hf hb (F j) (G j) (herror j)
  have htri := abs_sub_le
    (∫ x, f x ∂(μ n : Measure E)) (∫ x, F j x ∂(μ n : Measure E))
    (∫ x, f x ∂(ν : Measure E))
  have htri' := abs_sub_le
    (∫ x, F j x ∂(μ n : Measure E)) (∫ x, F j x ∂(ν : Measure E))
    (∫ x, f x ∂(ν : Measure E))
  rw [abs_sub_comm (∫ x, F j x ∂(ν : Measure E))] at htri'
  linarith [(abs_le.mp (le_of_lt hnG)).2]

end InvariantIsing

end

end OAI
