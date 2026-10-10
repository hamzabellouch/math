import OAI.Probability.FreeIsing.Estimates.CompensatedSquareLimit
import OAI.Probability.FreeIsing.Ising.ObservationPosteriorTransport
import OAI.Probability.FreeIsing.Posterior.TimeL2Continuity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.IsingObservationInnovation

theorem posterior_secondMoment_continuous {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    Continuous (fun t : ℝ≥0 => ∫ x, posterior beta v t x ^ 2 ∂observationLaw μ) := by
  have h := hμ.infiniteGibbsSpinMean_brownian_secondMoment_continuous hd hb hcrit
    (fun _ : TreeVertex d => uniform01)
    (fun _ => WienerSampler.sample_isBrownianReal.toIsPreBrownianReal)
    (fun _ t => (continuous_eval_const t).measurable.comp WienerSampler.measurable_sample)
    (fun _ u => (WienerSampler.sample u).continuous) v
  apply h.congr
  intro t
  exact (integral_posterior_pair_eq_uniform beta μ v v t t
    (measurable_fst.pow_const 2)).symm

theorem posterior_tendsto_meanSquare {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (t : ℝ≥0) :
    Tendsto (fun s : ℝ≥0 => ∫ x,
      (posterior beta v s x - posterior beta v t x) ^ 2 ∂observationLaw μ)
      (𝓝 t) (𝓝 0) := by
  simp_rw [integral_posterior_sub_sq_eq_uniform beta μ v]
  exact hμ.infiniteGibbsSpinMean_brownian_tendsto_meanSquare hd hb hcrit
    (fun _ : TreeVertex d => uniform01)
    (fun _ => WienerSampler.sample_isBrownianReal.toIsPreBrownianReal)
    (fun _ s => (continuous_eval_const s).measurable.comp WienerSampler.measurable_sample)
    (fun _ u => (WienerSampler.sample u).continuous) v t

theorem posterior_tendsto_eLpNorm_two {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (t : ℝ≥0) :
    Tendsto (fun s : ℝ≥0 => eLpNorm (posterior beta v s - posterior beta v t)
      2 (observationLaw μ)) (𝓝 t) (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  exact CompensatedSquareLimit.tendsto_eLpNorm_two_of_meanSquare
    (fun s => posterior_memLp beta μ v s 2) (posterior_memLp beta μ v t 2)
    (posterior_tendsto_meanSquare hμ hd hb hcrit v t)

theorem posterior_tendstoInMeasure {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (t : ℝ≥0) :
    TendstoInMeasure (observationLaw μ) (posterior beta v) (𝓝 t) (posterior beta v t) := by
  exact tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (posterior_tendsto_eLpNorm_two hμ hd hb hcrit v t)

end Problem367.IsingObservationInnovation

end

end OAI
