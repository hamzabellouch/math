import OAI.Probability.FreeIsing.Ising.ObservationPosteriorMartingale
import OAI.Probability.FreeIsing.Ising.PosteriorL2Continuity
import OAI.Probability.FreeIsing.Martingales.RightContinuation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.IsingObservationInnovation
open IsingObservationRecovery

theorem posterior_tendsto_eLpNorm_one {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (t : ℝ≥0) :
    Tendsto (fun s : ℝ≥0 => eLpNorm (posterior beta v s - posterior beta v t)
      1 (observationLaw μ)) (𝓝 t) (𝓝 0) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (posterior_tendsto_eLpNorm_two hμ hd hb hcrit v t) (fun _ => bot_le)
  intro s
  exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)

theorem posterior_martingale_rightCont {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    Martingale (posterior beta v) (filtration d).rightCont (observationLaw μ) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  apply martingale_rightCont_of_L1_rightContinuous (posterior_martingale hμ v)
  intro t
  exact (posterior_tendsto_eLpNorm_one hμ hd hb hcrit v t).mono_left nhdsWithin_le_nhds

theorem posterior_eq_condExp_decodedSpin_rightCont {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (t : ℝ≥0) :
    posterior beta v t =ᵐ[observationLaw μ]
      (observationLaw μ)[fun x => spinSign (decode x v) | (filtration d).rightCont t] := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  apply condExp_rightCont_of_L1_rightContinuous (integrable_decodedSpin μ v)
    (posterior_progressive beta v).stronglyAdapted
    (fun s => posterior_eq_condExp_decodedSpin hμ v s) _ t
  intro s
  exact (posterior_tendsto_eLpNorm_one hμ hd hb hcrit v s).mono_left nhdsWithin_le_nhds

end Problem367.IsingObservationInnovation

end

end OAI
