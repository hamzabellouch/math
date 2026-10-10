import OAI.Probability.FreeIsing.Ising.CopyVarianceContinuity
import OAI.Probability.FreeIsing.Ising.PosteriorL2Continuity

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

theorem continuous_field_difference_energy
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    Continuous (fun t : ℝ≥0 => ∫ q,
      (field beta v t q.2.1 - field beta v t q.2.2) ^ 2 ∂copies beta μ) :=
  continuous_field_difference_energy_of_posterior_meanSquare hμ hb v
    (posterior_tendsto_meanSquare hμ hd hb hcrit v)

theorem continuous_field_difference_energy_real
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) (v : TreeVertex d) :
    Continuous (fun t : ℝ => ∫ q,
      (field beta v t.toNNReal q.2.1 - field beta v t.toNNReal q.2.2) ^ 2
        ∂copies beta μ) :=
  (continuous_field_difference_energy hμ hd hb hcrit v).comp continuous_real_toNNReal

end Problem367.IsingObservationFactor

end

end OAI
