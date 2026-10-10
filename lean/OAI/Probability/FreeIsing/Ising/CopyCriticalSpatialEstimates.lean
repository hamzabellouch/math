import OAI.Probability.FreeIsing.Ising.CopyCriticalSpatialBounds
import OAI.Probability.FreeIsing.Ising.CopyNoiseLongBound

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal
namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationFactor IsingCopySmallLogLoss IsingCriticalSmallLogLoss ConnectedHull

theorem exists_critical_spatial_endpoint_bounds
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1) (T : ℝ≥0) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (t : ℝ≥0), 0 < t → t ≤ T →
      ∀ (u w : TreeVertex d), treeAdj u w → 0 < siteVariance beta μ (root d) t →
      CriticalSpatialEndpointBounds
        (∫ z, IsingCopyEnergy.density beta (root d) t z ∂copies beta μ)
        (∑' n, noiseShellEnergy (μ := μ) hb t n)
        (∑' n, linearShellEnergy (μ := μ) hb t n)
        (∑' n, Real.sqrt (noiseShellEnergy (μ := μ) hb t n))
        (logVariance hb μ u w t) (siteVariance beta μ (root d) t)
        M (varianceScale d beta T) (min (Real.sqrt (t : ℝ)) 1) := by
  obtain ⟨B, E, c, a, q, C₀, hB, hE, hc, ha, hq, _, hnoise⟩ :=
    exists_noise_energy_long_constants hμ hd hb hcritical T
  exact exists_actual_spatial_endpoint_of_noise_bound hμ hd hb hcritical T
    hB hE hc ha hq hnoise

end Problem367.IsingCopyResponseRowPaths

end

end OAI
