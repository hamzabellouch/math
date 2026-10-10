import OAI.Probability.FreeIsing.Ising.CanonicalContinuousFields

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

theorem ae_horizon_stopped_continuousDifference_bound
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (τ : IsingConditionalCopyBounds.CopySpace d → WithTop ℝ≥0)
    (T : ℝ≥0) :
    ∀ᵐ q ∂copies beta μ, ∀ t ≤ T,
      |stoppedProcess (continuousDifference beta v) τ t q| ≤
        2 * (T : ℝ) + 2 * (d : ℝ) * beta := by
  obtain ⟨hc, he⟩ := continuousDifference_modification hd hμ hb hcrit v
  filter_upwards [ae_horizon_field_difference_version_bound hμ hb v hc he T] with q hq
  intro t ht
  exact hq _ ((WithTop.untopA_le (min_le_left (t : WithTop ℝ≥0) (τ q))).trans ht)

theorem ae_stopped_representation_bound
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (τ : IsingConditionalCopyBounds.CopySpace d → WithTop ℝ≥0)
    {M b : ℝ≥0 → IsingConditionalCopyBounds.CopySpace d → ℝ}
    (hrep : ∀ t, (fun q => M t q + nnrealTimePrimitive b t q) =ᵐ[copies beta μ]
      stoppedProcess (continuousDifference beta v) τ t)
    (T t : ℝ≥0) (ht : t ≤ T) :
    ∀ᵐ q ∂copies beta μ, |M t q + nnrealTimePrimitive b t q| ≤
      2 * (T : ℝ) + 2 * (d : ℝ) * beta := by
  filter_upwards [hrep t, ae_horizon_stopped_continuousDifference_bound
    hd hμ hb hcrit v τ T] with q hq hbq
  rw [hq]
  exact hbq t ht

end Problem367.IsingObservationFactor

end

end OAI
