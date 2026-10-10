import OAI.Probability.FreeIsing.Energy.DiscrepancyRowEnergy

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.DiscrepancyEnergy

theorem hasSum_intervalIntegral_sq_row
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {μ : Measure Ω} [SFinite μ] {c : ι → ℝ≥0 → Ω → ℝ}
    (T : ℝ≥0)
    (hc : ∀ i, AEStronglyMeasurable
      (fun p : ℝ × Ω => c i p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod μ))
    (hs : ∀ᵐ p ∂(volume.restrict (Ioc (0 : ℝ) T)).prod μ,
      Summable (fun i => c i p.1.toNNReal p.2 ^ 2))
    (hA : Integrable (fun p : ℝ × Ω => ∑' i, c i p.1.toNNReal p.2 ^ 2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod μ)) :
    HasSum (fun i => ∫ t in (0 : ℝ)..(T : ℝ),
      ∫ ω, c i t.toNNReal ω ^ 2 ∂μ)
      (∫ p : ℝ × Ω, ∑' i, c i p.1.toNNReal p.2 ^ 2
        ∂(volume.restrict (Ioc (0 : ℝ) T)).prod μ) := by
  have hi (i : ι) : Integrable (fun p : ℝ × Ω => c i p.1.toNNReal p.2 ^ 2)
      ((volume.restrict (Ioc (0 : ℝ) T)).prod μ) := by
    apply hA.mono' ((hc i).pow 2)
    filter_upwards [hs] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hp.le_tsum i (fun j _ => sq_nonneg _)
  have he (i : ι) :
      (∫ p : ℝ × Ω, c i p.1.toNNReal p.2 ^ 2
        ∂(volume.restrict (Ioc (0 : ℝ) T)).prod μ) =
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, c i t.toNNReal ω ^ 2 ∂μ := by
    rw [integral_prod _ (hi i), intervalIntegral.integral_of_le T.coe_nonneg]
  simpa only [he] using hasSum_integral_sq_row hc hs hA

end Problem367.DiscrepancyEnergy

end

end OAI
