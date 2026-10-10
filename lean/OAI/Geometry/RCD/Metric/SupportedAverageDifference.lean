import OAI.Geometry.RCD.Metric.AverageMassEnvelope

namespace OAI

/-! # Kernel differences need control only on the fixed cutoff support -/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] [IsLocallyFiniteMeasure μ] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {χ : X → ℝ} (hχ : Continuous χ) (hsχ : HasCompactSupport χ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- An all-pole kernel bound on the cutoff support suffices for the full
positive source measure. No volume bounds are required away from that support. -/
theorem cutoffAverageHeatMass_difference_le_supported
    (M : PositiveBilinearMeasure X E) (hχpos : ∀ z, 0 ≤ χ z)
    {t : ℝ} (ht : 0 < t) (s : Set X) (hs : MeasurableSet s)
    (hbounded : Bornology.IsBounded s) (x : X) (B : X → ℝ) (hB : Continuous B)
    (hbound : ∀ z, χ z ≠ 0 → |kernelAverage μ ker t s z - ker t x z| ≤ B z)
    (v : E) :
    |⟪v, (cutoffAverageHeatMass μ hQ hk hχ hsχ M ht s hs hbounded -
      cutoffHeatMass μ hQ hk hχ hsχ M ht x) v⟫_ℝ| ≤
        ∫ z, χ z * B z ∂(M.measure v) := by
  have hia := (hχ.mul (kernelAverage_continuous μ hQ hk ht hs hbounded)).integrable_of_hasCompactSupport
    (μ := M.measure v) hsχ.mul_right
  have hip := (hχ.mul (hk.continuous_right t ht x)).integrable_of_hasCompactSupport
    (μ := M.measure v) hsχ.mul_right
  have hib := (hχ.mul hB).integrable_of_hasCompactSupport (μ := M.measure v) hsχ.mul_right
  change Integrable (fun z => χ z * kernelAverage μ ker t s z) (M.measure v) at hia
  change Integrable (fun z => χ z * ker t x z) (M.measure v) at hip
  change Integrable (fun z => χ z * B z) (M.measure v) at hib
  simp only [sub_apply, inner_sub_right, cutoffAverageHeatMass_integral,
    cutoffHeatMass_energy]
  rw [← integral_sub hia hip]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono ((hia.sub hip).abs) hib
  intro z
  change |χ z * kernelAverage μ ker t s z - χ z * ker t x z| ≤ χ z * B z
  by_cases hz : χ z = 0
  · simpa only [hz, zero_mul, sub_self, abs_zero] using (le_refl (0 : ℝ))
  · rw [← mul_sub, abs_mul, abs_of_nonneg (hχpos z)]
    exact mul_le_mul_of_nonneg_left (hbound z hz) (hχpos z)

end RegularPointCoordinates

end

end OAI
