import OAI.Probability.FreeIsing.Brownian.ArrayMoments
import OAI.Probability.FreeIsing.Stochastic.StoppedBrownianArraySquare

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.PlantedStoppedBrownianSquare
open StoppedSimpleIntegral StoppedBrownianArraySquare

theorem planted_grid_square_martingale
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ j, IsPreBrownianReal (B j) (μ j))
    (hmB : ∀ j t, Measurable (B j t))
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (H : ι → ℕ → S × (ι → Ω) → ℝ)
    (hH : ∀ j i, StronglyMeasurable[signalArrayFiltration B hmB (τ i)] (H j i))
    (K : ι → ℕ → ℝ)
    (hbound : ∀ j i, ∀ᵐ q ∂ν.prod (Measure.infinitePi μ), ‖H j i q‖ ≤ K j i)
    (I : Finset ι) (n : ℕ) :
    Martingale (fun t q =>
      (∑ j ∈ I, ∑ i ∈ Finset.range n,
        intervalSum (fun u q => B j u (q.2 j)) (H j i) (τ i) (τ (i + 1)) t q) ^ 2 -
      ∑ j ∈ I, ∑ i ∈ Finset.range n,
        H j i q ^ 2 * ((min t (τ (i + 1)) : ℝ) - (min t (τ i) : ℝ)))
      (signalArrayFiltration B hmB) (ν.prod (Measure.infinitePi μ)) := by
  have (j : ι) : IsProbabilityMeasure (μ j) :=
    (hB j).isGaussianProcess.isProbabilityMeasure
  apply stopped_brownian_array_square_martingale
    (fun j t q => B j t (q.2 j))
    (fun j => planted_coordinate_preBrownian ν μ hB j)
    (fun j => (preBrownian_martingale_signalArrayFiltration ν μ hB hmB j).stronglyAdapted)
    ?_ ?_ τ hτ H hH K hbound I n
  · intro s t hst
    rw [signalArrayFiltration_eq_comap B hmB s]
    exact planted_array_increments_indep_signal_past ν μ hB hmB hst
  · intro s t _hst j k hjk
    exact planted_coordinate_increments_indep ν μ hB hmB s t hjk

end Problem367.PlantedStoppedBrownianSquare

end

end OAI
