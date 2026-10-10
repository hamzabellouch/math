import OAI.Probability.FreeIsing.Posterior.FilteringCrossLimit
import OAI.Probability.FreeIsing.Posterior.ProgressiveIsingPosterior

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

theorem stronglyMeasurable_latent_signalArrayFiltration
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (hmB : ∀ i t, Measurable (B i t))
    {Q : S → ℝ} (hQ : Measurable Q) (t : ℝ≥0) :
    StronglyMeasurable[signalArrayFiltration B hmB t]
      (fun q : S × (ι → Ω) => Q q.1) := by
  have hm : StronglyMeasurable[MeasurableSpace.comap
      (Prod.fst : S × (ι → Ω) → S) inferInstance] (fun q => Q q.1) :=
    (hQ.comp (comap_measurable Prod.fst)).stronglyMeasurable
  exact hm.mono le_sup_left

theorem planted_array_posterior_uniformSum_cross_energy
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t))
    {σ : S → ι → ℝ} (hσ : Measurable σ) (i : ι)
    {Q : S → ℝ} (hQ : Measurable Q) {A C D : ℝ}
    (hQb : ∀ᵐ q ∂ν, |Q q| ≤ D)
    (hσint : Integrable (fun q => σ q i) ν)
    (hσb : ∀ᵐ q ∂ν, |σ q i| ≤ C)
    {m K : ℝ≥0 → S × (ι → Ω) → ℝ}
    (hm : IsStronglyProgressive (arrayObservationFiltration B hmB σ hσ) m)
    (hpost : ∀ r, m r =ᵐ[ν.prod (Measure.infinitePi μ)]
      (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => σ q.1 i) |
        arrayObservationFiltration B hmB σ hσ r])
    (hK : StronglyAdapted (arrayObservationFiltration B hmB σ hσ) K)
    (hKc : ∀ᵐ q ∂ν.prod (Measure.infinitePi μ), Continuous (fun r => K r q))
    (hA : 0 ≤ A)
    (hKb : ∀ᵐ q ∂ν.prod (Measure.infinitePi μ), ∀ r, |K r q| ≤ A)
    (hKversion : ∀ r, K r =ᵐ[ν.prod (Measure.infinitePi μ)] fun q =>
      (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => Q q.1 * σ q.1 i) |
        arrayObservationFiltration B hmB σ hσ r] q -
      (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => Q q.1) |
        arrayObservationFiltration B hmB σ hσ r] q * m r q)
    (T : ℝ≥0) :
    Tendsto (fun n : ℕ => ∫ q,
      (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => Q q.1) |
        arrayObservationFiltration B hmB σ hσ T] q *
      BrownianGrid.uniformSum
        (fun t q => plantedArrayObservation B σ i t q - nnrealTimePrimitive m t q)
        K T n q ∂ν.prod (Measure.infinitePi μ)) atTop
      (𝓝 (∫ r in (0 : ℝ)..(T : ℝ),
        ∫ q, K r.toNNReal q ^ 2 ∂ν.prod (Measure.infinitePi μ))) := by
  have (index : ι) : IsProbabilityMeasure (μ index) :=
    (hB index).isGaussianProcess.isProbabilityMeasure
  exact FilteringCrossEnergy.tendsto_posterior_uniformSum_cross_energy
    (preBrownian_martingale_signalArrayFiltration ν μ hB hmB i)
    (arrayObservationFiltration_le_signalArrayFiltration B hmB σ hσ)
    (stronglyMeasurable_latent_signalArrayFiltration B hmB hQ 0)
    (Measure.quasiMeasurePreserving_fst.ae hQb)
    (hσint.comp_fst (Measure.infinitePi μ))
    (Measure.quasiMeasurePreserving_fst.ae hσb)
    (arrayNaturalFiltration_stronglyAdapted (plantedArrayObservation B σ)
      (plantedArrayObservation_measurable hmB hσ) i)
    hm hpost hK hKc hA hKb hKversion T

end Problem367

end

end OAI
