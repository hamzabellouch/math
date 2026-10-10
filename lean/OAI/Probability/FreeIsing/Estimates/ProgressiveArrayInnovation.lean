import OAI.Probability.FreeIsing.Brownian.ArrayObservation
import OAI.Probability.FreeIsing.Estimates.ProgressivePrimitiveFubini

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem preBrownian_array_innovation_martingale_of_progressive_posterior
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t))
    {σ : S → ι → ℝ} (hσ : Measurable σ) (i : ι)
    {C : ℝ} (hσbound : ∀ᵐ s ∂ν, |σ s i| ≤ C)
    {m : ℝ≥0 → S × (ι → Ω) → ℝ}
    (hm : IsStronglyProgressive (arrayObservationFiltration B hmB σ hσ) m)
    (hposterior : ∀ t, m t =ᵐ[ν.prod (Measure.infinitePi μ)]
      (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => σ q.1 i) |
        arrayObservationFiltration B hmB σ hσ t]) :
    Martingale
      (fun t q => plantedArrayObservation B σ i t q - nnrealTimePrimitive m t q)
      (arrayObservationFiltration B hmB σ hσ) (ν.prod (Measure.infinitePi μ)) := by
  have (j : ι) : IsProbabilityMeasure (μ j) :=
    (hB j).isGaussianProcess.isProbabilityMeasure
  have hσint : Integrable (fun s => σ s i) ν :=
    (integrable_const C).mono'
      (((measurable_pi_apply i).comp hσ).aestronglyMeasurable)
      (by simpa only [Real.norm_eq_abs] using hσbound)
  have hbound : ∀ t, ∀ᵐ q ∂ν.prod (Measure.infinitePi μ), |m t q| ≤ C :=
    posterior_version_ae_abs_le hposterior
      (Measure.quasiMeasurePreserving_fst.ae hσbound)
  exact preBrownian_array_observation_innovation_martingale ν μ hB hmB hσ i hσint
    hm.stronglyAdapted hposterior
    (stronglyAdapted_nnrealTimePrimitive hm)
    (fun s t _ => integrable_nnreal_process_interval_of_progressive_bounded hm C hbound s t)

theorem ae_lipschitzWith_array_posterior_primitive
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    [∀ j, IsProbabilityMeasure (μ j)]
    {B : ι → ℝ≥0 → Ω → ℝ} (hmB : ∀ i t, Measurable (B i t))
    {σ : S → ι → ℝ} (hσ : Measurable σ) (i : ι)
    {C : ℝ≥0} (hσbound : ∀ᵐ s ∂ν, |σ s i| ≤ (C : ℝ))
    {m : ℝ≥0 → S × (ι → Ω) → ℝ}
    (hm : IsStronglyProgressive (arrayObservationFiltration B hmB σ hσ) m)
    (hposterior : ∀ t, m t =ᵐ[ν.prod (Measure.infinitePi μ)]
      (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => σ q.1 i) |
        arrayObservationFiltration B hmB σ hσ t]) :
    ∀ᵐ q ∂ν.prod (Measure.infinitePi μ),
      LipschitzWith C (fun t => nnrealTimePrimitive m t q) :=
  ae_lipschitzWith_nnrealTimePrimitive hm
    (posterior_version_ae_abs_le hposterior
      (Measure.quasiMeasurePreserving_fst.ae hσbound))

theorem brownian_array_innovation_regular_martingale
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t))
    {σ : S → ι → ℝ} (hσ : Measurable σ) (i : ι)
    {C : ℝ≥0} (hσbound : ∀ᵐ s ∂ν, |σ s i| ≤ (C : ℝ))
    {m : ℝ≥0 → S × (ι → Ω) → ℝ}
    (hm : IsStronglyProgressive (arrayObservationFiltration B hmB σ hσ) m)
    (hposterior : ∀ t, m t =ᵐ[ν.prod (Measure.infinitePi μ)]
      (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => σ q.1 i) |
        arrayObservationFiltration B hmB σ hσ t]) :
    Martingale
      (fun t q => plantedArrayObservation B σ i t q - nnrealTimePrimitive m t q)
      (arrayObservationFiltration B hmB σ hσ) (ν.prod (Measure.infinitePi μ)) ∧
    (∀ᵐ q ∂ν.prod (Measure.infinitePi μ),
      Continuous (fun t => plantedArrayObservation B σ i t q - nnrealTimePrimitive m t q)) ∧
    (∀ᵐ q ∂ν.prod (Measure.infinitePi μ),
      plantedArrayObservation B σ i 0 q - nnrealTimePrimitive m 0 q = 0) := by
  have (j : ι) : IsProbabilityMeasure (μ j) :=
    (hB j).toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  refine ⟨preBrownian_array_innovation_martingale_of_progressive_posterior
    ν μ (fun j => (hB j).toIsPreBrownianReal) hmB hσ i hσbound hm hposterior, ?_, ?_⟩
  · have hcont := (planted_noise_coordinate_measurePreserving ν μ i).quasiMeasurePreserving.ae
      (hB i).cont
    filter_upwards [hcont,
      ae_lipschitzWith_array_posterior_primitive ν μ hmB hσ i hσbound hm hposterior]
      with q hcontq hA
    change Continuous (fun t => B i t (q.2 i) + (t : ℝ) * σ q.1 i -
      nnrealTimePrimitive m t q)
    exact (hcontq.add (continuous_subtype_val.mul continuous_const)).sub hA.continuous
  · have hzero := (planted_noise_coordinate_measurePreserving ν μ i).quasiMeasurePreserving.ae
      (hB i).eval_zero_ae_eq_zero
    filter_upwards [hzero] with q hq
    simpa only [plantedArrayObservation, nnrealTimePrimitive, NNReal.coe_zero,
      zero_mul, add_zero, intervalIntegral.integral_same, sub_zero] using hq

end Problem367

end

end OAI
