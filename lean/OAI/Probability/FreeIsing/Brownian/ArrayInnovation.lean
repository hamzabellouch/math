import OAI.Probability.FreeIsing.Brownian.ArrayMoments
import OAI.Probability.FreeIsing.Brownian.Innovation
import OAI.Probability.FreeIsing.Estimates.ProgressiveArrayInnovation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem ae_array_innovation_increment_drift_bound
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
        arrayObservationFiltration B hmB σ hσ t])
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∀ᵐ q ∂ν.prod (Measure.infinitePi μ),
      |((plantedArrayObservation B σ i t q - nnrealTimePrimitive m t q) -
          (plantedArrayObservation B σ i s q - nnrealTimePrimitive m s q)) -
        (B i t (q.2 i) - B i s (q.2 i))| ≤
        (2 * (C : ℝ)) * ((t : ℝ) - (s : ℝ)) := by
  have hsignal : ∀ᵐ q ∂ν.prod (Measure.infinitePi μ), |σ q.1 i| ≤ (C : ℝ) :=
    Measure.quasiMeasurePreserving_fst.ae hσbound
  filter_upwards [hsignal,
    ae_lipschitzWith_array_posterior_primitive ν μ hmB hσ i hσbound hm hposterior]
    with q hsq hlip
  have htime : 0 ≤ (t : ℝ) - (s : ℝ) := sub_nonneg.mpr hst
  have hprim : |nnrealTimePrimitive m t q - nnrealTimePrimitive m s q| ≤
      (C : ℝ) * ((t : ℝ) - (s : ℝ)) := by
    simpa only [Real.dist_eq, NNReal.dist_eq, abs_of_nonneg htime] using
      hlip.dist_le_mul t s
  have heq : ((plantedArrayObservation B σ i t q - nnrealTimePrimitive m t q) -
      (plantedArrayObservation B σ i s q - nnrealTimePrimitive m s q)) -
      (B i t (q.2 i) - B i s (q.2 i)) =
      ((t : ℝ) - (s : ℝ)) * σ q.1 i -
        (nnrealTimePrimitive m t q - nnrealTimePrimitive m s q) := by
    unfold plantedArrayObservation
    ring
  rw [heq]
  calc
    _ ≤ |((t : ℝ) - (s : ℝ)) * σ q.1 i| +
        |nnrealTimePrimitive m t q - nnrealTimePrimitive m s q| := abs_sub _ _
    _ ≤ ((t : ℝ) - (s : ℝ)) * (C : ℝ) +
        (C : ℝ) * ((t : ℝ) - (s : ℝ)) := by
      rw [abs_mul, abs_of_nonneg htime]
      exact add_le_add (mul_le_mul_of_nonneg_left hsq htime) hprim
    _ = _ := by ring

theorem preBrownian_array_innovation_of_progressive_posterior
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t))
    {σ : S → ι → ℝ} (hσ : Measurable σ) (i : ι)
    {C : ℝ≥0} (hσbound : ∀ᵐ s ∂ν, |σ s i| ≤ (C : ℝ))
    {m : ℝ≥0 → S × (ι → Ω) → ℝ}
    (hm : IsStronglyProgressive (arrayObservationFiltration B hmB σ hσ) m)
    (hposterior : ∀ t, m t =ᵐ[ν.prod (Measure.infinitePi μ)]
      (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => σ q.1 i) |
        arrayObservationFiltration B hmB σ hσ t]) :
    IsPreBrownianReal
      (fun t q => plantedArrayObservation B σ i t q - nnrealTimePrimitive m t q)
      (ν.prod (Measure.infinitePi μ)) := by
  classical
  have (j : ι) : IsProbabilityMeasure (μ j) :=
    (hB j).isGaussianProcess.isProbabilityMeasure
  apply BrownianInnovation.isPreBrownianReal_of_bounded_drift
    (planted_coordinate_preBrownian ν μ hB i)
    (preBrownian_array_innovation_martingale_of_progressive_posterior
      ν μ hB hmB hσ i hσbound hm hposterior)
    (L := 2 * (C : ℝ))
  · intro s t hst
    have hv := planted_weighted_increment_sq_condExp_subfield ν μ hB hmB hst
      ({i} : Finset ι) (fun _ => (1 : ℝ))
      (arrayObservationFiltration_le_signalArrayFiltration B hmB σ hσ s)
    simpa using hv
  · positivity
  · intro s t hst
    exact ae_array_innovation_increment_drift_bound ν μ hmB hσ i hσbound hm hposterior hst
  · have hzero := (planted_noise_coordinate_measurePreserving ν μ i).quasiMeasurePreserving.ae
      (hB i).eval_zero_ae_eq_zero
    filter_upwards [hzero] with q hq
    simpa only [plantedArrayObservation, nnrealTimePrimitive, NNReal.coe_zero,
      zero_mul, add_zero, intervalIntegral.integral_same, sub_zero] using hq

theorem brownian_array_innovation_of_progressive_posterior
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
    IsBrownianReal
      (fun t q => plantedArrayObservation B σ i t q - nnrealTimePrimitive m t q)
      (ν.prod (Measure.infinitePi μ)) :=
  ⟨preBrownian_array_innovation_of_progressive_posterior
      ν μ (fun j => (hB j).toIsPreBrownianReal) hmB hσ i hσbound hm hposterior,
    (brownian_array_innovation_regular_martingale ν μ hB hmB hσ i hσbound hm hposterior).2.1⟩

end Problem367

end

end OAI
