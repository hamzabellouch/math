import OAI.Probability.FreeIsing.Estimates.ArrayInnovationProjection
import OAI.Probability.FreeIsing.Gaussian.ArrayCharacterization
import OAI.Probability.FreeIsing.Stochastic.WienerSampler

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
open Problem367.ConditionalCharacteristic

namespace Problem367.ArrayInnovationLaw

variable {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
  (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
  {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
  (hmB : ∀ i t, Measurable (B i t))
  {σ : S → ι → ℝ} (hσ : Measurable σ)
  {C : ℝ≥0} (hσbound : ∀ i, ∀ᵐ s ∂ν, |σ s i| ≤ (C : ℝ))
  {m : ι → ℝ≥0 → S × (ι → Ω) → ℝ}
  (hm : ∀ i, IsStronglyProgressive (arrayObservationFiltration B hmB σ hσ) (m i))
  (hposterior : ∀ i t, m i t =ᵐ[ν.prod (Measure.infinitePi μ)]
    (ν.prod (Measure.infinitePi μ))[(fun q : S × (ι → Ω) => σ q.1 i) |
      arrayObservationFiltration B hmB σ hσ t])

include hB hmB hσ hσbound hm hposterior

theorem conditional_weighted_character
    (I : Finset ι) (s t : ℝ≥0) (hst : s ≤ t) (a : I → ℝ) :
    (ν.prod (Measure.infinitePi μ))[character (fun q => ∑ i : I, a i *
      ((plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q) -
        (plantedArrayObservation B σ i s q - nnrealTimePrimitive (m i) s q))) 1 |
          arrayObservationFiltration B hmB σ hσ s] =ᵐ[ν.prod (Measure.infinitePi μ)]
      fun _ => Complex.exp (-(∑ i : I, (((t - s : ℝ≥0) : ℝ) : ℂ) * (a i : ℂ)^2) / 2) := by
  classical
  have (i : ι) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  apply ConditionalGaussianVector.condExp_weighted_character_of_unit_character
    ((arrayObservationFiltration B hmB σ hσ).le s) (t - s) _ a
  intro b hb u
  let c : ι → ℝ := fun i => if hi : i ∈ I then b ⟨i, hi⟩ else 0
  have hc (i : I) : c i = b i := by simp [c, i.property]
  have hcs : ∑ i ∈ I, c i ^ 2 = 1 := by
    rw [← Finset.sum_coe_sort I]
    simpa only [hc] using hb
  have h := array_innovation_unit_projection_condExp_character
    ν μ hB hmB hσ hσbound hm hposterior I c hcs hst u
  have heq : (fun q => ∑ i ∈ I, c i *
      ((plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q) -
        (plantedArrayObservation B σ i s q - nnrealTimePrimitive (m i) s q))) =
      (fun q => ∑ i : I, b i *
      ((plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q) -
        (plantedArrayObservation B σ i s q - nnrealTimePrimitive (m i) s q))) := by
    funext q
    rw [← Finset.sum_coe_sort I]
    simp only [hc]
  rw [heq] at h
  exact h

theorem isGaussianProcess_innovation_array :
    IsGaussianProcess (fun p : (_ : ι) × ℝ≥0 => fun q =>
      plantedArrayObservation B σ p.1 p.2 q - nnrealTimePrimitive (m p.1) p.2 q)
      (ν.prod (Measure.infinitePi μ)) := by
  classical
  have (i : ι) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  apply GaussianArrayCharacterization.isGaussianProcess_array_of_conditional_finite_characters
    (B := fun i t q => plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q)
    (P := ν.prod (Measure.infinitePi μ)) (arrayObservationFiltration B hmB σ hσ)
  · exact fun i => (preBrownian_array_innovation_martingale_of_progressive_posterior
      ν μ hB hmB hσ i (hσbound i) (hm i) (hposterior i)).stronglyAdapted.adapted
  · exact fun i => (preBrownian_array_innovation_of_progressive_posterior
      ν μ hB hmB hσ i (hσbound i) (hm i) (hposterior i)).eval_zero_ae_eq_zero
  · exact conditional_weighted_character ν μ hB hmB hσ hσbound hm hposterior

theorem map_innovation_array_eq_infinitePi_reference
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {R : ℝ≥0 → Ω' → ℝ} (hR : IsPreBrownianReal R Q)
    (hmR : ∀ t, Measurable (R t)) :
    (ν.prod (Measure.infinitePi μ)).map (fun q i t =>
      plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q) =
      Measure.infinitePi (fun _ : ι => Q.map (fun ω t => R t ω)) := by
  classical
  have (i : ι) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  apply GaussianArrayCharacterization.map_brownianArray_eq_infinitePi_of_conditional_finite_characters
    (arrayObservationFiltration B hmB σ hσ) _ _ _ hR hmR
  · exact fun i => (preBrownian_array_innovation_martingale_of_progressive_posterior
      ν μ hB hmB hσ i (hσbound i) (hm i) (hposterior i)).stronglyAdapted.adapted
  · exact fun i => (preBrownian_array_innovation_of_progressive_posterior
      ν μ hB hmB hσ i (hσbound i) (hm i) (hposterior i)).eval_zero_ae_eq_zero
  · exact conditional_weighted_character ν μ hB hmB hσ hσbound hm hposterior

theorem exists_continuous_innovation_array_wiener_law
    (hcontinuous : ∀ i, ∀ᵐ ω ∂μ i, Continuous (fun t => B i t ω)) :
    ∃ X : ι → S × (ι → Ω) → WienerSampler.Path,
      (∀ i, Measurable (X i)) ∧
      (∀ i, ∀ᵐ q ∂ν.prod (Measure.infinitePi μ), ∀ t,
        X i q t = plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q) ∧
      (ν.prod (Measure.infinitePi μ)).map (fun q i => X i q) =
        Measure.infinitePi (fun _ : ι => WienerSampler.wienerMeasure) := by
  classical
  have (i : ι) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := ν.prod (Measure.infinitePi μ)
  let F := arrayObservationFiltration B hmB σ hσ
  let W : ι → ℝ≥0 → S × (ι → Ω) → ℝ := fun i t q =>
    plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q
  have hW (i : ι) : Martingale (W i) F P :=
    preBrownian_array_innovation_martingale_of_progressive_posterior
      ν μ hB hmB hσ i (hσbound i) (hm i) (hposterior i)
  have hpre (i : ι) : IsPreBrownianReal (W i) P :=
    preBrownian_array_innovation_of_progressive_posterior
      ν μ hB hmB hσ i (hσbound i) (hm i) (hposterior i)
  have hcont (i : ι) : ∀ᵐ q ∂P, Continuous (fun t => W i t q) :=
    (brownian_array_innovation_of_progressive_posterior
      ν μ (fun j => ⟨hB j, hcontinuous j⟩) hmB hσ i (hσbound i)
      (hm i) (hposterior i)).cont
  choose X hXm hXe using fun i => WienerSampler.exists_measurable_path_version
    P (W i) (fun t => ((hW i).stronglyMeasurable t).mono (F.le t) |>.measurable) (hcont i)
  refine ⟨X, hXm, hXe, ?_⟩
  have hcross := GaussianArrayCharacterization.crossCovariance_of_conditional_finite_characters
    F (fun i => (hW i).stronglyAdapted.adapted)
    (fun i => (hpre i).eval_zero_ae_eq_zero)
    (conditional_weighted_character ν μ hB hmB hσ hσbound hm hposterior)
  have hG : IsGaussianProcess (fun p : (_ : ι) × ℝ≥0 => W p.1 p.2) P :=
    isGaussianProcess_innovation_array ν μ hB hmB hσ hσbound hm hposterior
  have hi : iIndepFun (fun i q t => X i q t) P :=
    (iIndepFun_of_gaussianArray_crossCovariance hG hcross).congr (fun i => by
      filter_upwards [hXe i] with q hq
      exact funext (fun t => (hq t).symm))
  have hiX : iIndepFun X P := iIndepFun_continuousPaths_of_evaluations hi
  rw [hiX.map_fun_eq_infinitePi_map hXm]
  congr 1
  funext i
  have hpx : IsPreBrownianReal (fun t q => X i q t) P := (hpre i).congr (fun t => by
    filter_upwards [hXe i] with q hq
    exact (hq t).symm)
  simpa only [Measure.map_id] using map_continuousPreBrownian_eq (hXm i)
    (measurable_id : Measurable (id : WienerSampler.Path → WienerSampler.Path)) hpx
    WienerSampler.coordinate_isBrownianReal.toIsPreBrownianReal

end Problem367.ArrayInnovationLaw

end

end OAI
