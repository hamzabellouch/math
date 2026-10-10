import OAI.Probability.FreeIsing.Brownian.ArrayInnovation
import OAI.Probability.FreeIsing.Stochastic.PlantedBrownianLinearCombination

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Problem367.ConditionalCharacteristic

namespace Problem367

theorem array_innovation_unit_projection_setIntegral_character
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
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
    (I : Finset ι) (a : ι → ℝ) (ha : ∑ i ∈ I, a i ^ 2 = 1)
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set (S × (ι → Ω))}
    (hA : MeasurableSet[arrayObservationFiltration B hmB σ hσ s] A) (u : ℝ) :
    (∫ q in A, character (fun q => ∑ i ∈ I, a i *
      ((plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q) -
        (plantedArrayObservation B σ i s q - nnrealTimePrimitive (m i) s q))) u q
          ∂ν.prod (Measure.infinitePi μ)) =
      (ν.prod (Measure.infinitePi μ)).real A *
        Complex.exp (-(((t - s : ℝ≥0) : ℝ) : ℂ) * (u : ℂ)^2 / 2) := by
  classical
  have (i : ι) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  let P := ν.prod (Measure.infinitePi μ)
  let F := arrayObservationFiltration B hmB σ hσ
  let W : ℝ≥0 → S × (ι → Ω) → ℝ := fun t q => ∑ i ∈ I, a i *
    (plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q)
  let N : ℝ≥0 → S × (ι → Ω) → ℝ := fun t q => ∑ i ∈ I, a i * B i t (q.2 i)
  have hN : IsPreBrownianReal N P :=
    planted_finite_projection_preBrownian ν μ hB hmB I a ha
  have hW : Martingale W F P := by
    have h := BrownianLinearCombination.martingale_sum F
      (fun i : I => preBrownian_array_innovation_martingale_of_progressive_posterior
        ν μ hB hmB hσ i (hσbound i) (hm i) (hposterior i)) (fun i : I => a i)
    convert h using 1
    funext t q
    exact (Finset.sum_coe_sort I (fun i => a i *
      (plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q))).symm
  have hvariance : ∀ r v : ℝ≥0, r ≤ v →
      P[(fun q => (N v q - N r q)^2) | F r] =ᵐ[P]
        fun _ => (v : ℝ) - (r : ℝ) := by
    intro r v hrv
    have h := planted_weighted_increment_sq_condExp_subfield ν μ hB hmB hrv I a
      (arrayObservationFiltration_le_signalArrayFiltration B hmB σ hσ r)
    simpa only [N, P, F, mul_sub, Finset.sum_sub_distrib, ha, mul_one] using h
  have hbound : ∀ r v : ℝ≥0, r ≤ v → ∀ᵐ q ∂P,
      |(W v q - W r q) - (N v q - N r q)| ≤
        (2 * (C : ℝ) * ∑ i ∈ I, |a i|) * ((v : ℝ) - (r : ℝ)) := by
    intro r v hrv
    have hcoords : ∀ᵐ q ∂P, ∀ i : I,
        |((plantedArrayObservation B σ i v q - nnrealTimePrimitive (m i) v q) -
            (plantedArrayObservation B σ i r q - nnrealTimePrimitive (m i) r q)) -
          (B i v (q.2 i) - B i r (q.2 i))| ≤
          (2 * (C : ℝ)) * ((v : ℝ) - (r : ℝ)) :=
      ae_all_iff.mpr fun i => ae_array_innovation_increment_drift_bound
        ν μ hmB hσ i (hσbound i) (hm i) (hposterior i) hrv
    filter_upwards [hcoords] with q hq
    let D : ι → ℝ := fun i =>
      ((plantedArrayObservation B σ i v q - nnrealTimePrimitive (m i) v q) -
        (plantedArrayObservation B σ i r q - nnrealTimePrimitive (m i) r q)) -
          (B i v (q.2 i) - B i r (q.2 i))
    have heq : (W v q - W r q) - (N v q - N r q) = ∑ i ∈ I, a i * D i := by
      simp only [W, N, D, mul_sub, Finset.sum_sub_distrib]
    rw [heq]
    calc
      |∑ i ∈ I, a i * D i| ≤ ∑ i ∈ I, |a i * D i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ I, |a i| * |D i| := by simp only [abs_mul]
      _ ≤ ∑ i ∈ I, |a i| * ((2 * (C : ℝ)) * ((v : ℝ) - (r : ℝ))) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hq ⟨i, hi⟩) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have h := BrownianInnovation.setIntegral_character_of_bounded_drift hN hW hvariance
    (by positivity : 0 ≤ 2 * (C : ℝ) * ∑ i ∈ I, |a i|) hbound hst hA u
  simpa only [W, mul_sub, Finset.sum_sub_distrib] using h

theorem array_innovation_unit_projection_condExp_character
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
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
    (I : Finset ι) (a : ι → ℝ) (ha : ∑ i ∈ I, a i ^ 2 = 1)
    {s t : ℝ≥0} (hst : s ≤ t) (u : ℝ) :
    (ν.prod (Measure.infinitePi μ))[character (fun q => ∑ i ∈ I, a i *
      ((plantedArrayObservation B σ i t q - nnrealTimePrimitive (m i) t q) -
        (plantedArrayObservation B σ i s q - nnrealTimePrimitive (m i) s q))) u |
          arrayObservationFiltration B hmB σ hσ s] =ᵐ[ν.prod (Measure.infinitePi μ)]
      fun _ => Complex.exp (-(((t - s : ℝ≥0) : ℝ) : ℂ) * (u : ℂ)^2 / 2) := by
  classical
  have (i : ι) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hW (i : ι) (r : ℝ≥0) : Measurable (fun q =>
      plantedArrayObservation B σ i r q - nnrealTimePrimitive (m i) r q) :=
    ((preBrownian_array_innovation_martingale_of_progressive_posterior
      ν μ hB hmB hσ i (hσbound i) (hm i) (hposterior i)).stronglyMeasurable r).mono
        ((arrayObservationFiltration B hmB σ hσ).le r) |>.measurable
  apply BrownianCharacterization.condExp_character_of_setIntegral
    ((arrayObservationFiltration B hmB σ hσ).le s)
  · exact Finset.measurable_sum I fun i _ => ((hW i t).sub (hW i s)).const_mul (a i)
  · intro A hA
    exact array_innovation_unit_projection_setIntegral_character
      ν μ hB hmB hσ hσbound hm hposterior I a ha hst hA u

end Problem367

end

end OAI
