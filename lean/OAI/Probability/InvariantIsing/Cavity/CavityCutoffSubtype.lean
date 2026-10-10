import OAI.Probability.InvariantIsing.Cavity.CavityReplicaCutoff
import OAI.Probability.IsingPerceptron.NormalizedRestrictionPi

namespace OAI

/-! The normalized two-replica cutoff is exactly the Gibbs test on the
restricted prior used in the finite geometric comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Classical

namespace InvariantIsing

lemma cavity_cutoff_replica_eq_restricted {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) (hp : ν s ≠ 0)
    (F : (Fin 2 → X) → ℝ) :
    cavityCutoffReplicaMean ν H s F = referenceReplicaMean (normalizedRestriction ν s) H F := by
  let μ := Measure.pi (fun _ : Fin 2 => ν)
  let S := univ.pi (fun _ : Fin 2 => s)
  let E := fun σ : Fin 2 → X => Real.exp (∑ i, H (σ i))
  have hS : MeasurableSet S := MeasurableSet.univ_pi (fun _ => hs)
  have hpS : μ S ≠ 0 := replica_restriction_mass_ne_zero hp
  have hrS : (μ S).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hpS, measure_ne_top _ _⟩
  have hz : (referencePartition ν H)^2 ≠ 0 := pow_ne_zero _
    (MeasureTheory.integral_exp_pos hH).ne'
  have hn : (∫ σ, E σ * (if ∀ i, σ i ∈ s then F σ else 0) ∂μ) =
      ∫ σ in S, E σ * F σ ∂μ := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    exact ae_of_all _ fun σ => by
      by_cases h : ∀ i, σ i ∈ s
      · simp [S, h]
      · simp [S, h]
  have hd : (∫ σ, E σ * (if ∀ i, σ i ∈ s then (1 : ℝ) else 0) ∂μ) =
      ∫ σ in S, E σ ∂μ := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    exact ae_of_all _ fun σ => by
      by_cases h : ∀ i, σ i ∈ s
      · simp [S, h]
      · simp [S, h]
  let := normalizedRestriction_probability hp
  rw [cavityCutoffReplicaMean, referenceReplicaMean, referenceReplicaMean]
  change ((∫ σ, E σ * (if ∀ i, σ i ∈ s then F σ else 0) ∂μ) / _) /
      ((∫ σ, E σ * (if ∀ i, σ i ∈ s then (1 : ℝ) else 0) ∂μ) / _) = _
  rw [hn, hd, div_div_div_cancel_right₀ hz]
  rw [referenceReplicaMean_eq_ratio,
    normalizedRestriction_pi (fun _ : Fin 2 => s) (fun _ => hp)]
  change _ = (∫ σ, E σ * F σ ∂normalizedRestriction μ S) /
    (∫ σ, E σ ∂normalizedRestriction μ S)
  rw [integral_normalizedRestriction, integral_normalizedRestriction,
    div_div_div_cancel_right₀ hrS]

theorem cavity_cutoff_replica_eq_subtype {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) (hp : ν s ≠ 0)
    (F : (Fin 2 → X) → ℝ) :
    cavityCutoffReplicaMean ν H s F = referenceReplicaMean (subtypeReference ν s)
      (fun x => H x) (fun σ => F (fun i => (σ i : X))) := by
  rw [cavity_cutoff_replica_eq_restricted ν H hH s hs hp F]
  exact (referenceReplicaMean_subtype hs hp (measurable_of_countable H)
    (measurable_of_countable F)).symm

end InvariantIsing

end

end OAI
