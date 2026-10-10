import OAI.Probability.InvariantIsing.Arrays.CountableReplicaRestriction

namespace OAI

/-! Bounded two- and three-replica Ward terms pass through leaf exhaustion.
A finite Ward bound is preserved in the countable-leaf limit. -/

noncomputable section

open MeasureTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

def expectedReplicaWard {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (ν : Measure X) (H : Ω × X → ℝ)
    (D₂ : Ω × (Fin 2 → X) → ℝ) (D₃ : Ω × (Fin 3 → X) → ℝ) : ℝ :=
  (∫ ω, referenceReplicaMean ν (fun x => H (ω,x)) (fun σ => D₂ (ω,σ)) ∂P) -
    2 * ∫ ω, referenceReplicaMean ν (fun x => H (ω,x)) (fun σ => D₃ (ω,σ)) ∂P

theorem expectedReplicaWard_restriction_tendsto {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) ν)
    (D₂ : Ω × (Fin 2 → X) → ℝ) (hD₂ : Measurable D₂)
    (D₃ : Ω × (Fin 3 → X) → ℝ) (hD₃ : Measurable D₃)
    {B₂ B₃ : ℝ} (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (hb₂ : ∀ z, |D₂ z| ≤ B₂) (hb₃ : ∀ z, |D₃ z| ≤ B₃)
    {S : ℕ → Set X} (hS : ∀ n, MeasurableSet (S n))
    (hexh : ∀ x, ∀ᶠ n in atTop, x ∈ S n) (hpos : ∀ n, ν (S n) ≠ 0) :
    Tendsto (fun n => expectedReplicaWard P (normalizedRestriction ν (S n)) H D₂ D₃) atTop
      (𝓝 (expectedReplicaWard P ν H D₂ D₃)) := by
  exact (expected_referenceReplicaMean_restriction_tendsto P ν H hH he D₂ hD₂ hB₂ hb₂
    hS hexh hpos).sub
      ((expected_referenceReplicaMean_restriction_tendsto P ν H hH he D₃ hD₃ hB₃ hb₃
        hS hexh hpos).const_mul 2)

/-- Uniform finite Ward residual bounds are preserved for the full countable
Gibbs prior. No convergence or integrability of a Gaussian correction is needed. -/
theorem expectedReplicaWard_abs_le_of_restriction {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : Ω × X → ℝ) (hH : Measurable H)
    (he : ∀ᵐ ω ∂P, Integrable (fun x => Real.exp (H (ω,x))) ν)
    (D₂ : Ω × (Fin 2 → X) → ℝ) (hD₂ : Measurable D₂)
    (D₃ : Ω × (Fin 3 → X) → ℝ) (hD₃ : Measurable D₃)
    {B₂ B₃ : ℝ} (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃)
    (hb₂ : ∀ z, |D₂ z| ≤ B₂) (hb₃ : ∀ z, |D₃ z| ≤ B₃)
    {S : ℕ → Set X} (hS : ∀ n, MeasurableSet (S n))
    (hexh : ∀ x, ∀ᶠ n in atTop, x ∈ S n) (hpos : ∀ n, ν (S n) ≠ 0)
    {ε : ℝ} (hfinite : ∀ n,
      |expectedReplicaWard P (normalizedRestriction ν (S n)) H D₂ D₃| ≤ ε) :
    |expectedReplicaWard P ν H D₂ D₃| ≤ ε := by
  exact le_of_tendsto (expectedReplicaWard_restriction_tendsto P ν H hH he
    D₂ hD₂ D₃ hD₃ hB₂ hB₃ hb₂ hb₃ hS hexh hpos).abs
      (Filter.Eventually.of_forall hfinite)

end InvariantIsing

end

end OAI
