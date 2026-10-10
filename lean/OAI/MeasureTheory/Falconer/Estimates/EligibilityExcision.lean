import OAI.MeasureTheory.Falconer.Graphs.EligibleDyadicGraph
import OAI.MeasureTheory.Falconer.Estimates.EnergySplitting

namespace OAI

/-!
# Removing all ineligible cell terms from the exact expansion

The exceptional angular sets are chosen before the radial frequency.
Consequently the finite whole-cell decision is valid in the full product
integral and never truncates an angular support by a nonsmooth test.
-/

namespace Falconer
open Set MeasureTheory MeasureTheory.Measure
attribute [local instance] Classical.propDecidable

theorem capIncidence_nonneg {d : ℕ} (ρ : Measure (Space d))
    (η : Sphere d → ℝ) (b : Space d → Sphere d → ℂ) (hη : ∀ w, 0 ≤ η w) :
    0 ≤ capIncidence ρ η b :=
  integral_nonneg (fun w => mul_nonneg (hη w) (integral_nonneg (fun _ => sq_nonneg _)))

theorem DyadicCube.cap_sum_eq_eligible {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (n : ℕ) (M : ℝ)
    (η : Sphere d → ℝ) (hηm : Measurable η) (hη : ∀ w, 0 ≤ η w)
    (b : Space d → Sphere d → ℂ) (hb : Measurable (Function.uncurry b))
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hηB : ∀ w, η w ≤ B) (hbC : ∀ x w, ‖b x w‖ ≤ C) :
    ∀ᵐ w ∂sphereMeasure d, ∀ r, η w ≠ 0 →
      (∑ p ∈ Q.occupiedPaths μ n,
        endpointTransform (μ.restrict (Q.descendant p).carrier) M b r w) =
      ∑ p ∈ Q.eligiblePaths μ n η b,
        endpointTransform (μ.restrict (Q.descendant p).carrier) M b r w := by
  have hp (p : List (Fin d → Bool)) (hp : p ∈ Q.occupiedPaths μ n) :
      ∀ᵐ w ∂sphereMeasure d, ∀ r, η w ≠ 0 → p ∉ Q.eligiblePaths μ n η b →
        endpointTransform (μ.restrict (Q.descendant p).carrier) M b r w = 0 := by
    by_cases he : p ∈ Q.eligiblePaths μ n η b
    · exact Filter.Eventually.of_forall (fun _ _ _ h => (h he).elim)
    have hz : capIncidence (μ.restrict (Q.descendant p).carrier) η b = 0 := by
      apply le_antisymm _ (capIncidence_nonneg _ η b hη)
      apply le_of_not_gt
      intro hpos
      exact he (Finset.mem_filter.mpr ⟨hp,hpos⟩)
    have hzero := capIncidence_zero_transform (μ.restrict (Q.descendant p).carrier)
      η hηm hη b hb hB hC hηB hbC hz M
    filter_upwards [hzero] with w hw
    intro r hne _
    exact hw (lt_of_le_of_ne (hη w) (Ne.symm hne)) r
  have hall := (Q.occupiedPaths μ n).eventually_all.mpr hp
  filter_upwards [hall] with w hw
  intro r hηne
  symm
  apply Finset.sum_subset (Q.eligiblePaths_subset μ n η b)
  intro p hp hpe
  exact hw p hp r hηne hpe

private theorem pair_transform_sum {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) (M₁ M₂ : ℝ) (b c : Space d → Sphere d → ℂ)
    (A B : Finset (List (Fin d → Bool))) (z : ℝ × (Sphere d × Sphere d)) :
    (∑ row ∈ A ×ˢ B, dyadicPairTransform Q₁ Q₂ μ ν M₁ M₂ b c row z) =
      (∑ p ∈ A, endpointTransform (μ.restrict (Q₁.descendant p).carrier) M₁ b z.1 z.2.1) *
      (∑ q ∈ B, endpointTransform (ν.restrict (Q₂.descendant q).carrier) M₂ c z.1 z.2.2) := by
  simp only [Finset.sum_product, dyadicPairTransform, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem weighted_dyadic_expansion_excision {d : ℕ} (Q₁ Q₂ : DyadicCube d)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (n : ℕ) (M₁ M₂ : ℝ)
    (η₁ η₂ : Sphere d → ℝ) (hη₁m : Measurable η₁) (hη₂m : Measurable η₂)
    (hη₁ : ∀ w, 0 ≤ η₁ w) (hη₂ : ∀ w, 0 ≤ η₂ w)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B₁ B₂ C₁ C₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hη₁B : ∀ w, η₁ w ≤ B₁) (hη₂B : ∀ w, η₂ w ≤ B₂)
    (hbC : ∀ x w, ‖b x w‖ ≤ C₁) (hcC : ∀ x w, ‖c x w‖ ≤ C₂)
    (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    (fun z : ℝ × (Sphere d × Sphere d) => (η₁ z.2.1 * η₂ z.2.2) •
      (∑ row ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
        ∑ col ∈ Q₁.occupiedPaths μ n ×ˢ Q₂.occupiedPaths ν n,
          dyadicPairTransform Q₁ Q₂ μ ν M₁ M₂ b c row z *
            star (dyadicPairTransform Q₁ Q₂ μ ν M₁ M₂ b c col z))) =ᵐ[angularProductMeasure d v Ψ]
    (fun z => (η₁ z.2.1 * η₂ z.2.2) •
      (∑ row ∈ Q₁.eligiblePaths μ n η₁ b ×ˢ Q₂.eligiblePaths ν n η₂ c,
        ∑ col ∈ Q₁.eligiblePaths μ n η₁ b ×ˢ Q₂.eligiblePaths ν n η₂ c,
          dyadicPairTransform Q₁ Q₂ μ ν M₁ M₂ b c row z *
            star (dyadicPairTransform Q₁ Q₂ μ ν M₁ M₂ b c col z))) := by
  have h₁ := Q₁.cap_sum_eq_eligible μ n M₁ η₁ hη₁m hη₁ b hb hB₁ hC₁ hη₁B hbC
  have h₂ := Q₂.cap_sum_eq_eligible ν n M₂ η₂ hη₂m hη₂ c hc hB₂ hC₂ hη₂B hcC
  have h₁' : ∀ᵐ w ∂(sphereMeasure d).prod (sphereMeasure d), ∀ r, η₁ w.1 ≠ 0 →
      (∑ p ∈ Q₁.occupiedPaths μ n,
        endpointTransform (μ.restrict (Q₁.descendant p).carrier) M₁ b r w.1) =
      ∑ p ∈ Q₁.eligiblePaths μ n η₁ b,
        endpointTransform (μ.restrict (Q₁.descendant p).carrier) M₁ b r w.1 :=
    quasiMeasurePreserving_fst.ae h₁
  have h₂' : ∀ᵐ w ∂(sphereMeasure d).prod (sphereMeasure d), ∀ r, η₂ w.2 ≠ 0 →
      (∑ p ∈ Q₂.occupiedPaths ν n,
        endpointTransform (ν.restrict (Q₂.descendant p).carrier) M₂ c r w.2) =
      ∑ p ∈ Q₂.eligiblePaths ν n η₂ c,
        endpointTransform (ν.restrict (Q₂.descendant p).carrier) M₂ c r w.2 :=
    quasiMeasurePreserving_snd.ae h₂
  have hz₁ := (quasiMeasurePreserving_snd
    (μ := PlanarFalconer.sourceAngularShellMeasure v Ψ)).ae h₁'
  have hz₂ := (quasiMeasurePreserving_snd
    (μ := PlanarFalconer.sourceAngularShellMeasure v Ψ)).ae h₂'
  filter_upwards [hz₁,hz₂] with z hz₁ hz₂
  by_cases hzero₁ : η₁ z.2.1 = 0
  · simp [hzero₁]
  by_cases hzero₂ : η₂ z.2.2 = 0
  · simp [hzero₂]
  congr 1
  rw [← complex_sum_square, ← complex_sum_square,
    pair_transform_sum, pair_transform_sum, hz₁ z.1 hzero₁, hz₂ z.1 hzero₂]

end Falconer

end OAI
