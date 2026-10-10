import OAI.MeasureTheory.Falconer.Estimates.RegularizationPairBounds
import OAI.MeasureTheory.Falconer.Shells.OriginalClassDistance
import OAI.MeasureTheory.Falconer.Estimates.ClassPairWeights

namespace OAI

/-! # Exact original-mass mixture for the two-class distance law -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal NNReal
variable {d : ℕ}

noncomputable def classPairWeight (Q₁ Q₂ : DyadicCube d) (μ ν : Measure (Space d))
    (N B₁ B₂ : ℕ) (i : List ℕ × List ℕ) : ℝ≥0 :=
  (classMeasure Q₁ μ (regularizationLeaves Q₁ μ N) (regularizationLabel Q₁ μ N B₁) i.1 univ *
    classMeasure Q₂ ν (regularizationLeaves Q₂ ν N) (regularizationLabel Q₂ ν N B₂) i.2 univ).toNNReal

theorem classPairWeight_sum_le_one (Q₁ Q₂ : DyadicCube d)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side)
    (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) :
    (∑ i ∈ (regularizationIndex Q₁ μ N B₁ t₁).product (regularizationIndex Q₂ ν N B₂ t₂),
      (classPairWeight Q₁ Q₂ μ ν N B₁ B₂ i : ℝ)) ≤ 1 :=
  retained_class_pair_real_mass_sum_le_one Q₁ Q₂ hQ₁ hQ₂ μ ν
    (Finset.filter_subset _ _) (Finset.filter_subset _ _) _ _ _ _
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem classPairWeight_coe (Q₁ Q₂ : DyadicCube d) (μ ν : Measure (Space d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (N B₁ B₂ : ℕ) (i : List ℕ × List ℕ) :
    (classPairWeight Q₁ Q₂ μ ν N B₁ B₂ i : ℝ≥0∞) =
      classMeasure Q₁ μ (regularizationLeaves Q₁ μ N) (regularizationLabel Q₁ μ N B₁) i.1 univ *
      classMeasure Q₂ ν (regularizationLeaves Q₂ ν N) (regularizationLabel Q₂ ν N B₂) i.2 univ := by
  apply ENNReal.coe_toNNReal
  apply ENNReal.mul_ne_top
  · change μ.restrict _ univ ≠ ∞
    exact measure_ne_top _ _
  · change ν.restrict _ univ ≠ ∞
    exact measure_ne_top _ _

noncomputable def regularizationPairDistance (Q₁ Q₂ : DyadicCube d) (μ ν : Measure (Space d))
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (σ κ : ℝ)
    (p₁ p₂ : List ℕ → CellPath d) (c : List ℕ × List ℕ → ℕ)
    (Γ : Set (Space d × Space d)) : Measure ℝ :=
  partitionEndpointDistance μ ν Γ
    ((regularizationIndex Q₁ μ N B₁ t₁).product (regularizationIndex Q₂ ν N B₂ t₂))
    (fun i => regularizationSet Q₁ μ N B₁ i.1) (fun i => regularizationSet Q₂ ν N B₂ i.2)
    (fun i => sourceOuterMask Q₁ μ N B₁ σ κ (p₁ i.1) (c i))
    (fun i => sourceOuterMask Q₂ ν N B₂ σ κ (p₂ i.2) (c i))

theorem regularizationPairDistance_eq_mixture {k : ℕ}
    (Q₁ Q₂ : DyadicCube d) (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (σ κ : ℝ)
    (p₁ p₂ : List ℕ → CellPath d)
    (he₁ : ∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, regularizationLabel Q₁ μ N B₁ (p₁ T) = T)
    (he₂ : ∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, regularizationLabel Q₂ ν N B₂ (p₂ T) = T)
    (c : List ℕ × List ℕ → ℕ) (A D : Fin k → Set (Space d))
    (hm : ∀ j, MeasurableSet (A j) ∧ MeasurableSet (D j))
    (hd : Pairwise fun j l => Disjoint (A j ×ˢ D j) (A l ×ˢ D l)) :
    regularizationPairDistance Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c (⋃ j, A j ×ˢ D j) =
      ∑ i ∈ (regularizationIndex Q₁ μ N B₁ t₁).product (regularizationIndex Q₂ ν N B₂ t₂),
        classPairWeight Q₁ Q₂ μ ν N B₁ B₂ i •
          ∑ j, endpointWeightedDistance ((sourceClass Q₁ μ N B₁ (p₁ i.1)).restrict (A j))
            ((sourceClass Q₂ ν N B₂ (p₂ i.2)).restrict (D j)) 1 1 1
              (sourceOuterMask Q₁ μ N B₁ σ κ (p₁ i.1) (c i))
              (sourceOuterMask Q₂ ν N B₂ σ κ (p₂ i.2) (c i)) := by
  unfold regularizationPairDistance
  rw [partitionEndpointDistance_product_sum μ ν A D hm hd]
  · apply Finset.sum_congr rfl
    intro i hi
    have hi₁ := (Finset.mem_product.mp hi).1
    have hi₂ := (Finset.mem_product.mp hi).2
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [regularizationSet]
    rw [original_class_endpoint_distance Q₁ Q₂ μ ν _ _ _ _ i.1 i.2
      (ht₁.trans_le (Finset.mem_filter.mp hi₁).2).ne'
      (ht₂.trans_le (Finset.mem_filter.mp hi₂).2).ne' (A j) (D j) (hm j).1 (hm j).2]
    rw [← sourceClass_eq_normalized Q₁ μ N B₁ (p₁ i.1) i.1 (he₁ i.1 hi₁),
      ← sourceClass_eq_normalized Q₂ ν N B₂ (p₂ i.2) i.2 (he₂ i.2 hi₂)]
    rw [← classPairWeight_coe Q₁ Q₂ μ ν N B₁ B₂ i]
    rfl
  · exact fun _ _ => regularizationSet_measurable _ _ _ _ _
  · exact fun _ _ => regularizationSet_measurable _ _ _ _ _
  · exact fun _ _ => regularOuterMask_measurable _ _ _ _ _ _ _
  · exact fun _ _ => regularOuterMask_measurable _ _ _ _ _ _ _
  · exact fun _ _ _ _ => (regularOuterMask_bounds _ _ _ _ _ _ _ _ _).1
  · exact fun _ _ _ _ => (regularOuterMask_bounds _ _ _ _ _ _ _ _ _).1

end Falconer.Regularization

end OAI
