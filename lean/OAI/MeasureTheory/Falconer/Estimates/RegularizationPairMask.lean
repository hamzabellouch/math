import OAI.MeasureTheory.Falconer.Estimates.RegularizationTestBad
import OAI.MeasureTheory.Falconer.Estimates.RegularOuterMask
import OAI.MeasureTheory.Falconer.Measures.ProductPartitionMask
import OAI.MeasureTheory.Falconer.Estimates.PairExceptional

namespace OAI

/-! # Restoration of the actual two-class outer mask on the original pair -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def retainedRegion (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (t : ℝ≥0∞) : Set (Space d) :=
  ⋃ T ∈ regularizationIndex Q μ N B t, regularizationSet Q μ N B T

noncomputable def sourceOuterMask (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (σ κ : ℝ) (p : CellPath d) (c : ℕ) : Space d → Space d → ℝ :=
  regularOuterMask Q (sourceClass Q μ N B p) (sourceUnitProfile Q μ N B p) N σ κ c

noncomputable def regularizationPairMask (Q₁ Q₂ : DyadicCube d) (μ ν : Measure (Space d))
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (σ κ : ℝ)
    (p₁ p₂ : List ℕ → CellPath d) (c : List ℕ × List ℕ → ℕ) : Space d × Space d → ℝ :=
  productPartitionMask (regularizationIndex Q₁ μ N B₁ t₁) (regularizationIndex Q₂ ν N B₂ t₂)
    (regularizationSet Q₁ μ N B₁) (regularizationSet Q₂ ν N B₂)
    (fun i => sourceOuterMask Q₁ μ N B₁ σ κ (p₁ i.1) (c i))
    (fun i => sourceOuterMask Q₂ ν N B₂ σ κ (p₂ i.2) (c i))

noncomputable def regularizationPairExceptional (Q₁ Q₂ : DyadicCube d) (μ ν : Measure (Space d))
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (σ κ : ℝ)
    (p₁ p₂ : List ℕ → CellPath d) (w₀ : Sphere d) (G : Set (Space d × Space d)) :
    Set (Space d × Space d) :=
  pairExceptional (retainedRegion Q₁ μ N B₁ t₁) (retainedRegion Q₂ ν N B₂ t₂)
    (regularizationTestBad w₀ Q₁ μ N B₁ t₁ σ (PlanarFalconer.sourceSmoothingLevels σ κ) p₁ G)
    (regularizationTestBad w₀ Q₂ ν N B₂ t₂ σ (PlanarFalconer.sourceSmoothingLevels σ κ) p₂
      (Prod.swap ⁻¹' G))

theorem uniform_regularizationPairMask_restoration {σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 0 < N →
      ∀ (Q₁ Q₂ : DyadicCube d), Q₁.side = 1 → Q₂.side = 1 →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (p₁ p₂ : List ℕ → CellPath d),
      (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, p₁ T ∈ regularizationLeaves Q₁ μ N) →
      (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, p₂ T ∈ regularizationLeaves Q₂ ν N) →
      ∀ c : List ℕ × List ℕ → ℕ,
      (∀ i ∈ (regularizationIndex Q₁ μ N B₁ t₁).product (regularizationIndex Q₂ ν N B₂ t₂), c i ≤ N) →
      ∀ (w₀ : Sphere d) (G : Set (Space d × Space d)) (z : Space d × Space d),
      z.1 ≠ z.2 → z ∈ G →
      z ∉ regularizationPairExceptional Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ w₀ G →
      regularizationPairMask Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c z = 1 := by
  obtain ⟨N₀,h₀⟩ := uniform_regularOuterMask_restoration (d := d) hσ hκ
  refine ⟨N₀,?_⟩
  intro N hN hNp Q₁ Q₂ hQ₁ hQ₂ μ ν _ _ B₁ B₂ t₁ t₂ p₁ p₂ hp₁ hp₂ c hc w₀ G z hne hz hout
  have hside₁ : 0 < Q₁.side := by rw [hQ₁]; norm_num
  have hside₂ : 0 < Q₂.side := by rw [hQ₂]; norm_num
  obtain ⟨hret₁,hret₂,hbad₁,hbad₂⟩ := pairExceptional_outside hout
  apply productPartitionMask_eq_one _ _ _ _ _ _
    (hS := fun _ _ _ _ hne => regularizationSet_disjoint Q₁ hside₁ μ N B₁ hne)
    (hT := fun _ _ _ _ hne => regularizationSet_disjoint Q₂ hside₂ ν N B₂ hne)
    hret₁ hret₂
  · intro i hi hx hy
    have hi₁ := (Finset.mem_product.mp hi).1
    let : IsProbabilityMeasure (sourceClass Q₁ μ N B₁ (p₁ i.1)) :=
      regularization_class_probability Q₁ hside₁ μ N B₁ (hp₁ i.1 hi₁)
    have hgood : z ∉ allDescriptorTestBad w₀ Q₁ (sourceClass Q₁ μ N B₁ (p₁ i.1))
        (fun u => sourceUnitProfile Q₁ μ N B₁ (p₁ i.1) (u/N)) N σ
          (PlanarFalconer.sourceSmoothingLevels σ κ) G := by
      intro hb
      exact hbad₁ (mem_iUnion₂.mpr ⟨i.1,hi₁,⟨hx,mem_univ _⟩,hb⟩)
    exact (h₀ N hN hNp Q₁ hQ₁ _ _ (c i) (hc i hi) w₀ G z.1 z.2
      (leafUnion_subset Q₁ hside₁ _ hx) hne hz hgood).1
  · intro i hi hx hy
    have hi₂ := (Finset.mem_product.mp hi).2
    let : IsProbabilityMeasure (sourceClass Q₂ ν N B₂ (p₂ i.2)) :=
      regularization_class_probability Q₂ hside₂ ν N B₂ (hp₂ i.2 hi₂)
    have hgood : z.swap ∉ allDescriptorTestBad w₀ Q₂ (sourceClass Q₂ ν N B₂ (p₂ i.2))
        (fun u => sourceUnitProfile Q₂ ν N B₂ (p₂ i.2) (u/N)) N σ
          (PlanarFalconer.sourceSmoothingLevels σ κ) (Prod.swap ⁻¹' G) := by
      intro hb
      exact hbad₂ (mem_iUnion₂.mpr ⟨i.2,hi₂,⟨hy,mem_univ _⟩,hb⟩)
    exact (h₀ N hN hNp Q₂ hQ₂ _ _ (c i) (hc i hi) w₀ (Prod.swap ⁻¹' G) z.2 z.1
      (leafUnion_subset Q₂ hside₂ _ hy) hne.symm hz hgood).2

end Falconer.Regularization

end OAI
