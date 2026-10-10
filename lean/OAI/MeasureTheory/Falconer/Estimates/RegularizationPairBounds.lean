import OAI.MeasureTheory.Falconer.Estimates.RegularizationPairMask

namespace OAI

/-! # Measurability, range and original-pair cost of the assembled mask -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem regularizationPairMask_measurable (Q₁ Q₂ : DyadicCube d) (μ ν : Measure (Space d))
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (σ κ : ℝ)
    (p₁ p₂ : List ℕ → CellPath d) (c : List ℕ × List ℕ → ℕ) :
    Measurable (regularizationPairMask Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c) :=
  productPartitionMask_measurable _ _ _ _ _ _
    (fun _ _ => regularizationSet_measurable _ _ _ _ _)
    (fun _ _ => regularizationSet_measurable _ _ _ _ _)
    (fun _ _ => regularOuterMask_measurable _ _ _ _ _ _ _)
    (fun _ _ => regularOuterMask_measurable _ _ _ _ _ _ _)

theorem regularizationPairMask_bounds (Q₁ Q₂ : DyadicCube d)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side) (μ ν : Measure (Space d))
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (σ κ : ℝ)
    (p₁ p₂ : List ℕ → CellPath d) (c : List ℕ × List ℕ → ℕ) (z : Space d × Space d) :
    regularizationPairMask Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c z ∈ Icc (0:ℝ) 1 :=
  productPartitionMask_bounds _ _ _ _ _ _
    (fun _ _ _ _ hne => regularizationSet_disjoint Q₁ hQ₁ μ N B₁ hne)
    (fun _ _ _ _ hne => regularizationSet_disjoint Q₂ hQ₂ ν N B₂ hne)
    (fun _ _ => regularOuterMask_bounds _ _ _ _ _ _ _)
    (fun _ _ => regularOuterMask_bounds _ _ _ _ _ _ _) z

theorem regularizationPairExceptional_measurable (Q₁ Q₂ : DyadicCube d)
    (hQ₁ : 0 < Q₁.side) (hQ₂ : 0 < Q₂.side) (μ ν : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (σ κ : ℝ)
    (p₁ p₂ : List ℕ → CellPath d)
    (hp₁ : ∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, p₁ T ∈ regularizationLeaves Q₁ μ N)
    (hp₂ : ∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, p₂ T ∈ regularizationLeaves Q₂ ν N)
    (w₀ : Sphere d) {G : Set (Space d × Space d)} (hG : MeasurableSet G) :
    MeasurableSet (regularizationPairExceptional Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ w₀ G) :=
  pairExceptional_measurable
    (Finset.measurableSet_biUnion _ (fun _ _ => regularizationSet_measurable _ _ _ _ _))
    (Finset.measurableSet_biUnion _ (fun _ _ => regularizationSet_measurable _ _ _ _ _))
    (regularizationTestBad_measurable w₀ Q₁ μ N B₁ t₁ σ _ p₁ hp₁ hQ₁ hG)
    (regularizationTestBad_measurable w₀ Q₂ ν N B₂ t₂ σ _ p₂ hp₂ hQ₂ (hG.preimage measurable_swap))

theorem uniform_regularizationPairExceptional_bound {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q₁ Q₂ : DyadicCube d), Q₁.side = 1 → Q₂.side = 1 →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (B₁ B₂ : ℕ), 0 < B₁ → 0 < B₂ →
      (B₁:ℝ) ≤ σ*N → (B₂:ℝ) ≤ σ*N →
      (2:ℝ)^(N/B₁+2) ≤ ((2:ℝ)^N)^σ → (2:ℝ)^(N/B₂+2) ≤ ((2:ℝ)^N)^σ →
      ∀ (t₁ t₂ : ℝ≥0∞), 0 < t₁ → 0 < t₂ → ∀ p₁ p₂ : List ℕ → CellPath d,
      (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, p₁ T ∈ regularizationLeaves Q₁ μ N) →
      (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, p₂ T ∈ regularizationLeaves Q₂ ν N) →
      (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, regularizationLabel Q₁ μ N B₁ (p₁ T) = T) →
      (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, regularizationLabel Q₂ ν N B₂ (p₂ T) = T) →
      ∀ (w₀ : Sphere d) (G : Set (Space d × Space d)), MeasurableSet G →
      (∀ᵐ x ∂μ, ∀ u : Space d, ∀ r : ℝ, ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
        originalRadialSphereLaw w₀ ν G x {w : Sphere d | dist (w:Space d) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^σ*r^((d:ℝ)/2))) →
      (∀ᵐ y ∂ν, ∀ u : Space d, ∀ r : ℝ, ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
        originalRadialSphereLaw w₀ μ (Prod.swap ⁻¹' G) y {w : Sphere d | dist (w:Space d) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^σ*r^((d:ℝ)/2))) →
      ∀ κ : ℝ,
      (μ.prod ν) (regularizationPairExceptional Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ w₀ G) ≤
        μ (retainedRegion Q₁ μ N B₁ t₁)ᶜ + ν (retainedRegion Q₂ ν N B₂ t₂)ᶜ +
          (4*(N+1)^2:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-σ)) := by
  obtain ⟨N₀,h₀⟩ := uniform_regularization_test_bad_mass (d := d) hσ
  refine ⟨N₀,?_⟩
  intro N hN Q₁ Q₂ hQ₁ hQ₂ μ ν _ _ B₁ B₂ hB₁ hB₂ hw₁ hw₂ hl₁ hl₂
    t₁ t₂ ht₁ ht₂ p₁ p₂ hp₁ hp₂ he₁ he₂ w₀ G hG hc₁ hc₂ κ
  have hside₂ : 0 < Q₂.side := by rw [hQ₂]; norm_num
  have hm₂ := regularizationTestBad_measurable w₀ Q₂ ν N B₂ t₂ σ
    (PlanarFalconer.sourceSmoothingLevels σ κ) p₂ hp₂ hside₂ (hG.preimage measurable_swap)
  have hb₁ := h₀ N hN Q₁ hQ₁ μ ν B₁ hB₁ hw₁ hl₁ t₁ ht₁ p₁ hp₁ he₁ w₀ G hG hc₁
    (PlanarFalconer.sourceSmoothingLevels σ κ)
  have hb₂ := h₀ N hN Q₂ hQ₂ ν μ B₂ hB₂ hw₂ hl₂ t₂ ht₂ p₂ hp₂ he₂ w₀
    (Prod.swap ⁻¹' G) (hG.preimage measurable_swap) hc₂ (PlanarFalconer.sourceSmoothingLevels σ κ)
  apply (pairExceptional_mass μ ν _ _ _ _ hm₂).trans
  calc
    _ ≤ μ (retainedRegion Q₁ μ N B₁ t₁)ᶜ + ν (retainedRegion Q₂ ν N B₂ t₂)ᶜ +
        (2*(N+1)^2:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-σ)) +
        (2*(N+1)^2:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-σ)) :=
      add_le_add (add_le_add le_rfl hb₁) hb₂
    _ = _ := by
      have hn : 4*(N+1)^2 = 2*(N+1)^2+2*(N+1)^2 := by omega
      rw [hn,Nat.cast_add,add_mul]
      exact add_assoc _ _ _

end Falconer.Regularization

end OAI
