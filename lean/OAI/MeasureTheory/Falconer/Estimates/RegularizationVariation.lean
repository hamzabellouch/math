import OAI.MeasureTheory.Falconer.Shells.ClassPairDistance
import OAI.MeasureTheory.Falconer.Estimates.ScopedMaskVariation

namespace OAI

/-! # Original-law variation cost of the actual regularized mask -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem regularizationPairDistance_eq_masked (Q₁ Q₂ : DyadicCube d) (μ ν : Measure (Space d))
    (N B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (σ κ : ℝ)
    (p₁ p₂ : List ℕ → CellPath d) (c : List ℕ × List ℕ → ℕ)
    (Γ : Set (Space d × Space d)) :
    regularizationPairDistance Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c Γ =
      (((μ.prod ν).restrict Γ).withDensity (fun z => distanceWeight (((d:ℝ)-1)/2) z *
        ENNReal.ofReal (regularizationPairMask Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c z))).map
          (fun z => dist z.1 z.2) := by
  unfold regularizationPairDistance partitionEndpointDistance
  congr 1
  congr 1
  funext z
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg dist_nonneg _)]
  rfl

theorem distanceWeight_upper {δ : ℝ} (hd : 1 ≤ d) (hδ : 0 < δ)
    {π : Measure (Space d × Space d)} (hsep : ∀ᵐ z ∂π, δ ≤ dist z.1 z.2) :
    ∀ᵐ z ∂π, distanceWeight (((d:ℝ)-1)/2) z ≤ ENNReal.ofReal (δ^(-(((d:ℝ)-1)/2))) := by
  have hh : (1:ℝ) ≤ d := by exact_mod_cast hd
  filter_upwards [hsep] with z hz
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hδ hz (by linarith))

theorem uniform_regularization_variation {σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hd : 1 ≤ d) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 0 < N →
      ∀ (Q₁ Q₂ : DyadicCube d), Q₁.side = 1 → Q₂.side = 1 →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞) (p₁ p₂ : List ℕ → CellPath d),
      (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, p₁ T ∈ regularizationLeaves Q₁ μ N) →
      (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, p₂ T ∈ regularizationLeaves Q₂ ν N) →
      ∀ c : List ℕ × List ℕ → ℕ,
      (∀ i ∈ (regularizationIndex Q₁ μ N B₁ t₁).product (regularizationIndex Q₂ ν N B₂ t₂), c i ≤ N) →
      ∀ (w₀ : Sphere d) (Γ D : Set (Space d × Space d)), MeasurableSet Γ →
      ∀ (δ : ℝ) (hδ : 0 < δ) (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2),
      ∃ τ : FiniteMeasure ℝ,
        (τ : Measure ℝ) = regularizationPairDistance Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c Γ ∧
        letI := finite_withDensity_of_bounded (μ.prod ν) (distanceWeight (((d:ℝ)-1)/2))
          ENNReal.ofReal_lt_top (distanceWeight_upper hd hδ hsep)
        PlanarFalconer.variationDistance
          ⟨filteredPushforward (fun z : Space d × Space d => dist z.1 z.2)
            ((μ.prod ν).withDensity (distanceWeight (((d:ℝ)-1)/2))) Γ,inferInstance⟩ τ ≤
          ENNReal.ofReal (δ^(-(((d:ℝ)-1)/2))) *
            ((μ.prod ν) D + (μ.prod ν)
              (regularizationPairExceptional Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ w₀ (Γ \ D))) := by
  obtain ⟨N₀,h₀⟩ := uniform_regularizationPairMask_restoration (d := d) hσ hκ
  refine ⟨N₀,?_⟩
  intro N hN hNp Q₁ Q₂ hQ₁ hQ₂ μ ν _ _ B₁ B₂ t₁ t₂ p₁ p₂ hp₁ hp₂ c hc w₀ Γ D hΓ δ hδ hsep
  let w : Space d × Space d → ℝ≥0∞ := distanceWeight (((d:ℝ)-1)/2)
  let mask := regularizationPairMask Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c
  let E := regularizationPairExceptional Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ w₀ (Γ \ D)
  have hside₁ : 0 < Q₁.side := by rw [hQ₁]; norm_num
  have hside₂ : 0 < Q₂.side := by rw [hQ₂]; norm_num
  have hbound : ∀ᵐ z ∂μ.prod ν, w z ≤ ENNReal.ofReal (δ^(-(((d:ℝ)-1)/2))) :=
    distanceWeight_upper hd hδ hsep
  let := finite_withDensity_of_bounded (μ.prod ν) w ENNReal.ofReal_lt_top hbound
  have hout : ∀ᵐ z ∂μ.prod ν, z ∈ Γ → z ∉ D ∪ E → ENNReal.ofReal (mask z) = 1 := by
    filter_upwards [hsep] with z hz hΓz hgood
    have hnD : z ∉ D := fun h => hgood (Or.inl h)
    have hnE : z ∉ E := fun h => hgood (Or.inr h)
    have hne : z.1 ≠ z.2 := dist_pos.mp (hδ.trans_le hz)
    change ENNReal.ofReal (regularizationPairMask Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c z) = 1
    rw [h₀ N hN hNp Q₁ Q₂ hQ₁ hQ₂ μ ν B₁ B₂ t₁ t₂ p₁ p₂ hp₁ hp₂ c hc w₀
      (Γ \ D) z hne ⟨hΓz,hnD⟩ hnE]
    simp
  obtain ⟨τ,hτ,hvar⟩ := filtered_masked_variation_on_le
    (fun z : Space d × Space d => dist z.1 z.2) (by fun_prop) (μ.prod ν) w
    (fun z => ENNReal.ofReal (mask z))
    (by unfold w distanceWeight; fun_prop)
    ((regularizationPairMask_measurable Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c).ennreal_ofReal)
    (fun z => (ENNReal.ofReal_le_ofReal (regularizationPairMask_bounds Q₁ Q₂ hside₁ hside₂
      μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c z).2).trans_eq (by simp))
    Γ (D ∪ E) hΓ _ hbound hout
  refine ⟨τ,?_,?_⟩
  · rw [regularizationPairDistance_eq_masked]
    exact hτ
  · exact hvar.trans (mul_le_mul' le_rfl (measure_union_le _ _))

end Falconer.Regularization

end OAI
