import OAI.MeasureTheory.Falconer.Slicing.GaussianSelectPrunedPairCosts
import OAI.MeasureTheory.Falconer.Slicing.GaussianActiveRelation

namespace OAI

/-! # Simultaneous row-cost bounds after the original active-cover deletion -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem gaussian_select_active_costs
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {D : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (i₀ : ι) (hi₀ : D < r i₀)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (a : κ → Space (n+1)) {R : ℝ} (hR : 0 ≤ R)
    {Nc T : ℝ≥0∞} (hN : ∀ w, ((J w).card:ℝ≥0∞) ≤ Nc)
    (hT : T ≠ 0) (hTfin : T ≠ ∞)
    (C₁ C₂ : (Fin h → Space (n+1)) → ℝ≥0∞) (hC₁ : Measurable C₁) (hC₂ : Measurable C₂)
    (t₁ t₂ b : ℝ≥0∞) (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0) (ht₁top : t₁ ≠ ∞) (ht₂top : t₂ ≠ ∞)
    (hmean : (b*volume (coordinateBox h (D*(ε+1)+δ))+
      (TP i₀*M*volume (coordinateBox h (D*(ε+1)+δ)))*
        ((∫⁻ A, C₁ A ∂(gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε))/t₁)+
      (TP i₀*M*volume (coordinateBox h (D*(ε+1)+δ)))*
        ((∫⁻ A, C₂ A ∂(gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε))/t₂))+
      TP i₀*(Nc*ENNReal.ofReal ((2*R)^h)/T)*M <
      ∫⁻ p, gaussianPrunedIncidence μ ν δ r TP TD M E p
        ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume) :
    ∃ A ∈ gaussianRowNeighborhood B ε, ∃ z ∈ coordinateBox h (D*(ε+1)+δ),
      C₁ A < t₁ ∧ C₂ A < t₂ ∧
      b < gaussianPrunedPairMass μ ν δ r TP TD M (gaussianActiveRelation E J a R T true) (A,z) := by
  have hξ : ((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod
      (volume : Measure (Space h)) ≤ (gaussianRows (n+1) h).prod volume :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  have hl := gaussian_active_pruning_loss μ ν _ hξ δ r TP TD M E hE J hJ a hR hN hT hTfin
    (fun p => gaussianPointGood_mass μ δ r TP p hμ i₀ hi₀)
  apply gaussian_select_pruned_pair_costs B hB hε μ ν hμ δ r TP TD M i₀ hi₀
    (gaussianActiveRelation E J a R T true) (gaussianActiveRelation_measurable E hE J hJ a R T true)
    C₁ C₂ hC₁ hC₂ t₁ t₂ b ht₁ ht₂ ht₁top ht₂top
  exact lt_of_add_lt_add_right (hmean.trans_le hl)

end Falconer

end OAI
