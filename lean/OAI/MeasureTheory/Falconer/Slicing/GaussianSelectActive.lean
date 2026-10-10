import OAI.MeasureTheory.Falconer.Slicing.GaussianActiveRelation

namespace OAI

/-! # Choosing a quantitatively nonempty slice with its original active tube covers -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem gaussian_select_active_slice
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {D : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : κ → Space (n+1))
    {R : ℝ} (hR : 0 ≤ R) {N T P b : ℝ≥0∞} (hN : ∀ w, ((J w).card : ℝ≥0∞) ≤ N)
    (hT : T ≠ 0) (hTfin : T ≠ ∞)
    (hP : ∀ p : (Fin h → Space (n+1)) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)) univ ≤ P)
    (hmean : b*volume (coordinateBox h (D*(ε+1)+δ)) + P*(N*ENNReal.ofReal ((2*R)^h)/T)*M <
      ∫⁻ p, gaussianPrunedIncidence μ ν δ r TP TD M E p
        ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume) :
    ∃ A ∈ gaussianRowNeighborhood B ε, ∃ z ∈ coordinateBox h (D*(ε+1)+δ),
      b < gaussianPrunedPairMass μ ν δ r TP TD M (gaussianActiveRelation E J a R T true) (A,z) := by
  have hξ : ((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod
      (volume : Measure (Space h)) ≤ (gaussianRows (n+1) h).prod volume :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  have hl := gaussian_active_pruning_loss μ ν _ hξ δ r TP TD M E hE J hJ a hR hN hT hTfin hP
  apply gaussian_select_pruned_pair B hB hε μ ν hμ δ r TP TD M _
  exact lt_of_add_lt_add_right (hmean.trans_le hl)

end Falconer

end OAI
