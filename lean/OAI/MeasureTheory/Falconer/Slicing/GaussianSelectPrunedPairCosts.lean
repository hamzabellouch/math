import OAI.MeasureTheory.Falconer.Estimates.GoodRowSelectionAE
import OAI.MeasureTheory.Falconer.Slicing.GaussianPrunedPair
import OAI.MeasureTheory.Falconer.Slicing.GaussianPrunedMass

namespace OAI

/-! # A controlled original slice with simultaneous costs for a parameter-dependent relation -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussian_select_pruned_pair_costs
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {D : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (i₀ : ι) (hi₀ : D < r i₀) (E : Set (((Fin h → Space (n+1)) × Space h) × (Space (n+1) × Sphere (n+1)))) (hE : MeasurableSet E)
    (C₁ C₂ : (Fin h → Space (n+1)) → ℝ≥0∞) (hC₁ : Measurable C₁) (hC₂ : Measurable C₂)
    (t₁ t₂ a : ℝ≥0∞) (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0) (ht₁top : t₁ ≠ ∞) (ht₂top : t₂ ≠ ∞)
    (hmean : a*volume (coordinateBox h (D*(ε+1)+δ))+
      (TP i₀*M*volume (coordinateBox h (D*(ε+1)+δ)))*
        ((∫⁻ A, C₁ A ∂(gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε))/t₁)+
      (TP i₀*M*volume (coordinateBox h (D*(ε+1)+δ)))*
        ((∫⁻ A, C₂ A ∂(gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε))/t₂) <
      ∫⁻ p, gaussianPrunedPairMass μ ν δ r TP TD M E p
        ∂((gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ε)).prod volume) :
    ∃ A ∈ gaussianRowNeighborhood B ε, ∃ z ∈ coordinateBox h (D*(ε+1)+δ),
      C₁ A < t₁ ∧ C₂ A < t₂ ∧ a < gaussianPrunedPairMass μ ν δ r TP TD M E (A,z) := by
  let G := gaussianRowNeighborhood B ε
  let ξ := (gaussianRows (n+1) h).restrict G
  let Z := coordinateBox h (D*(ε+1)+δ)
  let I := gaussianPrunedPairMass (h := h) μ ν δ r TP TD M E
  let F := (G ×ˢ univ).indicator I
  have hG : MeasurableSet G := gaussianRowNeighborhood_measurable B ε
  have hI : Measurable I := gaussianPrunedPairMass_measurable μ ν δ r TP TD M E hE
  have hF : Measurable F := hI.indicator (hG.prod MeasurableSet.univ)
  have hrow : ∀ᵐ p : (Fin h → Space (n+1)) × Space h ∂ξ.prod volume, p.1 ∈ G :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hG)
  have hFI : F =ᵐ[ξ.prod volume] I := by
    filter_upwards [hrow] with p hp
    exact indicator_of_mem (show p ∈ G ×ˢ univ from ⟨hp,mem_univ _⟩) I
  have hξ : ξ univ ≤ 1 := by
    exact (Measure.restrict_le_self univ).trans (by simp)
  have hbound : ∀ p, F p ≤ TP i₀*M := by
    intro p
    have hi : I p ≤ TP i₀*M := (gaussian_pruned_incidence_le_masses μ ν δ r TP TD M {t | (p,t) ∈ E} p).trans
      (mul_le_mul' (gaussianPointGood_mass μ δ r TP p hμ i₀ hi₀)
        (gaussianDirectionGood_mass ν δ r TD M p.1))
    by_cases hp : p.1 ∈ G
    · simpa only [F,indicator_of_mem (show p ∈ G ×ˢ univ from ⟨hp,mem_univ _⟩)] using hi
    · rw [show F p = 0 from indicator_of_notMem (fun h => hp h.1) I]
      exact bot_le
  have hsupport : ∀ᵐ p ∂ξ.prod volume, p.2 ∉ Z → F p = 0 := by
    filter_upwards [hFI,gaussianPrunedPairMass_parameter_support B hB hε μ ν hμ δ r TP TD M E]
      with p hp hs hnot
    rw [hp]
    exact hs (fun h => hnot h.2)
  obtain ⟨A,z,hz,h₁,h₂,hlarge⟩ := good_row_selection_ae ξ volume hξ F hF C₁ C₂ hC₁ hC₂
    Z (coordinateBox_measurable _) (TP i₀*M) t₁ t₂ a ht₁ ht₂ ht₁top ht₂top hbound hsupport
    (by rw [lintegral_congr_ae hFI]; exact hmean)
  have hA : A ∈ G := by
    by_contra hn
    rw [show F (A,z) = 0 from indicator_of_notMem (fun h => hn h.1) I] at hlarge
    exact (not_lt_of_ge (bot_le : (0 : ℝ≥0∞) ≤ _)) hlarge
  refine ⟨A,hA,z,hz,h₁,h₂,?_⟩
  simpa only [F,indicator_of_mem (show (A,z) ∈ G ×ˢ univ from ⟨hA,mem_univ _⟩)] using hlarge

end Falconer

end OAI
