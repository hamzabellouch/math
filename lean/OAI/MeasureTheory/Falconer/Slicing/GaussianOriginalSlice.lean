import OAI.MeasureTheory.Falconer.Slicing.GaussianControlledLedger
import OAI.MeasureTheory.Falconer.Slicing.GaussianSelectActive

namespace OAI

/-! # A retained original-label slice from the explicit four-cost budget -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem gaussian_select_original_slice
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {D δ ρ : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ)
    (r : ι → ℝ) (TP TD CP CD : ι → ℝ≥0∞)
    (hTP : ∀ i, 0 < TP i) (hTD : ∀ i, 0 < TD i)
    (i₀ : ι) (hi₀ : D < r i₀)
    {M Q : ℝ≥0∞} (hM : 0 < M) (hMtop : M ≠ ∞)
    (hpoint : ∀ i, (∫⁻ p : (Fin h → Space (n+1)) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows (n+1) h).prod volume) ≤ CP i)
    (hdir : ∀ i, (∫⁻ A : Fin h → Space (n+1),
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows (n+1) h) ≤ CD i)
    (hmoment : (∫⁻ A : Fin h → Space (n+1), (gaussianDirectionMass ν δ A)^2
      ∂gaussianRows (n+1) h) ≤ Q)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : κ → Space (n+1))
    {R : ℝ} (hR : 0 ≤ R) {N T b : ℝ≥0∞} (hN : ∀ w, ((J w).card : ℝ≥0∞) ≤ N)
    (hT : T ≠ 0) (hTfin : T ≠ ∞)
    (hbudget : (b*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ)) +
      TP i₀*(N*ENNReal.ofReal ((2*R)^h)/T)*M) +
      (∑ i, (TP i)⁻¹*CP i)*M +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (TD i)⁻¹*CD i) +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(M⁻¹*Q) <
      ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*(μ.prod ν) E) :
    ∃ A ∈ gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ)),
      ∃ z ∈ coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ),
      b < gaussianPrunedPairMass μ ν δ r TP TD M (gaussianActiveRelation E J a R T true) (A,z) := by
  have hρ : 0 ≤ ρ := hδ.le.trans hδρ
  have hlo := gaussian_controlled_pruning_ledger B hB μ ν hδ hδρ hwB r TP TD CP CD
    hTP hTD hM hMtop hpoint hdir hmoment E hE
  have hlt := hbudget.trans_le hlo
  have hmean := lt_of_add_lt_add_right (lt_of_add_lt_add_right (lt_of_add_lt_add_right hlt))
  apply gaussian_select_active_slice B hB (by positivity) μ ν hμ δ r TP TD M E hE J hJ a
    hR hN hT hTfin (fun p => gaussianPointGood_mass μ δ r TP p hμ i₀ hi₀)
  exact hmean

end Falconer

end OAI
