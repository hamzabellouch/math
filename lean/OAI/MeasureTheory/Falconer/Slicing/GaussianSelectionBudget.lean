import OAI.MeasureTheory.Falconer.Slicing.GaussianSelectPruned
import OAI.MeasureTheory.Falconer.Slicing.GaussianPruningLedger
import OAI.MeasureTheory.Falconer.Slicing.GaussianControlledIncidence

namespace OAI

/-! # A quantitative retained slice from the proved Gaussian moment bounds -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussian_select_slice_of_budget
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {D δ ρ : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ)
    (r : ι → ℝ) (TP TD CP CD : ι → ℝ≥0∞)
    (hTP : ∀ i, 0 < TP i) (hTD : ∀ i, 0 < TD i)
    {M Q a : ℝ≥0∞} (hM : 0 < M) (hMtop : M ≠ ∞)
    (hpoint : ∀ i, (∫⁻ p : (Fin h → Space (n+1)) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows (n+1) h).prod volume) ≤ CP i)
    (hdir : ∀ i, (∫⁻ A : Fin h → Space (n+1),
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows (n+1) h) ≤ CD i)
    (hmoment : (∫⁻ A : Fin h → Space (n+1), (gaussianDirectionMass ν δ A)^2
      ∂gaussianRows (n+1) h) ≤ Q)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (hbudget : a*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ)) +
      (∑ i, (TP i)⁻¹*CP i)*M +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (TD i)⁻¹*CD i) +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(M⁻¹*Q) <
      ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*(μ.prod ν) E) :
    ∃ A ∈ gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ)),
      ∃ z ∈ coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ),
      a < gaussianPrunedIncidence μ ν δ r TP TD M E (A,z) := by
  let G := gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))
  let ξ := ((gaussianRows (n+1) h).restrict G).prod (volume : Measure (Space h))
  have hρ : 0 ≤ ρ := hδ.le.trans hδρ
  have hξ : ξ ≤ (gaussianRows (n+1) h).prod volume :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  have hlo := gaussian_controlled_incidence_mean_lower B hB μ ν E hE hδ hδρ hρ hwB
  have hraw : Measurable (fun p : (Fin h → Space (n+1)) × Space h =>
      (gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianDirectionSliceMeasure ν p.1 δ) E) :=
    gaussian_pair_restriction_mass_measurable μ ν δ (Prod.snd ⁻¹' E)
      (hE.preimage measurable_snd)
  rw [← lintegral_prod _ (show AEMeasurable
    (fun p : (Fin h → Space (n+1)) × Space h =>
      (gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianDirectionSliceMeasure ν p.1 δ) E) ξ from
        hraw.aemeasurable)] at hlo
  have hhi := gaussian_pruning_integral_loss μ ν ξ hξ hδ r TP TD CP CD hTP hTD hM hMtop
    hpoint hdir hmoment E hE
  have hlt := hbudget.trans_le (hlo.trans hhi)
  have hmean : a*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+δ)) <
      ∫⁻ p, gaussianPrunedIncidence μ ν δ r TP TD M E p ∂ξ := by
    exact lt_of_add_lt_add_right (lt_of_add_lt_add_right (lt_of_add_lt_add_right hlt))
  exact gaussian_select_pruned_slice B hB (by positivity) μ ν hμ δ r TP TD M E hmean

end Falconer

end OAI
