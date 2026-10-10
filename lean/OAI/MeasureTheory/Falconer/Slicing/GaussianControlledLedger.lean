import OAI.MeasureTheory.Falconer.Slicing.GaussianPruningLedger
import OAI.MeasureTheory.Falconer.Slicing.GaussianControlledIncidence

namespace OAI

/-! # Original incidence survives controlled-row marginal pruning -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussian_controlled_pruning_ledger
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ)
    (r : ι → ℝ) (TP TD CP CD : ι → ℝ≥0∞)
    (hTP : ∀ i, 0 < TP i) (hTD : ∀ i, 0 < TD i)
    {M Q : ℝ≥0∞} (hM : 0 < M) (hMtop : M ≠ ∞)
    (hpoint : ∀ i, (∫⁻ p : (Fin h → Space (n+1)) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows (n+1) h).prod volume) ≤ CP i)
    (hdir : ∀ i, (∫⁻ A : Fin h → Space (n+1),
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows (n+1) h) ≤ CD i)
    (hmoment : (∫⁻ A : Fin h → Space (n+1), (gaussianDirectionMass ν δ A)^2
      ∂gaussianRows (n+1) h) ≤ Q)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E) :
    ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*(μ.prod ν) E ≤
      (∫⁻ p, gaussianPrunedIncidence μ ν δ r TP TD M E p
        ∂((gaussianRows (n+1) h).restrict
          (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ)))).prod volume) +
      (∑ i, (TP i)⁻¹*CP i)*M +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (TD i)⁻¹*CD i) +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(M⁻¹*Q) := by
  let G := gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))
  let ξ := ((gaussianRows (n+1) h).restrict G).prod (volume : Measure (Space h))
  have hlo := gaussian_controlled_incidence_mean_lower B hB μ ν E hE hδ hδρ
    (hδ.le.trans hδρ) hwB
  have hraw : Measurable (fun p : (Fin h → Space (n+1)) × Space h =>
      (gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianDirectionSliceMeasure ν p.1 δ) E) :=
    gaussian_pair_restriction_mass_measurable μ ν δ (Prod.snd ⁻¹' E) (hE.preimage measurable_snd)
  rw [← lintegral_prod _ (show AEMeasurable
    (fun p : (Fin h → Space (n+1)) × Space h =>
      (gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianDirectionSliceMeasure ν p.1 δ) E) ξ
      from hraw.aemeasurable)] at hlo
  exact hlo.trans (gaussian_pruning_integral_loss μ ν ξ
    (Measure.prod_mono Measure.restrict_le_self le_rfl) hδ r TP TD CP CD hTP hTD hM hMtop
    hpoint hdir hmoment E hE)

end Falconer

end OAI
