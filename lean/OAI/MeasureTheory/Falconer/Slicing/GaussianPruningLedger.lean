import OAI.MeasureTheory.Falconer.Slicing.GaussianPrunedIncidence
import OAI.MeasureTheory.Falconer.Slicing.GaussianPruningCosts

namespace OAI

/-! # The combined incidence ledger for the three marginal slice deletions -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

theorem gaussian_pruning_integral_loss
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ξ : Measure ((Fin h → Space d) × Space h)) (hξ : ξ ≤ (gaussianRows d h).prod volume)
    {δ : ℝ} (hδ : 0 < δ) (r : ι → ℝ) (TP TD CP CD : ι → ℝ≥0∞)
    (hTP : ∀ i, 0 < TP i) (hTD : ∀ i, 0 < TD i)
    {M B : ℝ≥0∞} (hM : 0 < M) (hMtop : M ≠ ∞)
    (hpoint : ∀ i, (∫⁻ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianPointSliceMeasure μ p.1 p.2 δ))
        {z | dist z.1 z.2 < 2*r i} ∂(gaussianRows d h).prod volume) ≤ CP i)
    (hdir : ∀ i, (∫⁻ A : Fin h → Space d,
      ((gaussianDirectionSliceMeasure ν A δ).prod (gaussianDirectionSliceMeasure ν A δ))
        {z | dist z.1 z.2 < 2*r i} ∂gaussianRows d h) ≤ CD i)
    (hmoment : (∫⁻ A : Fin h → Space d, (gaussianDirectionMass ν δ A)^2 ∂gaussianRows d h) ≤ B)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E) :
    (∫⁻ p : (Fin h → Space d) × Space h,
      (gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianDirectionSliceMeasure ν p.1 δ) E ∂ξ) ≤
      (∫⁻ p, gaussianPrunedIncidence μ ν δ r TP TD M E p ∂ξ) +
      (∑ i, (TP i)⁻¹*CP i)*M +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (TD i)⁻¹*CD i) +
      (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(M⁻¹*B) := by
  let f := gaussianPrunedIncidence (h := h) μ ν δ r TP TD M E
  let a := fun p : (Fin h → Space d) × Space h =>
    gaussianPointSliceMeasure μ p.1 p.2 δ (gaussianPointGood μ δ r TP p)ᶜ*M
  let b := fun p : (Fin h → Space d) × Space h => gaussianPointMass μ δ p*
    gaussianDirectionSliceMeasure ν p.1 δ (finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r TD)ᶜ
  let c := fun p : (Fin h → Space d) × Space h =>
    if M < gaussianDirectionMass ν δ p.1 then gaussianPointMass μ δ p*gaussianDirectionMass ν δ p.1 else 0
  have hf : Measurable f := gaussianPrunedIncidence_measurable μ ν δ r TP TD M E hE
  have ha : Measurable a := (gaussian_point_good_compl_mass_measurable μ δ r TP).mul_const M
  have hb : Measurable b := (gaussianPointMass_measurable μ δ).mul
    ((gaussian_direction_good_compl_mass_measurable ν δ r TD).comp measurable_fst)
  have hia : (∫⁻ p, a p ∂ξ) ≤ (∑ i, (TP i)⁻¹*CP i)*M :=
    (lintegral_mono' hξ le_rfl).trans (gaussian_point_pruning_incidence_cost μ δ r TP CP hTP M hpoint)
  have hib : (∫⁻ p, b p ∂ξ) ≤ (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(∑ i, (TD i)⁻¹*CD i) :=
    (lintegral_mono' hξ le_rfl).trans (gaussian_direction_pruning_incidence_cost μ ν hδ r TD CD hTD hdir)
  have hic : (∫⁻ p, c p ∂ξ) ≤ (ENNReal.ofReal ((2:ℝ)^h)*μ univ)*(M⁻¹*B) := by
    apply (lintegral_mono' hξ le_rfl).trans
    simpa only [c,mul_ite,mul_zero] using gaussian_mass_pruning_incidence_cost μ ν hδ hM hMtop hmoment
  calc
    _ ≤ ∫⁻ p, f p+a p+b p+c p ∂ξ :=
      lintegral_mono (fun p => gaussian_pruning_pointwise_loss μ ν δ r TP TD M E hE p)
    _ = ((∫⁻ p, f p ∂ξ)+(∫⁻ p, a p ∂ξ))+(∫⁻ p, b p ∂ξ)+(∫⁻ p, c p ∂ξ) := by
      rw [lintegral_add_left (show Measurable (fun p => f p+a p+b p) from (hf.add ha).add hb),
        lintegral_add_left (show Measurable (fun p => f p+a p) from hf.add ha),lintegral_add_left hf]
    _ ≤ _ := add_le_add (add_le_add (add_le_add le_rfl hia) hib) hic

end Falconer

end OAI
