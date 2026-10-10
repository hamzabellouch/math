import OAI.Analysis.CircleDomains.Probability.PhysicalOccupationCode
import OAI.Analysis.CircleDomains.Selection.SquareVisitTolls
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace OAI

/-! Weighted physical costs are integrals against the actual mean
occupation. Square bounds on the density, differential and visit weights
give the finite costs needed for the parameter-time payment measure. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem lintegral_physicalOccupationCode (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (μ : ProbabilityMeasure C(PathTime, X)) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ γ, ∫⁻ y, g y ∂physicalOccupationCode e y₀ γ ∂(μ : Measure _)) =
      ∫⁻ y, g y ∂meanPhysicalOccupation e y₀ μ := by
  exact (Measure.lintegral_bind (measurable_physicalOccupationCode e hU y₀).aemeasurable
    hg.aemeasurable).symm

theorem lintegral_physical_cost_le_square_norms (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (μ : ProbabilityMeasure C(PathTime, X)) (σ : Measure Y)
    (ρ g : Y → ℝ≥0∞) (hρ : Measurable ρ) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ μ = σ.withDensity ρ) :
    (∫⁻ γ, ∫⁻ y, g y ∂physicalOccupationCode e y₀ γ ∂(μ : Measure _)) ≤
      (∫⁻ y, ρ y ^ 2 ∂σ) ^ (1 / 2 : ℝ) * (∫⁻ y, g y ^ 2 ∂σ) ^ (1 / 2 : ℝ) := by
  rw [lintegral_physicalOccupationCode e hU y₀ μ g hg, hocc,
    lintegral_withDensity_eq_lintegral_mul _ hρ hg]
  have hconj : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  simpa only [Pi.mul_apply, ENNReal.rpow_two] using
    ENNReal.lintegral_mul_le_Lp_mul_Lq σ hconj hρ.aemeasurable hg.aemeasurable

theorem ae_physical_cost_finite (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (μ : ProbabilityMeasure C(PathTime, X)) (σ : Measure Y)
    (ρ g : Y → ℝ≥0∞) (hρ : Measurable ρ) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ μ = σ.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂σ) < ∞) (hg2 : (∫⁻ y, g y ^ 2 ∂σ) < ∞) :
    ∀ᵐ γ ∂(μ : Measure _), (∫⁻ y, g y ∂physicalOccupationCode e y₀ γ) < ∞ := by
  apply ae_lt_top ((Measure.measurable_lintegral hg).comp
    (measurable_physicalOccupationCode e hU y₀))
  exact ((lintegral_physical_cost_le_square_norms e hU y₀ μ σ ρ g hρ hg hocc).trans_lt
    (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hρ2.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hg2.ne))).ne

variable [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

theorem ae_physical_and_visit_cost_finite (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (μ : ProbabilityMeasure C(PathTime, X)) (σ : Measure Y)
    (ρ g : Y → ℝ≥0∞) (hρ : Measurable ρ) (hg : Measurable g)
    (hocc : meanPhysicalOccupation e y₀ μ = σ.withDensity ρ)
    (hρ2 : (∫⁻ y, ρ y ^ 2 ∂σ) < ∞) (hg2 : (∫⁻ y, g y ^ 2 ∂σ) < ∞)
    (m : X → ℝ≥0∞) (hm : (support m).Countable)
    (hweight : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support m => meanVisitCount μ x.val) < ∞) :
    ∀ᵐ γ ∂(μ : Measure _),
      (∫⁻ y, g y ∂physicalOccupationCode e y₀ γ) + boundaryToll γ m < ∞ := by
  filter_upwards [ae_physical_cost_finite e hU y₀ μ σ ρ g hρ hg hocc hρ2 hg2,
    ae_boundaryToll_finite μ m hm hweight hvisits] with γ hγ hγ'
  exact ENNReal.add_lt_top.mpr ⟨hγ, hγ'⟩

end CircleDomainRigidity

end

end OAI
