import OAI.Analysis.CircleDomains.Probability.DensityMassBound
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

namespace OAI

/-! Recover the pointwise density bound from domination of actual measures. -/

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MeasurableSpace X]

theorem exists_density_le_of_domination (σ ν : Measure X) [SigmaFinite σ] [SigmaFinite ν]
    (g : X → ℝ≥0∞) (h : ν ≤ σ.withDensity g) :
    ∃ f : X → ℝ≥0∞, Measurable f ∧ ν = σ.withDensity f ∧ f ≤ᵐ[σ] g := by
  have hac : ν ≪ σ := (Measure.absolutelyContinuous_of_le h).trans (withDensity_absolutelyContinuous σ g)
  refine ⟨ν.rnDeriv σ, Measure.measurable_rnDeriv ν σ,
    (Measure.withDensity_rnDeriv_eq ν σ hac).symm, ?_⟩
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv ν σ)
  intro S hS _
  rw [← withDensity_apply _ hS, ← withDensity_apply _ hS]
  exact (Measure.withDensity_rnDeriv_le ν σ S).trans (h S)

theorem exists_localized_density_of_square_domination (σ ν : Measure X) [IsFiniteMeasure σ]
    (g : X → ℝ≥0∞) (hg : Measurable g) (he : (∫⁻ x, g x ^ 2 ∂σ) < ∞)
    (W : Set X) (hW : MeasurableSet W)
    (h : ν ≤ (2 : ℝ≥0∞) • (σ.withDensity g).restrict W) :
    ∃ f : X → ℝ≥0∞, Measurable f ∧ ν = σ.withDensity f ∧
      f ≤ᵐ[σ] (fun x => 2 * W.indicator g x) := by
  have hmass : (σ.withDensity g) univ < ∞ :=
    (mass_le_densityMassBound σ hg le_rfl).trans_lt (densityMassBound_lt_top σ he)
  let : IsFiniteMeasure (σ.withDensity g) := ⟨hmass⟩
  have hfin : ((2 : ℝ≥0∞) • (σ.withDensity g).restrict W) univ < ∞ := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (by norm_num) (measure_lt_top _ _)
  let : IsFiniteMeasure ν := ⟨(h univ).trans_lt hfin⟩
  apply exists_density_le_of_domination σ ν (fun x => 2 * W.indicator g x)
  convert h using 1
  change σ.withDensity ((2 : ℝ≥0∞) • W.indicator g) = _
  rw [withDensity_smul 2 (hg.indicator hW), withDensity_indicator hW,
    restrict_withDensity hW]

end CircleDomainRigidity

end

end OAI
