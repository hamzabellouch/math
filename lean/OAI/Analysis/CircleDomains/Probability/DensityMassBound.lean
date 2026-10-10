import OAI.Analysis.CircleDomains.Probability.BorelDensityBudget
import Mathlib.MeasureTheory.Integral.MeanInequalities

namespace OAI

/-! A finite reference measure turns the square-density estimate into the
uniform mass cap needed for the Borel family of candidate laws. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MeasurableSpace X]

def densityMassBound (σ : Measure X) (energy : ℝ≥0∞) : ℝ≥0∞ :=
  energy ^ (1 / 2 : ℝ) * (σ univ) ^ (1 / 2 : ℝ)

theorem densityMassBound_lt_top (σ : Measure X) [IsFiniteMeasure σ]
    {energy : ℝ≥0∞} (henergy : energy < ∞) : densityMassBound σ energy < ∞ := by
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) henergy.ne)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top σ univ))

theorem mass_le_densityMassBound (σ : Measure X) {g : X → ℝ≥0∞}
    (hg : Measurable g) {energy : ℝ≥0∞} (henergy : (∫⁻ x, g x ^ 2 ∂σ) ≤ energy) :
    (σ.withDensity g) univ ≤ densityMassBound σ energy := by
  have hconj : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq σ hconj hg.aemeasurable
    (g := fun _ => 1) measurable_const.aemeasurable
  have hb : (∫⁻ x, g x ∂σ) ≤
      (∫⁻ x, g x ^ 2 ∂σ) ^ (1 / 2 : ℝ) * (σ univ) ^ (1 / 2 : ℝ) := by
    simpa [Pi.mul_apply, ENNReal.rpow_two] using h
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  exact hb.trans (mul_le_mul' (ENNReal.rpow_le_rpow henergy (by norm_num)) le_rfl)

theorem boundedDensityBudget_of_square_bound (σ : Measure X) (μ : Measure X)
    {g : X → ℝ≥0∞} (hg : Measurable g) (hμ : μ = σ.withDensity g)
    {energy : ℝ≥0∞} (henergy : (∫⁻ x, g x ^ 2 ∂σ) ≤ energy) :
    BoundedDensityBudget σ μ (densityMassBound σ energy) energy := by
  refine ⟨?_, g, hg, hμ, henergy⟩
  rw [hμ]
  exact mass_le_densityMassBound σ hg henergy

end CircleDomainRigidity

end

end OAI
