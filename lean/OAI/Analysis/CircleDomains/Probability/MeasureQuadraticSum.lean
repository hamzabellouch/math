import OAI.Analysis.CircleDomains.Probability.MeasureFamilyModulusBasic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

namespace OAI

/-! A countable square-sum of extended nonnegative densities. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_quadratic_sum_density {Z ι : Type*} [MeasurableSpace Z] [Countable ι]
    (σ : Measure Z) (g : ι → Z → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    ∃ h : Z → ℝ≥0∞, Measurable h ∧ (∀ i z, g i z ≤ h z) ∧
      (∫⁻ z, h z ^ 2 ∂σ) = ∑' i, ∫⁻ z, g i z ^ 2 ∂σ := by
  let h : Z → ℝ≥0∞ := fun z => (∑' i, g i z ^ 2) ^ (1/2 : ℝ)
  have hh : Measurable h :=
    (Measurable.tsum (fun i => (hg i).pow_const 2)).pow_const (1/2 : ℝ)
  have hsq (z : Z) : h z ^ 2 = ∑' i, g i z ^ 2 := by
    dsimp only [h]
    rw [← ENNReal.rpow_two,← ENNReal.rpow_mul]
    norm_num
  refine ⟨h,hh,?_,?_⟩
  · intro i z
    have he : (g i z ^ 2) ^ (1/2 : ℝ) = g i z := by
      rw [← ENNReal.rpow_two,← ENNReal.rpow_mul]
      norm_num
    rw [← he]
    exact ENNReal.rpow_le_rpow (ENNReal.le_tsum (f := fun j => g j z ^ 2) i) (by norm_num)
  · simp_rw [hsq]
    exact lintegral_tsum (fun i => ((hg i).pow_const 2).aemeasurable)

end CircleDomainRigidity

end

end OAI
