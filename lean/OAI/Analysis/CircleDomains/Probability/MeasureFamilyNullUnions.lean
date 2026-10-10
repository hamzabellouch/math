import OAI.Analysis.CircleDomains.Probability.MeasureFamilyModulusBasic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

namespace OAI

/-! Countable unions of pointwise zero-modulus families have zero modulus.
The admissible density is the square root of the sum of the squared
individual densities, so the argument keeps every family member. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma measureFamilyModulus_zero_of_countable_cover
    {A Z ι : Type*} [MeasurableSpace Z] [Countable ι]
    (σ : Measure Z) (K : A → FiniteMeasure Z) (S : ι → Set A)
    (hcover : ∀ a, ∃ i, a ∈ S i)
    (hz : ∀ i, measureFamilyModulus (S i) Z σ (fun a => K a.val) = 0) :
    measureFamilyModulus A Z σ K = 0 := by
  classical
  apply (measureFamilyModulus_zero_iff σ K).mpr
  intro ε hε
  obtain ⟨b,hb,hbsum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ι
  have hex (i : ι) := (measureFamilyModulus_zero_iff σ (fun a : S i => K a.val)).mp
    (hz i) (b i) (hb i)
  choose g hgm hga hge using hex
  let h : Z → ℝ≥0∞ := fun z => (∑' i, g i z ^ 2) ^ (1/2 : ℝ)
  have hh : Measurable h := (Measurable.tsum (fun i => (hgm i).pow_const 2)).pow_const (1/2 : ℝ)
  have hsq (z : Z) : h z ^ 2 = ∑' i, g i z ^ 2 := by
    dsimp only [h]
    rw [← ENNReal.rpow_two,← ENNReal.rpow_mul]
    norm_num
  have hdom (i : ι) (z : Z) : g i z ≤ h z := by
    have he : (g i z ^ 2) ^ (1/2 : ℝ) = g i z := by
      rw [← ENNReal.rpow_two,← ENNReal.rpow_mul]
      norm_num
    rw [← he]
    exact ENNReal.rpow_le_rpow (ENNReal.le_tsum (f := fun j => g j z ^ 2) i) (by norm_num)
  refine ⟨h,hh,?_,?_⟩
  · intro a
    obtain ⟨i,hai⟩ := hcover a
    exact (hga i ⟨a,hai⟩).trans (lintegral_mono (hdom i))
  · simp_rw [hsq]
    rw [lintegral_tsum (fun i => ((hgm i).pow_const 2).aemeasurable)]
    exact (ENNReal.tsum_le_tsum (fun i => (hge i).le)).trans_lt hbsum

end CircleDomainRigidity

end

end OAI
