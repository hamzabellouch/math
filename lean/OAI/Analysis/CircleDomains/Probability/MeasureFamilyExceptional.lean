import OAI.Analysis.CircleDomains.Probability.MeasureFamilyModulusBasic
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace OAI

/-! Fuglede's elementary exceptional-family estimate: an L² reference
density has infinite integral only along a family of zero pointwise modulus. -/
open Set Function MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

variable {A Z : Type*} [MeasurableSpace Z]

lemma measureFamilyModulus_zero_of_infinite_integral
    (σ : Measure Z) (K : A → FiniteMeasure Z) {g : Z → ℝ≥0∞}
    (hg : Measurable g) (hE : (∫⁻ z, g z ^ 2 ∂σ) ≠ ∞)
    (hK : ∀ a, ∫⁻ z, g z ∂(K a : Measure Z) = ∞) :
    measureFamilyModulus A Z σ K = 0 := by
  by_contra hm
  obtain ⟨δ,hδ,hsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt hE hm
  let c : ℝ≥0 := min δ 1
  have hc : 0 < c := lt_min hδ zero_lt_one
  have hc2 : c ^ 2 ≤ δ := by
    have hc1 : c ≤ 1 := min_le_right _ _
    have hcδ : c ≤ δ := min_le_left _ _
    calc
      c ^ 2 = c*c := pow_two c
      _ ≤ c := mul_le_of_le_one_right (show (0 : ℝ≥0) ≤ c from zero_le) hc1
      _ ≤ δ := hcδ
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  let h : Z → ℝ≥0∞ := fun z => c * g z
  have hh : Measurable h := measurable_const.mul hg
  have ha (a : A) : 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z) := by
    rw [lintegral_const_mul _ hg,hK a,ENNReal.mul_top hc0]
    exact le_top
  have he : ∫⁻ z, h z ^ 2 ∂σ = (c : ℝ≥0∞)^2 * ∫⁻ z, g z ^ 2 ∂σ := by
    simp only [h,mul_pow]
    exact lintegral_const_mul _ (hg.pow_const 2)
  have hb := measureFamilyModulus_le_admissible σ K hh ha
  rw [he] at hb
  have hc2' : (c : ℝ≥0∞)^2 ≤ δ := by exact_mod_cast hc2
  exact (not_lt_of_ge (hb.trans (mul_le_mul_left hc2' _))) hsmall

end CircleDomainRigidity

end

end OAI
