import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Algebra.Order.Ring.Basic

namespace OAI

/-! Adding a bounded nonnegative penalty preserves finite quadratic energy
on a finite measure space, including densities with null-set infinities. -/

open MeasureTheory
open scoped ENNReal NNReal

namespace CircleDomainRigidity

theorem ennreal_add_sq_le (a b : ℝ≥0∞) : (a+b)^2 ≤ 2 * (a^2+b^2) := by
  by_cases ha : a = ∞
  · simp [ha]
  by_cases hb : b = ∞
  · simp [hb]
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  exact_mod_cast (add_sq_le : (a+b)^2 ≤ 2 * (a^2+b^2))

theorem lintegral_add_sq_lt_top_of_bounded
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (g h : X → ℝ≥0∞) (hg : Measurable g)
    (hg₂ : (∫⁻x, g x ^ 2 ∂μ) < ∞) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hh : ∀x, h x ≤ C) : (∫⁻x, (g x + h x)^2 ∂μ) < ∞ := by
  have hpoint (x : X) : (g x + h x)^2 ≤ 2 * (g x ^ 2 + C^2) :=
    (ennreal_add_sq_le _ _).trans (mul_le_mul' le_rfl (add_le_add le_rfl (pow_le_pow_left' (hh x) 2)))
  have hbound : (∫⁻x, (g x + h x)^2 ∂μ) ≤ 2 * ((∫⁻x, g x ^ 2 ∂μ) + C^2 * μ Set.univ) := by
    calc
      _ ≤ ∫⁻x, 2 * (g x ^ 2 + C^2) ∂μ := lintegral_mono hpoint
      _ = _ := by
        have hm : Measurable (fun x => g x ^ 2 + C^2) := (hg.pow_const 2).add measurable_const
        rw [lintegral_const_mul 2 hm, lintegral_add_left (hg.pow_const 2), lintegral_const]
  exact hbound.trans_lt (ENNReal.mul_lt_top (by norm_num)
    (ENNReal.add_lt_top.mpr ⟨hg₂, ENNReal.mul_lt_top (ENNReal.pow_lt_top hC.lt_top) (measure_lt_top μ _)⟩))

end CircleDomainRigidity

end OAI
