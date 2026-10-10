import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem bounded_test_comparison_weighted {X X' Y : Type*}
    [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure X') (F : X → Y) (G : X' → Y) {ε : ℝ}
    (hcompare : ∀ f : Y → ℝ, Measurable f → (∀ y, ‖f y‖ ≤ 1) →
      |(∫ x, f (F x) ∂μ) - ∫ x, f (G x) ∂ν| ≤ ε)
    (w : Y → ℝ) (hw : Measurable w) {B : ℝ} (hB : 0 ≤ B) (hcap : ∀ y, ‖w y‖ ≤ B)
    (f : Y → ℝ) (hf : Measurable f) (hbound : ∀ y, ‖f y‖ ≤ 1) :
    |(∫ x, w (F x) * f (F x) ∂μ) - ∫ x, w (G x) * f (G x) ∂ν| ≤ B * ε := by
  by_cases hB0 : B = 0
  · have hw0 : w = 0 := by
      funext y
      exact norm_eq_zero.mp (le_antisymm (by simpa only [hB0] using hcap y) (norm_nonneg _))
    simp [hB0, hw0]
  have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  have hnorm (y : Y) : ‖w y * f y / B‖ ≤ 1 := by
    rw [norm_div, norm_mul, Real.norm_eq_abs B, abs_of_pos hBpos]
    apply (div_le_one hBpos).mpr
    simpa only [mul_one] using mul_le_mul (hcap y) (hbound y) (norm_nonneg _) hB
  have he := hcompare (fun y => w y * f y / B) ((hw.mul hf).div_const B) hnorm
  simp only [integral_div] at he
  rw [← sub_div, abs_div, abs_of_pos hBpos] at he
  simpa only [mul_comm] using (div_le_iff₀ hBpos).mp he

end Erdos3

end

end OAI
