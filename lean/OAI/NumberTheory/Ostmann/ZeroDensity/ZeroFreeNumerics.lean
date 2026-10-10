import OAI.NumberTheory.Ostmann.ZeroDensity.RealZeroKernel

namespace OAI

/-! # Concrete kernel comparisons for the low-height zero-free region -/

namespace Ostmann

theorem real_zero_near_mass (δ a y : ℝ) (hδ : 0 < δ) (ha : δ ≤ a)
    (ha' : a ≤ (21 / 20) * δ) (hy : |y| ≤ δ / 2) :
    7 / 10 ≤ δ * realZeroKernel a y := by
  have ha0 : 0 < a := hδ.trans_le ha
  have hden : 0 < a ^ 2 + y ^ 2 := by positivity
  have hasq : a ^ 2 ≤ ((21 / 20) * δ) ^ 2 := by nlinarith
  have hysq : y ^ 2 ≤ (δ / 2) ^ 2 := by
    nlinarith [sq_abs y, abs_nonneg y]
  have had : δ ^ 2 ≤ δ * a := by nlinarith
  unfold realZeroKernel
  rw [← mul_div_assoc, le_div_iff₀ hden]
  nlinarith [sq_pos_of_pos hδ]

theorem real_zero_double_height_mass (δ t : ℝ) (hδ : 0 < δ) (ht : δ / 2 ≤ |t|) :
    δ * realZeroKernel δ (2 * t) ≤ 1 / 2 := by
  have hden : 0 < δ ^ 2 + (2 * t) ^ 2 := by positivity
  have htsq : δ ^ 2 / 4 ≤ t ^ 2 := by nlinarith [sq_abs t]
  unfold realZeroKernel
  rw [← mul_div_assoc, div_le_iff₀ hden]
  nlinarith

theorem real_zero_shifted_mass (δ a : ℝ) (hδ : 0 < δ) (ha : δ ≤ a)
    (ha' : a ≤ (21 / 20) * δ) : 18 / 5 < δ * (4 / a) := by
  have ha0 : 0 < a := hδ.trans_le ha
  rw [← mul_div_assoc, lt_div_iff₀ ha0]
  nlinarith

end Ostmann

end OAI
