import OAI.NumberTheory.CubicMoment.Estimates.TypeIMixedScale

namespace OAI

/-! The actual early-stopped bilinear range automatically satisfies the
level condition of the published Type-I estimate. -/
noncomputable section
namespace CubicFirstMoment

lemma stopped_mixed_level {b A : ℝ} (hb : 2 ≤ b) (hA : b^(3/2:ℝ) ≤ A) :
    1 ≤ A ∧ 2 ≤ (b/2)*A ∧ b/2 ≤ ((b/2)*A)^(51/100:ℝ) := by
  have hb1 : 1 ≤ b := by linarith
  have hbp : 0 < b := by linarith
  have hbpower : b ≤ b^(3/2:ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hb1 (show (1:ℝ) ≤ 3/2 by norm_num)
  have hbA : b ≤ A := hbpower.trans hA
  have hr : 1 ≤ b/2 := by linarith
  have hrp : 0 < b/2 := zero_lt_one.trans_le hr
  have hprod : (b/2)^2 ≤ (b/2)*A := by nlinarith
  refine ⟨hb1.trans hbA,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hbA hrp.le
    nlinarith
  · calc
      _ ≤ (b/2)^((2:ℝ)*(51/100)) := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hr (show (1:ℝ) ≤ 2*(51/100) by norm_num)
      _ = ((b/2)^2)^(51/100:ℝ) := by rw [←Real.rpow_natCast (b/2) 2,←Real.rpow_mul hrp.le]; norm_num
      _ ≤ _ := Real.rpow_le_rpow (sq_nonneg _) hprod (by norm_num)

end CubicFirstMoment

end

end OAI
