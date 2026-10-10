import OAI.NumberTheory.CubicMoment.Estimates.LongPrimeSW

namespace OAI

/-! Polynomial losses in log X are negligible on the actual long-prime
scale exp(sqrt(log X)). This includes logarithmic prime exclusions. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

theorem long_prime_power_absorption {C D E : ℝ} (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hE : 0 ≤ E) :
    ∀ᶠ P : ℝ in atTop, ∀ T : ℝ, 1 ≤ T → T ≤ (Real.log P)^2 →
      C*T^E ≤ P/T^D := by
  have hs := ((isLittleO_log_rpow_rpow_atTop (2*(D+E))
    (by norm_num : (0:ℝ) < 1)).const_mul_left C).def zero_lt_one
  filter_upwards [hs,eventually_gt_atTop (1:ℝ)] with P hsmall hP T hT hTP
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hl : 0 < Real.log P := Real.log_pos hP
  have hbound : C*(Real.log P)^(2*(D+E)) ≤ P := by
    simpa only [Real.rpow_one,one_mul,Real.norm_of_nonneg (mul_nonneg hC
      (Real.rpow_nonneg hl.le _)),Real.norm_of_nonneg hP0.le] using hsmall
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hT0 D)).mpr
  calc
    C*T^E*T^D = C*T^(D+E) := by rw [Real.rpow_add hT0]; ring
    _ ≤ C*((Real.log P)^2)^(D+E) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hT0.le hTP (add_nonneg hD hE)) hC
    _ = C*(Real.log P)^(2*(D+E)) := by
      rw [←Real.rpow_natCast_mul hl.le 2 (D+E)]
      norm_num
    _ ≤ P := hbound

end CubicFirstMoment

end

end OAI
