import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarForcing

namespace OAI

/-! An explicit global modulus for the forcing used by the numerical
quadrature. Unlike an unspecified compact-support derivative bound, the
constant is a fixed integer usable by the literal sample-count program. -/

noncomputable section
namespace ContinuumCoulomb

theorem clippedSquare_formula {r : ℝ} (hr : 0 ≤ r) :
    max (1 - r ^ 2) 0 = 1 - (min r 1) ^ 2 := by
  by_cases h : r ≤ 1
  · rw [min_eq_left h, max_eq_left]
    nlinarith
  · rw [min_eq_right (le_of_not_ge h), max_eq_right]
    · norm_num
    · nlinarith

theorem clippedSquare_lipschitz {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |max (1 - r ^ 2) 0 - max (1 - s ^ 2) 0| ≤ 2 * |r - s| := by
  have har : 0 ≤ min r 1 := le_min hr zero_le_one
  have hbr : 0 ≤ min s 1 := le_min hs zero_le_one
  have hau : min r 1 ≤ 1 := min_le_right _ _
  have hbu : min s 1 ≤ 1 := min_le_right _ _
  have hmin : |min r 1 - min s 1| ≤ |r - s| := by
    simpa only [max_neg_neg, neg_sub_neg, abs_sub_comm] using
      abs_max_sub_max_le_abs (-r) (-s) (-1)
  rw [clippedSquare_formula hr, clippedSquare_formula hs]
  have heq : (1 - min r 1 ^ 2) - (1 - min s 1 ^ 2) =
      (min s 1 - min r 1) * (min s 1 + min r 1) := by ring
  rw [heq, abs_mul, abs_of_nonneg (add_nonneg hbr har), abs_sub_comm (min s 1) (min r 1)]
  have hsum : min s 1 + min r 1 ≤ 2 := by linarith
  calc
    _ ≤ |min r 1 - min s 1| * 2 :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ ≤ |r - s| * 2 := mul_le_mul_of_nonneg_right hmin (by norm_num)
    _ = _ := by ring

theorem planarForcing_norm_sub_explicit (x y : PlanarPosition) :
    |planarForcing x - planarForcing y| ≤ 32 * ‖x - y‖ := by
  let a := max (1 - ‖x‖ ^ 2) 0
  let b := max (1 - ‖y‖ ^ 2) 0
  have ha0 : 0 ≤ a := le_max_right _ _
  have hb0 : 0 ≤ b := le_max_right _ _
  have ha1 : a ≤ 1 := max_le (by nlinarith [sq_nonneg ‖x‖]) zero_le_one
  have hb1 : b ≤ 1 := max_le (by nlinarith [sq_nonneg ‖y‖]) zero_le_one
  have hab : |a - b| ≤ 2 * |‖x‖ - ‖y‖| :=
    clippedSquare_lipschitz (norm_nonneg x) (norm_nonneg y)
  have hm : max |a| |b| ≤ 1 := by
    rw [abs_of_nonneg ha0, abs_of_nonneg hb0]
    exact max_le ha1 hb1
  have hp := abs_pow_sub_pow_le a b 16
  have hp' : |a ^ 16 - b ^ 16| ≤ |a - b| * 16 := by
    calc
      _ ≤ |a - b| * 16 * max |a| |b| ^ (16 - 1) := hp
      _ ≤ |a - b| * 16 * 1 := mul_le_mul_of_nonneg_left
        (by simpa using pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg a)) hm 15)
        (by positivity)
      _ = _ := mul_one _
  change |a ^ 16 - b ^ 16| ≤ _
  have hnorm := abs_norm_sub_norm_le x y
  nlinarith

end ContinuumCoulomb

end

end OAI
