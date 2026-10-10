import OAI.NumberTheory.CubicMoment.Estimates.SmallBRealLength

namespace OAI

/-! The small-B scale remains valid after the exact common-factor and
Möbius changes of variables. -/
noncomputable section
namespace CubicFirstMoment

lemma smallB_common_outer_scale {Z A k m : ℝ} (hZ : 0 ≤ Z)
    (hk : 1 ≤ k) (hm : 0 < m) (hmk : m ≤ k) (hA : Z^(3/2:ℝ) ≤ A) :
    (Z/k)^(3/2:ℝ) ≤ A/m := by
  have hkp : 0 < k := zero_lt_one.trans_le hk
  have hkpw : k ≤ k^(3/2:ℝ) := by
    calc
      k = k^(1:ℝ) := (Real.rpow_one k).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hk (by norm_num)
  rw [Real.div_rpow hZ hkp.le]
  exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hZ _) hm (hmk.trans hkpw)).trans
    (div_le_div_of_nonneg_right hA hm.le)

lemma smallB_common_height_scale {Z T k : ℝ} (hZ : 0 ≤ Z) (hk : 1 ≤ k)
    (hT : Z^(1/50:ℝ) ≤ T) : (Z/k)^(1/50:ℝ) ≤ T := by
  exact (Real.rpow_le_rpow (by positivity)
    (div_le_self hZ hk) (by norm_num)).trans hT

lemma smallB_common_bound_scale {Z A k m : ℝ} (hZ : 0 ≤ Z) (hA : 0 ≤ A)
    (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (A/m)^(2/3:ℝ)*(Z/k)^(2/3-1/40000:ℝ) ≤
      A^(2/3:ℝ)*Z^(2/3-1/40000:ℝ) := by
  exact mul_le_mul
    (Real.rpow_le_rpow (by positivity) (div_le_self hA hm) (by norm_num))
    (Real.rpow_le_rpow (by positivity) (div_le_self hZ hk) (by norm_num))
    (by positivity) (by positivity)

end CubicFirstMoment

end

end OAI
