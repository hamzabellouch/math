import Mathlib

namespace OAI

section
section
noncomputable section
namespace Coulomb

def screenBaseMass (a : ℝ) : ℝ := max ((a^3)⁻¹) 1

lemma screenBaseMass_nonneg (a : ℝ) : 0 ≤ screenBaseMass a :=
  le_trans (by norm_num) (le_max_right _ _)

lemma screenBaseMass_ge_one (a : ℝ) : 1 ≤ screenBaseMass a := le_max_right _ _

lemma screenBaseMass_scale {a : ℝ} (ha : 0 < a) : 1 ≤ a*screenBaseMass a := by
  by_cases h : 1 ≤ a
  · calc
      1 ≤ a := h
      _ ≤ a*screenBaseMass a := le_mul_of_one_le_right ha.le (screenBaseMass_ge_one a)
  · have h' : a ≤ 1 := (lt_of_not_ge h).le
    have hpow : a^3 ≤ a := by nlinarith [sq_nonneg a,mul_nonneg ha.le (sub_nonneg.mpr h')]
    have hi : a⁻¹ ≤ (a^3)⁻¹ := (inv_le_inv₀ ha (by positivity)).2 hpow
    calc
      1 = a*a⁻¹ := (mul_inv_cancel₀ ha.ne').symm
      _ ≤ a*screenBaseMass a := mul_le_mul_of_nonneg_left (hi.trans (le_max_left _ _)) ha.le

lemma screenBaseMass_cuberoot_scale {a : ℝ} (ha : 0 < a) :
    1 ≤ a*(screenBaseMass a)^(1/3:ℝ) := by
  have hi : ((a^3)⁻¹)^(1/3:ℝ) = a⁻¹ := by
    rw [Real.inv_rpow (pow_nonneg ha.le 3),←Real.rpow_natCast a 3,←Real.rpow_mul ha.le]
    norm_num
  calc
    1 = a*((a^3)⁻¹)^(1/3:ℝ) := by rw [hi,mul_inv_cancel₀ ha.ne']
    _ ≤ a*(screenBaseMass a)^(1/3:ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (le_max_left _ _) (by norm_num)) ha.le

end Coulomb
end

end
end

end OAI
