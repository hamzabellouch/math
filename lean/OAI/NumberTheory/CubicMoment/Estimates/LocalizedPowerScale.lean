import OAI.NumberTheory.CubicMoment.Estimates.ThinCellNormalized

namespace OAI

/-! The finite derivative cost of log-cell localization is absorbed at a
fixed positive power scale, without a lower bound near A = Z². -/
noncomputable section
namespace CubicFirstMoment

lemma thinCellExponent_le (d : ℕ) : thinCellExponent d ≤ 1/240000 := by
  unfold thinCellExponent
  apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
  nlinarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]

lemma localized_height_ratio {J T : ℝ} (hJ : 1 ≤ J) (hT : J^2 ≤ T) :
    J*(J/T)^2 ≤ 1 := by
  have hJp : 0 < J := by linarith
  have hTp : 0 < T := (sq_pos_of_pos hJp).trans_le hT
  have he : J*(J/T)^2 = J^3/T^2 := by field_simp
  rw [he]
  apply (div_le_one (sq_pos_of_pos hTp)).mpr
  have hh := pow_le_pow_left₀ (sq_nonneg J) hT 2
  have hj := mul_nonneg (pow_nonneg hJp.le 3) (sub_nonneg.mpr hJ)
  nlinarith

lemma localized_remainder_scale (d : ℕ) {Z A : ℝ} (hZ : 1 ≤ Z) (hA : 0 ≤ A) :
    (Z^(thinCellExponent d))^d*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ) ≤
      A^(2/3:ℝ)*Z^(2/3-2*thinCellExponent d/3) := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hJ : 1 ≤ Z^(thinCellExponent d) := Real.one_le_rpow hZ (thinCellExponent_pos d).le
  have hp := pow_le_pow_right₀ hJ (Nat.le_succ d)
  rw [thinCellScale_power d hZp] at hp
  have hex : (1/240000:ℝ)+(2/3-1/80000) ≤ 2/3-2*thinCellExponent d/3 := by
    linarith [thinCellExponent_le d]
  calc
    _ ≤ Z^(1/240000:ℝ)*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (by positivity)) (by positivity)
    _ = A^(2/3:ℝ)*Z^((1/240000:ℝ)+(2/3-1/80000)) := by rw [Real.rpow_add hZp]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hex) (Real.rpow_nonneg hA _)

lemma localized_root_scale (d : ℕ) {Z A : ℝ} (hZ : 1 ≤ Z) (hA : 0 < A)
    (hupper : A ≤ Z^(2+thinCellExponent d)) :
    Real.sqrt (A/Z^(thinCellExponent d))+
      Real.sqrt ((Z^(thinCellExponent d))^d*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)) ≤
      2*Real.sqrt (A^(2/3:ℝ)*Z^(2/3-2*thinCellExponent d/3)) := by
  have ha := Real.sqrt_le_sqrt (thinCell_outer_scale (zero_lt_one.trans_le hZ) hA hupper)
  have hb := Real.sqrt_le_sqrt (localized_remainder_scale d hZ hA.le)
  linarith

lemma localized_height_power (d : ℕ) {Z T : ℝ} (hZ : 1 ≤ Z)
    (hT : Z^(1/50:ℝ) ≤ T) : (Z^(thinCellExponent d))^2 ≤ T := by
  rw [←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans hZ)]
  exact (Real.rpow_le_rpow_of_exponent_le hZ
    (by norm_num; linarith [thinCellExponent_le d])).trans hT

end CubicFirstMoment

end

end OAI
