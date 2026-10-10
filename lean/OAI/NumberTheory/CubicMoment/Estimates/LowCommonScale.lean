import OAI.NumberTheory.CubicMoment.Estimates.LowNormScale

namespace OAI

/-! The residual norm factor is summable; it is retained through the
common-divisor decomposition instead of discarded by monotonicity. -/
noncomputable section
namespace CubicFirstMoment

lemma low_common_residual_scale {A Z r d : ℝ} (j : ℕ)
    (hA : 0 ≤ A) (hZ : 1 ≤ Z) (hr : 0 < r) (hd : 1 ≤ d)
    (hrZ : r ≤ Z^(1/2:ℝ)) :
    (A/d)^(2/3:ℝ)*(Z/r)^(5/3:ℝ)/(1+Real.log (Z/r))^j ≤
      (2:ℝ)^j*A^(2/3:ℝ)*Z^(5/3:ℝ)*r^(-(5/3:ℝ))/(1+Real.log Z)^j := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hrZ' : r ≤ Z := hrZ.trans (by
    calc
      Z^(1/2:ℝ) ≤ Z^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
      _ = Z := Real.rpow_one Z)
  have hratio : 1 ≤ Z/r := (le_div_iff₀ hr).mpr (by simpa using hrZ')
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ]
  have hR : 0 < 1+Real.log (Z/r) := by linarith [Real.log_nonneg hratio]
  have hlogs : (1+Real.log Z)^j ≤ (2:ℝ)^j*(1+Real.log (Z/r))^j := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ hL.le (residual_log_comparison hZ hr hrZ) j
  have houter : (A/d)^(2/3:ℝ) ≤ A^(2/3:ℝ) :=
    Real.rpow_le_rpow (div_nonneg hA (by linarith)) (div_le_self hA hd) (by norm_num)
  have hquot : (Z/r)^(5/3:ℝ) = Z^(5/3:ℝ)*r^(-(5/3:ℝ)) := by
    rw [Real.div_rpow hZp.le hr.le,Real.rpow_neg hr.le,div_eq_mul_inv]
  apply (div_le_div_iff₀ (pow_pos hR _) (pow_pos hL _)).mpr
  rw [hquot]
  calc
    _ ≤ (A^(2/3:ℝ)*(Z^(5/3:ℝ)*r^(-(5/3:ℝ))))*(1+Real.log Z)^j := by
      gcongr
    _ ≤ (A^(2/3:ℝ)*(Z^(5/3:ℝ)*r^(-(5/3:ℝ))))*
        ((2:ℝ)^j*(1+Real.log (Z/r))^j) :=
      mul_le_mul_of_nonneg_left hlogs (by positivity)
    _ = _ := by ring

lemma low_common_floor_large {Z r : ℝ} (hZ : (65536:ℝ)^2 ≤ Z)
    (hr : 0 < r) (hrZ : r ≤ Z^(1/2:ℝ)) :
    65536 ≤ (⌊Z/r⌋₊:ℝ) ∧ 16 ≤ (⌊Z/r⌋₊:ℝ)^(3/4:ℝ) := by
  have hZp : 0 < Z := by nlinarith
  have hroot : 65536 ≤ Z^(1/2:ℝ) := by
    rw [←Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt hZp.le,Real.sqrt_nonneg Z]
  have hratio : Z^(1/2:ℝ) ≤ Z/r := by
    calc
      _ = Z/Z^(1/2:ℝ) := by
        have hh := Real.rpow_sub hZp (1:ℝ) (1/2:ℝ)
        norm_num at hh
        exact hh
      _ ≤ _ := div_le_div_of_nonneg_left hZp.le hr hrZ
  have hf : 65536 ≤ ⌊Z/r⌋₊ := Nat.le_floor (by exact_mod_cast hroot.trans hratio)
  have hfr : (65536:ℝ) ≤ (⌊Z/r⌋₊:ℝ) := by exact_mod_cast hf
  refine ⟨hfr,?_⟩
  have hs : 16 ≤ (⌊Z/r⌋₊:ℝ)^(1/2:ℝ) := by
    rw [←Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (show 0 ≤ (⌊Z/r⌋₊:ℝ) by positivity),
      Real.sqrt_nonneg (⌊Z/r⌋₊:ℝ)]
  exact hs.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))

end CubicFirstMoment

end

end OAI
