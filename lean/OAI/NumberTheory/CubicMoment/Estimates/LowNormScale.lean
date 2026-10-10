import OAI.NumberTheory.CubicMoment.Estimates.LowHeightLogScale

namespace OAI

/-! Logarithmic normalization at an integral norm cutoff and at a
small common-factor residual length. -/
noncomputable section
namespace CubicFirstMoment

lemma log_floor_norm_comparison {Z : ℝ} (hZ : 1 ≤ (⌊Z⌋₊:ℝ)) :
    1+Real.log Z ≤ 2*(1+Real.log (⌊Z⌋₊:ℝ)) := by
  have hZ0 : 0 ≤ Z := by
    by_contra h
    rw [Nat.floor_of_nonpos (le_of_not_ge h)] at hZ
    norm_num at hZ
  have hfloor := Nat.floor_le hZ0
  have hZp : 0 < Z := by linarith
  have hf : 0 < (⌊Z⌋₊:ℝ) := by linarith
  have htwo : Z ≤ 2*(⌊Z⌋₊:ℝ) := by
    have hh := Nat.lt_floor_add_one Z
    linarith
  have hl := Real.log_le_log hZp htwo
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hf.ne'] at hl
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  have hlogf := Real.log_nonneg hZ
  linarith

lemma log_floor_power_comparison {Z : ℝ} (hZ : 1 ≤ (⌊Z⌋₊:ℝ)) (k : ℕ) :
    (1+Real.log Z)^k ≤ (2:ℝ)^k*(1+Real.log (⌊Z⌋₊:ℝ))^k := by
  rw [←mul_pow]
  apply pow_le_pow_left₀ _ (log_floor_norm_comparison hZ)
  have hZ0 : 0 ≤ Z := by
    by_contra h
    rw [Nat.floor_of_nonpos (le_of_not_ge h)] at hZ
    norm_num at hZ
  have hf := Nat.floor_le hZ0
  have hZ1 : 1 ≤ Z := hZ.trans hf
  linarith [Real.log_nonneg hZ1]

lemma residual_log_comparison {Z r : ℝ} (hZ : 1 ≤ Z) (hr : 0 < r)
    (hsmall : r ≤ Z^(1/2:ℝ)) :
    1+Real.log Z ≤ 2*(1+Real.log (Z/r)) := by
  have hZp := zero_lt_one.trans_le hZ
  have hl := Real.log_le_log hr hsmall
  rw [Real.log_rpow hZp] at hl
  rw [Real.log_div hZp.ne' hr.ne']
  linarith

end CubicFirstMoment

end

end OAI
