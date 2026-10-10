import OAI.Probability.ThorpShuffle.FixedLists.Energy

namespace OAI


noncomputable section
open scoped BigOperators
open Filter
namespace Thorp.FixedLists

def energyEnvelope (C d : ℕ) : ℝ :=
  (63 / 64 : ℝ) ^ (C * (d + 4)) + 64 * (9 / 10 : ℝ) ^ (2 ^ d)

lemma energyEnvelope_nonneg (C d : ℕ) : 0 ≤ energyEnvelope C d := by
  unfold energyEnvelope
  positivity

lemma geometric_base_256 : (2 : ℝ) ^ 3 * (63 / 64 : ℝ) ^ 254 < 1 := by
  have h : (63 / 64 : ℝ) ^ 64 ≤ 1 / 2 := by norm_num
  have h' : (63 / 64 : ℝ) ^ 192 ≤ (1 / 2) ^ 3 := by
    rw [show 192 = 64 * 3 by norm_num, pow_mul]
    exact pow_le_pow_left₀ (by positivity) h 3
  have h'' : (63 / 64 : ℝ) ^ 254 ≤ (63 / 64 : ℝ) ^ 193 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
  have h''' : (63 / 64 : ℝ) ^ 193 ≤ (1 / 2) ^ 3 * (63 / 64) := by
    rw [show 193 = 192 + 1 by norm_num, pow_succ]
    exact mul_le_mul_of_nonneg_right h' (by norm_num)
  have he := h''.trans h'''
  calc
    _ ≤ (2 : ℝ) ^ 3 * ((1 / 2) ^ 3 * (63 / 64)) :=
      mul_le_mul_of_nonneg_left he (by norm_num)
    _ < 1 := by norm_num

lemma geometric_base_1024 : (2 : ℝ) ^ 6 * (63 / 64 : ℝ) ^ 1022 < 1 := by
  have h : (63 / 64 : ℝ) ^ 64 ≤ 1 / 2 := by norm_num
  have h' : (63 / 64 : ℝ) ^ 448 ≤ (1 / 2) ^ 7 := by
    rw [show 448 = 64 * 7 by norm_num, pow_mul]
    exact pow_le_pow_left₀ (by positivity) h 7
  have h'' : (63 / 64 : ℝ) ^ 1022 ≤ (63 / 64 : ℝ) ^ 448 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
  have hb : (1 / 2 : ℝ) ^ 7 = 1 / 128 := by norm_num
  rw [hb] at h'
  calc
    _ ≤ (2 : ℝ) ^ 6 * (1 / 128 : ℝ) := mul_le_mul_of_nonneg_left (h''.trans h') (by norm_num)
    _ < 1 := by norm_num

lemma scaledEnergy_tendsto (C p : ℕ)
    (hbase : (2 : ℝ) ^ p * (63 / 64 : ℝ) ^ C < 1) :
    Tendsto (fun d : ℕ => ((2 : ℝ) ^ (d + 4)) ^ p * energyEnvelope C d)
      atTop (nhds 0) := by
  have h₁ := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by positivity : (0 : ℝ) ≤ 2 ^ p * (63 / 64 : ℝ) ^ C) hbase).comp
    (tendsto_add_atTop_nat 4)
  have h₂ := (tendsto_pow_const_mul_const_pow_of_lt_one p
    (by norm_num : (0 : ℝ) ≤ 9 / 10) (by norm_num : (9 / 10 : ℝ) < 1)).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  have hh := h₁.add (h₂.const_mul (64 * (16 : ℝ) ^ p))
  convert hh using 1
  · funext d
    simp only [energyEnvelope, Function.comp_def, Nat.cast_pow, Nat.cast_ofNat]
    rw [mul_add]
    congr 1
    · rw [← pow_mul, Nat.mul_comm (d + 4) p, pow_mul, pow_mul, ← mul_pow]
    · rw [pow_add, mul_pow]
      norm_num
      ring
  · simp

def listRate (d : ℕ) : ℝ :=
  Real.sqrt (((2 : ℝ) ^ (d + 4)) ^ 3 * energyEnvelope 254 d)

lemma listRate_tendsto : Tendsto listRate atTop (nhds 0) := by
  unfold listRate
  simpa only [Real.sqrt_zero] using (scaledEnergy_tendsto 254 3 geometric_base_256).sqrt

lemma scalar_tv_finish (n a : ℝ) (hn : 0 < n) (ha : 0 ≤ a)
    (h : n ^ 6 * a ≤ 2) : n / 2 * Real.sqrt (n * a) ≤ Real.rpow n (-(3 : ℝ) / 2) := by
  simp only [Real.rpow_eq_pow]
  have hr : (n ^ (-(3 : ℝ) / 2)) ^ (2 : ℕ) = 1 / n ^ 3 := by
    rw [← Real.rpow_mul_natCast hn.le]
    norm_num only [Nat.cast_ofNat, neg_div, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [Real.rpow_neg hn.le, Real.rpow_ofNat]
    simp only [one_div]
  apply (sq_le_sq₀ (by positivity) (Real.rpow_nonneg hn.le _)).mp
  rw [hr]
  apply (le_div_iff₀ (pow_pos hn 3)).mpr
  calc
    (n / 2 * Real.sqrt (n * a)) ^ 2 * n ^ 3 = n ^ 6 * a / 4 := by
      rw [mul_pow, div_pow, Real.sq_sqrt (mul_nonneg hn.le ha)]
      ring
    _ ≤ 1 := by linarith

end Thorp.FixedLists

end

end OAI
