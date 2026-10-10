import Mathlib

namespace OAI

namespace MetricKMedianRecovery.FailureBudget

noncomputable def failure (g : ℝ) (e N : ℕ) : ℝ :=
  g / (24*((N:ℝ)+2)^e)

lemma failure_pos {g : ℝ} (hg : 0 < g) (e N : ℕ) : 0 < failure g e N := by
  unfold failure
  positivity

lemma failure_le_margin {g : ℝ} (hg : 0 ≤ g) (e N : ℕ) : failure g e N ≤ g/24 := by
  have hp : (1:ℝ) ≤ ((N:ℝ)+2)^e := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) N])
  unfold failure
  apply div_le_div_of_nonneg_left hg (by norm_num)
  nlinarith

lemma failure_le_power {g a : ℝ} (hg1 : g ≤ 1) (N : ℕ) :
    failure g ⌈a⌉₊ N ≤ Real.rpow ((N:ℝ)+2) (-a) := by
  have hb : (0:ℝ) < (N:ℝ)+2 := by positivity
  have hb1 : (1:ℝ) ≤ (N:ℝ)+2 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have he : Real.rpow ((N:ℝ)+2) a ≤ ((N:ℝ)+2)^⌈a⌉₊ := by
    simpa only [Real.rpow_eq_pow,Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hb1 (Nat.le_ceil a)
  have hp : (0:ℝ) < ((N:ℝ)+2)^⌈a⌉₊ := pow_pos hb _
  calc
    failure g ⌈a⌉₊ N ≤ 1 / (((N:ℝ)+2)^⌈a⌉₊) := by
      unfold failure
      apply (div_le_div_iff₀ (mul_pos (by norm_num) hp) hp).mpr
      nlinarith
    _ ≤ 1 / Real.rpow ((N:ℝ)+2) a :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hb _) he
    _ = _ := by simpa only [Real.rpow_eq_pow,one_div] using (Real.rpow_neg hb.le a).symm

lemma expectation_margin {g P ζ : ℝ} (hP : 0 ≤ P) (hζ : ζ ≤ g/24) :
    (2-g/2+6*ζ)*P ≤ (2-g/4)*P := by
  apply mul_le_mul_of_nonneg_right _ hP
  linarith

lemma failure_log {g : ℝ} (hg : 0 < g) (e N : ℕ) :
    Real.log (1/failure g e N) = Real.log (24/g) + (e:ℝ)*Real.log ((N:ℝ)+2) := by
  have hb : (0:ℝ) < (N:ℝ)+2 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have he : 1/failure g e N = (24/g)*((N:ℝ)+2)^e := by unfold failure; field_simp
  rw [he,Real.log_mul (div_ne_zero (by norm_num) hg.ne') (pow_ne_zero _ hb.ne'),Real.log_pow]

end MetricKMedianRecovery.FailureBudget

end OAI
