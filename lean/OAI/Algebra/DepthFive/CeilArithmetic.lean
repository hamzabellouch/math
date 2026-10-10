import OAI.Algebra.DepthFive.Basic

namespace OAI

namespace Problem335

@[simp] theorem ceilSqrt_zero : ceilSqrt 0 = 0 := by
  simp [ceilSqrt]

@[simp] theorem ceilSqrt_one : ceilSqrt 1 = 1 := by
  simp [ceilSqrt]

@[simp] theorem ceilSqrt_two : ceilSqrt 2 = 2 := by
  norm_num [ceilSqrt, Nat.sqrt_two]

theorem sqrt_le_ceilSqrt (n : ℕ) : Nat.sqrt n ≤ ceilSqrt n := by
  unfold ceilSqrt
  omega

theorem ceilSqrt_le_sqrt_add_one (n : ℕ) : ceilSqrt n ≤ Nat.sqrt n + 1 := by
  unfold ceilSqrt
  split <;> omega

theorem self_le_ceilSqrt_sq (n : ℕ) : n ≤ ceilSqrt n ^ 2 := by
  unfold ceilSqrt
  split
  · rename_i h
    simpa using h.ge
  · simpa [Nat.succ_eq_add_one] using (Nat.lt_succ_sqrt' n).le

theorem ceilSqrt_pos {n : ℕ} (hn : 0 < n) : 0 < ceilSqrt n :=
  lt_of_lt_of_le (Nat.sqrt_pos.mpr hn) (sqrt_le_ceilSqrt n)

theorem ceilSqrt_le_self (n : ℕ) : ceilSqrt n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  by_cases h : n = 1
  · subst n
    simp
  have hn' : 1 < n := by omega
  exact (ceilSqrt_le_sqrt_add_one n).trans (Nat.succ_le_of_lt (Nat.sqrt_lt_self hn'))

theorem two_le_ceilSqrt {n : ℕ} (hn : 2 ≤ n) : 2 ≤ ceilSqrt n := by
  have h := self_le_ceilSqrt_sq n
  by_contra hh
  have hh' : ceilSqrt n ≤ 1 := by omega
  have : ceilSqrt n ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left hh' 2
  omega

theorem ceilSqrt_cast_le_real_sqrt_add_one (n : ℕ) :
    (ceilSqrt n : ℝ) ≤ Real.sqrt (n : ℝ) + 1 := by
  have hnat : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' n
  have hceil : (ceilSqrt n : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by
    exact_mod_cast ceilSqrt_le_sqrt_add_one n
  linarith

theorem real_sqrt_le_ceilSqrt_cast (n : ℕ) :
    Real.sqrt (n : ℝ) ≤ (ceilSqrt n : ℝ) := by
  apply (Real.sqrt_le_left (Nat.cast_nonneg _)).mpr
  exact_mod_cast self_le_ceilSqrt_sq n

theorem ceilDiv_le_iff {n t r : ℕ} (ht : 0 < t) :
    ceilDiv n t ≤ r ↔ n ≤ r * t := by
  unfold ceilDiv
  rw [Nat.div_le_iff_le_mul_add_pred ht]
  rw [Nat.mul_comm t r]
  omega

theorem self_le_ceilDiv_mul (n : ℕ) {t : ℕ} (ht : 0 < t) :
    n ≤ ceilDiv n t * t :=
  (ceilDiv_le_iff ht).mp le_rfl

theorem ceilDiv_le_self (n : ℕ) {t : ℕ} (ht : 0 < t) :
    ceilDiv n t ≤ n := by
  apply (ceilDiv_le_iff ht).mpr
  exact Nat.le_mul_of_pos_right n ht

theorem ceilDiv_pos {n t : ℕ} (hn : 0 < n) (ht : 0 < t) :
    0 < ceilDiv n t := by
  by_contra h
  have hh : ceilDiv n t ≤ 0 := by omega
  have := (ceilDiv_le_iff ht).mp hh
  omega

theorem ceilDiv_ceilSqrt_le (n : ℕ) : ceilDiv n (ceilSqrt n) ≤ ceilSqrt n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ceilDiv]
  apply (ceilDiv_le_iff (ceilSqrt_pos hn)).mpr
  simpa [pow_two] using self_le_ceilSqrt_sq n

end Problem335

end OAI
