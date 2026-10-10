import Mathlib

namespace OAI

/-! Uniform numerical estimates for the size parameter. -/

namespace Paper320

theorem parameter_ge_eighty_one {d M : ℕ} (hd : 1 ≤ d) (hM : 9 ^ (d + 1) ≤ M) :
    81 ≤ M := by
  have hp : (9 : ℕ) ^ 2 ≤ 9 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at hp
  exact hp.trans hM

theorem ceil_sqrt_max_le_two_sqrt {M : ℕ} (hM : 81 ≤ M) :
    (max (Nat.ceil (Real.sqrt (M : ℝ))) 16 : ℕ) ≤ 2 * Real.sqrt (M : ℝ) := by
  have hs : (9 : ℝ) ≤ Real.sqrt (M : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact_mod_cast hM
  have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (M : ℝ))
  push_cast
  exact max_le (by linarith) (by linarith)

theorem parameter_sqrt_lower {d M : ℕ} (hM : 9 ^ (d + 1) ≤ M) :
    (3 : ℝ) ^ (d + 1) ≤ Real.sqrt (M : ℝ) := by
  apply Real.le_sqrt_of_sq_le
  calc
    ((3 : ℝ) ^ (d + 1)) ^ 2 = ((3 : ℝ) ^ 2) ^ (d + 1) := by
      simp only [← pow_mul, Nat.mul_comm]
    _ = (9 : ℝ) ^ (d + 1) := by norm_num
    _ ≤ M := by exact_mod_cast hM

theorem parameter_epsilon_budget {d M : ℕ} (hd : 1 ≤ d) (hM : 9 ^ (d + 1) ≤ M) :
    ((max (Nat.ceil (Real.sqrt (M : ℝ))) 16 : ℕ) : ℝ) / M * 3 ^ (d + 1) ≤ 2 := by
  have h81 := parameter_ge_eighty_one hd hM
  have hpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hm := ceil_sqrt_max_le_two_sqrt h81
  have hp := parameter_sqrt_lower hM
  calc
    _ ≤ (2 * Real.sqrt (M : ℝ)) / M * Real.sqrt (M : ℝ) :=
      mul_le_mul (div_le_div_of_nonneg_right hm hpos.le) hp (by positivity) (by positivity)
    _ = 2 := by
      field_simp
      nlinarith [Real.sq_sqrt hpos.le]

theorem parameter_epsilon_le {d M : ℕ} (hd : 1 ≤ d) (hM : 9 ^ (d + 1) ≤ M) :
    ((max (Nat.ceil (Real.sqrt (M : ℝ))) 16 : ℕ) : ℝ) / M ≤ 2 / 3 ^ (d + 1) := by
  exact (le_div_iff₀ (by positivity)).2 (parameter_epsilon_budget hd hM)

theorem parameter_epsilon_sqrt {d M : ℕ} (hd : 1 ≤ d) (hM : 9 ^ (d + 1) ≤ M) :
    ((max (Nat.ceil (Real.sqrt (M : ℝ))) 16 : ℕ) : ℝ) / M ≤
      2 / Real.sqrt (M : ℝ) ∧
      2 / Real.sqrt (M : ℝ) ≤ 2 / (3 : ℝ) ^ (d + 1) := by
  have h81 := parameter_ge_eighty_one hd hM
  have hpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hspos := Real.sqrt_pos.mpr hpos
  constructor
  · calc
      _ ≤ (2 * Real.sqrt (M : ℝ)) / M :=
        div_le_div_of_nonneg_right (ceil_sqrt_max_le_two_sqrt h81) hpos.le
      _ = 2 / Real.sqrt (M : ℝ) := by
        field_simp
        nlinarith [Real.sq_sqrt hpos.le]
  · exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (parameter_sqrt_lower hM)

end Paper320

end OAI
