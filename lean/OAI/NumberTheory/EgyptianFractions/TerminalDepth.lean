import Mathlib

namespace OAI
noncomputable section

namespace Problem337.TerminalDepth

/-- Number of contractions reducing a logarithmic height `S` to one. -/
def depth (α S : ℝ) : ℕ := ⌈Real.log S / (-Real.log α)⌉₊

theorem depth_contracts {α S : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hS : 1 ≤ S) : α ^ depth α S * S ≤ 1 := by
  have hlogα : 0 < -Real.log α := neg_pos.2 (Real.log_neg hα hα1)
  have hSpos : 0 < S := by linarith
  have hceil : Real.log S ≤ (depth α S : ℝ) * (-Real.log α) :=
    (div_le_iff₀ hlogα).1 (Nat.le_ceil _)
  have hpowpos : 0 < α ^ depth α S := pow_pos hα _
  apply (Real.log_le_log_iff (mul_pos hpowpos hSpos) (by norm_num : (0 : ℝ) < 1)).1
  rw [Real.log_mul (ne_of_gt hpowpos) (ne_of_gt hSpos), Real.log_pow, Real.log_one]
  nlinarith

theorem depth_budget {α S : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hlogS : 1 ≤ Real.log S) :
    (depth α S : ℝ) ≤ (1 / (-Real.log α) + 1) * Real.log S := by
  have hlogα : 0 < -Real.log α := neg_pos.2 (Real.log_neg hα hα1)
  have hceil : (depth α S : ℝ) < Real.log S / (-Real.log α) + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (by linarith) hlogα.le)
  calc
    (depth α S : ℝ) ≤ Real.log S / (-Real.log α) + 1 := hceil.le
    _ ≤ (1 / (-Real.log α) + 1) * Real.log S := by
      rw [add_mul, one_mul, one_div_mul_eq_div]
      linarith

/-- The base-two exponent needed by the terminal binary range. -/
def binaryExponent (D S : ℝ) : ℕ := ⌈D * Real.log S / Real.log 2⌉₊

theorem binary_log_lower {D S : ℝ} (hD : 1 ≤ D) (hlogS : 1 ≤ Real.log S) :
    1 ≤ Real.log ((2 : ℝ) ^ binaryExponent D S) := by
  rw [Real.log_pow]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : D * Real.log S ≤ (binaryExponent D S : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog2).1 (Nat.le_ceil _)
  nlinarith

theorem terminal_length_budget {D α S : ℝ} (hD : 1 ≤ D)
    (hα : 0 < α) (hα1 : α < 1) (hlogS : 1 ≤ Real.log S) :
    ((binaryExponent D S + 1 + depth α S : ℕ) : ℝ) ≤
      (D / Real.log 2 + 1 / (-Real.log α) + 3) * Real.log S := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogα : 0 < -Real.log α := neg_pos.2 (Real.log_neg hα hα1)
  have hD0 : 0 ≤ D := by linarith
  have hS0 : 0 ≤ Real.log S := by linarith
  have ha : (binaryExponent D S : ℝ) < D * Real.log S / Real.log 2 + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hD0 hS0) hlog2.le)
  have hd : (depth α S : ℝ) < Real.log S / (-Real.log α) + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hS0 hlogα.le)
  push_cast
  calc
    (binaryExponent D S : ℝ) + 1 + depth α S ≤
        D * Real.log S / Real.log 2 + Real.log S / (-Real.log α) + 3 := by linarith
    _ ≤ (D / Real.log 2 + 1 / (-Real.log α) + 3) * Real.log S := by
      rw [add_mul, add_mul]
      have h1 : D / Real.log 2 * Real.log S = D * Real.log S / Real.log 2 := by ring
      have h2 : 1 / (-Real.log α) * Real.log S = Real.log S / (-Real.log α) := by ring
      rw [h1, h2]
      linarith

theorem potential_bound {α S : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hS : 1 ≤ S) (u : ℕ) (hu : (u : ℝ) ≤ Real.exp S) :
    α ^ depth α S * Real.log (u : ℝ) ≤ 1 := by
  by_cases hu0 : u = 0
  · subst u
    norm_num
  have hupos : (0 : ℝ) < u := by exact_mod_cast (Nat.pos_of_ne_zero hu0)
  have hlogu : Real.log (u : ℝ) ≤ S := (Real.log_le_iff_le_exp hupos).2 hu
  exact (mul_le_mul_of_nonneg_left hlogu (pow_nonneg hα.le _)).trans
    (depth_contracts hα hα1 hS)

theorem rpow_le_binary {D S : ℝ} (hS : 0 < S) :
    S ^ D ≤ (2 : ℝ) ^ binaryExponent D S := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : D * Real.log S ≤ (binaryExponent D S : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog2).1 (Nat.le_ceil _)
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hS D) (by positivity)).1
  rw [Real.log_rpow hS, Real.log_pow]
  exact hceil

end Problem337.TerminalDepth

end

end OAI
