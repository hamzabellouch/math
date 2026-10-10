import Mathlib

namespace OAI
noncomputable section

namespace Problem337

/-- The elementary box estimate already gives a linear upper bound on the
    double logarithm, including the zero and singleton cases. -/
theorem counting_loglog_upper_of_box (f : ℕ → ℕ)
    (hbox : ∀ k : ℕ, f k ≤ k ^ (2 ^ k - 1))
    (k : ℕ) (hk : 2 ≤ k) :
    Real.log (Real.log (f k : ℝ)) ≤ 3 * (k : ℝ) := by
  by_cases hf : f k ≤ 1
  · have hcases : f k = 0 ∨ f k = 1 := by omega
    rcases hcases with hzero | hone
    · simp [hzero]
    · simp [hone]
  · have hf2 : 2 ≤ f k := by omega
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hfR : (2 : ℝ) ≤ (f k : ℝ) := by exact_mod_cast hf2
    have hlogf : 0 < Real.log (f k : ℝ) := Real.log_pos (by linarith)
    have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
    have hbox' : f k ≤ k ^ (2 ^ k) :=
      (hbox k).trans (pow_le_pow_right' (by omega : 1 ≤ k) (Nat.sub_le _ _))
    have hboxR : (f k : ℝ) ≤ (k : ℝ) ^ (2 ^ k) := by exact_mod_cast hbox'
    have hfirst : Real.log (f k : ℝ) ≤ (2 : ℝ) ^ k * Real.log (k : ℝ) := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < (f k : ℝ)) hboxR
      simpa only [Real.log_pow, Nat.cast_pow, Nat.cast_ofNat] using h
    have hsecond := Real.log_le_log hlogf hfirst
    rw [Real.log_mul (by positivity) (ne_of_gt hlogk), Real.log_pow] at hsecond
    have hlog2 : Real.log (2 : ℝ) ≤ 2 := Real.log_le_self (by norm_num)
    have hloglogk : Real.log (Real.log (k : ℝ)) ≤ (k : ℝ) :=
      (Real.log_le_self (le_of_lt hlogk)).trans (Real.log_le_self (by positivity))
    have hmul : (k : ℝ) * Real.log 2 ≤ (k : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left hlog2 (by positivity)
    linarith

end Problem337

end

end OAI
