import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRoughIteration

namespace OAI

/-! # A rounded cutoff that terminates the descent in a fixed number of steps -/

namespace Ostmann

noncomputable def quadraticDescentCutoff (N r : ℕ) : ℕ :=
  ⌈4 * (N : ℝ) ^ (1 / (r : ℝ))⌉₊

theorem quadratic_descent_root_power {N r : ℕ} (hr : 0 < r) :
    ((N : ℝ) ^ (1 / (r : ℝ))) ^ r = N := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  have hr₀ : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  rw [one_div_mul_cancel hr₀, Real.rpow_one]

theorem quadratic_descent_cutoff_bounds {N r : ℕ} (hN : 0 < N) (hr : 0 < r) :
    4 ≤ quadraticDescentCutoff N r ∧
      (quadraticDescentCutoff N r : ℝ) ≤ 5 * (N : ℝ) ^ (1 / (r : ℝ)) ∧
      2 ^ r * N < quadraticDescentCutoff N r ^ r := by
  let Y := (N : ℝ) ^ (1 / (r : ℝ))
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hY : 1 ≤ Y := Real.one_le_rpow hN₁ (by positivity)
  have hlo : 4 * Y ≤ (quadraticDescentCutoff N r : ℝ) := Nat.le_ceil _
  have hhi : (quadraticDescentCutoff N r : ℝ) < 4 * Y + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hD : (4 : ℝ) ≤ quadraticDescentCutoff N r := by linarith
  refine ⟨by exact_mod_cast hD, by linarith, ?_⟩
  have hstrict : 2 * Y < (quadraticDescentCutoff N r : ℝ) := by linarith
  have hp := pow_lt_pow_left₀ hstrict (by positivity : (0 : ℝ) ≤ 2 * Y) (Nat.ne_of_gt hr)
  rw [mul_pow, quadratic_descent_root_power hr] at hp
  exact_mod_cast hp

theorem quadratic_descent_cutoff_fifth {N r : ℕ} (hN : 0 < N) (hr : 0 < r) :
    (quadraticDescentCutoff N r : ℝ) ^ 5 ≤ 5 ^ 5 * (N : ℝ) ^ (5 / (r : ℝ)) := by
  have hb := (quadratic_descent_cutoff_bounds hN hr).2.1
  apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hb 5).trans_eq
  rw [mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1
  ring

end Ostmann

end OAI
