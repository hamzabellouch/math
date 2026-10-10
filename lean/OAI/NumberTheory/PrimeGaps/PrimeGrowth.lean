import Mathlib

namespace OAI

open Filter

namespace Problem344.PrimeGrowth

lemma primeCounting_nth_prime (n : ℕ) :
    Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ]
  simp only [Nat.prime_nth_prime, ite_true]
  exact congrArg (fun k => k + 1) (Nat.primeCounting'_nth_eq n)

lemma eventually_log_add_one_le_half_log_two_mul :
    ∀ᶠ x : ℝ in atTop, Real.log (x + 1) ≤ (Real.log 2 / 2) * x := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h := Real.isLittleO_log_id_atTop.bound (show 0 < Real.log 2 / 4 by positivity)
  have ht : Tendsto (fun x : ℝ => x + 1) atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_id
  filter_upwards [ht.eventually h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  simp only [Function.id_def, Real.norm_eq_abs] at hx
  rw [abs_of_nonneg (Real.log_nonneg (by linarith)), abs_of_nonneg (by linarith)] at hx
  nlinarith

lemma eventually_primeCounting_mul_log_lower :
    ∀ᶠ p : ℕ in atTop,
      (Real.log 2 / 2) * (p : ℝ) ≤ (Nat.primeCounting p : ℝ) * Real.log p := by
  have ht : Tendsto (fun p : ℕ => (p : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually eventually_log_add_one_le_half_log_two_mul,
    eventually_ge_atTop (2 : ℕ)] with p hp hp2
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hpi := (div_le_iff₀ hlog).mp (Chebyshev.pi_ge p)
  nlinarith

lemma eventually_nth_prime_ratio_le_log :
    ∀ᶠ n : ℕ in atTop,
      (Nat.nth Nat.Prime (n - 1) : ℝ) / (n : ℝ) ≤
        (2 / Real.log 2) * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventually_primeCounting_mul_log_lower
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  have hnpos : 0 < n := by omega
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hp : N ≤ Nat.nth Nat.Prime (n - 1) := by
    have := Nat.add_two_le_nth_prime (n - 1)
    omega
  have hpi := hN _ hp
  have hc : Nat.primeCounting (Nat.nth Nat.Prime (n - 1)) = n := by
    rw [primeCounting_nth_prime]
    omega
  rw [hc] at hpi
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpbound : (Nat.nth Nat.Prime (n - 1) : ℝ) ≤
      ((n : ℝ) * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ)) / (Real.log 2 / 2) := by
    apply (le_div_iff₀ (show 0 < Real.log (2 : ℝ) / 2 by positivity)).mpr
    nlinarith
  calc
    _ ≤ (((n : ℝ) * Real.log (Nat.nth Nat.Prime (n - 1) : ℝ)) /
        (Real.log 2 / 2)) / (n : ℝ) := div_le_div_of_nonneg_right hpbound hnr.le
    _ = _ := by field_simp

end Problem344.PrimeGrowth

end OAI
