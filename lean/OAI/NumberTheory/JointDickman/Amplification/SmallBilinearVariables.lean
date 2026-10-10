import OAI.NumberTheory.JointDickman.Arithmetic.PrimeLogHarmonic
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeLogarithmicReduction

namespace OAI

/-! # Removing small variables from the prime bilinear sum -/
namespace JointDickman
open Finset

lemma nat_div_cast_le (N d : ℕ) (hd : 0 < d) :
    ((N/d:ℕ):ℝ) ≤ (N:ℝ)/d := by
  apply (le_div_iff₀ (by exact_mod_cast hd : (0:ℝ) < d)).mpr
  exact_mod_cast Nat.div_mul_le_self N d

lemma prime_bilinear_inner_norm_le (c : ℕ → ℕ → ℂ) (N p : ℕ) (hp : p.Prime)
    (hc : ∀ m ∈ Ioc 0 (N/p), ‖c p m‖ ≤ Real.log p) :
    ‖∑ m ∈ Ioc 0 (N/p), c p m‖ ≤ (N:ℝ)*(Real.log p/p) := by
  calc
    _ ≤ ∑ m ∈ Ioc 0 (N/p), ‖c p m‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Ioc 0 (N/p), Real.log p := sum_le_sum hc
    _ = ((N/p:ℕ):ℝ)*Real.log p := by simp
    _ ≤ ((N:ℝ)/p)*Real.log p := mul_le_mul_of_nonneg_right
      (nat_div_cast_le N p hp.pos) (Real.log_natCast_nonneg p)
    _ = _ := by ring

theorem small_prime_bilinear_norm_le (c : ℕ → ℕ → ℂ) (N Z : ℕ)
    (hc : ∀ p ∈ Nat.primesLE Z, ∀ m ∈ Ioc 0 (N/p), ‖c p m‖ ≤ Real.log p) :
    ‖∑ p ∈ Nat.primesLE Z, ∑ m ∈ Ioc 0 (N/p), c p m‖ ≤
      N*Real.log 4*(1+Real.log Z) := by
  calc
    _ ≤ ∑ p ∈ Nat.primesLE Z, ‖∑ m ∈ Ioc 0 (N/p), c p m‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ Nat.primesLE Z, (N:ℝ)*(Real.log p/p) := by
      apply sum_le_sum
      intro p hp
      exact prime_bilinear_inner_norm_le c N p (Nat.mem_primesLE.mp hp).2 (hc p hp)
    _ = (N:ℝ)*∑ p ∈ Nat.primesLE Z, Real.log p/p := (mul_sum _ _ _).symm
    _ ≤ (N:ℝ)*(Real.log 4*(1+Real.log Z)) :=
      mul_le_mul_of_nonneg_left (prime_log_reciprocal_sum_le Z) (Nat.cast_nonneg N)
    _ = _ := by ring

lemma small_integer_inner_norm_le (c : ℕ → ℕ → ℂ) (N m : ℕ) (hm : 0 < m)
    (hc : ∀ p ∈ Nat.primesLE (N/m), ‖c p m‖ ≤ Real.log p) :
    ‖∑ p ∈ Nat.primesLE (N/m), c p m‖ ≤ Real.log 4*(N:ℝ)/m := by
  calc
    _ ≤ ∑ p ∈ Nat.primesLE (N/m), ‖c p m‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ Nat.primesLE (N/m), Real.log p := sum_le_sum hc
    _ = Chebyshev.theta ((N/m:ℕ):ℝ) := (Chebyshev.theta_eq_sum_primesLE_log _).symm
    _ ≤ Real.log 4*((N/m:ℕ):ℝ) := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (N/m))
    _ ≤ Real.log 4*((N:ℝ)/m) := mul_le_mul_of_nonneg_left
      (nat_div_cast_le N m hm) (Real.log_nonneg (by norm_num))
    _ = _ := by ring

theorem small_integer_bilinear_norm_le (c : ℕ → ℕ → ℂ) (N Z : ℕ)
    (hc : ∀ m ∈ Ioc 0 Z, ∀ p ∈ Nat.primesLE (N/m), ‖c p m‖ ≤ Real.log p) :
    ‖∑ m ∈ Ioc 0 Z, ∑ p ∈ Nat.primesLE (N/m), c p m‖ ≤
      N*Real.log 4*(1+Real.log Z) := by
  calc
    _ ≤ ∑ m ∈ Ioc 0 Z, ‖∑ p ∈ Nat.primesLE (N/m), c p m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Ioc 0 Z, Real.log 4*(N:ℝ)/m := by
      apply sum_le_sum
      intro m hm
      exact small_integer_inner_norm_le c N m (mem_Ioc.mp hm).1 (hc m hm)
    _ = (N:ℝ)*Real.log 4*∑ m ∈ Ioc 0 Z, 1/(m:ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro m hm
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_initial_sum Z) (by positivity)

end JointDickman

end OAI
