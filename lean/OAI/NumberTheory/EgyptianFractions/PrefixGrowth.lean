import Mathlib

namespace OAI
namespace Problem337

/-- The elementary growth estimate for successive products of denominators. -/
theorem prefix_growth_bound (k t : ℕ) (P : ℕ → ℕ)
    (hzero : P 0 = 1)
    (hstep : ∀ i < t, P (i + 1) ≤ k * (P i) ^ 2) :
    ∀ i ≤ t, P i ≤ k ^ (2 ^ i - 1) := by
  intro i hi
  induction i with
  | zero => simp [hzero]
  | succ i ih =>
    have hit : i < t := by omega
    have hip := ih (by omega)
    have hpow : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by omega)
    have hexp : 1 + (2 ^ i - 1) * 2 = 2 ^ (i + 1) - 1 := by
      rw [pow_succ]
      omega
    calc
      P (i + 1) ≤ k * (P i) ^ 2 := hstep i hit
      _ ≤ k * (k ^ (2 ^ i - 1)) ^ 2 := Nat.mul_le_mul_left k (Nat.pow_le_pow_left hip 2)
      _ = k ^ (2 ^ (i + 1) - 1) := by
        rw [← pow_mul, ← pow_succ']
        congr 1
        omega

/-- The bound for the next denominator follows from the prefix-product bound. -/
theorem denominator_growth_bound (k i P n : ℕ)
    (hP : P ≤ k ^ (2 ^ i - 1)) (hn : n ≤ k * P) :
    n ≤ k ^ (2 ^ i) := by
  have hpow : 1 ≤ 2 ^ i := Nat.one_le_pow i 2 (by omega)
  calc
    n ≤ k * P := hn
    _ ≤ k * k ^ (2 ^ i - 1) := Nat.mul_le_mul_left k hP
    _ = k ^ (2 ^ i) := by
      rw [← pow_succ']
      congr 1
      omega

end Problem337

end OAI
