import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFrequencyTwist

namespace OAI

/-! # The actual square-root denominator in the first Poisson comparison -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticSqrtNormalize (v : ℕ → ℂ) (n : ℕ) : ℂ :=
  v n / (Real.sqrt (n : ℝ) : ℂ)

 theorem quadraticSqrtNormalize_norm_sq (v : ℕ → ℂ) (n : ℕ) :
    ‖quadraticSqrtNormalize v n‖ ^ 2 = ‖v n‖ ^ 2 / (n : ℝ) := by
  rw [quadraticSqrtNormalize, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

 theorem quadraticSqrtNormalize_zero (v : ℕ → ℂ) {n : ℕ} (hn : v n = 0) :
    quadraticSqrtNormalize v n = 0 := by simp [quadraticSqrtNormalize, hn]

 theorem quadraticSqrtNormalize_energy (N R : ℕ) (hN : 0 < N) (v : ℕ → ℂ)
    (hv : ∀ n < N, v n = 0) :
    quadraticSieveEnergy R (quadraticSqrtNormalize v) ≤ quadraticSieveEnergy R v / N := by
  unfold quadraticSieveEnergy
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro n _
  rw [quadraticSqrtNormalize_norm_sq]
  by_cases hn : n < N
  · simp [hv n hn]
  · apply div_le_div_of_nonneg_left (sq_nonneg _) (by exact_mod_cast hN)
    exact_mod_cast (Nat.le_of_not_gt hn)

 theorem quadraticSqrtNormalize_moment (N R : ℕ) (hN : 0 < N) (v : ℕ → ℂ)
    (hv : ∀ n < N, v n = 0) :
    quadraticDivisorMoment R (quadraticSqrtNormalize v) ≤ quadraticDivisorMoment R v / N := by
  unfold quadraticDivisorMoment
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro n _
  rw [quadraticSqrtNormalize_norm_sq, ← mul_div_assoc]
  by_cases hn : n < N
  · simp [hv n hn]
  · apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hN)
    exact_mod_cast (Nat.le_of_not_gt hn)

end Ostmann

end OAI
