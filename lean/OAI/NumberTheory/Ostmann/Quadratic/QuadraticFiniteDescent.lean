import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRoughDescent

namespace OAI

/-! # The finite length of the actual coefficient descent -/

namespace Ostmann

open scoped Classical BigOperators

def quadraticDescentBudget (A B : ℝ) : ℕ → ℝ
  | 0 => 0
  | r + 1 => A + B * quadraticDescentBudget A B r

theorem quadraticDescentBudget_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (r : ℕ) :
    0 ≤ quadraticDescentBudget A B r := by
  induction r with
  | zero => rfl
  | succ r ih => exact add_nonneg hA (mul_nonneg hB ih)

theorem quadraticDescentBudget_bound {A B : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (r : ℕ) :
    quadraticDescentBudget A B r ≤ (r : ℝ) * B ^ r * A := by
  induction r with
  | zero => simp [quadraticDescentBudget]
  | succ r ih =>
    have hBA : A ≤ B ^ (r + 1) * A := le_mul_of_one_le_left hA (one_le_pow₀ hB)
    calc
      _ ≤ A + B * ((r : ℝ) * B ^ r * A) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left ih (le_trans zero_le_one hB))
      _ ≤ B ^ (r + 1) * A + B * ((r : ℝ) * B ^ r * A) := add_le_add hBA le_rfl
      _ = _ := by rw [pow_succ, Nat.cast_add, Nat.cast_one]; ring

theorem quadratic_rough_zero (M K : ℕ) (T : ℝ) : QuadraticRoughBound M 0 K T := by
  intro v
  simp [quadraticRoughEnergy, quadraticTransposeSum, quadraticSieveEnergy, oddSquarefreeRange]

theorem quadratic_quotient_descent_cutoff {D n r : ℕ} (hD : 0 < D)
    (h : 2 ^ (r + 1) * n < D ^ (r + 1)) :
    2 ^ r * (2 * n / D) < D ^ r := by
  have hdiv : (2 * n / D) * D ≤ 2 * n := Nat.div_mul_le_self _ _
  have hmul := Nat.mul_le_mul_left (2 ^ r) hdiv
  have hstrict : (2 ^ r * (2 * n / D)) * D < D ^ r * D := by
    calc
      _ ≤ 2 ^ r * (2 * n) := by simpa only [mul_assoc] using hmul
      _ < D ^ r * D := by simpa only [pow_succ, mul_assoc] using h
  exact (Nat.mul_lt_mul_right hD).mp hstrict

/-- Iterate the concrete `n ↦ 2*n/D` descent. The power condition proves that
the last coefficient range is empty; no limiting or supremum argument occurs. -/
theorem quadratic_rough_finite_descent {M N₀ K D : ℕ} {A B : ℝ}
    (hD : 2 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hstep : ∀ n : ℕ, 0 < n → n ≤ N₀ → ∀ T : ℝ, 0 ≤ T →
      QuadraticRoughBound M (2 * n / D) K T → QuadraticRoughBound M n K (A + B * T))
    (r n : ℕ) (hn : n ≤ N₀) (hcut : 2 ^ r * n < D ^ r) :
    QuadraticRoughBound M n K (quadraticDescentBudget A B r) := by
  induction r generalizing n with
  | zero =>
    have : n = 0 := by simpa using hcut
    subst n
    exact quadratic_rough_zero M K _
  | succ r ih =>
    by_cases hn₀ : n = 0
    · subst n
      exact quadratic_rough_zero M K _
    have hsmall : 2 * n / D ≤ n := by
      calc
        _ ≤ 2 * n / 2 := Nat.div_le_div_left hD (by norm_num)
        _ = n := by omega
    have hnext := ih (2 * n / D) (hsmall.trans hn) (quadratic_quotient_descent_cutoff (by omega) hcut)
    exact hstep n (Nat.pos_of_ne_zero hn₀) hn _ (quadraticDescentBudget_nonneg hA hB r) hnext

end Ostmann

end OAI
