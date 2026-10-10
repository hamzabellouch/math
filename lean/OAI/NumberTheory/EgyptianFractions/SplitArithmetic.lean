import Mathlib

namespace OAI
noncomputable section

namespace Problem337

/-- Splitting a positive unit fraction into the two usual larger fractions. -/
theorem unit_fraction_split (n : ℕ) (hn : 0 < n) :
    (1 : ℚ) / n = 1 / (n + 1 : ℕ) + 1 / (n * (n + 1) : ℕ) := by
  have hq : (n : ℚ) ≠ 0 := by positivity
  have hq1 : (n : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp


/-- A composite denominator admits a split strictly between the two
exceptional denominators for ordinary unit-fraction splitting. -/
theorem composite_unit_fraction_split (n : ℕ) (hn : 2 ≤ n)
    (hp : ¬ Nat.Prime n) :
    ∃ u v : ℕ, n + 1 < u ∧ u < v ∧ v < n * (n + 1) ∧
      (1 : ℚ) / n = 1 / u + 1 / v := by
  obtain ⟨a, b, han, hbn, hab⟩ := (Nat.not_prime_iff_exists_mul_eq hn).mp hp
  have ha : 2 ≤ a := by
    by_contra h
    have : a = 0 ∨ a = 1 := by omega
    rcases this with h | h
    · simp [h] at hab
      omega
    · simp [h] at hab
      omega
  have hb : 2 ≤ b := by
    by_contra h
    have : b = 0 ∨ b = 1 := by omega
    rcases this with h | h
    · simp [h] at hab
      omega
    · simp [h] at hab
      omega
  refine ⟨n + a, b * (n + a), ?_, ?_, ?_, ?_⟩
  · omega
  · nlinarith
  · nlinarith
  · have hna : (n + a : ℕ) ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    have hqna : ((n + a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hna
    have hqb : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
    have hqn : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
    have habq : (a : ℚ) * b = n := by exact_mod_cast hab
    push_cast at hqna ⊢
    field_simp
    nlinarith

end Problem337

end

end OAI
