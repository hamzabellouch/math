import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDivisorFamily

namespace OAI

/-! # Absorbing the divisor moment by an arbitrarily small power -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_divisor_moment_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ a : ℕ → ℂ,
      quadraticDivisorMoment N a ≤ C * (N : ℝ) ^ ε * quadraticSieveEnergy N a := by
  obtain ⟨C, hC, hc⟩ := quadratic_divisor_bound (ε / 2) (by positivity)
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro N a
  unfold quadraticDivisorMoment quadraticSieveEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 := (Finset.mem_filter.mp hn).2.2.ne_zero
  have hnN : (n : ℝ) ≤ N := by
    exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
  have hdiv : (n.divisors.card : ℝ) ≤ C * (N : ℝ) ^ (ε / 2) :=
    (hc n hn0).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hnN (by positivity)) hC.le)
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg n.divisors.card) hdiv 2
  have he : (C * (N : ℝ) ^ (ε / 2)) ^ 2 = C ^ 2 * (N : ℝ) ^ ε := by
    rw [mul_pow]
    congr 1
    calc
      _ = ((N : ℝ) ^ (ε / 2)) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = (N : ℝ) ^ ((ε / 2) * 2) := (Real.rpow_mul (Nat.cast_nonneg N) _ _).symm
      _ = _ := by congr 1; ring
  rw [he] at hsq
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

 theorem quadratic_divisor_family_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N₁ N₂ : ℕ, ∀ S₁ S₂ : Finset ℕ,
    ∀ K₁ K₂ : ℝ, 0 ≤ K₁ → 0 ≤ K₂ →
    (∀ s ∈ S₁, Squarefree s ∧ Odd s) →
    (∀ s ∈ S₂, Squarefree s ∧ Odd s) →
    (∀ s ∈ S₁, QuadraticSieveBound M (N₁ / s) K₁) →
    (∀ s ∈ S₂, QuadraticSieveBound M (N₂ / s) K₂) → ∀ a b : ℕ → ℂ,
    (∑ s₁ ∈ S₁, ∑ s₂ ∈ S₂, ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticCoprimeBilinear N₁ N₂
        (fun n => if s₁ ∣ n then a n else 0)
        (fun n => if s₂ ∣ n then b n else 0) m‖) ≤
      Real.sqrt (2 * K₁ * S₁.card * (C * (N₁ : ℝ) ^ ε * quadraticSieveEnergy N₁ a)) *
      Real.sqrt (2 * K₂ * S₂.card * (C * (N₂ : ℝ) ^ ε * quadraticSieveEnergy N₂ b)) := by
  obtain ⟨C, hC, hc⟩ := quadratic_divisor_moment_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro M N₁ N₂ S₁ S₂ K₁ K₂ hK₁ hK₂ hs₁ hs₂ h₁ h₂ a b
  apply (quadratic_divisor_family_bound M N₁ N₂ S₁ S₂ K₁ K₂ hK₁ hK₂
    hs₁ hs₂ h₁ h₂ a b).trans
  apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hc N₁ a) (by positivity))
  · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hc N₂ b) (by positivity))

end Ostmann

end OAI
