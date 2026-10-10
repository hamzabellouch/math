import OAI.NumberTheory.Ostmann.Quadratic.QuadraticBilinearBound

namespace OAI

/-! # Divisor restrictions shorten each side of the coprime bilinear form

The Möbius divisor is kept separate from the fixed divisor. No replacement
of two divisibility conditions by their product is needed.
-/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_restricted_transpose_energy {M N s D : ℕ} {K : ℝ}
    (hs : Squarefree s) (ho : Odd s) (hK : 0 ≤ K)
    (h : QuadraticSieveBound M (N / s) K) (a : ℕ → ℂ) :
    (∑ u ∈ Finset.Icc 1 D, ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticTransposeSum N
        (fun n => if u ∣ n then (if s ∣ n then a n else 0) else 0) m‖ ^ 2) ≤
      2 * K * ∑ n ∈ oddSquarefreeRange N,
        (n.divisors.card : ℝ) * ‖if s ∣ n then a n else 0‖ ^ 2 := by
  calc
    _ ≤ ∑ u ∈ Finset.Icc 1 D,
        2 * K * quadraticSieveEnergy N
          (fun n => if u ∣ n then (if s ∣ n then a n else 0) else 0) := by
      apply Finset.sum_le_sum
      intro u _
      have heq : (fun n => if u ∣ n then (if s ∣ n then a n else 0) else 0) =
          (fun n => if s ∣ n then (if u ∣ n then a n else 0) else 0) := by
        funext n
        by_cases hu : u ∣ n <;> by_cases hs' : s ∣ n <;> simp [hu, hs']
      rw [heq]
      exact quadratic_divisibility_energy hs ho h _
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (quadratic_divisibility_partial_energy D N (fun n => if s ∣ n then a n else 0))
        (by positivity)

 theorem quadratic_coprime_restricted_bound {M N₁ N₂ s₁ s₂ : ℕ} {K₁ K₂ : ℝ}
    (hs₁ : Squarefree s₁) (ho₁ : Odd s₁) (hs₂ : Squarefree s₂) (ho₂ : Odd s₂)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M (N₁ / s₁) K₁)
    (h₂ : QuadraticSieveBound M (N₂ / s₂) K₂) (a b : ℕ → ℂ) :
    (∑ m ∈ oddSquarefreeRange M,
      ‖quadraticCoprimeBilinear N₁ N₂
        (fun n => if s₁ ∣ n then a n else 0)
        (fun n => if s₂ ∣ n then b n else 0) m‖) ≤
      Real.sqrt (2 * K₁ * ∑ n ∈ oddSquarefreeRange N₁,
        (n.divisors.card : ℝ) * ‖if s₁ ∣ n then a n else 0‖ ^ 2) *
      Real.sqrt (2 * K₂ * ∑ n ∈ oddSquarefreeRange N₂,
        (n.divisors.card : ℝ) * ‖if s₂ ∣ n then b n else 0‖ ^ 2) := by
  apply (quadratic_coprime_bilinear_cauchy M N₁ N₂ _ _).trans
  exact mul_le_mul
    (Real.sqrt_le_sqrt (quadratic_restricted_transpose_energy hs₁ ho₁ hK₁ h₁ a))
    (Real.sqrt_le_sqrt (quadratic_restricted_transpose_energy hs₂ ho₂ hK₂ h₂ b))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end Ostmann

end OAI
