import OAI.NumberTheory.Ostmann.Quadratic.QuadraticRestrictedBilinear
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDivisorSplit

namespace OAI

/-! # Summing the two divisor ranges in Heath-Brown's bilinear comparison -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticDivisorWeight (N s : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ oddSquarefreeRange N,
    (n.divisors.card : ℝ) * ‖if s ∣ n then a n else 0‖ ^ 2

noncomputable def quadraticDivisorMoment (N : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ oddSquarefreeRange N, (n.divisors.card : ℝ) ^ 2 * ‖a n‖ ^ 2

 theorem quadraticDivisorWeight_nonneg (N s : ℕ) (a : ℕ → ℂ) :
    0 ≤ quadraticDivisorWeight N s a := by
  apply Finset.sum_nonneg
  intro n _
  positivity

 theorem quadraticDivisorMoment_nonneg (N : ℕ) (a : ℕ → ℂ) :
    0 ≤ quadraticDivisorMoment N a := by
  apply Finset.sum_nonneg
  intro n _
  positivity

 theorem quadratic_divisor_weight_sum (N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ s ∈ S, quadraticDivisorWeight N s a) ≤ quadraticDivisorMoment N a := by
  unfold quadraticDivisorWeight quadraticDivisorMoment
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 := (Finset.mem_filter.mp hn).2.2.ne_zero
  have hsub : S.filter (fun s => s ∣ n) ⊆ n.divisors := by
    intro s hs
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hs).2, hn0⟩
  have hc : ((S.filter (fun s => s ∣ n)).card : ℝ) ≤ n.divisors.card := by
    exact_mod_cast Finset.card_le_card hsub
  simp only [apply_ite, norm_zero, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ (n.divisors.card : ℝ) * ((n.divisors.card : ℝ) * ‖a n‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

 theorem quadratic_divisor_weight_sqrt_sum (N : ℕ) (S : Finset ℕ)
    (K : ℝ) (hK : 0 ≤ K) (a : ℕ → ℂ) :
    (∑ s ∈ S, Real.sqrt (2 * K * quadraticDivisorWeight N s a)) ≤
      Real.sqrt (2 * K * S.card * quadraticDivisorMoment N a) := by
  have hw (s : ℕ) : 0 ≤ 2 * K * quadraticDivisorWeight N s a :=
    mul_nonneg (by positivity) (quadraticDivisorWeight_nonneg N s a)
  have hc := Real.sum_mul_le_sqrt_mul_sqrt S (fun _ => (1 : ℝ))
    (fun s => Real.sqrt (2 * K * quadraticDivisorWeight N s a))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  have he : (∑ s ∈ S, Real.sqrt (2 * K * quadraticDivisorWeight N s a) ^ 2) =
      2 * K * ∑ s ∈ S, quadraticDivisorWeight N s a := by
    simp only [Real.sq_sqrt (hw _), Finset.mul_sum]
  rw [he, ← Real.sqrt_mul (Nat.cast_nonneg S.card)] at hc
  apply hc.trans
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ (S.card : ℝ) * (2 * K * quadraticDivisorMoment N a) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (quadratic_divisor_weight_sum N S a) (by positivity))
        (Nat.cast_nonneg _)
    _ = _ := by ring

 theorem quadratic_divisor_family_bound (M N₁ N₂ : ℕ) (S₁ S₂ : Finset ℕ)
    (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hs₁ : ∀ s ∈ S₁, Squarefree s ∧ Odd s)
    (hs₂ : ∀ s ∈ S₂, Squarefree s ∧ Odd s)
    (h₁ : ∀ s ∈ S₁, QuadraticSieveBound M (N₁ / s) K₁)
    (h₂ : ∀ s ∈ S₂, QuadraticSieveBound M (N₂ / s) K₂) (a b : ℕ → ℂ) :
    (∑ s₁ ∈ S₁, ∑ s₂ ∈ S₂, ∑ m ∈ oddSquarefreeRange M,
      ‖quadraticCoprimeBilinear N₁ N₂
        (fun n => if s₁ ∣ n then a n else 0)
        (fun n => if s₂ ∣ n then b n else 0) m‖) ≤
      Real.sqrt (2 * K₁ * S₁.card * quadraticDivisorMoment N₁ a) *
      Real.sqrt (2 * K₂ * S₂.card * quadraticDivisorMoment N₂ b) := by
  calc
    _ ≤ ∑ s₁ ∈ S₁, ∑ s₂ ∈ S₂,
        Real.sqrt (2 * K₁ * quadraticDivisorWeight N₁ s₁ a) *
        Real.sqrt (2 * K₂ * quadraticDivisorWeight N₂ s₂ b) := by
      apply Finset.sum_le_sum
      intro s₁ hs₁'
      apply Finset.sum_le_sum
      intro s₂ hs₂'
      exact quadratic_coprime_restricted_bound (hs₁ s₁ hs₁').1 (hs₁ s₁ hs₁').2
        (hs₂ s₂ hs₂').1 (hs₂ s₂ hs₂').2 hK₁ hK₂ (h₁ s₁ hs₁') (h₂ s₂ hs₂') a b
    _ = (∑ s₁ ∈ S₁, Real.sqrt (2 * K₁ * quadraticDivisorWeight N₁ s₁ a)) *
        ∑ s₂ ∈ S₂, Real.sqrt (2 * K₂ * quadraticDivisorWeight N₂ s₂ b) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro _ _
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul (quadratic_divisor_weight_sqrt_sum N₁ S₁ K₁ hK₁ a)
      (quadratic_divisor_weight_sqrt_sum N₂ S₂ K₂ hK₂ b)
      (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end Ostmann

end OAI
