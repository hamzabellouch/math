import Mathlib.Data.Nat.Log
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDivisorRange

namespace OAI

/-! # A disjoint dyadic partition of the actual odd-squarefree divisors -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticDyadicDivisors (N j : ℕ) : Finset ℕ :=
  (oddSquarefreeRange N).filter (fun s => Nat.log 2 s = j)

 theorem quadraticDyadicDivisors_bounds {N j s : ℕ}
    (hs : s ∈ quadraticDyadicDivisors N j) : 2 ^ j ≤ s ∧ s < 2 ^ (j + 1) := by
  obtain ⟨hs, hj⟩ := Finset.mem_filter.mp hs
  have hn := (Finset.mem_filter.mp hs).2.2.ne_zero
  have hlo := Nat.pow_log_le_self 2 hn
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) s
  rw [hj] at hlo hhi
  exact ⟨hlo, hhi⟩

 theorem quadraticDyadicDivisors_card (N j : ℕ) :
    (quadraticDyadicDivisors N j).card ≤ 2 ^ j := by
  have hs : quadraticDyadicDivisors N j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)) := by
    intro s hs
    exact Finset.mem_Ico.mpr (quadraticDyadicDivisors_bounds hs)
  calc
    _ ≤ (Finset.Ico (2 ^ j) (2 ^ (j + 1))).card := Finset.card_le_card hs
    _ = 2 ^ j := by rw [Nat.card_Ico, pow_succ]; omega

 theorem quadratic_dyadic_divisors_sum {R : Type*} [AddCommMonoid R]
    (N : ℕ) (f : ℕ → R) :
    (∑ j ∈ Finset.range (Nat.log 2 N + 1), ∑ s ∈ quadraticDyadicDivisors N j, f s) =
      ∑ s ∈ oddSquarefreeRange N, f s := by
  simp only [quadraticDyadicDivisors, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  have hle : Nat.log 2 s < Nat.log 2 N + 1 := by
    have hh := Nat.log_mono_right (b := 2)
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2
    omega
  simp only [Finset.sum_ite_eq, Finset.mem_range, hle, ite_true]

 theorem quadratic_dyadic_pair_sum {R : Type*} [AddCommMonoid R]
    (N₁ N₂ : ℕ) (f : ℕ → ℕ → R) :
    (∑ i ∈ Finset.range (Nat.log 2 N₁ + 1), ∑ j ∈ Finset.range (Nat.log 2 N₂ + 1),
      ∑ s ∈ quadraticDyadicDivisors N₁ i, ∑ t ∈ quadraticDyadicDivisors N₂ j, f s t) =
      ∑ s ∈ oddSquarefreeRange N₁, ∑ t ∈ oddSquarefreeRange N₂, f s t := by
  calc
    _ = ∑ i ∈ Finset.range (Nat.log 2 N₁ + 1), ∑ s ∈ quadraticDyadicDivisors N₁ i,
        ∑ j ∈ Finset.range (Nat.log 2 N₂ + 1), ∑ t ∈ quadraticDyadicDivisors N₂ j, f s t :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ i ∈ Finset.range (Nat.log 2 N₁ + 1), ∑ s ∈ quadraticDyadicDivisors N₁ i,
        ∑ t ∈ oddSquarefreeRange N₂, f s t := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun s _ => quadratic_dyadic_divisors_sum N₂ (f s))
    _ = _ := quadratic_dyadic_divisors_sum N₁ _

 theorem quadratic_dyadic_divisor_family_bound (M N₁ N₂ i j : ℕ)
    (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (h₁ : QuadraticSieveBound M (N₁ / 2 ^ i) K₁)
    (h₂ : QuadraticSieveBound M (N₂ / 2 ^ j) K₂) (a b : ℕ → ℂ) :
    (∑ s₁ ∈ quadraticDyadicDivisors N₁ i, ∑ s₂ ∈ quadraticDyadicDivisors N₂ j,
      ∑ m ∈ oddSquarefreeRange M, ‖quadraticCoprimeBilinear N₁ N₂
        (fun n => if s₁ ∣ n then a n else 0)
        (fun n => if s₂ ∣ n then b n else 0) m‖) ≤
      Real.sqrt (2 * K₁ * (2 ^ i : ℕ) * quadraticDivisorMoment N₁ a) *
      Real.sqrt (2 * K₂ * (2 ^ j : ℕ) * quadraticDivisorMoment N₂ b) := by
  have hs (N k s : ℕ) (h : s ∈ quadraticDyadicDivisors N k) :
      Squarefree s ∧ Odd s := by
    obtain ⟨hr, _⟩ := Finset.mem_filter.mp h
    exact ⟨(Finset.mem_filter.mp hr).2.2, (Finset.mem_filter.mp hr).2.1⟩
  have hcut₁ : ∀ s ∈ quadraticDyadicDivisors N₁ i,
      QuadraticSieveBound M (N₁ / s) K₁ := by
    intro s hs'
    exact QuadraticSieveBound.mono_second (Nat.div_le_div_left
      (quadraticDyadicDivisors_bounds hs').1 (by positivity)) h₁
  have hcut₂ : ∀ s ∈ quadraticDyadicDivisors N₂ j,
      QuadraticSieveBound M (N₂ / s) K₂ := by
    intro s hs'
    exact QuadraticSieveBound.mono_second (Nat.div_le_div_left
      (quadraticDyadicDivisors_bounds hs').1 (by positivity)) h₂
  apply (quadratic_divisor_family_bound M N₁ N₂ _ _ K₁ K₂ hK₁ hK₂
    (hs N₁ i) (hs N₂ j) hcut₁ hcut₂ a b).trans
  apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast quadraticDyadicDivisors_card N₁ i)
        (by positivity)) (quadraticDivisorMoment_nonneg N₁ a)
  · apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by exact_mod_cast quadraticDyadicDivisors_card N₂ j)
        (by positivity)) (quadraticDivisorMoment_nonneg N₂ b)

end Ostmann

end OAI
