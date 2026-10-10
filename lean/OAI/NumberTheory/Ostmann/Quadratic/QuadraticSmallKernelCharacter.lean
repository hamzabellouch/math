import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallKernels
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCoprimeMask

namespace OAI

/-! # The literal character after the small-kernel reindexing -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem jacobi_square_mul (a : ℕ) (b : ℤ) {q : ℕ} (hq : q ≠ 0) :
    jacobiSym ((a : ℤ) ^ 2 * b) q =
      if a.Coprime q then jacobiSym b q else 0 := by
  rw [jacobiSym.mul_left, jacobiSym.pow_left]
  split_ifs with h
  · rw [jacobiSym.sq_one (by exact h), one_mul]
  · rw [(jacobiSym.eq_zero_iff).mpr ⟨hq, by exact h⟩,
      zero_pow (by decide : 2 ≠ 0), zero_mul]

 theorem jacobi_pair_square_mul (a b : ℕ) {n₁ n₂ : ℕ}
    (h₁ : Squarefree n₁) (h₂ : Squarefree n₂) :
    (jacobiSym (a ^ 2 * b : ℕ) n₁ : ℂ) * (jacobiSym (a ^ 2 * b : ℕ) n₂ : ℂ) =
      (if a.Coprime (n₁ * n₂) then (1 : ℂ) else 0) *
      (if b.Coprime (n₁.gcd n₂) then (1 : ℂ) else 0) *
      (jacobiSym b (quadraticPairKernel n₁ n₂) : ℂ) := by
  have ht : n₁ * n₂ ≠ 0 := mul_ne_zero h₁.ne_zero h₂.ne_zero
  rw [← Int.cast_mul, ← jacobiSym.mul_right' _ h₁.ne_zero h₂.ne_zero]
  push_cast
  rw [jacobi_square_mul _ _ ht]
  have hb := jacobi_pair_kernel h₁ h₂ (b : ℤ)
  rw [← jacobiSym.mul_right' _ h₁.ne_zero h₂.ne_zero] at hb
  have hb' : jacobiSym (b : ℤ) (n₁ * n₂) =
      if b.Coprime (n₁.gcd n₂) then jacobiSym (b : ℤ) (quadraticPairKernel n₁ n₂) else 0 := hb
  rw [hb']
  split_ifs <;> simp

 theorem quadratic_small_kernel_pair_sum (M K : ℕ) (w : ℕ → ℂ)
    {n₁ n₂ : ℕ} (h₁ : Squarefree n₁) (h₂ : Squarefree n₂) :
    (∑ m ∈ quadraticSmallKernelRange M K,
      w m * (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ)) =
      ∑ z ∈ quadraticSmallKernelPairs M K,
        w (z.1 ^ 2 * z.2) *
        (if z.1.Coprime (n₁ * n₂) then (1 : ℂ) else 0) *
        (if z.2.Coprime (n₁.gcd n₂) then (1 : ℂ) else 0) *
        (jacobiSym z.2 (quadraticPairKernel n₁ n₂) : ℂ) := by
  rw [sum_quadraticSmallKernelRange]
  apply Finset.sum_congr rfl
  intro z _
  rw [mul_assoc (w _) (jacobiSym _ n₁ : ℂ), jacobi_pair_square_mul _ _ h₁ h₂]
  ring

end Ostmann

end OAI
