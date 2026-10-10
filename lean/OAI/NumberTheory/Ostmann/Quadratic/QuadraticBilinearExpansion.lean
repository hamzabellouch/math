import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCoprimeBound

namespace OAI

/-! # The two-array coprime expansion needed for divisor restrictions -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

noncomputable def quadraticCoprimeBilinear (N₁ N₂ : ℕ) (a b : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ n₁ ∈ oddSquarefreeRange N₁, ∑ n₂ ∈ oddSquarefreeRange N₂,
    (if n₁.Coprime n₂ then (1 : ℂ) else 0) *
      a n₁ * conj (b n₂) * (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ)

 theorem quadratic_coprime_bilinear_expansion (N₁ N₂ : ℕ) (a b : ℕ → ℂ) (m : ℤ) :
    quadraticCoprimeBilinear N₁ N₂ a b m =
      ∑ d ∈ Finset.Icc 1 N₂, (ArithmeticFunction.moebius d : ℂ) *
        quadraticTransposeSum N₁ (fun n => if d ∣ n then a n else 0) m *
        conj (quadraticTransposeSum N₂ (fun n => if d ∣ n then b n else 0) m) := by
  have hp (n₁ n₂ : ℕ) (hn₂ : n₂ ∈ oddSquarefreeRange N₂) :
      (if n₁.Coprime n₂ then (1 : ℂ) else 0) *
        a n₁ * conj (b n₂) * (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) =
      ∑ d ∈ Finset.Icc 1 N₂, (ArithmeticFunction.moebius d : ℂ) *
        (if d ∣ n₁ then a n₁ else 0) * conj (if d ∣ n₂ then b n₂ else 0) *
        (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) := by
    have hr := (Finset.mem_filter.mp hn₂).1
    rw [coprime_mask_truncated n₁ n₂ N₂ (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    by_cases h₁ : d ∣ n₁ <;> by_cases h₂ : d ∣ n₂ <;>
      simp [h₁, h₂, mul_left_comm, mul_comm]
  unfold quadraticCoprimeBilinear
  calc
    _ = ∑ n₁ ∈ oddSquarefreeRange N₁, ∑ n₂ ∈ oddSquarefreeRange N₂,
        ∑ d ∈ Finset.Icc 1 N₂, (ArithmeticFunction.moebius d : ℂ) *
          (if d ∣ n₁ then a n₁ else 0) * conj (if d ∣ n₂ then b n₂ else 0) *
          (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) := by
      apply Finset.sum_congr rfl
      intro n₁ _
      exact Finset.sum_congr rfl (fun n₂ hn₂ => hp n₁ n₂ hn₂)
    _ = ∑ n₁ ∈ oddSquarefreeRange N₁, ∑ d ∈ Finset.Icc 1 N₂,
        ∑ n₂ ∈ oddSquarefreeRange N₂, (ArithmeticFunction.moebius d : ℂ) *
          (if d ∣ n₁ then a n₁ else 0) * conj (if d ∣ n₂ then b n₂ else 0) *
          (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ d ∈ Finset.Icc 1 N₂, ∑ n₁ ∈ oddSquarefreeRange N₁,
        ∑ n₂ ∈ oddSquarefreeRange N₂, (ArithmeticFunction.moebius d : ℂ) *
          (if d ∣ n₁ then a n₁ else 0) * conj (if d ∣ n₂ then b n₂ else 0) *
          (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      simp only [quadraticTransposeSum, map_sum, map_mul, map_intCast,
        Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n₁ _
      apply Finset.sum_congr rfl
      intro n₂ _
      ring

end Ostmann

end OAI
