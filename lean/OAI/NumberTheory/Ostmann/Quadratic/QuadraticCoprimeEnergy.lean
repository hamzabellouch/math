import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdExpansion
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCoprimeMask
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveDivisibility

namespace OAI

/-! # Möbius expansion of the coprime quadratic bilinear form -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

 theorem coprime_mask_truncated (n₁ n₂ N : ℕ) (hn₂ : 0 < n₂) (hN : n₂ ≤ N) :
    (if n₁.Coprime n₂ then (1 : ℂ) else 0) =
      ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℂ) *
        (if d ∣ n₁ then 1 else 0) * (if d ∣ n₂ then 1 else 0) := by
  have hc := congrArg (Int.cast : ℤ → ℂ) (coprime_mask_moebius n₂ n₁ hn₂.ne')
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_sum] at hc
  rw [hc]
  have hsub : n₂.divisors ⊆ Finset.Icc 1 N := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
      (Nat.le_of_dvd hn₂ (Nat.dvd_of_mem_divisors hd)).trans hN⟩
  have hh := Finset.sum_subset hsub
    (f := fun d => (ArithmeticFunction.moebius d : ℂ) *
      (if d ∣ n₁ then 1 else 0) * (if d ∣ n₂ then 1 else 0)) (by
        intro d _ hd
        have hd₂ : ¬d ∣ n₂ := fun h => hd (Nat.mem_divisors.mpr ⟨h, hn₂.ne'⟩)
        simp [hd₂])
  rw [← hh]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Nat.dvd_of_mem_divisors hd, ite_true, mul_one]
  split_ifs <;> simp

private theorem coprime_kernel_coefficient (N n₁ n₂ : ℕ)
    (h₁ : n₁ ∈ oddSquarefreeRange N) (h₂ : n₂ ∈ oddSquarefreeRange N)
    (b : ℕ → ℂ) (m : ℤ) :
    (if n₁.gcd n₂ = 1 then
      b n₁ * conj (b n₂) * (jacobiSym m (quadraticPairKernel n₁ n₂) : ℂ) else 0) =
      ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℂ) *
        (if d ∣ n₁ then b n₁ else 0) * conj (if d ∣ n₂ then b n₂ else 0) *
        (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ) := by
  obtain ⟨hr₁, _, hs₁⟩ := Finset.mem_filter.mp h₁
  obtain ⟨hr₂, _, hs₂⟩ := Finset.mem_filter.mp h₂
  have hm := coprime_mask_truncated n₁ n₂ N
    (Finset.mem_Icc.mp hr₂).1 (Finset.mem_Icc.mp hr₂).2
  have hj : (if n₁.gcd n₂ = 1 then
      b n₁ * conj (b n₂) * (jacobiSym m (quadraticPairKernel n₁ n₂) : ℂ) else 0) =
      (b n₁ * conj (b n₂) * (jacobiSym m n₁ : ℂ) * (jacobiSym m n₂ : ℂ)) *
        (if n₁.Coprime n₂ then 1 else 0) := by
    by_cases h : n₁.Coprime n₂
    · have hg := h.gcd_eq_one
      rw [ite_eq_left hg, ite_eq_left h, mul_one]
      simp only [quadraticPairKernel, hg, Nat.div_one]
      rw [jacobiSym.mul_right' m hs₁.ne_zero hs₂.ne_zero]
      push_cast
      ring
    · have hg : n₁.gcd n₂ ≠ 1 := h
      rw [ite_eq_right hg, ite_eq_right h, mul_zero]
  rw [hj, hm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd₁ : d ∣ n₁ <;> by_cases hd₂ : d ∣ n₂ <;>
    simp [hd₁, hd₂, mul_assoc, mul_left_comm, mul_comm]

 theorem quadratic_coprime_energy_expansion (N : ℕ) (b : ℕ → ℂ) (m : ℤ) :
    quadraticGcdKernelSum N 1 b m =
      ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℂ) *
        (‖quadraticTransposeSum N (fun n => if d ∣ n then b n else 0) m‖ ^ 2 : ℂ) := by
  unfold quadraticGcdKernelSum quadraticGcdPairs
  rw [Finset.sum_filter]
  calc
    _ = ∑ z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N),
        ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℂ) *
          (if d ∣ z.1 then b z.1 else 0) * conj (if d ∣ z.2 then b z.2 else 0) *
          (jacobiSym m z.1 : ℂ) * (jacobiSym m z.2 : ℂ) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact coprime_kernel_coefficient N z.1 z.2
        (Finset.mem_product.mp hz).1 (Finset.mem_product.mp hz).2 b m
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [quadraticTranspose_norm_sq_expand, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

end Ostmann

end OAI
