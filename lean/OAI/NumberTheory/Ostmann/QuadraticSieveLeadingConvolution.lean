import OAI.NumberTheory.Ostmann.QuadraticSieveLeadingArithmetic
import OAI.NumberTheory.Ostmann.QuadraticSieveTotientRows

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate
open scoped ArithmeticFunction.Moebius

theorem leadingDivisor_totient_row (Δ b : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ S, ∑ t ∈ S, if Nat.Coprime n t then
      a n * conj (a t) * ((Nat.totient (n*t) : ℂ) / (n*t : ℕ)) *
        leadingDivisorCoefficient Δ (n*t) * (jacobiSym (b : ℤ) (n*t) : ℂ) else 0) =
      ∑ e ∈ Δ.divisors, ((μ e : ℂ) / (Real.sqrt (e : ℝ) : ℂ)) *
        coprimeTotientJacobiRow S a ((e*b : ℕ) : ℤ) := by
  classical
  let F : ℕ → ℕ → ℕ → ℂ := fun n t e => if Nat.Coprime n t then
    ((μ e : ℂ) / (Real.sqrt (e : ℝ) : ℂ)) *
      (a n * conj (a t) * ((Nat.totient (n*t) : ℂ) / (n*t : ℕ)) *
        (jacobiSym ((e*b : ℕ) : ℤ) (n*t) : ℂ)) else 0
  calc
    _ = ∑ n ∈ S, ∑ t ∈ S, ∑ e ∈ Δ.divisors, F n t e := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hc : Nat.Coprime n t
      · simp only [ite_eq_left hc, F, leadingDivisorCoefficient, Finset.mul_sum,
          Finset.sum_mul, Nat.cast_mul, jacobiSym.mul_left, Int.cast_mul]
        apply Finset.sum_congr rfl
        intro e he
        ring
      · simp [F,hc]
    _ = ∑ n ∈ S, ∑ e ∈ Δ.divisors, ∑ t ∈ S, F n t e := by
      apply Finset.sum_congr rfl
      intro n hn
      exact Finset.sum_comm
    _ = ∑ e ∈ Δ.divisors, ∑ n ∈ S, ∑ t ∈ S, F n t e := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [coprimeTotientJacobiRow,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hc : Nat.Coprime n t <;> simp [F,hc]

theorem dual_leading_eq_convolution (K Δ : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ b ∈ oddSquarefreeUpTo K, (1 / (Real.sqrt (b : ℝ) : ℂ)) *
      ∑ n ∈ S, ∑ t ∈ S, if Nat.Coprime n t then
        a n * conj (a t) * ((Nat.totient (n*t) : ℂ) / (n*t : ℕ)) *
          leadingDivisorCoefficient Δ (n*t) * (jacobiSym (b : ℤ) (n*t) : ℂ) else 0) =
      ∑ e ∈ Δ.divisors, (μ e : ℂ) * ∑ b ∈ oddSquarefreeUpTo K,
        coprimeTotientJacobiRow S a ((e*b : ℕ) : ℤ) /
          (Real.sqrt ((e*b : ℕ) : ℝ) : ℂ) := by
  simp_rw [leadingDivisor_totient_row,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Nat.cast_mul]
  rw [Real.sqrt_mul (Nat.cast_nonneg e),Complex.ofReal_mul]
  ring

theorem coprimeTotientJacobiRow_square (Δ u : ℕ) (S : Finset ℕ) (a : ℕ → ℂ)
    (hu : u ∣ Δ) (v : ℤ) (hS : ∀ n ∈ S, 0 < n ∧ Nat.Coprime n Δ) :
    coprimeTotientJacobiRow S a ((u : ℤ)^2*v) = coprimeTotientJacobiRow S a v := by
  rw [coprimeTotientJacobiRow_eq,coprimeTotientJacobiRow_eq]
  exact coprimeProductDivisorJacobiRow_square S S (totientCoefficients a)
    (fun n => conj (totientCoefficients a n)) 1 Δ u hu v hS hS

theorem complement_leading_eq_convolution (K Δ : ℕ) (hΔ : 0 < Δ)
    (S : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, 0 < n ∧ Nat.Coprime n Δ) :
    ((Nat.totient Δ : ℂ) / (Δ : ℂ)) *
      (∑ v ∈ oddSquarefreeUpTo K, if Nat.Coprime v Δ then
        coprimeTotientJacobiRow S a (v : ℤ) / (Real.sqrt (v : ℝ) : ℂ) else 0) =
      ∑ u ∈ Δ.divisors, (μ u : ℂ) * ∑ v ∈ oddSquarefreeUpTo K,
        if Nat.Coprime v Δ then
          coprimeTotientJacobiRow S a ((u^2*v : ℕ) : ℤ) /
            (Real.sqrt ((u^2*v : ℕ) : ℝ) : ℂ) else 0 := by
  classical
  rw [← sum_moebius_div_divisors Δ hΔ,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hc : Nat.Coprime v Δ
  · rw [ite_eq_left hc,ite_eq_left hc]
    have hrow : coprimeTotientJacobiRow S a ((u^2*v : ℕ) : ℤ) =
        coprimeTotientJacobiRow S a (v : ℤ) := by
      push_cast
      exact coprimeTotientJacobiRow_square Δ u S a (Nat.mem_divisors.mp hu).1 v hS
    rw [hrow,Nat.cast_mul,Nat.cast_pow,Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (Nat.cast_nonneg u),Complex.ofReal_mul]
    push_cast
    ring
  · simp only [ite_eq_right hc,mul_zero]

end Ostmann.QuadraticSieve

end OAI
