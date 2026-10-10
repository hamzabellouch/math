import OAI.NumberTheory.Ostmann.QuadraticSieveLeadingConvolution

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate
open scoped ArithmeticFunction.Moebius

noncomputable def dualLeadingCorrelation (M : ℝ) (I : ℂ) (K Δ : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  (I / 2) * ∑ b ∈ oddSquarefreeUpTo K, (Real.sqrt (M / b) : ℂ) *
    ∑ n ∈ S, ∑ t ∈ S, if Nat.Coprime n t then
      a n * conj (a t) * ((Nat.totient (n*t) : ℂ) / (n*t : ℕ)) *
        leadingDivisorCoefficient Δ (n*t) * (jacobiSym (b : ℤ) (n*t) : ℂ) else 0

noncomputable def complementLeadingCorrelation (M : ℝ) (I : ℂ) (K Δ : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) : ℂ :=
  I * ∑ v ∈ oddSquarefreeUpTo K, (Real.sqrt (M / v) : ℂ) *
    ∑ n ∈ S, ∑ t ∈ S, if Nat.Coprime n t ∧ Nat.Coprime v Δ then
      a n * conj (a t) * ((Nat.totient (2*(n*t)*Δ) : ℂ) / (2*(n*t)*Δ : ℕ)) *
        (jacobiSym (v : ℤ) (n*t) : ℂ) else 0

theorem dualLeadingCorrelation_eq (M : ℝ) (hM : 0 ≤ M) (I : ℂ) (K Δ : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    dualLeadingCorrelation M I K Δ S a = (I / 2) * (Real.sqrt M : ℂ) *
      ∑ e ∈ Δ.divisors, (μ e : ℂ) * ∑ b ∈ oddSquarefreeUpTo K,
        coprimeTotientJacobiRow S a ((e*b : ℕ) : ℤ) /
          (Real.sqrt ((e*b : ℕ) : ℝ) : ℂ) := by
  rw [dualLeadingCorrelation, ← dual_leading_eq_convolution K Δ S a]
  simp only [Real.sqrt_div hM,Complex.ofReal_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring_nf

theorem complementLeadingCorrelation_eq (M : ℝ) (hM : 0 ≤ M) (I : ℂ) (K Δ : ℕ)
    (hΔ : 0 < Δ) (hodd : Odd Δ) (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n ∧ Odd n ∧ Nat.Coprime n Δ) :
    complementLeadingCorrelation M I K Δ S a = (I / 2) * (Real.sqrt M : ℂ) *
      ∑ u ∈ Δ.divisors, (μ u : ℂ) * ∑ v ∈ oddSquarefreeUpTo K,
        if Nat.Coprime v Δ then
          coprimeTotientJacobiRow S a ((u^2*v : ℕ) : ℤ) /
            (Real.sqrt ((u^2*v : ℕ) : ℝ) : ℂ) else 0 := by
  rw [← complement_leading_eq_convolution K Δ hΔ S a
    (fun n hn => ⟨(hS n hn).1,(hS n hn).2.2⟩)]
  unfold complementLeadingCorrelation
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hc : Nat.Coprime v Δ
  · rw [ite_eq_left hc]
    simp only [coprimeTotientJacobiRow,
      Real.sqrt_div hM,Complex.ofReal_div,Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hnt : Nat.Coprime n t
    · rw [ite_eq_left (show Nat.Coprime n t ∧ Nat.Coprime v Δ from ⟨hnt,hc⟩),
        ite_eq_left hnt]
      have hqd : Nat.Coprime (n*t) Δ := (hS n hn).2.2.mul_left (hS t ht).2.2
      rw [complementary_totient_factor (n*t) Δ ((hS n hn).2.1.mul (hS t ht).2.1) hodd hqd]
      ring
    · rw [ite_eq_right (show ¬ (Nat.Coprime n t ∧ Nat.Coprime v Δ) from fun h => hnt h.1),
        ite_eq_right hnt]
      simp only [mul_zero,zero_div]
  · rw [ite_eq_right hc]
    simp only [mul_zero]
    apply Finset.sum_eq_zero
    intro n hn
    apply Finset.sum_eq_zero
    intro t ht
    rw [ite_eq_right (show ¬ (Nat.Coprime n t ∧ Nat.Coprime v Δ) from fun h => hc h.2)]
    simp only [mul_zero]

end Ostmann.QuadraticSieve

end OAI
