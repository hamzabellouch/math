import OAI.NumberTheory.Ostmann.QuadraticSieveLeadingIntegral
import OAI.NumberTheory.Ostmann.QuadraticSieveMainCancellationEstimate

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate

noncomputable def totientCoefficients (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((Nat.totient n : ℂ) / (n : ℂ)) * a n

theorem coefficientEnergy_totient_le (S : Finset ℕ) (a : ℕ → ℂ) :
    coefficientEnergy S (totientCoefficients a) ≤ coefficientEnergy S a := by
  unfold coefficientEnergy
  apply Finset.sum_le_sum
  intro n hn
  have hd : ‖(Nat.totient n : ℂ) / (n : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    by_cases hn0 : n = 0
    · simp [hn0]
    · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn0)).mpr
      exact_mod_cast Nat.totient_le n
  have he : ‖totientCoefficients a n‖ ≤ ‖a n‖ := by
    rw [totientCoefficients, norm_mul]
    exact (mul_le_mul_of_nonneg_right hd (norm_nonneg _)).trans_eq (one_mul _)
  exact pow_le_pow_left₀ (norm_nonneg _) he 2

noncomputable def coprimeTotientJacobiRow (S : Finset ℕ) (a : ℕ → ℂ) (m : ℤ) : ℂ :=
  ∑ n ∈ S, ∑ t ∈ S, if Nat.Coprime n t then
    a n * conj (a t) * ((Nat.totient (n * t) : ℂ) / (n * t : ℕ)) *
      (jacobiSym m (n * t) : ℂ) else 0

theorem coprimeTotientJacobiRow_eq (S : Finset ℕ) (a : ℕ → ℂ) (m : ℤ) :
    coprimeTotientJacobiRow S a m =
      coprimeProductDivisorJacobiRow S S (totientCoefficients a)
        (fun n => conj (totientCoefficients a n)) 1 m := by
  unfold coprimeTotientJacobiRow coprimeProductDivisorJacobiRow
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro t ht
  simp only [one_dvd, and_true]
  by_cases hnt : Nat.Coprime n t
  · rw [ite_eq_left hnt, ite_eq_left hnt, Nat.totient_mul hnt]
    simp only [totientCoefficients, map_mul, map_div₀, map_natCast, Nat.cast_mul]
    ring
  · rw [ite_eq_right hnt, ite_eq_right hnt]

theorem totient_mainConvolution_difference_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K Δ N : ℕ), 0 < K → 0 < Δ → Odd Δ → Δ ≤ N →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), S ⊆ oddSquarefreeUpTo N →
      (∀ n ∈ S, Nat.Coprime n Δ) →
      let f : ℕ → ℂ := fun w => coprimeTotientJacobiRow S a (w : ℤ) / (Real.sqrt (w : ℝ) : ℂ)
      ‖(∑ e ∈ Δ.divisors, (ArithmeticFunction.moebius e : ℂ) * ∑ b ∈ oddSquarefreeUpTo K, f (e * b)) -
        (∑ u ∈ Δ.divisors, (ArithmeticFunction.moebius u : ℂ) * ∑ v ∈ oddSquarefreeUpTo K,
          if Nat.Coprime v Δ then f (u ^ 2 * v) else 0)‖ ≤
        C * (N : ℝ) ^ ε / Real.sqrt (K : ℝ) *
          quadraticNorm (oddSquarefreeUpTo (K * Δ ^ 2)) (oddSquarefreeUpTo N) *
          coefficientEnergy S a := by
  obtain ⟨C,hC,hbound⟩ := mainConvolution_difference_bound ε hε
  refine ⟨C,hC,?_⟩
  intro K Δ N hK hΔ hodd hΔN S a hS hcop f
  have h := hbound K Δ N hK hΔ hodd hΔN S (totientCoefficients a) hS hcop
  dsimp only at h
  have hf : f = fun w : ℕ =>
      coprimeProductDivisorJacobiRow S S (totientCoefficients a)
        (fun n => conj (totientCoefficients a n)) 1 (w : ℤ) / (Real.sqrt (w : ℝ) : ℂ) := by
    funext w
    exact congrArg (fun z : ℂ => z / (Real.sqrt (w : ℝ) : ℂ)) (coprimeTotientJacobiRow_eq S a (w : ℤ))
  rw [hf]
  apply h.trans
  exact mul_le_mul_of_nonneg_left (coefficientEnergy_totient_le S a)
    (mul_nonneg (by positivity) (quadraticNorm_nonneg _ _))

end Ostmann.QuadraticSieve

end OAI
