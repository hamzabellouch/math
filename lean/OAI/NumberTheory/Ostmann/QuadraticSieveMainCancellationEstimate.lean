import OAI.NumberTheory.Ostmann.QuadraticSieveMainConvolutionTail
import OAI.NumberTheory.Ostmann.QuadraticSieveMainRemainderEstimate

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped ArithmeticFunction.Moebius
open ComplexConjugate

theorem mainConvolution_difference_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K Δ N : ℕ), 0 < K → 0 < Δ → Odd Δ → Δ ≤ N →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), S ⊆ oddSquarefreeUpTo N →
      (∀ n ∈ S, Nat.Coprime n Δ) →
      let f : ℕ → ℂ := fun w =>
        coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) 1 (w : ℤ) /
          (Real.sqrt (w : ℝ) : ℂ)
      ‖(∑ e ∈ Δ.divisors, (μ e : ℂ) * ∑ b ∈ oddSquarefreeUpTo K, f (e * b)) -
        (∑ u ∈ Δ.divisors, (μ u : ℂ) * ∑ v ∈ oddSquarefreeUpTo K,
          if Nat.Coprime v Δ then f (u ^ 2 * v) else 0)‖ ≤
        C * (N : ℝ) ^ ε / Real.sqrt (K : ℝ) *
          quadraticNorm (oddSquarefreeUpTo (K * Δ ^ 2)) (oddSquarefreeUpTo N) *
          coefficientEnergy S a := by
  obtain ⟨C,hC,hbound⟩ := mainRemainder_character_sum_bound ε hε
  refine ⟨C,hC,?_⟩
  intro K Δ N hK hΔ hodd hΔN S a hS hcop f
  rw [mainConvolution_difference_eq_tail K Δ hΔ hodd f]
  have heq : (∑ w ∈ Finset.Ioc K (K * Δ ^ 2), (mainRemainder K Δ w : ℂ) * f w) =
      ∑ w ∈ Finset.Ioc K (K * Δ ^ 2),
        ((mainRemainder K Δ w : ℂ) / (Real.sqrt (w : ℝ) : ℂ)) *
          coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) 1 (w : ℤ) := by
    apply Finset.sum_congr rfl
    intro w hw
    dsimp only [f]
    ring
  rw [heq]
  exact hbound K Δ N hK hΔ hΔN S a hS hcop

end Ostmann.QuadraticSieve

end OAI
