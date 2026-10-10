import OAI.NumberTheory.Ostmann.Arithmetic.DivisorGrowth
import OAI.NumberTheory.Ostmann.QuadraticSieveMainRemainderBound

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate

theorem mainRemainder_character_sum_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K Δ N : ℕ), 0 < K → 0 < Δ → Δ ≤ N →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), S ⊆ oddSquarefreeUpTo N →
      (∀ n ∈ S, Nat.Coprime n Δ) →
      ‖∑ w ∈ Finset.Ioc K (K * Δ ^ 2),
        ((mainRemainder K Δ w : ℂ) / (Real.sqrt (w : ℝ) : ℂ)) *
          coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) 1 (w : ℤ)‖ ≤
        C * (N : ℝ) ^ ε / Real.sqrt (K : ℝ) *
          quadraticNorm (oddSquarefreeUpTo (K * Δ ^ 2)) (oddSquarefreeUpTo N) *
          coefficientEnergy S a := by
  obtain ⟨C₁, hC₁, hdiv⟩ := Ostmann.Arithmetic.divisors_card_pow_le_rpow 2 (ε / 2) (by positivity)
  obtain ⟨C₂, hC₂, hrow⟩ := coprime_jacobi_L1_bound (ε / 2) (by positivity)
  refine ⟨2 * C₁ * C₂, by positivity, ?_⟩
  intro K Δ N hK hΔ hΔN S a hS hcop
  have hN : 0 < N := hΔ.trans_le hΔN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) = (N : ℝ) ^ ε := by
    rw [← Real.rpow_add hNr]
    congr 1
    ring
  have hd : (Δ.divisors.card : ℝ) ^ 2 ≤ C₁ * (N : ℝ) ^ (ε / 2) :=
    (hdiv Δ hΔ).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg Δ) (by exact_mod_cast hΔN) (by positivity)) hC₁.le)
  have hr := hrow (oddSquarefreeUpTo (K * Δ ^ 2)) S a N hN
    (fun v hv => (mem_oddSquarefreeUpTo.mp hv).2.2.1) hS
  have hQ := quadraticNorm_nonneg (oddSquarefreeUpTo (K * Δ ^ 2)) (oddSquarefreeUpTo N)
  have hE := coefficientEnergy_nonneg S a
  have hsum : 0 ≤ ∑ r ∈ oddSquarefreeUpTo (K * Δ ^ 2),
      ‖coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) 1 (r : ℤ)‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc
    _ ≤ (2 * (Δ.divisors.card : ℝ) ^ 2 / Real.sqrt (K : ℝ)) *
        ∑ r ∈ oddSquarefreeUpTo (K * Δ ^ 2),
          ‖coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) 1 (r : ℤ)‖ :=
      mainRemainder_character_sum_le K Δ hK hΔ S a
        (fun n hn => ⟨(mem_oddSquarefreeUpTo.mp (hS hn)).1, hcop n hn⟩)
    _ ≤ (2 * (C₁ * (N : ℝ) ^ (ε / 2)) / Real.sqrt (K : ℝ)) *
        (C₂ * (N : ℝ) ^ (ε / 2) *
          quadraticNorm (oddSquarefreeUpTo (K * Δ ^ 2)) (oddSquarefreeUpTo N) *
          coefficientEnergy S a) := by
      apply mul_le_mul _ hr hsum (by positivity)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num))
        (Real.sqrt_nonneg _)
    _ = (2 * C₁ * C₂) * ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2)) /
        Real.sqrt (K : ℝ) *
        quadraticNorm (oddSquarefreeUpTo (K * Δ ^ 2)) (oddSquarefreeUpTo N) *
        coefficientEnergy S a := by ring
    _ = _ := by rw [hpow]

end Ostmann.QuadraticSieve

end OAI
