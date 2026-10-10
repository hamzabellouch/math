import OAI.NumberTheory.Ostmann.QuadraticSieveLeadingCorrelations

namespace OAI

namespace Ostmann.QuadraticSieve

theorem leading_correlations_difference_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ) (I : ℂ) (K Δ N : ℕ),
      0 < M → 0 < K → 0 < Δ → Odd Δ → Δ ≤ N →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), S ⊆ oddSquarefreeUpTo N →
      (∀ n ∈ S, Nat.Coprime n Δ) →
      ‖dualLeadingCorrelation M I K Δ S a - complementLeadingCorrelation M I K Δ S a‖ ≤
        C * (‖I‖ / 2) * (N : ℝ) ^ ε * Real.sqrt (M / K) *
          quadraticNorm (oddSquarefreeUpTo (K * Δ ^ 2)) (oddSquarefreeUpTo N) *
          coefficientEnergy S a := by
  obtain ⟨C,hC,hbound⟩ := totient_mainConvolution_difference_bound ε hε
  refine ⟨C,hC,?_⟩
  intro M I K Δ N hM hK hΔ hodd hΔN S a hS hcop
  have hSmem (n : ℕ) (hn : n ∈ S) : 0 < n ∧ Odd n ∧ Nat.Coprime n Δ := by
    have h := mem_oddSquarefreeUpTo.mp (hS hn)
    exact ⟨h.1,h.2.2.1,hcop n hn⟩
  rw [dualLeadingCorrelation_eq M hM.le I K Δ S a,
    complementLeadingCorrelation_eq M hM.le I K Δ hΔ hodd S a hSmem,←mul_sub]
  have h := hbound K Δ N hK hΔ hodd hΔN S a hS hcop
  dsimp only at h
  rw [norm_mul,norm_mul,norm_div,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg M)]
  calc
    _ ≤ (‖I‖/2*Real.sqrt M) *
        (C*(N : ℝ)^ε/Real.sqrt K *
          quadraticNorm (oddSquarefreeUpTo (K*Δ^2)) (oddSquarefreeUpTo N)*coefficientEnergy S a) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by rw [Real.sqrt_div hM.le]; ring

end Ostmann.QuadraticSieve

end OAI
