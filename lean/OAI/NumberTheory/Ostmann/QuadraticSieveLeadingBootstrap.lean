import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateNorm
import OAI.NumberTheory.Ostmann.QuadraticSieveLeadingBootstrapScales
import OAI.NumberTheory.Ostmann.QuadraticSieveLeadingCancellation

namespace OAI

namespace Ostmann.QuadraticSieve

theorem leading_correlations_bootstrap {ξ : ℝ}
    (_hξ1 : 1<ξ) (hξ2 : ξ≤2)
    (hξ : ExponentBound
      (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (M P : ℝ) (I : ℂ) (K Δ N : ℕ),
      1≤M → 1≤P → 0<K → 0<Δ → 0<N → (K:ℝ)≤P^3 →
      (Δ:ℝ)≤P → (N:ℝ)≤P → Odd Δ → Δ≤N →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), S ⊆ oddSquarefreeUpTo N →
      (∀ n ∈ S, n.Coprime Δ) → Real.sqrt (M/K)*N≤M →
      ‖dualLeadingCorrelation M I K Δ S a - complementLeadingCorrelation M I K Δ S a‖ ≤
        C*‖I‖*P^ε*(Δ:ℝ)^4*(M+Real.sqrt M*(K:ℝ)^(ξ-1/2))*coefficientEnergy S a := by
  let δ : ℝ := ε/7
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨C₀,hC₀,hcancel⟩ := leading_correlations_difference_bound δ hδ
  obtain ⟨C₁,hC₁,hsmall⟩ := exponentBound_smaller_norm hξ δ hδ
  refine ⟨C₀*C₁,mul_pos hC₀ hC₁,?_⟩
  intro M P I K Δ N hM hP hK hΔ hN hKP hΔP hNP hodd hΔN S a hS hcop hsqrt
  have hMp : 0<M := by linarith
  have hKr : (0:ℝ)<K := by exact_mod_cast hK
  have hΔr : (1:ℝ)≤Δ := by exact_mod_cast hΔ
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hE := coefficientEnergy_nonneg S a
  have hQ : quadraticNorm (oddSquarefreeUpTo (K*Δ^2)) (oddSquarefreeUpTo N) ≤
      C₁*((K:ℝ)*(Δ:ℝ)^2*N)^δ*(((K:ℝ)*(Δ:ℝ)^2)^ξ+(N:ℝ)) := by
    have hb := hsmall (K*Δ^2) N 1 (oddSquarefreeUpTo (K*Δ^2)) (by positivity) hN
      (by norm_num) (Finset.Subset.refl _)
    have hcast : ((K*Δ^2:ℕ):ℝ)=(K:ℝ)*(Δ:ℝ)^2 := by norm_cast
    rw [hcast] at hb
    simpa only [Nat.div_one, Nat.cast_one, div_one] using hb
  have hpowers : (N:ℝ)^δ*((K:ℝ)*(Δ:ℝ)^2*N)^δ ≤ P^ε := by
    have he : 7*δ=ε := by dsimp only [δ]; ring
    simpa only [he] using leading_bootstrap_power_budget hP hKr.le
      (Nat.cast_nonneg Δ) hNr.le hKP hΔP hNP hδ.le
  have hscalar := leading_bootstrap_scalar_budget hMp hKr hΔr hξ2 hsqrt
  have hhalf : ‖I‖/2≤‖I‖ := by linarith [norm_nonneg I]
  calc
    _ ≤ C₀*(‖I‖/2)*(N:ℝ)^δ*Real.sqrt (M/K)*
        quadraticNorm (oddSquarefreeUpTo (K*Δ^2)) (oddSquarefreeUpTo N)*
          coefficientEnergy S a :=
      hcancel M I K Δ N hMp hK hΔ hodd hΔN S a hS hcop
    _ ≤ C₀*(‖I‖/2)*(N:ℝ)^δ*Real.sqrt (M/K)*
        (C₁*((K:ℝ)*(Δ:ℝ)^2*N)^δ*(((K:ℝ)*(Δ:ℝ)^2)^ξ+(N:ℝ)))*
          coefficientEnergy S a := by gcongr
    _ = (C₀*C₁)*(‖I‖/2)*((N:ℝ)^δ*((K:ℝ)*(Δ:ℝ)^2*N)^δ)*
        (Real.sqrt (M/K)*(((K:ℝ)*(Δ:ℝ)^2)^ξ+(N:ℝ)))*coefficientEnergy S a := by ring
    _ ≤ (C₀*C₁)*‖I‖*P^ε*
        ((Δ:ℝ)^4*(M+Real.sqrt M*(K:ℝ)^(ξ-1/2)))*coefficientEnergy S a := by
      gcongr
    _ = _ := by ring

end Ostmann.QuadraticSieve

end OAI
