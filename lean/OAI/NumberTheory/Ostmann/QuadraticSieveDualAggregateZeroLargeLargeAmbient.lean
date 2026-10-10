import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateZeroLargeEnergy
import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateZeroLargeLarge

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate

theorem dual_large_all_rows_ambient {ξ : ℝ} (hξ1 : 1<ξ) (hξ2 : ξ≤2)
    (hξ : ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (M H P η A : ℝ) (K e N : ℕ)
      (S : Finset ℕ) (a : ℕ → ℂ) (c : ℤ) (g : ℕ → ℕ → ℂ),
      1≤M → 0<H → 1≤P → 0<η → η≤ε/100 → 0≤A → 0<K → 0<e → 0<N →
      (N:ℝ)≤P → (K:ℝ)≤P^3 → (N:ℝ)≤2*H →
      S ⊆ oddSquarefreeUpTo N → (∀ n ∈ S, H≤(n:ℝ)) →
      (∀ d v : ℕ, ‖g d v‖≤A) →
      (∀ d v : ℕ, g d v≠0 → dualWindowLower M H (P^η) e v<(d:ℝ)) →
      ‖∑ v ∈ oddSquarefreeUpTo K, ∑ d ∈ Finset.Icc 1 (N^2),
        ((Real.sqrt (M/((e:ℝ)*v))/(d:ℝ):ℝ):ℂ)*g d v*gaussProductDivisorJacobiRow S S (sqrtCoefficients a)
          (sqrtCoefficients (fun n => conj (a n))) c d (v:ℤ)‖ ≤
        C*A*P^ε*(M+Real.sqrt M*(K:ℝ)^(ξ-1/2))*coefficientEnergy S a := by
  let δ : ℝ := ε/100
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨C₀,hC₀,hrows⟩ := dual_large_all_rows_bound (2*δ) (by positivity)
  obtain ⟨C₁,hC₁,hnorm⟩ := exponentBound_binary_smaller_norm hξ δ hδ
  obtain ⟨C₂,hC₂,hgrowth⟩ := dual_aggregate_depth_loss ε hε
  refine ⟨128*C₁*Real.sqrt C₀*C₂,by positivity,?_⟩
  intro M H P η A K e N S a c g hM hH hP hη hηε hA hK he hN hNP hKP hNH hS hSH hg hsupp
  have hMp : 0<M := by linarith
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hE := coefficientEnergy_nonneg S a
  have hb := hrows M H (P^η) (C₁*(((2*K:ℕ):ℝ)*N)^δ) A ξ K e N S a c g
    hMp hH (Real.one_le_rpow hP hη.le) (by positivity) hA hξ1 hξ2 hK he hN
    hNH hS hSH (fun j hj q hq => hnorm K N j q hK hN hj hq) hg hsupp
  rw [dual_zero_large_root_energy hC₀ hNr hE] at hb
  have hgrowth' : ((Nat.log 2 K+1:ℕ):ℝ)*((Nat.log 2 (N^2)+2:ℕ):ℝ)*
      (((2*K:ℕ):ℝ)*N)^δ*(N:ℝ)^δ*P^η≤C₂*P^ε :=
    hgrowth η P K N hη hηε hP hK hN hNP hKP
  calc
    _ ≤ _ := hb
    _ = (128*C₁*Real.sqrt C₀)*A*
        (((Nat.log 2 K+1:ℕ):ℝ)*((Nat.log 2 (N^2)+2:ℕ):ℝ)*
          (((2*K:ℕ):ℝ)*N)^δ*(N:ℝ)^δ*P^η)*
        (M+Real.sqrt M*(K:ℝ)^(ξ-1/2))*coefficientEnergy S a := by ring
    _ ≤ (128*C₁*Real.sqrt C₀)*A*(C₂*P^ε)*
        (M+Real.sqrt M*(K:ℝ)^(ξ-1/2))*coefficientEnergy S a := by gcongr
    _ = _ := by ring

end Ostmann.QuadraticSieve

end OAI
