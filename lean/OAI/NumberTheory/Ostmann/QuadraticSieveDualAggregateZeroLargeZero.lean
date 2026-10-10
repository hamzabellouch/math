import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateZeroLargePartition

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate

theorem dual_zero_all_rows_bound (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (M H T R A ξ : ℝ) (K e N : ℕ)
      (S : Finset ℕ) (a : ℕ → ℂ) (c : ℤ) (g : ℕ → ℕ → ℂ),
      0<M → 0<H → 1≤T → 0≤R → 0≤A → 1<ξ → ξ≤2 → 0<K → 0<e → 0<N →
      (N:ℝ)≤2*H → S ⊆ oddSquarefreeUpTo N → (∀ n ∈ S, H≤(n:ℝ)) →
      (∀ j ∈ Finset.range (Nat.log 2 K+1), ∀ q : ℕ, 0<q →
        quadraticNorm (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/q)) ≤
          R*(((2*2^j:ℕ):ℝ)^ξ+(N:ℝ)/q)) →
      (∀ d v : ℕ, ‖g d v‖≤A) →
      (∀ d v : ℕ, g d v≠0 → (d:ℝ)≤dualWindowUpper M H T e v) →
      ‖∑ v ∈ oddSquarefreeUpTo K, ∑ d ∈ Finset.Icc 1 (N^2),
        ((M/e:ℝ):ℂ)*g d v*gaussProductDivisorJacobiRow S S a (fun n => conj (a n)) c d (v:ℤ)‖ ≤
        (Nat.log 2 K+1:ℕ)*(Nat.log 2 (N^2)+2:ℕ)*
          (32*A*T*R)*Real.sqrt (C*(N:ℝ)^ε*coefficientEnergy S a*coefficientEnergy S a)*
            (M+Real.sqrt M*(K:ℝ)^(ξ-1/2)) := by
  obtain ⟨C₀,hC₀,hann⟩ := dual_zero_active_range_bound ε hε
  obtain ⟨C₁,hC₁,hboundary⟩ := dual_zero_active_boundary_bound ε hε
  refine ⟨C₀+C₁,by positivity,?_⟩
  intro M H T R A ξ K e N S a c g hM hH hT hR hA hξ hξ2 hK he hN hNH hS hSH hnorm hg hsupp
  have hE := coefficientEnergy_nonneg S a
  have hC0 : C₀≤C₀+C₁ := by linarith
  have hC1 : C₁≤C₀+C₁ := by linarith
  have hrec (j : ℕ) (hj : j ∈ Finset.range (Nat.log 2 K+1)) :
      M+Real.sqrt (M/(2^j:ℕ))*(((2*2^j:ℕ):ℝ)^ξ) ≤
        4*(M+Real.sqrt M*(K:ℝ)^(ξ-1/2)) := by
    have hb : (((2^j:ℕ):ℝ))≤K := by exact_mod_cast binary_base_le_cutoff hK hj
    have hh := binary_recursion_term_le hM
      (by positivity : (0:ℝ)<(2^j:ℕ)) hb hξ hξ2
    have hc : ((2*2^j:ℕ):ℝ)=2*((2^j:ℕ):ℝ) := by norm_cast
    simpa only [hc] using hh
  let B : ℝ := (8*A*T*R)*
    Real.sqrt ((C₀+C₁)*(N:ℝ)^ε*coefficientEnergy S a*coefficientEnergy S a)*
      (4*(M+Real.sqrt M*(K:ℝ)^(ξ-1/2)))
  have hfirst (j : ℕ) (hj : j ∈ Finset.range (Nat.log 2 K+1)) :
      ‖∑ v ∈ binarySquarefreeRows K j, ((M/e:ℝ):ℂ)*g 1 v*gaussProductDivisorJacobiRow S S a (fun n => conj (a n)) c 1 (v:ℤ)‖≤B := by
    have hb := hboundary M H T (((2*2^j:ℕ):ℝ)^ξ) R A K j e N S a c (g 1)
      hM hH hT (by positivity) hR hA he hN hNH hS hSH (hnorm j hj)
      (fun v hv => hg 1 v) (fun v hv hnz => by simpa only [Nat.cast_one] using hsupp 1 v hnz)
    apply hb.trans
    dsimp only [B]
    gcongr
    exact hrec j hj
  have hblocks (j : ℕ) (hj : j ∈ Finset.range (Nat.log 2 K+1))
      (k : ℕ) (hk : k ∈ Finset.range (Nat.log 2 (N^2)+1)) :
      ‖∑ d ∈ Finset.Ioc (2^k) (2*2^k), ∑ v ∈ binarySquarefreeRows K j,
        if d≤N^2 then ((M/e:ℝ):ℂ)*g d v*gaussProductDivisorJacobiRow S S a (fun n => conj (a n)) c d (v:ℤ) else 0‖≤B := by
    let g' : ℕ → ℕ → ℂ := fun d v => if d≤N^2 then g d v else 0
    have hg' (d v : ℕ) : ‖g' d v‖≤A := by
      dsimp only [g']
      split_ifs
      · exact hg d v
      · simpa only [norm_zero] using hA
    have hs' (d v : ℕ) (hh : g' d v≠0) : (d:ℝ)≤dualWindowUpper M H T e v := by
      have hnz : g d v≠0 := by
        intro hz
        apply hh
        simp only [g',hz,ite_self]
      exact hsupp d v hnz
    have hb := hann M H T (((2*2^j:ℕ):ℝ)^ξ) R A K j e (2^k) N S a c g'
      hM hH hT (by positivity) hR hA he (by positivity) hN hNH hS hSH
      (hnorm j hj) (fun d hd v hv => hg' d v) (fun d hd v hv hnz => hs' d v hnz)
    have heq : (∑ d ∈ Finset.Ioc (2^k) (2*2^k), ∑ v ∈ binarySquarefreeRows K j,
        ((M/e:ℝ):ℂ)*g' d v*gaussProductDivisorJacobiRow S S a (fun n => conj (a n)) c d (v:ℤ)) =
        ∑ d ∈ Finset.Ioc (2^k) (2*2^k), ∑ v ∈ binarySquarefreeRows K j,
          if d≤N^2 then ((M/e:ℝ):ℂ)*g d v*gaussProductDivisorJacobiRow S S a (fun n => conj (a n)) c d (v:ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro v hv
      dsimp only [g']
      split_ifs <;> ring
    rw [heq] at hb
    apply hb.trans
    dsimp only [B]
    gcongr
    exact hrec j hj
  have hh := dual_zero_large_partition_bound K N hN
    (fun d v => ((M/e:ℝ):ℂ)*g d v*gaussProductDivisorJacobiRow S S a (fun n => conj (a n)) c d (v:ℤ)) B hfirst hblocks
  convert hh using 1
  dsimp only [B]
  ring

end Ostmann.QuadraticSieve

end OAI
