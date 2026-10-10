import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateFourierDivisors

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate
open scoped SchwartzMap FourierTransform

noncomputable def dualAggregateFourierSum (W : 𝓢(ℝ,ℂ)) (M T : ℝ) (K Δ N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (g : ℕ → ℕ → ℕ → ℂ) : ℂ :=
  ∑ e ∈ (2*Δ).divisors, ∑ s ∈ signedSquarefreeMultipliers,
    ∑ d ∈ Finset.Icc 1 (N^2), ∑ v ∈ oddSquarefreeUpTo K,
      ((Real.sqrt (M/((e : ℝ)*v))/d : ℝ) : ℂ)*g e d v*
        (∑ l ∈ nonzeroIntegerCutoff (16*T^2), dualAggregateFourierRow W M e S a s l d v)

theorem dual_fourier_raw_sum_bound (W : 𝓢(ℝ,ℂ)) {ξ : ℝ}
    (hξ1 : 1 < ξ) (hξ2 : ξ ≤ 2)
    (hξ : ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ)
    (σ δ : ℝ) (hσ : 0 < σ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P M H T A : ℝ) (K Δ N : ℕ)
      (S : Finset ℕ) (a : ℕ → ℂ) (g : ℕ → ℕ → ℕ → ℂ),
      1 ≤ P → 0 < M → M ≤ P → 0 < H → 1 ≤ T → 0 ≤ A →
      0 < K → 0 < Δ → 0 < N → (N : ℝ) ≤ P → (K : ℝ) ≤ P^3 →
      (N : ℝ) ≤ 2*H → S ⊆ oddSquarefreeUpTo N → (∀ n ∈ S, H ≤ (n : ℝ)) →
      (∀ e ∈ (2*Δ).divisors, ∀ d, ∀ v ∈ oddSquarefreeUpTo K, ‖g e d v‖ ≤ A) →
      (∀ e ∈ (2*Δ).divisors, ∀ d, ∀ v ∈ oddSquarefreeUpTo K, g e d v ≠ 0 →
        dualWindowLower M H T e v < (d : ℝ)) →
      ‖dualAggregateFourierSum W M T K Δ N S a g‖ ≤
        C*A*(Nat.log 2 K+1 : ℕ)*(Nat.log 2 (N^2)+2 : ℕ)*(2*(K : ℝ)*N)^δ*(N : ℝ)^δ*
          (Δ : ℝ)*T^3*(2*Real.sqrt 2*P^4)^σ*
          (M+Real.sqrt M*(K : ℝ)^(ξ-1/2))*coefficientEnergy S a := by
  classical
  obtain ⟨Cf,hCf,hdiv⟩ := dual_fourier_divisor_sum_bound W σ δ hσ hδ
  obtain ⟨Cn,hCn,hnorm⟩ := exponentBound_binary_smaller_norm hξ δ hδ
  refine ⟨512*Cf*Cn,by positivity,?_⟩
  intro P M H T A K Δ N S a g hP hM hMP hH hT hA hK hΔ hN hNP hKP hNH hS hSH hg hsupp
  have hE := coefficientEnergy_nonneg S a
  let R : ℝ := Cn*(2*(K : ℝ)*N)^δ
  let U : ℝ := M+Real.sqrt M*(K : ℝ)^(ξ-1/2)
  let F : ℝ := (Nat.log 2 (N^2)+2 : ℕ)*(64*A*Cf*T^3*R)*(N : ℝ)^δ*
    (2*Real.sqrt 2*P^4)^σ*U*coefficientEnergy S a
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hF : 0 ≤ F := by dsimp [F,U]; positivity
  have hblock (e : ℕ) (he : e ∈ (2*Δ).divisors) (s : ℤ) (hs : s ∈ signedSquarefreeMultipliers)
      (j : ℕ) (hj : j ∈ Finset.range (Nat.log 2 K+1)) :
      ‖∑ d ∈ Finset.Icc 1 (N^2), ∑ v ∈ binarySquarefreeRows K j,
        ((Real.sqrt (M/((e : ℝ)*v))/d : ℝ) : ℂ)*g e d v*
          (∑ l ∈ nonzeroIntegerCutoff (16*T^2), dualAggregateFourierRow W M e S a s l d v)‖ ≤ F := by
    have hvsub : binarySquarefreeRows K j ⊆ oddSquarefreeUpTo K := Finset.filter_subset _ _
    have hn : ∀ q : ℕ, 0 < q → quadraticNorm (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/q)) ≤
        R*(((2*2^j : ℕ) : ℝ)^ξ+(N : ℝ)/q) := by
      intro q hq
      simpa only [R,Nat.cast_mul,Nat.cast_ofNat] using hnorm K N j q hK hN hj hq
    have hh := hdiv P M H T (((2*2^j : ℕ) : ℝ)^ξ) R A K j e N S a s (g e)
      hP hM hMP hH hT (by positivity) hR hA hK (Nat.pos_of_mem_divisors he) hN hNP hKP hj hNH hS hSH hs hn
      (fun d v hv => hg e he d v (hvsub hv))
      (fun d v hv hnz => hsupp e he d v (hvsub hv) hnz)
    have hbK : ((2^j : ℕ) : ℝ) ≤ K := by exact_mod_cast binary_base_le_cutoff hK hj
    have hscale := binary_recursion_term_le hM (by positivity : (0 : ℝ) < (2^j : ℕ)) hbK hξ1 hξ2
    push_cast at hscale
    apply hh.trans
    dsimp [F,U]
    push_cast
    calc
      _ ≤ (Nat.log 2 (N^2)+2 : ℕ)*(16*A*Cf*T^3*R)*(N : ℝ)^δ*
          (2*Real.sqrt 2*P^4)^σ*(4*(M+Real.sqrt M*(K : ℝ)^(ξ-1/2)))*coefficientEnergy S a := by
        push_cast
        gcongr
      _ = _ := by push_cast; ring
  have heBound (e : ℕ) (he : e ∈ (2*Δ).divisors) (s : ℤ) (hs : s ∈ signedSquarefreeMultipliers) :
      ‖∑ d ∈ Finset.Icc 1 (N^2), ∑ v ∈ oddSquarefreeUpTo K,
        ((Real.sqrt (M/((e : ℝ)*v))/d : ℝ) : ℂ)*g e d v*
          (∑ l ∈ nonzeroIntegerCutoff (16*T^2), dualAggregateFourierRow W M e S a s l d v)‖ ≤
        (Nat.log 2 K+1 : ℕ)*F := by
    simp_rw [sum_oddSquarefree_eq_dyadic K]
    rw [Finset.sum_comm]
    apply (norm_sum_le _ _).trans
    exact (Finset.sum_le_sum (hblock e he s hs)).trans_eq (by simp [nsmul_eq_mul])
  have hcard : (2*Δ).divisors.card ≤ 2*Δ := by
    calc
      _ ≤ (Finset.Icc 1 (2*Δ)).card := Finset.card_le_card (by
        intro e he
        exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors he,
          Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp he).1⟩)
      _ = _ := by simp
  unfold dualAggregateFourierSum
  calc
    _ ≤ ∑ e ∈ (2*Δ).divisors, ∑ s ∈ signedSquarefreeMultipliers,
        ‖∑ d ∈ Finset.Icc 1 (N^2), ∑ v ∈ oddSquarefreeUpTo K,
          ((Real.sqrt (M/((e : ℝ)*v))/d : ℝ) : ℂ)*g e d v*
            (∑ l ∈ nonzeroIntegerCutoff (16*T^2), dualAggregateFourierRow W M e S a s l d v)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e he => norm_sum_le _ _))
    _ ≤ (2*Δ).divisors.card*(4*((Nat.log 2 K+1 : ℕ)*F)) := by
      have hh := Finset.sum_le_sum (fun e he => Finset.sum_le_sum (heBound e he))
      simpa only [Finset.sum_const,nsmul_eq_mul,card_signedSquarefreeMultipliers,Nat.cast_ofNat] using hh
    _ ≤ (2*(Δ : ℝ))*(4*((Nat.log 2 K+1 : ℕ)*F)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by dsimp [F,R,U]; ring

end Ostmann.QuadraticSieve

end OAI
