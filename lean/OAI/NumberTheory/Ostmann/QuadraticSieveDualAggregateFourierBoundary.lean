import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateFourierBlocks
import OAI.NumberTheory.Ostmann.QuadraticSieveGaussBoundaryFourier

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory ComplexConjugate
open scoped SchwartzMap FourierTransform

theorem dual_fourier_active_boundary_bound (W : 𝓢(ℝ,ℂ)) (σ δ : ℝ)
    (hσ : 0 < σ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M H T x R A : ℝ) (K j e N : ℕ)
      (S : Finset ℕ) (a : ℕ → ℂ) (s : ℤ) (g : ℕ → ℂ),
      0 < M → 0 < H → 1 ≤ T → 0 ≤ x → 0 ≤ R → 0 ≤ A → 0 < e → 0 < N →
      (N : ℝ) ≤ 2*H → S ⊆ oddSquarefreeUpTo N → (∀ n ∈ S, H ≤ (n : ℝ)) →
      s ∈ signedSquarefreeMultipliers →
      (∀ q : ℕ, 0 < q → quadraticNorm (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/q)) ≤
        R*(x+(N : ℝ)/q)) →
      (∀ v ∈ binarySquarefreeRows K j, ‖g v‖ ≤ A) →
      (∀ v ∈ binarySquarefreeRows K j, g v ≠ 0 →
        dualWindowLower M H T e v < (1 : ℝ)) →
      ‖∑ v ∈ binarySquarefreeRows K j,
        ((Real.sqrt (M/((e : ℝ)*v))/1 : ℝ) : ℂ)*g v*
          (∑ l ∈ nonzeroIntegerCutoff (16*T^2), dualAggregateFourierRow W M e S a s l 1 v)‖ ≤
        (16*A*C*T^3*R)*(N : ℝ)^δ*
          (Real.sqrt (2*(2^j : ℕ))*Real.sqrt (M/e))^σ*
          (M+Real.sqrt (M/(2^j : ℕ))*x)*coefficientEnergy S a := by
  obtain ⟨C,hC,hbound⟩ := dual_fourier_frequency_boundary_bound W σ δ hσ hδ
  refine ⟨C,hC,?_⟩
  intro M H T x R A K j e N S a s g hM hH hT hx hR hA he hN hNH hS hSH hs hnorm hg hsupp
  have hTp : 0 < T := by linarith
  have hep : (0 : ℝ) < e := by exact_mod_cast he
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hB : (0 : ℝ) < (2^j : ℕ) := by positivity
  have hrows : ∀ v ∈ binarySquarefreeRows K j, 0 < v ∧ Odd v ∧ (v : ℝ) ≤ 2*(2^j : ℕ) := by
    intro v hv
    obtain ⟨hv',hlo,hhi⟩ := Finset.mem_filter.mp hv
    have hsf := mem_oddSquarefreeUpTo.mp hv'
    refine ⟨hsf.1,hsf.2.2.1,?_⟩
    exact_mod_cast (show v ≤ 2*(2^j : ℕ) by simpa only [pow_succ,mul_comm] using hhi.le)
  have hE := coefficientEnergy_nonneg S a
  by_cases hactive : ∃ v ∈ binarySquarefreeRows K j, g v ≠ 0
  · obtain ⟨v,hv,hnz⟩ := hactive
    have hrow := hbound M e N T (2*(2^j : ℕ)) H
      (binarySquarefreeRows K j) S a hM he hN hT (by positivity) hH hrows hS hSH s hs
    have hdcut := hsupp v hv hnz
    rw [dualWindowLower, squarefreeDyadicBase_eq_of_mem hv] at hdcut
    have hcut : Real.sqrt ((e : ℝ)*H^2/(M*(2^j : ℕ))) ≤ 4*T*1 := by
      have hh := (div_lt_iff₀ (show 0 < 2*T by positivity)).mp hdcut
      nlinarith
    have hscale := dual_reciprocal_min_scale hM hNp hB hH he1 hT (by norm_num : (0:ℝ)<1*1) (by norm_num : (0:ℝ)<1) hNH (by norm_num : (1:ℝ)*1≤2*1) hcut
    have hQ1 := quadraticNorm_nonneg (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/1))
    have hQ2 := quadraticNorm_nonneg (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/1))
    have hboot := dual_range_bootstrap_scale hM hNp hB hx (by norm_num : (1:ℝ)≤1) (by norm_num : (1:ℝ)≤1) hR
      (show 0 ≤ 16*T by positivity)
      (show 0 ≤ ((N : ℝ)/H)*(Real.sqrt (M/((e : ℝ)*(2^j : ℕ)))/1) by positivity)
      hQ1 hQ2 (by simpa only [Nat.cast_one] using hnorm 1 (by omega)) (by simpa only [Nat.cast_one] using hnorm 1 (by omega)) hscale
    have hw : ∀ v ∈ binarySquarefreeRows K j,
        ‖((Real.sqrt (M/((e : ℝ)*v))/1 : ℝ) : ℂ)*g v‖ ≤
          (Real.sqrt (M/((e : ℝ)*(2^j : ℕ)))/1)*A := by
      intro v hv
      simpa only [Nat.cast_one] using dual_large_weight_le (g v) hM hep hB hA (by omega : 0<1) (by omega : 1≤1)
        (by exact_mod_cast (Finset.mem_filter.mp hv).2.1) (hg v hv)
    have hw' : ∀ d ∈ ({1} : Finset ℕ), ∀ v ∈ binarySquarefreeRows K j,
        ‖((Real.sqrt (M/((e : ℝ)*v))/1 : ℝ) : ℂ)*g v‖ ≤
          (Real.sqrt (M/((e : ℝ)*(2^j : ℕ)))/1)*A := fun d hd v hv => hw v hv
    have hweighted := norm_weighted_three_le ({1} : Finset ℕ) (binarySquarefreeRows K j)
      (nonzeroIntegerCutoff (16*T^2))
      (fun _ v => ((Real.sqrt (M/((e : ℝ)*v))/1 : ℝ) : ℂ)*g v)
      (fun l _ v => dualAggregateFourierRow W M e S a s l 1 v) _ (by positivity) hw'
    simp only [Finset.sum_singleton] at hweighted
    apply hweighted.trans
    have hrow' : (∑ l ∈ nonzeroIntegerCutoff (16*T^2), ∑ v ∈ binarySquarefreeRows K j,
        ‖dualAggregateFourierRow W M e S a s l 1 v‖) ≤
        C*T^2*(Real.sqrt (2*(2^j : ℕ))*Real.sqrt (M/e))^σ*(N/H)*(N : ℝ)^δ*
          quadraticNorm (binarySquarefreeRows K j) (oddSquarefreeUpTo N)*coefficientEnergy S a := by
      simpa only [dualAggregateFourierRow,Nat.cast_one,one_mul] using hrow
    apply (mul_le_mul_of_nonneg_left hrow'
      (show 0 ≤ (Real.sqrt (M/((e : ℝ)*(2^j : ℕ)))/1)*A by positivity)).trans
    have hQ := quadraticNorm_nonneg (binarySquarefreeRows K j) (oddSquarefreeUpTo N)
    simp only [Nat.div_one,one_mul] at hboot
    rw [←pow_two,Real.sqrt_sq hQ] at hboot
    have hh := mul_le_mul_of_nonneg_left hboot
      (show 0 ≤ A*C*T^2*(N : ℝ)^δ*
        (Real.sqrt (2*(2^j : ℕ))*Real.sqrt (M/e))^σ*coefficientEnergy S a by positivity)
    convert hh using 1 <;> push_cast <;> ring
  · have hz : ∀ v ∈ binarySquarefreeRows K j, g v = 0 := by
      intro v hv
      by_contra hnz
      exact hactive ⟨v,hv,hnz⟩
    have heq : (∑ v ∈ binarySquarefreeRows K j,
        ((Real.sqrt (M/((e : ℝ)*v))/1 : ℝ) : ℂ)*g v*
          (∑ l ∈ nonzeroIntegerCutoff (16*T^2), dualAggregateFourierRow W M e S a s l 1 v)) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      rw [hz v hv]
      ring
    rw [heq,norm_zero]
    positivity

end Ostmann.QuadraticSieve

end OAI
