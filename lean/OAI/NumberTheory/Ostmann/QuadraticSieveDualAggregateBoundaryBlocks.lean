import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateBlocks
import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateBoundary

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate

theorem dual_zero_active_boundary_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M H T x R A : ℝ) (K j e N : ℕ)
      (S : Finset ℕ) (a : ℕ → ℂ) (c : ℤ) (g : ℕ → ℂ),
      0 < M → 0 < H → 1 ≤ T → 0 ≤ x → 0 ≤ R → 0 ≤ A → 0 < e → 0 < N →
      (N : ℝ) ≤ 2*H → S ⊆ oddSquarefreeUpTo N → (∀ n ∈ S, H ≤ (n : ℝ)) →
      (∀ q : ℕ, 0 < q → quadraticNorm (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/q)) ≤
        R*(x+(N : ℝ)/q)) →
      (∀ v ∈ binarySquarefreeRows K j, ‖g v‖ ≤ A) →
      (∀ v ∈ binarySquarefreeRows K j, g v ≠ 0 →
        (1 : ℝ) ≤ dualWindowUpper M H T e v) →
      ‖∑ v ∈ binarySquarefreeRows K j,
        ((M/e : ℝ) : ℂ)*g v*gaussProductDivisorJacobiRow S S a (fun n => conj (a n)) c 1 (v : ℤ)‖ ≤
        (8*A*T*R)*Real.sqrt (C*(N : ℝ)^ε*coefficientEnergy S a*coefficientEnergy S a)*
          (M+Real.sqrt (M/(2^j : ℕ))*x) := by
  obtain ⟨C,hC,hbound⟩ := dual_gauss_weighted_boundary_bounds ε hε
  refine ⟨C,hC,?_⟩
  intro M H T x R A K j e N S a c g hM hH hT hx hR hA he hN hNH hS hSH hnorm hg hsupp
  have hTp : 0 < T := by linarith
  have hep : (0 : ℝ) < e := by exact_mod_cast he
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hB : (0 : ℝ) < (2^j : ℕ) := by positivity
  have hrows : ∀ v ∈ binarySquarefreeRows K j, Odd v := fun v hv =>
    (mem_oddSquarefreeUpTo.mp (Finset.mem_filter.mp hv).1).2.2.1
  have hE := coefficientEnergy_nonneg S a
  by_cases hactive : ∃ v ∈ binarySquarefreeRows K j, g v ≠ 0
  · obtain ⟨v,hv,hnz⟩ := hactive
    have hrow := hbound N (binarySquarefreeRows K j) S H hN hH hrows hS hSH
    have hdcut := hsupp v hv hnz
    rw [dualWindowUpper, squarefreeDyadicBase_eq_of_mem hv] at hdcut
    have hcut : (1 : ℝ)*1 ≤ 4*T*Real.sqrt ((e : ℝ)*H^2/(M*(2^j : ℕ))) := by nlinarith
    have hscale := dual_zero_min_scale hM hNp hB hH he1 hT (by norm_num : (0:ℝ)<1*1) hNH hcut
    have hQ1 := quadraticNorm_nonneg (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/1))
    have hQ2 := quadraticNorm_nonneg (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/1))
    have hboot := dual_range_energy_bootstrap hM hNp hB hx (by norm_num : (1:ℝ)≤1) (by norm_num : (1:ℝ)≤1) hR
      (show 0 ≤ 4*T by positivity) (show 0 ≤ M/((e : ℝ)*H) by positivity)
      hQ1 hQ2 (show 0 ≤ C*(N : ℝ)^ε by positivity) hE (by simpa only [Nat.cast_one] using hnorm 1 (by omega)) (by simpa only [Nat.cast_one] using hnorm 1 (by omega)) hscale
    have hw : ∀ v ∈ binarySquarefreeRows K j,
        ‖((M/e : ℝ) : ℂ)*g v‖ ≤ (M/e)*A := by
      intro v hv
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (div_pos hM hep)]
      exact mul_le_mul_of_nonneg_left (hg v hv) (by positivity)
    apply ((hrow a c (fun v => ((M/e : ℝ) : ℂ)*g v) ((M/e)*A) (by positivity) hw).1).trans
    have hh := mul_le_mul_of_nonneg_left hboot (show 0 ≤ 2*A by positivity)
    convert hh using 1 <;> simp only [Nat.div_one] at * <;> push_cast <;> ring_nf
  · have hz : ∀ v ∈ binarySquarefreeRows K j, g v = 0 := by
      intro v hv
      by_contra hnz
      exact hactive ⟨v,hv,hnz⟩
    have heq : (∑ v ∈ binarySquarefreeRows K j,
        ((M/e : ℝ) : ℂ)*g v*gaussProductDivisorJacobiRow S S a (fun n => conj (a n)) c 1 (v : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      rw [hz v hv]
      ring
    rw [heq,norm_zero]
    positivity

theorem dual_large_active_boundary_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M H T x R A : ℝ) (K j e N : ℕ)
      (S : Finset ℕ) (a : ℕ → ℂ) (c : ℤ) (g : ℕ → ℂ),
      0 < M → 0 < H → 1 ≤ T → 0 ≤ x → 0 ≤ R → 0 ≤ A → 0 < e → 0 < N →
      (N : ℝ) ≤ 2*H → S ⊆ oddSquarefreeUpTo N → (∀ n ∈ S, H ≤ (n : ℝ)) →
      (∀ q : ℕ, 0 < q → quadraticNorm (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/q)) ≤
        R*(x+(N : ℝ)/q)) →
      (∀ v ∈ binarySquarefreeRows K j, ‖g v‖ ≤ A) →
      (∀ v ∈ binarySquarefreeRows K j, g v ≠ 0 →
        dualWindowLower M H T e v < (1 : ℝ)) →
      ‖∑ v ∈ binarySquarefreeRows K j,
        ((Real.sqrt (M/((e : ℝ)*v))/1 : ℝ) : ℂ)*g v*
          gaussProductDivisorJacobiRow S S (sqrtCoefficients a)
            (sqrtCoefficients (fun n => conj (a n))) c 1 (v : ℤ)‖ ≤
        (32*A*T*R)*Real.sqrt (C*(N : ℝ)^ε*coefficientEnergy S a*coefficientEnergy S a)*
          (M+Real.sqrt (M/(2^j : ℕ))*x) := by
  obtain ⟨C,hC,hbound⟩ := dual_gauss_weighted_boundary_bounds ε hε
  refine ⟨C,hC,?_⟩
  intro M H T x R A K j e N S a c g hM hH hT hx hR hA he hN hNH hS hSH hnorm hg hsupp
  have hTp : 0 < T := by linarith
  have hep : (0 : ℝ) < e := by exact_mod_cast he
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hB : (0 : ℝ) < (2^j : ℕ) := by positivity
  have hrows : ∀ v ∈ binarySquarefreeRows K j, Odd v ∧ ((2^j : ℕ) : ℝ) ≤ v := by
    intro v hv
    obtain ⟨hv',hlo,hhi⟩ := Finset.mem_filter.mp hv
    exact ⟨(mem_oddSquarefreeUpTo.mp hv').2.2.1,by exact_mod_cast hlo⟩
  have hE := coefficientEnergy_nonneg S a
  by_cases hactive : ∃ v ∈ binarySquarefreeRows K j, g v ≠ 0
  · obtain ⟨v,hv,hnz⟩ := hactive
    have hrow := hbound N (binarySquarefreeRows K j) S H hN hH
      (fun v hv => (hrows v hv).1) hS hSH
    have hdcut := hsupp v hv hnz
    rw [dualWindowLower, squarefreeDyadicBase_eq_of_mem hv] at hdcut
    have hcut : Real.sqrt ((e : ℝ)*H^2/(M*(2^j : ℕ))) ≤ 4*T*1 := by
      have hh := (div_lt_iff₀ (show 0 < 2*T by positivity)).mp hdcut
      nlinarith
    have hscale := dual_reciprocal_min_scale hM hNp hB hH he1 hT (by norm_num : (0:ℝ)<1*1) (by norm_num : (0:ℝ)<1) hNH (by norm_num : (1:ℝ)*1≤2*1) hcut
    have hQ1 := quadraticNorm_nonneg (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/1))
    have hQ2 := quadraticNorm_nonneg (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/1))
    have hboot := dual_range_energy_bootstrap hM hNp hB hx (by norm_num : (1:ℝ)≤1) (by norm_num : (1:ℝ)≤1) hR
      (show 0 ≤ 16*T by positivity)
      (show 0 ≤ ((N : ℝ)/H)*(Real.sqrt (M/((e : ℝ)*(2^j : ℕ)))/1) by positivity)
      hQ1 hQ2 (show 0 ≤ C*(N : ℝ)^ε by positivity) hE (by simpa only [Nat.cast_one] using hnorm 1 (by omega)) (by simpa only [Nat.cast_one] using hnorm 1 (by omega)) hscale
    have hw : ∀ v ∈ binarySquarefreeRows K j,
        ‖((Real.sqrt (M/((e : ℝ)*v))/1 : ℝ) : ℂ)*g v‖ ≤
          (Real.sqrt (M/((e : ℝ)*(2^j : ℕ)))/1)*A := by
      intro v hv
      simpa only [Nat.cast_one] using dual_large_weight_le (g v) hM hep hB hA (by omega : 0<1)
        (by omega : 1≤1) (hrows v hv).2 (hg v hv)
    apply ((hrow a c (fun v => ((Real.sqrt (M/((e : ℝ)*v))/1 : ℝ) : ℂ)*g v)
      ((Real.sqrt (M/((e : ℝ)*(2^j : ℕ)))/1)*A) (by positivity) hw).2).trans
    have hh := mul_le_mul_of_nonneg_left hboot (show 0 ≤ 2*A by positivity)
    convert hh using 1 <;> simp only [Nat.div_one] at * <;> push_cast <;> ring_nf
  · have hz : ∀ v ∈ binarySquarefreeRows K j, g v = 0 := by
      intro v hv
      by_contra hnz
      exact hactive ⟨v,hv,hnz⟩
    have heq : (∑ v ∈ binarySquarefreeRows K j,
        ((Real.sqrt (M/((e : ℝ)*v))/1 : ℝ) : ℂ)*g v*
          gaussProductDivisorJacobiRow S S (sqrtCoefficients a)
            (sqrtCoefficients (fun n => conj (a n))) c 1 (v : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      rw [hz v hv]
      ring
    rw [heq,norm_zero]
    positivity

end Ostmann.QuadraticSieve

end OAI
