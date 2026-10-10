import OAI.Combinatorics.PolynomialVacuum.Algebra.FirstCupInterpolation
import OAI.Combinatorics.PolynomialVacuum.Algebra.CupSurfaceInterpolation

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

noncomputable def scaledDistinctGuard (S : Finset ℕ) (A : ℕ → ℂ) : MvPolynomial ℕ ℂ :=
  (∏ i ∈ S, C (A i)*X i) *
    ∏ i ∈ S, ∏ j ∈ S.erase i, (C (A i)*X i-C (A j)*X j)

theorem scaledDistinctGuard_ne_zero (S : Finset ℕ) (A : ℕ → ℂ) (hA : ∀ i∈S, A i≠0) :
    scaledDistinctGuard S A≠0 := by
  intro he
  have hv := congrArg (eval (fun i : ℕ => ((i:ℂ)+1)/A i)) he
  have heval (i : ℕ) (hi : i∈S) : A i*(((i:ℂ)+1)/A i)=(i:ℂ)+1 := by
    field_simp [hA i hi]
  have hprod : eval (fun i : ℕ => ((i:ℂ)+1)/A i) (scaledDistinctGuard S A)≠0 := by
    simp only [scaledDistinctGuard,map_mul,map_prod,map_sub,eval_C,eval_X]
    apply mul_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      rw [heval i hi]
      exact_mod_cast (show i+1≠0 by omega)
    · apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      obtain ⟨hji,hj⟩ := Finset.mem_erase.mp hj
      rw [heval i hi,heval j hj]
      intro hz
      have hcast : (i:ℂ)=(j:ℂ) := by linear_combination hz
      exact hji (Nat.cast_injective hcast).symm
  exact hprod (by simpa using hv)

theorem scaledDistinctGuard_good (S : Finset ℕ) (A Y : ℕ → ℂ)
    (h : eval Y (scaledDistinctGuard S A)≠0) :
    (∀ i∈S, A i*Y i≠0) ∧ Set.InjOn (fun i => A i*Y i) (S:Set ℕ) := by
  simp only [scaledDistinctGuard,map_mul,map_prod,map_sub,eval_C,eval_X] at h
  obtain ⟨h0,hd⟩ := mul_ne_zero_iff.mp h
  refine ⟨Finset.prod_ne_zero_iff.mp h0,?_⟩
  intro i hi j hj he
  by_contra hij
  have hh := Finset.prod_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hd i hi) j
    (Finset.mem_erase.mpr ⟨Ne.symm hij,hj⟩)
  exact hh (sub_eq_zero.mpr he)

theorem polynomial_zero_of_scaled_roots (c : ℕ) (S : Finset ℕ) (A : ℕ → ℂ)
    (hA : ∀ i∈S, A i≠0) (p : MvPolynomial ℕ ℂ)
    (hd : p.degreeOf c < S.card)
    (hz : ∀ Y i, i∈S → eval (Function.update Y c (A i*Y i)) p=0) : p=0 := by
  apply polynomial_eq_on_generic (scaledDistinctGuard_ne_zero S A hA)
  intro Y hY
  have hi := (scaledDistinctGuard_good S A Y hY).2
  have hp : polynomialSlice c Y p=0 := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S hi
    · exact Polynomial.degree_le_natDegree.trans_lt
        (WithBot.coe_lt_coe.mpr ((polynomialSlice_natDegree c Y p).trans_lt hd))
    · simp
    · intro i hi
      simpa only [eval_polynomialSlice,Polynomial.eval_zero,update_nat_decidable] using hz Y i hi
  have he := congrArg (fun P : Polynomial ℂ => P.eval (Y c)) hp
  simpa using he

theorem polynomial_zero_of_scaled_roots_zero (c : ℕ) (S : Finset ℕ) (A : ℕ → ℂ)
    (hA : ∀ i∈S, A i≠0) (p : MvPolynomial ℕ ℂ)
    (hd : p.degreeOf c ≤ S.card)
    (h0 : ∀ Y, eval (Function.update Y c 0) p=0)
    (hz : ∀ Y i, i∈S → eval (Function.update Y c (A i*Y i)) p=0) : p=0 := by
  apply polynomial_eq_on_generic (scaledDistinctGuard_ne_zero S A hA)
  intro Y hY
  obtain ⟨hpos,hi⟩ := scaledDistinctGuard_good S A Y hY
  have hp : polynomialSlice c Y p=0 := by
    have hh := polynomial_eq_on_scaled_nodes_zero S (fun i => (A i*Y i)/T)
      (by intro i hi' j hj' he; apply hi hi' hj'; exact mul_right_cancel₀ T_ne_zero ((div_eq_div_iff T_ne_zero T_ne_zero).mp he))
      (by intro i hi; exact div_ne_zero (hpos i hi) T_ne_zero)
      (polynomialSlice c Y p) 0 ((polynomialSlice_natDegree c Y p).trans hd) (by simp)
      (by simpa only [eval_polynomialSlice,Polynomial.eval_zero,update_nat_decidable] using h0 Y)
      (by intro i hi; simpa only [eval_polynomialSlice,Polynomial.eval_zero,update_nat_decidable, mul_div_cancel₀ _ T_ne_zero] using hz Y i hi)
    exact hh
  have he := congrArg (fun P : Polynomial ℂ => P.eval (Y c)) hp
  simpa using he

end PolynomialVacuumAlgebra

end OAI
