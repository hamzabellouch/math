import OAI.Combinatorics.PolynomialVacuum.Algebra.CupSurface
import OAI.Combinatorics.PolynomialVacuum.Algebra.PolynomialSlice

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem polynomial_eq_on_scaled_nodes {ι : Type*} (S : Finset ι) (Y : ι → ℂ)
    (hY : Set.InjOn Y (S : Set ι)) (p r : Polynomial ℂ)
    (hp : p.natDegree < S.card) (hr : r.natDegree < S.card)
    (h : ∀ i ∈ S, p.eval (T*Y i)=r.eval (T*Y i)) : p=r := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S
    (fun i hi j hj he => hY hi hj (mul_left_cancel₀ T_ne_zero he))
  · exact Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hp)
  · exact Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hr)
  · exact h

theorem polynomial_eq_on_scaled_nodes_zero {ι : Type*} (S : Finset ι) (Y : ι → ℂ)
    (hY : Set.InjOn Y (S : Set ι)) (h0 : ∀ i ∈ S, Y i≠0) (p r : Polynomial ℂ)
    (hp : p.natDegree ≤ S.card) (hr : r.natDegree ≤ S.card)
    (hz : p.eval 0=r.eval 0) (h : ∀ i ∈ S, p.eval (T*Y i)=r.eval (T*Y i)) : p=r := by
  let Z : Option ι → ℂ := fun i => i.elim 0 (fun j => T*Y j)
  let E : Finset (Option ι) := insert none (S.map ⟨some,Option.some_injective _⟩)
  have hi : Set.InjOn Z (E : Set (Option ι)) := by
    intro i hi j hj he
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j =>
        have hj' : j∈S := by simpa [E] using hj
        exact False.elim ((mul_ne_zero T_ne_zero (h0 j hj')) he.symm)
    | some i =>
      have hi' : i∈S := by simpa [E] using hi
      cases j with
      | none => exact False.elim ((mul_ne_zero T_ne_zero (h0 i hi')) he)
      | some j =>
        have hj' : j∈S := by simpa [E] using hj
        exact congrArg some (hY hi' hj' (mul_left_cancel₀ T_ne_zero he))
  have hc : E.card=S.card+1 := by simp [E]
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq E hi
  · rw [hc]
    exact Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (show p.natDegree < S.card+1 from by omega))
  · rw [hc]
    exact Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr (show r.natDegree < S.card+1 from by omega))
  · intro i hi
    cases i with
    | none => exact hz
    | some i => exact h i (by simpa [E] using hi)

theorem cupSurface_eq_of_nodes {ι : Type*} (a b c : ι) (hab : a≠b)
    (S : Finset ι) (p r : MvPolynomial ι ℂ)
    (hp : p.degreeOf c < S.card) (hr : r.degreeOf c < S.card)
    (h : ∀ Y, Y b=T*Y a → ∀ i ∈ S,
      eval (Function.update Y c (T*Y i)) p=eval (Function.update Y c (T*Y i)) r) :
    cupSpecialize a b p=cupSpecialize a b r := by
  apply polynomial_eq_on_generic (cupSpecialize_distinctGuard_ne_zero a b S)
  intro X hX
  simp only [eval_cupSpecialize] at hX ⊢
  let Y := Function.update X b (T*X a)
  have hY : Y b=T*Y a := by simp [Y,hab]
  obtain ⟨h0,hi⟩ := eval_distinctGuard_good S Y hX
  have he := polynomial_eq_on_scaled_nodes S Y hi (polynomialSlice c Y p) (polynomialSlice c Y r)
    ((polynomialSlice_natDegree c Y p).trans_lt hp) ((polynomialSlice_natDegree c Y r).trans_lt hr)
    (by intro i hi; simpa using h Y hY i hi)
  have he' := congrArg (fun P : Polynomial ℂ => P.eval (Y c)) he
  simpa only [eval_polynomialSlice,Function.update_eq_self] using he'

theorem cupSurface_eq_of_nodes_zero {ι : Type*} (a b c : ι) (hab : a≠b)
    (S : Finset ι) (p r : MvPolynomial ι ℂ)
    (hp : p.degreeOf c ≤ S.card) (hr : r.degreeOf c ≤ S.card)
    (hz : ∀ Y, Y b=T*Y a → eval (Function.update Y c 0) p=eval (Function.update Y c 0) r)
    (h : ∀ Y, Y b=T*Y a → ∀ i ∈ S,
      eval (Function.update Y c (T*Y i)) p=eval (Function.update Y c (T*Y i)) r) :
    cupSpecialize a b p=cupSpecialize a b r := by
  apply polynomial_eq_on_generic (cupSpecialize_distinctGuard_ne_zero a b S)
  intro X hX
  simp only [eval_cupSpecialize] at hX ⊢
  let Y := Function.update X b (T*X a)
  have hY : Y b=T*Y a := by simp [Y,hab]
  obtain ⟨h0,hi⟩ := eval_distinctGuard_good S Y hX
  have he := polynomial_eq_on_scaled_nodes_zero S Y hi h0 (polynomialSlice c Y p) (polynomialSlice c Y r)
    ((polynomialSlice_natDegree c Y p).trans hp) ((polynomialSlice_natDegree c Y r).trans hr)
    (by simpa using hz Y hY) (by intro i hi; simpa using h Y hY i hi)
  have he' := congrArg (fun P : Polynomial ℂ => P.eval (Y c)) he
  simpa only [eval_polynomialSlice,Function.update_eq_self] using he'

theorem eval_eq_of_cupSurface_eq {ι : Type*} (a b : ι) (p r : MvPolynomial ι ℂ)
    (h : cupSpecialize a b p=cupSpecialize a b r) (Y : ι → ℂ) (hY : Y b=T*Y a) :
    eval Y p=eval Y r := by
  have he := congrArg (eval Y) h
  simpa only [eval_cupSpecialize,← hY,Function.update_eq_self] using he

end PolynomialVacuumAlgebra

end OAI
