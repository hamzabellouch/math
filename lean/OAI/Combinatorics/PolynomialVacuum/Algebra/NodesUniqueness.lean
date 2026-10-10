import OAI.Combinatorics.PolynomialVacuum.Algebra.LastPolynomial

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

noncomputable def rootWithZero {m : ℕ} : Option (Fin m) → MvPolynomial (Fin m) ℂ
  | none => 0
  | some i => X i

theorem rootWithZero_injective {m : ℕ} : Function.Injective (rootWithZero (m:=m)) := by
  intro a b h
  cases a <;> cases b
  · rfl
  · exact False.elim (MvPolynomial.X_ne_zero _ h.symm)
  · exact False.elim (MvPolynomial.X_ne_zero _ h)
  · exact congrArg some (MvPolynomial.X_injective h)

theorem polynomial_eq_on_nodes_zero {m : ℕ}
    (p r : Polynomial (MvPolynomial (Fin m) ℂ))
    (hp : p.natDegree ≤ m) (hr : r.natDegree ≤ m)
    (hzero : p.eval 0=r.eval 0) (h : ∀ i, p.eval (X i)=r.eval (X i)) : p=r := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
    (Finset.univ : Finset (Option (Fin m))) rootWithZero_injective.injOn
  · have hp' : p.degree < ((m+1 : ℕ) : WithBot ℕ) :=
      (Polynomial.degree_le_natDegree.trans (WithBot.coe_le_coe.mpr hp)).trans_lt
        (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self m))
    simpa using hp'
  · have hr' : r.degree < ((m+1 : ℕ) : WithBot ℕ) :=
      (Polynomial.degree_le_natDegree.trans (WithBot.coe_le_coe.mpr hr)).trans_lt
        (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self m))
    simpa using hr'
  · intro i hi
    cases i with
    | none => exact hzero
    | some i => exact h i

theorem eval_map_rename_swap {m : ℕ} (p : Polynomial (MvPolynomial (Fin m) ℂ))
    (a b i : Fin m) :
    (p.map (rename (Equiv.swap a b)).toRingHom).eval (X i)=
      rename (Equiv.swap a b) (p.eval (X (Equiv.swap a b i))) := by
  rw [Polynomial.eval_map]
  have hx : (X i : MvPolynomial (Fin m) ℂ)=(rename (Equiv.swap a b)).toRingHom (X (Equiv.swap a b i)) := by simp
  rw [hx,Polynomial.eval₂_at_apply]; rfl

end PolynomialVacuumAlgebra

end OAI
