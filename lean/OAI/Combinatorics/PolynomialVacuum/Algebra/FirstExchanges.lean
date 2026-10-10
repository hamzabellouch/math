import OAI.Combinatorics.PolynomialVacuum.Algebra.NodesUniqueness
import OAI.Combinatorics.PolynomialVacuum.Algebra.PrescriptionCovariance

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical PolynomialVacuumInterpolation

theorem replacePair_last {n : ℕ} (j : Fin n) (s : Fin (n+2) → Spin) (ab : Pair) :
    replacePair s (pairLeft j.castSucc) (pairRight j.castSucc) ab (Fin.last (n+1))=
      s (Fin.last (n+1)) := by
  apply replacePair_other
  · intro h
    have hv:=congrArg Fin.val h
    simp only [pairLeft,Fin.val_last,Fin.val_castSucc] at hv
    have hj:=j.isLt; omega
  · intro h
    have hv:=congrArg Fin.val h
    simp only [pairRight,Fin.val_last,Fin.val_succ,Fin.val_castSucc] at hv
    have hj:=j.isLt; omega

theorem replacePair_castSucc {n : ℕ} (j : Fin n) (s : Fin (n+2) → Spin) (ab : Pair) :
    (replacePair s (pairLeft j.castSucc) (pairRight j.castSucc) ab) ∘ Fin.castSucc=
      replacePair (s ∘ Fin.castSucc) j.castSucc j.succ ab := by
  funext k
  simp only [Function.comp_apply,replacePair,Function.update_apply,pairLeft,pairRight,
    Fin.ext_iff,Fin.val_castSucc,Fin.val_succ]

theorem rename_prod_X {m : ℕ} (e : Equiv.Perm (Fin m)) :
    rename e (∏ i : Fin m, X i : MvPolynomial (Fin m) ℂ)=∏ i : Fin m, X i := by
  simp only [map_prod,rename_X]
  exact Equiv.prod_comp e (fun i => (X i : MvPolynomial (Fin m) ℂ))

 

theorem lastPolynomial_first_exchange {n : ℕ} (ψ : State n) (χ : State (n+1))
    (hψ : LowerExchange (liftState ψ) n) (hχ : LowerExchange (liftState χ) (n+1))
    (j : Fin n) (s : Fin (n+2) → Spin) :
    (∑ ab : Pair, Polynomial.C (polyExchangeNumerator (X j.castSucc) (X j.succ)
      (s (pairLeft j.castSucc),s (pairRight j.castSucc)) ab)*
      lastPolynomial ψ χ (replacePair s (pairLeft j.castSucc) (pairRight j.castSucc) ab))=
    Polynomial.C ((C (t^2)*X j.castSucc-X j.succ)*(C T*X j.castSucc-X j.succ))*
      (lastPolynomial ψ χ s).map (rename (Equiv.swap j.castSucc j.succ)).toRingHom := by
  let a:=pairLeft j.castSucc
  let b:=pairRight j.castSucc
  let A := ∑ ab : Pair, Polynomial.C (polyExchangeNumerator (X j.castSucc) (X j.succ)
    (s a,s b) ab)*lastPolynomial ψ χ (replacePair s a b ab)
  let B := Polynomial.C ((C (t^2)*X j.castSucc-X j.succ)*(C T*X j.castSucc-X j.succ))*
    (lastPolynomial ψ χ s).map (rename (Equiv.swap j.castSucc j.succ)).toRingHom
  change A=B
  have hnode (i : Fin (n+1)) : A.eval (X i)=B.eval (X i) := by
    simp only [A,B,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
      lastPolynomial_node ψ χ hψ,eval_map_rename_swap]
    exact congrFun (cupPrescription_covariance ψ hψ i j) s
  have hdegA (d : ℕ) (hd : ∀ ab : Pair, (lastPolynomial ψ χ (replacePair s a b ab)).natDegree ≤ d) :
      A.natDegree ≤ d := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro ab hab
    exact (Polynomial.natDegree_C_mul_le _ _).trans (hd ab)
  have hdegB (d : ℕ) (hd : (lastPolynomial ψ χ s).natDegree ≤ d) : B.natDegree ≤ d := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_map_le.trans hd)
  by_cases hs : s (Fin.last (n+1))=Spin.plus
  · apply regular_lagrange_unique (Finset.univ : Finset (Fin (n+1)))
    · have hd := hdegA n (by
        intro ab
        have he : replacePair s a b ab (Fin.last (n+1))=Spin.plus := (replacePair_last j s ab).trans hs
        simpa only [lastPolynomial,ite_eq_left he] using
          canonicalInterpolant_natDegree (fun i => cupPrescription ψ i (replacePair s a b ab)))
      simp only [Finset.card_univ,Fintype.card_fin]
      change A.degree < ((n+1 : ℕ) : WithBot ℕ)
      calc
        A.degree ≤ (A.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
        _ ≤ (n : WithBot ℕ) := WithBot.coe_le_coe.mpr hd
        _ < ((n+1 : ℕ) : WithBot ℕ) := by exact_mod_cast (Nat.lt_succ_self n)
    · have hd := hdegB n (by
        simpa only [lastPolynomial,ite_eq_left hs] using
          canonicalInterpolant_natDegree (fun i => cupPrescription ψ i s))
      simp only [Finset.card_univ,Fintype.card_fin]
      change B.degree < ((n+1 : ℕ) : WithBot ℕ)
      calc
        B.degree ≤ (B.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
        _ ≤ (n : WithBot ℕ) := WithBot.coe_le_coe.mpr hd
        _ < ((n+1 : ℕ) : WithBot ℕ) := by exact_mod_cast (Nat.lt_succ_self n)
    · intro i hi; exact hnode i
  · apply polynomial_eq_on_nodes_zero A B (hdegA (n+1) (fun _ => lastPolynomial_natDegree _ _ _))
      (hdegB (n+1) (lastPolynomial_natDegree _ _ _))
    · have he (ab : Pair) : replacePair s a b ab (Fin.last (n+1))≠Spin.plus := by
        simpa only [a,b,replacePair_last] using hs
      simp only [A,B,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
        Polynomial.eval_zero_map,lastPolynomial_zero _ _ _ hs,lastPolynomial_zero _ _ _ (he _)]
      simp only [a,b,replacePair_last,replacePair_castSucc]
      split_ifs with hz
      · simp only [map_mul,AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_prod_X]
        have h := congrFun (state_exchange_of_lower χ hχ j) (s ∘ Fin.castSucc)
        simp only [tensorExchange,Function.comp_apply] at h
        simp only [← mul_assoc]
        calc
          _ = (∏ i : Fin (n+1), X i)*
              ∑ ab : Pair, polyExchangeNumerator (X j.castSucc) (X j.succ)
                (s a,s b) ab*χ (replacePair (s ∘ Fin.castSucc) j.castSucc j.succ ab) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro ab hab
                  ring
          _ = _ := by
            have hh : (∑ ab : Pair, polyExchangeNumerator (X j.castSucc) (X j.succ)
                (s a,s b) ab*χ (replacePair (s ∘ Fin.castSucc) j.castSucc j.succ ab)) =
                (C (t^2)*X j.castSucc-X j.succ)*(C T*X j.castSucc-X j.succ)*
                rename (Equiv.swap j.castSucc j.succ) (χ (s ∘ Fin.castSucc)) := by
              simpa only [a,b,pairLeft,pairRight,Fin.succ_castSucc,replacePair] using h
            rw [hh]; ring
      · simp
    · exact hnode

end PolynomialVacuumAlgebra

end OAI
