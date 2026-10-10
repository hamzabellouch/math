import OAI.Combinatorics.PolynomialVacuum.Algebra.InterpolationNodes

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

noncomputable def lastPolynomial {n : ℕ} (ψ : State n) (χ : State (n+1))
    (s : Fin (n+2) → Spin) : Polynomial (MvPolynomial (Fin (n+1)) ℂ) :=
  if s (Fin.last (n+1))=Spin.plus then canonicalInterpolant (fun i => cupPrescription ψ i s)
  else Polynomial.X*canonicalInterpolant (fun i => dividedCupPrescription ψ i s) +
    if s (Fin.last (n+1))=Spin.zero then
      (∏ i : Fin (n+1), (Polynomial.C (X i)-Polynomial.X))*Polynomial.C (χ (s ∘ Fin.castSucc))
    else 0

theorem interpolateState_eq_reinsert {n : ℕ} (ψ : State n) (χ : State (n+1))
    (s : Fin (n+2) → Spin) :
    interpolateState ψ χ s=reinsertLast (lastPolynomial ψ χ s) := by
  unfold interpolateState lastPolynomial
  split_ifs <;> simp [reinsertLast,Polynomial.eval₂_mul,Polynomial.eval₂_add,Polynomial.eval₂_finsetProd,
    Polynomial.eval₂_sub]

theorem canonicalInterpolant_natDegree {n : ℕ} (V : Fin (n+1) → MvPolynomial (Fin (n+1)) ℂ) :
    (canonicalInterpolant V).natDegree ≤ n := by
  by_cases h : canonicalInterpolant V=0
  · simp [h]
  · exact Nat.le_of_lt_succ ((Polynomial.natDegree_lt_iff_degree_lt h).mpr (canonicalInterpolant_degree V))

theorem lastPolynomial_degree_plus {n : ℕ} (ψ : State n) (χ : State (n+1))
    (s : Fin (n+2) → Spin) (hs : s (Fin.last (n+1))=Spin.plus) :
    (lastPolynomial ψ χ s).degree < ((n+1 : ℕ) : WithBot ℕ) := by
  simpa only [lastPolynomial,ite_eq_left hs] using canonicalInterpolant_degree (fun i => cupPrescription ψ i s)

theorem lastPolynomial_natDegree {n : ℕ} (ψ : State n) (χ : State (n+1))
    (s : Fin (n+2) → Spin) : (lastPolynomial ψ χ s).natDegree ≤ n+1 := by
  have hprod : (∏ i : Fin (n+1), (Polynomial.C (X i)-Polynomial.X) :
      Polynomial (MvPolynomial (Fin (n+1)) ℂ)).natDegree ≤ n+1 := by
    apply (Polynomial.natDegree_prod_le _ _).trans
    calc
      _ ≤ ∑ _i : Fin (n+1), 1 := by
        apply Finset.sum_le_sum
        intro i hi
        exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
      _ = n+1 := by simp
  unfold lastPolynomial
  split_ifs with hs hs'
  · exact (canonicalInterpolant_natDegree _).trans (by omega)
  · apply Polynomial.natDegree_add_le_of_degree_le
    · exact Polynomial.natDegree_mul_le.trans (by
        simpa only [Polynomial.natDegree_X,Nat.add_comm] using
          Nat.add_le_add_right (canonicalInterpolant_natDegree
            (fun i => dividedCupPrescription ψ i s)) 1)
    · exact Polynomial.natDegree_mul_le.trans (by simpa using hprod)
  · simp only [add_zero]
    exact Polynomial.natDegree_mul_le.trans (by
      simpa only [Polynomial.natDegree_X,Nat.add_comm] using
        Nat.add_le_add_right (canonicalInterpolant_natDegree
          (fun i => dividedCupPrescription ψ i s)) 1)

theorem lastPolynomial_node {n : ℕ} (ψ : State n) (χ : State (n+1))
    (hψ : LowerExchange (liftState ψ) n) (s : Fin (n+2) → Spin) (i : Fin (n+1)) :
    (lastPolynomial ψ χ s).eval (X i)=cupPrescription ψ i s := by
  have hz : (∏ j : Fin (n+1), (X j-X i) : MvPolynomial (Fin (n+1)) ℂ)=0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  unfold lastPolynomial
  split_ifs with hs hs'
  · exact canonicalInterpolant_eval _ (cupPrescription_collision ψ hψ s) i
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_prod,Polynomial.eval_sub,
      Polynomial.eval_C,Polynomial.eval_X,hz,zero_mul,add_zero]
    rw [canonicalInterpolant_eval _ (dividedCupPrescription_collision ψ hψ s),cupPrescription_factor]
  · simp only [Polynomial.eval_mul,Polynomial.eval_X,add_zero]
    rw [canonicalInterpolant_eval _ (dividedCupPrescription_collision ψ hψ s),cupPrescription_factor]

theorem lastPolynomial_zero {n : ℕ} (ψ : State n) (χ : State (n+1))
    (s : Fin (n+2) → Spin) (hs : s (Fin.last (n+1))≠Spin.plus) :
    (lastPolynomial ψ χ s).eval 0=
      if s (Fin.last (n+1))=Spin.zero then (∏ i : Fin (n+1), X i)*χ (s ∘ Fin.castSucc) else 0 := by
  unfold lastPolynomial
  rw [ite_eq_right hs]
  split_ifs <;> simp [Polynomial.eval_prod]

end PolynomialVacuumAlgebra

end OAI
