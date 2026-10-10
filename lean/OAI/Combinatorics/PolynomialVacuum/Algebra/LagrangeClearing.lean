import OAI.Combinatorics.PolynomialVacuum.Algebra.LastPolynomial
import OAI.Combinatorics.PolynomialVacuum.Algebra.ExchangeDegrees

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical PolynomialVacuumInterpolation

noncomputable def nodeDenominator {m : ℕ} (i : Fin m) : MvPolynomial (Fin m) ℂ :=
  ∏ j ∈ Finset.univ.erase i, (X i-X j)
noncomputable def allNodeDenominators (m : ℕ) : MvPolynomial (Fin m) ℂ :=
  ∏ i, nodeDenominator i
noncomputable def exceptNodeDenominator {m : ℕ} (i : Fin m) : MvPolynomial (Fin m) ℂ :=
  ∏ j ∈ Finset.univ.erase i, nodeDenominator j
noncomputable def nodeNumerator {m : ℕ} (i : Fin m) : Polynomial (MvPolynomial (Fin m) ℂ) :=
  ∏ j ∈ Finset.univ.erase i, (Polynomial.X-Polynomial.C (X j))

theorem nodeDenominator_ne_zero {m : ℕ} (i : Fin m) : nodeDenominator i≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  exact fun he => (Finset.mem_erase.mp hj).1 (MvPolynomial.X_injective he).symm

theorem allNodeDenominators_ne_zero (m : ℕ) : allNodeDenominators m≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _; exact nodeDenominator_ne_zero i

theorem allNodeDenominators_factor {m : ℕ} (i : Fin m) :
    allNodeDenominators m=exceptNodeDenominator i*nodeDenominator i := by
  exact (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm

theorem nodeNumerator_self {m : ℕ} (i : Fin m) :
    (nodeNumerator i).eval (X i)=nodeDenominator i := by
  simp [nodeNumerator,nodeDenominator,Polynomial.eval_prod]

theorem nodeNumerator_other {m : ℕ} {i k : Fin m} (h : i≠k) :
    (nodeNumerator i).eval (X k)=0 := by
  simp only [nodeNumerator,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  apply Finset.prod_eq_zero (by simp [h.symm] : k ∈ Finset.univ.erase i)
  simp

theorem nodeNumerator_natDegree {n : ℕ} (i : Fin (n+1)) : (nodeNumerator i).natDegree ≤ n := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _j ∈ Finset.univ.erase i, 1 := by
      apply Finset.sum_le_sum
      intro j hj
      exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
    _ = n := by simp

 

theorem canonicalInterpolant_cleared {n : ℕ}
    (V : Fin (n+1) → MvPolynomial (Fin (n+1)) ℂ) (hV : CollisionCompatible V) :
    Polynomial.C (allNodeDenominators (n+1))*canonicalInterpolant V =
      ∑ i, Polynomial.C (exceptNodeDenominator i*V i)*nodeNumerator i := by
  apply regular_lagrange_unique (Finset.univ : Finset (Fin (n+1)))
  · have hn := (Polynomial.natDegree_C_mul_le (allNodeDenominators (n+1)) (canonicalInterpolant V)).trans
      (canonicalInterpolant_natDegree V)
    have hh : (Polynomial.C (allNodeDenominators (n+1))*canonicalInterpolant V).degree <
        ((n+1 : ℕ) : WithBot ℕ) :=
      (Polynomial.degree_le_natDegree.trans (WithBot.coe_le_coe.mpr hn)).trans_lt
        (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self n))
    simpa using hh
  · have hn : (∑ i : Fin (n+1), Polynomial.C (exceptNodeDenominator i*V i)*nodeNumerator i).natDegree ≤ n := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      exact (Polynomial.natDegree_C_mul_le _ _).trans (nodeNumerator_natDegree i)
    have hh : (∑ i : Fin (n+1), Polynomial.C (exceptNodeDenominator i*V i)*nodeNumerator i).degree <
        ((n+1 : ℕ) : WithBot ℕ) :=
      (Polynomial.degree_le_natDegree.trans (WithBot.coe_le_coe.mpr hn)).trans_lt
        (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self n))
    simpa using hh
  · intro k hk
    simp only [Polynomial.eval_mul,Polynomial.eval_C,canonicalInterpolant_eval V hV,
      Polynomial.eval_finsetSum]
    rw [Finset.sum_eq_single k]
    · rw [nodeNumerator_self,allNodeDenominators_factor k]; ring
    · intro i hi hik; rw [nodeNumerator_other hik,mul_zero]
    · simp

end PolynomialVacuumAlgebra

end OAI
