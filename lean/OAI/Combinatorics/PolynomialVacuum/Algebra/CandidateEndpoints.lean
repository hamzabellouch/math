import OAI.Combinatorics.PolynomialVacuum.Algebra.Candidate

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem interpolateState_minus_zero {n : ℕ} (ψ : State n) (χ : State (n+1))
    (s : Fin (n+2) → Spin) (Xv : Fin (n+2) → ℂ)
    (hs : s (Fin.last (n+1))=Spin.minus) (hz : Xv (Fin.last (n+1))=0) :
    eval Xv (interpolateState ψ χ s)=0 := by
  simp [interpolateState,hs,hz]

theorem interpolateState_zero_reduction {n : ℕ} (ψ : State n) (χ : State (n+1))
    (s : Fin (n+2) → Spin) (Xv : Fin (n+2) → ℂ)
    (hs : s (Fin.last (n+1))=Spin.zero) (hz : Xv (Fin.last (n+1))=0) :
    eval Xv (interpolateState ψ χ s)=
      (∏ j : Fin (n+1), Xv j.castSucc)*eval (Xv ∘ Fin.castSucc) (χ (s ∘ Fin.castSucc)) := by
  simp [interpolateState,hs,hz,eval_rename]

theorem vacuumCandidate_zero_reduction (n : ℕ)
    (s : Fin (n+1) → Spin) (Xv : Fin (n+1) → ℂ)
    (hs : s (Fin.last n)=Spin.zero) (hz : Xv (Fin.last n)=0) :
    eval Xv (vacuumCandidate (n+1) s)=
      (∏ j : Fin n, Xv j.castSucc)*eval (Xv ∘ Fin.castSucc) (vacuumCandidate n (s ∘ Fin.castSucc)) := by
  cases n with
  | zero => simpa [vacuumCandidate] using hs
  | succ n => exact interpolateState_zero_reduction _ _ _ _ hs hz

theorem degreeOf_rename_last {m : ℕ} (p : MvPolynomial (Fin m) ℂ) :
    (rename Fin.castSucc p).degreeOf (Fin.last m)=0 := by
  by_contra h
  obtain ⟨i,hi,he⟩ := mem_vars_rename Fin.castSucc p (mem_vars_iff_degreeOf_ne_zero.mpr h)
  exact Fin.castSucc_ne_last i he

theorem reinsertLast_degree {m : ℕ} (p : Polynomial (MvPolynomial (Fin m) ℂ)) :
    (reinsertLast p).degreeOf (Fin.last m) ≤ p.natDegree := by
  unfold reinsertLast
  rw [Polynomial.eval₂_eq_sum,Polynomial.sum_def]
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro i hi
  apply (degreeOf_mul_le _ _ _).trans
  change (rename Fin.castSucc (p.coeff i)).degreeOf (Fin.last m) +
    ((C T⁻¹*X (Fin.last m))^i : MvPolynomial (Fin (m+1)) ℂ).degreeOf (Fin.last m) ≤ p.natDegree
  rw [degreeOf_rename_last,zero_add]
  apply (degreeOf_pow_le _ _ _).trans
  have hz : (C T⁻¹*X (Fin.last m) : MvPolynomial (Fin (m+1)) ℂ).degreeOf (Fin.last m) ≤ 1 := by
    exact (degreeOf_C_mul_le _ _ _).trans (by simp)
  exact (Nat.mul_le_mul_left i hz).trans (by simpa using Polynomial.le_natDegree_of_mem_supp i hi)

end PolynomialVacuumAlgebra

end OAI
