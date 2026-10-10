import OAI.Analysis.Laughlin.Spin.Orthogonal

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

abbrev CoupledIndex (Q : ℕ) := Σ z : Fin (Q+1), Fin (coupledWeight Q z.val+1)

theorem fin_sum_values (n : ℕ) : (∑ i : Fin n, (i.val : ℝ)) = (n : ℝ)*(n-1)/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.cast_zero,zero_add,Fin.val_succ,Nat.cast_add,Nat.cast_one,
      Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,ih]
    ring

theorem coupledIndex_card (Q : ℕ) (hQ : 2 ≤ Q) :
    Fintype.card (CoupledIndex Q) = Fintype.card (PairOrbitalIndex Q) := by
  have hr : (Fintype.card (CoupledIndex Q) : ℝ) = (Fintype.card (PairOrbitalIndex Q) : ℝ) := by
    simp only [Fintype.card_sigma,Fintype.card_fin,Fintype.card_prod,Nat.cast_sum]
    have hc (z : Fin (Q+1)) : ((coupledWeight Q z.val+1 : ℕ) : ℝ) = 3*(Q : ℝ)-1-2*z.val := by
      unfold coupledWeight
      rw [Nat.cast_add,Nat.cast_one,Nat.cast_sub (by omega : 2*z.val ≤ 3*Q-2),
        Nat.cast_sub (by omega : 2 ≤ 3*Q)]
      push_cast; ring
    simp_rw [hc]
    rw [Finset.sum_sub_distrib,Finset.sum_const,← Finset.mul_sum,fin_sum_values]
    simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    rw [Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast
    ring
  exact_mod_cast hr

noncomputable def coupledBasisMatrix (Q : ℕ) (hQ : 2 ≤ Q) :
    Matrix (PairOrbitalIndex Q) (CoupledIndex Q) ℝ := fun i s =>
  normalizedCoupledDescendant Q s.1.val hQ (by omega) s.2.val i

theorem coupledBasis_isometry (Q : ℕ) (hQ : 2 ≤ Q) :
    (coupledBasisMatrix Q hQ)ᵀ * coupledBasisMatrix Q hQ = 1 := by
  ext s t
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply,coupledBasisMatrix,Matrix.one_apply]
  by_cases hst : s=t
  · subst t
    rw [ite_eq_left rfl]
    simpa only [vectorNormSq,pow_two] using
      normalizedCoupledDescendant_norm Q s.1.val s.2.val hQ (by omega) (by omega)
  · rw [ite_eq_right hst]
    apply normalizedCoupledDescendant_orthogonal
    rcases s with ⟨z,n⟩
    rcases t with ⟨w,m⟩
    by_cases hzw : z=w
    · subst w
      right
      intro hnm
      apply hst
      have he : n=m := Fin.ext hnm
      rw [he]
    · left
      intro h
      exact hzw (Fin.ext h)

theorem coupledBasis_complete (Q : ℕ) (hQ : 2 ≤ Q) :
    coupledBasisMatrix Q hQ * (coupledBasisMatrix Q hQ)ᵀ = 1 := by
  exact (Matrix.mul_eq_one_comm_of_card_eq (m := CoupledIndex Q) (n := PairOrbitalIndex Q)
    (R := ℝ) (coupledIndex_card Q hQ)).mp (coupledBasis_isometry Q hQ)

theorem coupledBasis_eigen (Q : ℕ) (hQ : 2 ≤ Q) :
    (threeGram Q-1)*coupledBasisMatrix Q hQ =
      coupledBasisMatrix Q hQ * Matrix.diagonal (fun s : CoupledIndex Q => gramEigenvalueFormula Q s.1.val) := by
  ext i s
  rw [Matrix.mul_apply,Matrix.mul_diagonal]
  have he := congrFun (normalizedCoupledDescendant_eigen Q s.1.val s.2.val hQ (by omega)) i
  simpa only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,coupledBasisMatrix,mul_comm] using he

theorem threeGram_diagonalization (Q : ℕ) (hQ : 2 ≤ Q) :
    threeGram Q-1 = coupledBasisMatrix Q hQ *
      Matrix.diagonal (fun s : CoupledIndex Q => gramEigenvalueFormula Q s.1.val) *
      (coupledBasisMatrix Q hQ)ᵀ := by
  calc
    _ = (threeGram Q-1)*(coupledBasisMatrix Q hQ*(coupledBasisMatrix Q hQ)ᵀ) := by
      rw [coupledBasis_complete Q hQ,Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc,coupledBasis_eigen Q hQ]

end Laughlin.Spin

end OAI
