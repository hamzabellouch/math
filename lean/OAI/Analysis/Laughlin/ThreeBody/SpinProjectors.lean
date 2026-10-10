import OAI.Analysis.Laughlin.Spin.Basis

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def coupledSelector (Q : ℕ) (z : Fin (Q+1)) :
    Matrix (CoupledIndex Q) (CoupledIndex Q) ℝ :=
  Matrix.diagonal (fun s => if s.1=z then 1 else 0)

noncomputable def threeSpinProjector (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℝ :=
  coupledBasisMatrix Q hQ * coupledSelector Q z * (coupledBasisMatrix Q hQ)ᵀ

theorem coupledSelector_sum (Q : ℕ) : (∑ z : Fin (Q+1), coupledSelector Q z) = 1 := by
  ext s t
  by_cases h : s=t
  · subst t
    simp [coupledSelector,Matrix.sum_apply]
  · simp [coupledSelector,Matrix.sum_apply,h]

theorem coupledSelector_eigenvalue_sum (Q : ℕ) :
    Matrix.diagonal (fun s : CoupledIndex Q => gramEigenvalueFormula Q s.1.val) =
      ∑ z : Fin (Q+1), gramEigenvalueFormula Q z.val • coupledSelector Q z := by
  ext s t
  by_cases h : s=t
  · subst t
    simp [coupledSelector,Matrix.sum_apply]
  · simp [coupledSelector,Matrix.sum_apply,h]

theorem threeSpinProjector_sum (Q : ℕ) (hQ : 2 ≤ Q) :
    (∑ z : Fin (Q+1), threeSpinProjector Q hQ z) = 1 := by
  unfold threeSpinProjector
  rw [← Matrix.sum_mul,← Matrix.mul_sum,coupledSelector_sum,Matrix.mul_one,coupledBasis_complete Q hQ]

theorem threeSpinProjector_transpose (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    (threeSpinProjector Q hQ z)ᵀ = threeSpinProjector Q hQ z := by
  simp only [threeSpinProjector,coupledSelector,Matrix.transpose_mul,Matrix.transpose_transpose,
    Matrix.diagonal_transpose,Matrix.mul_assoc]

theorem coupledSelector_mul (Q : ℕ) (z w : Fin (Q+1)) :
    coupledSelector Q z * coupledSelector Q w = if z=w then coupledSelector Q z else 0 := by
  unfold coupledSelector
  rw [Matrix.diagonal_mul_diagonal]
  ext s t
  by_cases hzw : z=w
  · subst w
    simp only [ite_true,Matrix.diagonal_apply]
    split_ifs <;> norm_num
  · simp only [ite_eq_right hzw,Matrix.diagonal_apply,Matrix.zero_apply]
    by_cases hst : s=t
    · subst t
      simp only [ite_true]
      by_cases hz : s.1=z
      · simp [hz,hzw]
      · simp [hz]
    · simp [hst]

theorem threeSpinProjector_mul (Q : ℕ) (hQ : 2 ≤ Q) (z w : Fin (Q+1)) :
    threeSpinProjector Q hQ z * threeSpinProjector Q hQ w =
      if z=w then threeSpinProjector Q hQ z else 0 := by
  unfold threeSpinProjector
  calc
    _ = coupledBasisMatrix Q hQ * coupledSelector Q z *
      ((coupledBasisMatrix Q hQ)ᵀ * coupledBasisMatrix Q hQ) * coupledSelector Q w *
      (coupledBasisMatrix Q hQ)ᵀ := by simp only [Matrix.mul_assoc]
    _ = coupledBasisMatrix Q hQ * (coupledSelector Q z * coupledSelector Q w) *
      (coupledBasisMatrix Q hQ)ᵀ := by rw [coupledBasis_isometry Q hQ,Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [coupledSelector_mul]; split_ifs <;> simp

theorem source_threeBody_spectral_decomposition (Q : ℕ) (hQ : 2 ≤ Q) :
    threeGram Q-1 = ∑ z : Fin (Q+1), gramEigenvalueFormula Q z.val • threeSpinProjector Q hQ z := by
  rw [threeGram_diagonalization Q hQ,coupledSelector_eigenvalue_sum]
  rw [Matrix.mul_sum,Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [threeSpinProjector,Matrix.mul_smul,Matrix.smul_mul]

theorem coupledSelector_eigen (Q : ℕ) (z : Fin (Q+1)) :
    Matrix.diagonal (fun s : CoupledIndex Q => gramEigenvalueFormula Q s.1.val) *
      coupledSelector Q z = gramEigenvalueFormula Q z.val • coupledSelector Q z := by
  unfold coupledSelector
  rw [Matrix.diagonal_mul_diagonal]
  ext s t
  by_cases hst : s=t
  · subst t
    simp only [Matrix.diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul]
    by_cases h : s.1=z
    · simp [h]
    · simp [h]
  · simp [hst]

theorem threeSpinProjector_sub_one_eigen (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    (threeGram Q-1)*threeSpinProjector Q hQ z =
      gramEigenvalueFormula Q z.val • threeSpinProjector Q hQ z := by
  unfold threeSpinProjector
  calc
    _ = ((threeGram Q-1)*coupledBasisMatrix Q hQ)*coupledSelector Q z*(coupledBasisMatrix Q hQ)ᵀ := by
      simp only [Matrix.mul_assoc]
    _ = coupledBasisMatrix Q hQ *
      (Matrix.diagonal (fun s : CoupledIndex Q => gramEigenvalueFormula Q s.1.val)*coupledSelector Q z)*
      (coupledBasisMatrix Q hQ)ᵀ := by rw [coupledBasis_eigen]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [coupledSelector_eigen]; simp only [Matrix.mul_smul,Matrix.smul_mul]

theorem threeSpinProjector_eigen (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    threeGram Q*threeSpinProjector Q hQ z =
      (1+gramEigenvalueFormula Q z.val) • threeSpinProjector Q hQ z := by
  have he := threeSpinProjector_sub_one_eigen Q hQ z
  rw [Matrix.sub_mul,Matrix.one_mul] at he
  calc
    _ = (threeGram Q*threeSpinProjector Q hQ z-threeSpinProjector Q hQ z)+threeSpinProjector Q hQ z := by abel
    _ = gramEigenvalueFormula Q z.val • threeSpinProjector Q hQ z+threeSpinProjector Q hQ z := by rw [he]
    _ = _ := by ext i j; simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]; ring

end Laughlin.Spin

end OAI
