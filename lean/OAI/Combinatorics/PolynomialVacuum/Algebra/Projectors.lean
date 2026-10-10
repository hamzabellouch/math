import OAI.Combinatorics.PolynomialVacuum.Algebra.Gram

namespace OAI

namespace PolynomialVacuumAlgebra

noncomputable def insertionMatrix : Matrix Pair Spin ℂ := insertion

noncomputable def cupColumn : Matrix Pair Unit ℂ := fun ab _ => cup ab

 theorem cupColumn_gram : cupColumn.transpose * cupColumn = (-nZero) • (1 : Matrix Unit Unit ℂ) := by
  ext a b
  cases a; cases b
  simp [Matrix.mul_apply,Matrix.transpose_apply,cupColumn,cup_norm]

theorem insertion_matrix_gram : insertionMatrix.transpose * insertionMatrix = nZero • (1 : Matrix Spin Spin ℂ) := by
  ext h k
  change (∑ a : Pair, insertion a h * insertion a k) = nZero * (if h=k then 1 else 0)
  rw [insertion_gram]
  by_cases he : h=k <;> simp [he]

theorem cupColumn_insertion : cupColumn.transpose * insertionMatrix = 0 := by
  ext a h
  cases a
  change (∑ a : Pair, cup a * insertion a h) = 0
  exact cup_insertion h

theorem insertion_cupColumn : insertionMatrix.transpose * cupColumn = 0 := by
  have h := congrArg Matrix.transpose cupColumn_insertion
  simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] using h

theorem Pzero_factor : Pzero = (-nZero)⁻¹ • (cupColumn * cupColumn.transpose) := by
  ext a b
  simp [Pzero,Matrix.mul_apply,cupColumn,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul,div_eq_mul_inv]
  ring

theorem Pone_factor : Pone = nZero⁻¹ • (insertionMatrix * insertionMatrix.transpose) := by
  ext a b
  change (∑ h : Spin, insertion a h * insertion b h) / nZero =
    nZero⁻¹ * (∑ h : Spin, insertion a h * insertion b h)
  ring

theorem gram_projection_idempotent {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (k : ℂ) (hk : k ≠ 0) (hGram : A.transpose*A=k • 1) :
    (k⁻¹ • (A*A.transpose))*(k⁻¹ • (A*A.transpose)) = k⁻¹ • (A*A.transpose) := by
  rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  have hassoc : (A*A.transpose)*(A*A.transpose) = A*(A.transpose*A)*A.transpose := by
    simp only [Matrix.mul_assoc]
  rw [hassoc,hGram,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,smul_smul]
  congr 1
  field_simp

theorem gram_projection_orthogonal {m n o : Type*} [Fintype m] [Fintype n] [Fintype o]
    (A : Matrix m n ℂ) (B : Matrix m o ℂ) (a b : ℂ) (hGram : A.transpose*B=0) :
    (a • (A*A.transpose))*(b • (B*B.transpose)) = 0 := by
  rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  have hassoc : (A*A.transpose)*(B*B.transpose) = A*(A.transpose*B)*B.transpose := by
    simp only [Matrix.mul_assoc]
  rw [hassoc,hGram,Matrix.mul_zero,Matrix.zero_mul,smul_zero]

theorem Pzero_idempotent : Pzero*Pzero=Pzero := by
  rw [Pzero_factor]
  exact gram_projection_idempotent cupColumn (-nZero) (neg_ne_zero.mpr nZero_ne_zero) cupColumn_gram

theorem Pone_idempotent : Pone*Pone=Pone := by
  rw [Pone_factor]
  exact gram_projection_idempotent insertionMatrix nZero nZero_ne_zero insertion_matrix_gram

theorem Pzero_Pone : Pzero*Pone=0 := by
  rw [Pzero_factor,Pone_factor]
  exact gram_projection_orthogonal cupColumn insertionMatrix _ _ cupColumn_insertion

theorem Pone_Pzero : Pone*Pzero=0 := by
  rw [Pzero_factor,Pone_factor]
  exact gram_projection_orthogonal insertionMatrix cupColumn _ _ insertion_cupColumn

theorem Pzero_Ptwo : Pzero*Ptwo=0 := by
  simp [Ptwo,mul_sub,Pzero_Pone,Pzero_idempotent]

theorem Ptwo_Pzero : Ptwo*Pzero=0 := by
  simp [Ptwo,sub_mul,Pone_Pzero,Pzero_idempotent]

theorem Pone_Ptwo : Pone*Ptwo=0 := by
  simp [Ptwo,mul_sub,Pone_idempotent,Pone_Pzero]

theorem Ptwo_Pone : Ptwo*Pone=0 := by
  simp [Ptwo,sub_mul,Pone_idempotent,Pzero_Pone]

theorem Ptwo_idempotent : Ptwo*Ptwo=Ptwo := by
  calc
    Ptwo*Ptwo = Ptwo*1-Ptwo*Pone-Ptwo*Pzero := by simp only [Ptwo,mul_sub]
    _ = Ptwo := by rw [mul_one,Ptwo_Pone,Ptwo_Pzero,sub_zero,sub_zero]

theorem projectors_sum : Pzero+Pone+Ptwo=1 := by simp [Ptwo]; abel

end PolynomialVacuumAlgebra

end OAI
