import OAI.Analysis.Triangular.Certificate.MatrixInterval

namespace OAI

noncomputable section

namespace AtomicTriangular.MatrixBounds

variable {n : Type*} [Fintype n] [Nonempty n] [DecidableEq n]

/-- A right residual with column norm less than one certifies invertibility. -/
lemma isUnit_of_right_residual (A B : Matrix n n ℝ)
    (h : matNorm (1 - A * B) < 1) : IsUnit A := by
  have hunit : IsUnit (A * B) := by
    apply isUnit_of_residual (A * B) 1
    have heq : A * B - 1 = -(1 - A * B) := by abel
    simpa only [Matrix.one_mul, heq, matNorm_neg] using h
  have hdet := (Matrix.isUnit_iff_isUnit_det (A * B)).mp hunit
  rw [Matrix.det_mul] at hdet
  exact (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_of_mul_isUnit_left hdet)

omit [Nonempty n] in
private lemma inverse_right_residual_identity (A B : Matrix n n ℝ) (hA : IsUnit A) :
    A⁻¹ - B = A⁻¹ * (1 - A * B) := by
  have hdet := (Matrix.isUnit_iff_isUnit_det A).mp hA
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul A hdet, Matrix.one_mul]

/-- The right residual bounds the norm of the actual matrix inverse. -/
lemma inverse_bound_of_right_residual (A B : Matrix n n ℝ) (k e : ℝ)
    (hB : matNorm B ≤ k) (hE : matNorm (1 - A * B) ≤ e) (he : e < 1) :
    matNorm A⁻¹ ≤ k / (1 - e) := by
  have hA := isUnit_of_right_residual A B (hE.trans_lt he)
  have hsplit : A⁻¹ = B + A⁻¹ * (1 - A * B) := by
    rw [← inverse_right_residual_identity A B hA]
    abel
  have hbound : matNorm A⁻¹ ≤ k + matNorm A⁻¹ * e := by
    calc
      matNorm A⁻¹ ≤ matNorm B + matNorm (A⁻¹ * (1 - A * B)) := by
        conv_lhs => rw [hsplit]
        exact matNorm_add _ _
      _ ≤ k + matNorm A⁻¹ * e :=
        add_le_add hB ((matNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_left hE (matNorm_nonneg _)))
  apply (le_div_iff₀ (sub_pos.mpr he)).mpr
  nlinarith

/-- One residual correction leaves a second order error in the inverse. -/
lemma inverse_second_order_right_residual_bound (A B : Matrix n n ℝ) (k e : ℝ)
    (hB : matNorm B ≤ k) (hE : matNorm (1 - A * B) ≤ e)
    (he0 : 0 ≤ e) (he : e < 1) :
    matNorm (A⁻¹ - (B + B * (1 - A * B))) ≤ k * e ^ 2 / (1 - e) := by
  have hA := isUnit_of_right_residual A B (hE.trans_lt he)
  have hrem : A⁻¹ - (B + B * (1 - A * B)) =
      A⁻¹ * ((1 - A * B) * (1 - A * B)) := by
    rw [← Matrix.mul_assoc, ← inverse_right_residual_identity A B hA,
      Matrix.sub_mul, ← inverse_right_residual_identity A B hA]
    abel
  have hE2 : matNorm ((1 - A * B) * (1 - A * B)) ≤ e ^ 2 := by
    exact (matNorm_mul _ _).trans ((mul_le_mul hE hE
      (matNorm_nonneg _) he0).trans_eq (by ring))
  rw [hrem]
  calc
    matNorm (A⁻¹ * ((1 - A * B) * (1 - A * B))) ≤
        matNorm A⁻¹ * matNorm ((1 - A * B) * (1 - A * B)) := matNorm_mul _ _
    _ ≤ (k / (1 - e)) * e ^ 2 := mul_le_mul
      (inverse_bound_of_right_residual A B k e hB hE he) hE2 (matNorm_nonneg _)
      (div_nonneg ((matNorm_nonneg B).trans hB) (sub_pos.mpr he).le)
    _ = k * e ^ 2 / (1 - e) := by ring

/-- The matrix norm certificate gives the same second order entrywise enclosure. -/
lemma inverse_entry_second_order_right_residual_bound (A B : Matrix n n ℝ) (k e : ℝ)
    (hB : matNorm B ≤ k) (hE : matNorm (1 - A * B) ≤ e)
    (he0 : 0 ≤ e) (he : e < 1) (i j : n) :
    |A⁻¹ i j - (B + B * (1 - A * B)) i j| ≤ k * e ^ 2 / (1 - e) := by
  exact (Interval.matrixEntry_le_norm (A⁻¹ - (B + B * (1 - A * B))) i j).trans
    (inverse_second_order_right_residual_bound A B k e hB hE he0 he)

end AtomicTriangular.MatrixBounds

end

end OAI
