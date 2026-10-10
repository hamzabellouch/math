import OAI.Probability.SpanningForest.DeterminantalResponse

namespace OAI

noncomputable section

open scoped Matrix

namespace Problem336.Determinantal

variable {ν ι κ : Type*}
variable [Fintype ν] [DecidableEq ν] [Fintype ι] [decidableColumns : DecidableEq ι]
variable [finiteAuxiliary : Fintype κ] [decidableAuxiliary : DecidableEq κ]

omit decidableColumns finiteAuxiliary decidableAuxiliary in
theorem transferKernel_submatrix [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ν ι ℝ) (f : κ → ι) :
    (A.submatrix id f).transpose * (A * A.transpose)⁻¹ * A.submatrix id f =
      (transferKernel A).submatrix f f := by
  ext i j
  rfl

theorem det_gram_update_div_det
    (A : Matrix ν ι ℝ) (hA : IsUnit (A * A.transpose).det)
    (f : κ → ι) (z : κ → ℝ) :
    (A * A.transpose + A.submatrix id f * Matrix.diagonal z *
      (A.submatrix id f).transpose).det / (A * A.transpose).det =
      (1 + Matrix.diagonal z * (transferKernel A).submatrix f f).det := by
  let C := A.submatrix id f
  have hd := Matrix.det_add_mul C (Matrix.diagonal z * C.transpose) hA
  have hc : C.transpose * (A * A.transpose)⁻¹ * C =
      (transferKernel A).submatrix f f := transferKernel_submatrix A f
  have heq : Matrix.diagonal z * C.transpose * (A * A.transpose)⁻¹ * C =
      Matrix.diagonal z * (transferKernel A).submatrix f f := by
    rw [← hc]
    simp only [Matrix.mul_assoc]
  rw [heq] at hd
  change (A * A.transpose + C * Matrix.diagonal z * C.transpose).det /
    (A * A.transpose).det = _
  rw [Matrix.mul_assoc C, hd]
  exact mul_div_cancel_left₀ _ hA.ne_zero

theorem det_gram_two_update_div_det
    (A : Matrix ν ι ℝ) (hA : IsUnit (A * A.transpose).det)
    (e f : ι) (s t : ℝ) :
    (A * A.transpose + A.submatrix id ![e, f] * Matrix.diagonal ![s, t] *
      (A.submatrix id ![e, f]).transpose).det / (A * A.transpose).det =
      1 + s * transferKernel A e e + t * transferKernel A f f +
        s * t * (pairMatrix (transferKernel A) e f).det := by
  rw [det_gram_update_div_det A hA, Matrix.det_fin_two, pairMatrix_det]
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.submatrix_apply,
    Matrix.one_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, ite_true, Fin.zero_ne_one, ite_false,
    zero_add]
  norm_num; ring

end Problem336.Determinantal

end

end OAI
