import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorFamilyAccuracy

namespace OAI

/-! Internal physical exchanges encode the one-site and scalar X/Z terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {n : ℕ} {τ : Type*} [Fintype τ]

def qmaFourTensorFields (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  ∑ e, qmaSiteMatrix (site e) (qmaFourAxisField (axis e) (weight e))

def qmaFourTensorFieldShift (axis : τ → Fin 2) (weight : τ → ℝ) : ℝ :=
  ∑ e, qmaFourAxisFieldShift (axis e) (weight e)

def qmaFourTensorOnsite (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) (constant : ℝ) :
    Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  qmaFourTensorFields site axis weight+((constant-qmaFourTensorFieldShift axis weight:ℝ):ℂ) • 1

theorem qmaFourTensorOnsite_compression (site : τ → Fin n) (axis : τ → Fin 2)
    (weight : τ → ℝ) (constant : ℝ) :
    (qmaFourTensorEncoding n).conjTranspose*qmaFourTensorOnsite site axis weight constant*qmaFourTensorEncoding n =
      (∑ e, (weight e:ℂ) • qmaSiteMatrix (site e) (qmaFourAxis (axis e)))+(constant:ℂ) • 1 := by
  simp only [qmaFourTensorOnsite,qmaFourTensorFields,Matrix.mul_add,Matrix.add_mul,
    Matrix.mul_sum,Matrix.sum_mul,qmaFourTensor_site_compression,qmaFourAxisField_compression,
    qmaSiteMatrix_add,qmaSiteMatrix_smul,qmaSiteMatrix_one,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,qmaFourTensorEncoding_gram,Finset.sum_add_distrib,← Finset.sum_smul]
  simp only [← Complex.ofReal_sum,qmaFourTensorFieldShift]
  module

theorem qmaFourTensorFields_star (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) :
    (qmaFourTensorFields site axis weight).conjTranspose = qmaFourTensorFields site axis weight := by
  simp only [qmaFourTensorFields,Matrix.conjTranspose_sum,qmaSiteMatrix_star,qmaFourAxisField_star]

theorem qmaFourTensorOnsite_star (site : τ → Fin n) (axis : τ → Fin 2)
    (weight : τ → ℝ) (constant : ℝ) :
    (qmaFourTensorOnsite site axis weight constant).conjTranspose = qmaFourTensorOnsite site axis weight constant := by
  simp only [qmaFourTensorOnsite,Matrix.conjTranspose_add,qmaFourTensorFields_star,
    Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_ofReal,Matrix.conjTranspose_one]

theorem qmaFourTensorFields_norm (site : τ → Fin n) (axis : τ → Fin 2) (weight : τ → ℝ) :
    ‖spinMatrixOperator (qmaFourTensorFields site axis weight)‖ ≤ 6*(∑ e, |weight e|) := by
  rw [qmaFourTensorFields,spinMatrixOperator_sum,Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ => qmaFourTensorAxisField_norm _ _ _))

theorem qmaFourAxisFieldShift_abs (a : Fin 2) (t : ℝ) : |qmaFourAxisFieldShift a t| ≤ |t| := by
  unfold qmaFourAxisFieldShift
  split_ifs
  · simpa only [abs_zero] using abs_nonneg t
  · rw [abs_div]
    norm_num

theorem qmaFourTensorFieldShift_abs (axis : τ → Fin 2) (weight : τ → ℝ) :
    |qmaFourTensorFieldShift axis weight| ≤ ∑ e, |weight e| := by
  unfold qmaFourTensorFieldShift
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun e _ => qmaFourAxisFieldShift_abs _ _))

theorem qmaFourTensorOnsite_norm (site : τ → Fin n) (axis : τ → Fin 2)
    (weight : τ → ℝ) (constant : ℝ) :
    ‖spinMatrixOperator (qmaFourTensorOnsite site axis weight constant)‖ ≤
      7*(∑ e, |weight e|)+|constant| := by
  have h1 : ‖spinMatrixOperator (1 : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)‖ ≤ 1 := by
    apply spinMatrixOperator_unitary_norm
    simp
  have hs := qmaFourTensorFieldShift_abs axis weight
  have hf := qmaFourTensorFields_norm site axis weight
  rw [qmaFourTensorOnsite,spinMatrixOperator_add]
  apply (norm_add_le _ _).trans
  rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  have hscalar := mul_le_mul_of_nonneg_left h1 (abs_nonneg (constant-qmaFourTensorFieldShift axis weight))
  have habs := abs_sub constant (qmaFourTensorFieldShift axis weight)
  nlinarith

end ContinuumCoulomb

end

end OAI
