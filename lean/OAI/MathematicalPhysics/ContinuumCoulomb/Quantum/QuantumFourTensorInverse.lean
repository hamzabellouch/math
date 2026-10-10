import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorHilbert

namespace OAI

/-! The bounded inverse acts exactly on the physical two-block excitations. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {n : ℕ}

theorem qmaFourTensor_padded_star (n : ℕ) :
    (qmaFourTensorPaddedMatrix n).conjTranspose = qmaFourTensorPaddedMatrix n := by
  simp only [qmaFourTensorPaddedMatrix,Matrix.conjTranspose_add,Matrix.conjTranspose_smul,
    qmaFourTensor_penalty_star,qmaFourTensor_projection_star]
  norm_num

theorem qmaFourTensorPadded_symmetric (n : ℕ) (r : ℝ)
    (x y : EuclideanSpace ℂ (Fin n → Fin 16)) :
    ⟪x,qmaFourTensorPadded n r y⟫_ℝ = ⟪qmaFourTensorPadded n r x,y⟫_ℝ := by
  change ⟪x,r^2 • qmaMatrixOperator _ y⟫_ℝ = ⟪r^2 • qmaMatrixOperator _ x,y⟫_ℝ
  rw [inner_smul_right,inner_smul_left,qmaMatrixOperator_real_symmetric _ (qmaFourTensor_padded_star n)]
  simp only [starRingEnd_apply,star_trivial]

theorem qmaFourTensorPadded_encoding (n : ℕ) :
    qmaFourTensorPaddedMatrix n*qmaFourTensorEncoding n = (4:ℂ) • qmaFourTensorEncoding n := by
  rw [qmaFourTensorPaddedMatrix,Matrix.add_mul,qmaFourTensorPenalty_encoding,
    Matrix.smul_mul,← qmaFourTensorEncoding_projector,Matrix.mul_assoc,qmaFourTensorEncoding_gram,
    Matrix.mul_one,zero_add]

theorem qmaFourTensorPadded_restrict (n : ℕ) (r : ℝ)
    (x : EuclideanSpace ℂ (Fin n → Fin 16)) :
    qmaFourTensorRestriction n (qmaFourTensorPadded n r x) =
      (4*r^2) • qmaFourTensorRestriction n x := by
  have hm := congrArg Matrix.conjTranspose (qmaFourTensorPadded_encoding n)
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_smul,qmaFourTensor_padded_star] at hm
  norm_num at hm
  have he := congrArg (fun M => qmaMatrixOperator M x) hm
  rw [qmaMatrixOperator_mul,qmaMatrixOperator_smul] at he
  change qmaFourTensorRestriction n (qmaMatrixOperator (qmaFourTensorPaddedMatrix n) x) =
    (4:ℂ) • qmaFourTensorRestriction n x at he
  change qmaFourTensorRestriction n (r^2 • qmaMatrixOperator (qmaFourTensorPaddedMatrix n) x) = _
  rw [map_smul,he]
  ext s
  simp only [PiLp.smul_apply,Complex.real_smul]
  push_cast
  ring

theorem qmaFourTensorInverse_high {r : ℝ} (hr : 0 < r)
    (T : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (hAT : ∀ x, qmaFourTensorPadded n r (T x) = x)
    (x : EuclideanSpace ℂ (Fin n → Fin 16)) (hx : qmaFourTensorRestriction n x = 0) :
    qmaFourTensorRestriction n (T x) = 0 := by
  have h := congrArg (qmaFourTensorRestriction n) (hAT x)
  rw [qmaFourTensorPadded_restrict,hx] at h
  exact (smul_eq_zero.mp h).resolve_left (by positivity)

theorem qmaFourTensorPadded_column
    (W : Matrix (Fin n → Fin 16) (Fin n → Fin 2) ℂ)
    (hW : (qmaFourTensorEncoding n).conjTranspose*W = 0)
    (hH : qmaFourTensorPenalty n*W = (8:ℂ) • W) :
    qmaFourTensorPaddedMatrix n*W = (8:ℂ) • W := by
  rw [qmaFourTensorPaddedMatrix,Matrix.add_mul,hH,Matrix.smul_mul,
    ← qmaFourTensorEncoding_projector,Matrix.mul_assoc,hW,Matrix.mul_zero,smul_zero,add_zero]

theorem qmaFourTensorInverse_column {r : ℝ} (hr : 0 < r)
    (T : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (hTA : ∀ x, T (qmaFourTensorPadded n r x) = x)
    (W : Matrix (Fin n → Fin 16) (Fin n → Fin 2) ℂ)
    (hW : (qmaFourTensorEncoding n).conjTranspose*W = 0)
    (hH : qmaFourTensorPenalty n*W = (8:ℂ) • W)
    (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    T (qmaMatrixOperator W p) = (8*r^2)⁻¹ • qmaMatrixOperator W p := by
  apply qmaInverse_eigenvector _ _ hTA _ (by positivity)
  have he := congrArg (fun M => qmaMatrixOperator M p) (qmaFourTensorPadded_column W hW hH)
  rw [qmaMatrixOperator_mul,qmaMatrixOperator_smul] at he
  change r^2 • qmaMatrixOperator (qmaFourTensorPaddedMatrix n) (qmaMatrixOperator W p) = _
  simp only [ContinuousLinearMap.comp_apply,_root_.smul_apply] at he
  rw [he]
  ext s
  simp only [PiLp.smul_apply,Complex.real_smul]
  push_cast
  ring

end ContinuumCoulomb

end

end OAI
