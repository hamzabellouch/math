import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorFamily
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCoerciveInverse
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorForms

namespace OAI

/-! Actual low/high coordinates and the bounded padded inverse for the four-spin code. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical ComplexOrder

def qmaFourTensorInclusion (n : ℕ) :
    EuclideanSpace ℂ (Fin n → Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16) :=
  (qmaMatrixOperator (qmaFourTensorEncoding n)).restrictScalars ℝ

def qmaFourTensorRestriction (n : ℕ) :
    EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 2) :=
  (qmaMatrixOperator (qmaFourTensorEncoding n).conjTranspose).restrictScalars ℝ

def qmaFourTensorHigh (n : ℕ) :
    EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16) :=
  (qmaMatrixOperator (1-qmaFourTensorProjection n)).restrictScalars ℝ

theorem qmaFourTensor_restrict_include (n : ℕ) (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    qmaFourTensorRestriction n (qmaFourTensorInclusion n p) = p := by
  change qmaMatrixOperator _ (qmaMatrixOperator _ p) = p
  rw [← ContinuousLinearMap.comp_apply,← qmaMatrixOperator_mul,qmaFourTensorEncoding_gram,
    qmaMatrixOperator_square,spinMatrixOperator_one]
  rfl

theorem qmaFourTensor_inclusion_adjoint (n : ℕ) (p : EuclideanSpace ℂ (Fin n → Fin 2))
    (x : EuclideanSpace ℂ (Fin n → Fin 16)) :
    ⟪qmaFourTensorInclusion n p,x⟫_ℝ = ⟪p,qmaFourTensorRestriction n x⟫_ℝ := by
  have h := ContinuousLinearMap.adjoint_inner_right (qmaMatrixOperator (qmaFourTensorEncoding n)) p x
  rw [← qmaMatrixOperator_star] at h
  rw [qmaEuclidean_real_inner,qmaEuclidean_real_inner]
  exact congrArg Complex.re h.symm

theorem qmaFourTensor_highPart (n : ℕ) (x : EuclideanSpace ℂ (Fin n → Fin 16)) :
    Perturbation.orthogonalHighPart (qmaFourTensorInclusion n) (qmaFourTensorRestriction n) x =
      qmaFourTensorHigh n x := by
  unfold Perturbation.orthogonalHighPart qmaFourTensorHigh qmaFourTensorInclusion qmaFourTensorRestriction
  change x-qmaMatrixOperator _ (qmaMatrixOperator _ x) = qmaMatrixOperator _ x
  rw [← ContinuousLinearMap.comp_apply,← qmaMatrixOperator_mul,qmaFourTensorEncoding_projector]
  simp only [qmaMatrixOperator_square,spinMatrixOperator_sub,spinMatrixOperator_one]
  rfl

theorem qmaFourTensorRestriction_high (n : ℕ) (x : EuclideanSpace ℂ (Fin n → Fin 16)) :
    qmaFourTensorRestriction n (qmaFourTensorHigh n x) = 0 := by
  rw [← qmaFourTensor_highPart]
  exact Perturbation.orthogonalHighPart_kernel _ _ (qmaFourTensor_restrict_include n) x

theorem qmaFourTensor_projection_star (n : ℕ) :
    (qmaFourTensorProjection n).conjTranspose = qmaFourTensorProjection n := by
  rw [← qmaFourTensorEncoding_projector,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]

theorem qmaFourTensor_penalty_star (n : ℕ) :
    (qmaFourTensorPenalty n).conjTranspose = qmaFourTensorPenalty n := by
  have h := (qmaFourTensorGap_posSemidef n).isHermitian
  have hp := qmaFourTensor_projection_star n
  have hs : ((4:ℂ) • (1-qmaFourTensorProjection n)).conjTranspose =
      (4:ℂ) • (1-qmaFourTensorProjection n) := by
    simp only [Matrix.conjTranspose_smul,Matrix.conjTranspose_sub,Matrix.conjTranspose_one,hp]
    norm_num
  have he := congrArg (fun M : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ =>
      M+(4:ℂ) • (1-qmaFourTensorProjection n)) h.eq
  simpa only [Matrix.conjTranspose_sub,hs,sub_add_cancel] using he

def qmaFourTensorPaddedMatrix (n : ℕ) : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ :=
  qmaFourTensorPenalty n+(4:ℂ) • qmaFourTensorProjection n

def qmaFourTensorPadded (n : ℕ) (r : ℝ) :
    EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16) :=
  r^2 • (qmaMatrixOperator (qmaFourTensorPaddedMatrix n)).restrictScalars ℝ

theorem qmaFourTensor_padded_gap (n : ℕ) (r : ℝ) (x : EuclideanSpace ℂ (Fin n → Fin 16)) :
    (4*r^2)*‖x‖^2 ≤ ⟪x,qmaFourTensorPadded n r x⟫_ℝ := by
  have he : qmaFourTensorPaddedMatrix n-(4:ℂ) • 1 =
      qmaFourTensorPenalty n-(4:ℂ) • (1-qmaFourTensorProjection n) := by
    unfold qmaFourTensorPaddedMatrix
    module
  have hh := (Complex.nonneg_iff.mp
    ((he ▸ qmaFourTensorGap_posSemidef n).dotProduct_mulVec_nonneg (fun i => x i))).1
  change 0 ≤ qmaQuadratic (qmaFourTensorPaddedMatrix n-(4:ℂ) • 1) (fun i => x i) at hh
  rw [qmaQuadratic_sub] at hh
  have hone : qmaQuadratic ((4:ℂ) • (1 : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ))
      (fun i => x i) = 4*‖x‖^2 := by
    rw [show (4:ℂ) = ((4:ℝ):ℂ) from rfl,qmaQuadratic_smul,qmaQuadratic_operator,
      qmaMatrixOperator_square,spinMatrixOperator_one,one_apply_eq_self,real_inner_self_eq_norm_sq]
  rw [hone] at hh
  have h := mul_le_mul_of_nonneg_left (sub_nonneg.mp hh) (sq_nonneg r)
  change _ ≤ ⟪x,r^2 • qmaMatrixOperator (qmaFourTensorPaddedMatrix n) x⟫_ℝ
  rw [inner_smul_right,← qmaQuadratic_operator]
  nlinarith

theorem qmaFourTensor_inverse_exists (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ T : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16),
      (∀ x, qmaFourTensorPadded n r (T x) = x) ∧
      (∀ x, T (qmaFourTensorPadded n r x) = x) ∧ ‖T‖ ≤ 1/(4*r^2) :=
  qmaCoerciveInverse_exists _ (by positivity) (qmaFourTensor_padded_gap n r)

end ContinuumCoulomb

end

end OAI
