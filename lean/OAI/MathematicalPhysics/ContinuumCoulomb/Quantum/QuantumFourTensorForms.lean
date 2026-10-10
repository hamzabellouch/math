import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorInverse

namespace OAI

/-! The full physical quadratic form in its actual encoded and orthogonal coordinates. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {n : ℕ}

theorem qmaFourTensor_inclusion_norm (n : ℕ) (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    ‖qmaFourTensorInclusion n p‖ = ‖p‖ :=
  Perturbation.orthogonalInclusion_norm _ _ (qmaFourTensor_restrict_include n)
    (qmaFourTensor_inclusion_adjoint n) p

theorem qmaFourTensor_norm_decomposition (n : ℕ) (x : EuclideanSpace ℂ (Fin n → Fin 16)) :
    ‖qmaFourTensorRestriction n x‖^2+‖qmaFourTensorHigh n x‖^2 = ‖x‖^2 := by
  rw [← qmaFourTensor_highPart]
  exact Perturbation.orthogonalParts_norm _ _ (qmaFourTensor_restrict_include n)
    (qmaFourTensor_inclusion_adjoint n) x

theorem qmaFourTensorHigh_norm (n : ℕ) : ‖qmaFourTensorHigh n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have h := qmaFourTensor_norm_decomposition n x
  have h0 := norm_nonneg (qmaFourTensorHigh n x)
  have h1 := norm_nonneg x
  rw [one_mul]
  nlinarith [sq_nonneg ‖qmaFourTensorRestriction n x‖]

theorem qmaFourTensorHigh_fixed (x : EuclideanSpace ℂ (Fin n → Fin 16))
    (hx : qmaFourTensorRestriction n x = 0) : qmaFourTensorHigh n x = x := by
  rw [← qmaFourTensor_highPart]
  simp only [Perturbation.orthogonalHighPart,hx,map_zero,sub_zero]

theorem qmaFourTensorHigh_symmetric (x y : EuclideanSpace ℂ (Fin n → Fin 16)) :
    ⟪x,qmaFourTensorHigh n y⟫_ℝ = ⟪qmaFourTensorHigh n x,y⟫_ℝ := by
  apply qmaMatrixOperator_real_symmetric
  simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,qmaFourTensor_projection_star]

theorem qmaFourTensor_penalty_low (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    qmaMatrixOperator (qmaFourTensorPenalty n) (qmaFourTensorInclusion n p) = 0 := by
  change qmaMatrixOperator _ (qmaMatrixOperator _ p) = 0
  rw [← ContinuousLinearMap.comp_apply,← qmaMatrixOperator_mul,qmaFourTensorPenalty_encoding]
  ext s
  simp only [qmaMatrixOperator_apply,Matrix.zero_apply,zero_mul,Finset.sum_const_zero,PiLp.zero_apply]

theorem qmaFourTensor_padded_high (r : ℝ) (x : EuclideanSpace ℂ (Fin n → Fin 16))
    (hx : qmaFourTensorRestriction n x = 0) :
    qmaFourTensorPadded n r x = r^2 • qmaMatrixOperator (qmaFourTensorPenalty n) x := by
  have hp : qmaMatrixOperator (qmaFourTensorProjection n) x = 0 := by
    rw [← qmaFourTensorEncoding_projector,qmaMatrixOperator_mul,ContinuousLinearMap.comp_apply]
    change qmaFourTensorInclusion n (qmaFourTensorRestriction n x) = 0
    rw [hx,map_zero]
  change r^2 • qmaMatrixOperator (_+_) x = _
  rw [qmaMatrixOperator_add,_root_.add_apply,qmaMatrixOperator_smul,
    _root_.smul_apply,hp,smul_zero,add_zero]

def qmaFourTensorPhysical (r : ℝ)
    (K : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16)) :=
  r^2 • (qmaMatrixOperator (qmaFourTensorPenalty n)).restrictScalars ℝ+K

def qmaFourTensorLow
    (K : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16)) :=
  (qmaFourTensorRestriction n).comp (K.comp (qmaFourTensorInclusion n))

def qmaFourTensorOff
    (K : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16)) :=
  (qmaFourTensorHigh n).comp (K.comp (qmaFourTensorInclusion n))

def qmaFourTensorHighPerturbation
    (K : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16)) :=
  (qmaFourTensorHigh n).comp (K.comp (qmaFourTensorHigh n))

theorem qmaFourTensorPhysical_symmetric (r : ℝ)
    (K : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (hK : ∀ x y, ⟪x,K y⟫_ℝ = ⟪K x,y⟫_ℝ) (x y : EuclideanSpace ℂ (Fin n → Fin 16)) :
    ⟪x,qmaFourTensorPhysical r K y⟫_ℝ = ⟪qmaFourTensorPhysical r K x,y⟫_ℝ := by
  change ⟪x,r^2 • qmaMatrixOperator (qmaFourTensorPenalty n) y+K y⟫_ℝ =
    ⟪r^2 • qmaMatrixOperator (qmaFourTensorPenalty n) x+K x,y⟫_ℝ
  simp only [inner_add_right,inner_add_left,inner_smul_right,inner_smul_left,
    starRingEnd_apply,star_trivial,hK,
    qmaMatrixOperator_real_symmetric _ (qmaFourTensor_penalty_star n)]

theorem qmaFourTensorPhysical_low (r : ℝ)
    (K : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    qmaFourTensorPhysical r K (qmaFourTensorInclusion n p) =
      qmaFourTensorInclusion n (qmaFourTensorLow K p)+qmaFourTensorOff K p := by
  change r^2 • qmaMatrixOperator (qmaFourTensorPenalty n) (qmaFourTensorInclusion n p)+
    K (qmaFourTensorInclusion n p) = _
  rw [qmaFourTensor_penalty_low,smul_zero,zero_add]
  symm
  have h := Perturbation.orthogonal_assemble (qmaFourTensorInclusion n)
    (qmaFourTensorRestriction n) (K (qmaFourTensorInclusion n p))
  rw [qmaFourTensor_highPart] at h
  exact h

theorem qmaFourTensorPhysical_high (r : ℝ)
    (K : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (x : EuclideanSpace ℂ (Fin n → Fin 16)) (hx : qmaFourTensorRestriction n x = 0) :
    ⟪x,qmaFourTensorPhysical r K x⟫_ℝ =
      Perturbation.penaltyForm (qmaFourTensorPadded n r) x+⟪x,qmaFourTensorHighPerturbation K x⟫_ℝ := by
  change ⟪x,r^2 • qmaMatrixOperator (qmaFourTensorPenalty n) x+K x⟫_ℝ = _
  rw [inner_add_right,← qmaFourTensor_padded_high r x hx]
  congr 1
  change ⟪x,K x⟫_ℝ = ⟪x,qmaFourTensorHigh n (K (qmaFourTensorHigh n x))⟫_ℝ
  rw [qmaFourTensorHigh_fixed x hx,qmaFourTensorHigh_symmetric,qmaFourTensorHigh_fixed x hx]

theorem qmaFourTensorPhysical_energy (r : ℝ)
    (K : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (hK : ∀ x y, ⟪x,K y⟫_ℝ = ⟪K x,y⟫_ℝ) (x : EuclideanSpace ℂ (Fin n → Fin 16)) :
    ⟪x,qmaFourTensorPhysical r K x⟫_ℝ =
      Perturbation.lowBlockEnergy (qmaFourTensorLow K) (qmaFourTensorPadded n r)
        (qmaFourTensorHighPerturbation K) (qmaFourTensorOff K)
        (qmaFourTensorRestriction n x) (qmaFourTensorHigh n x) := by
  rw [← qmaFourTensor_highPart]
  apply Perturbation.orthogonalBlock_full_energy
    (qmaFourTensorInclusion n) (qmaFourTensorRestriction n)
  · exact qmaFourTensor_restrict_include n
  · exact qmaFourTensor_inclusion_adjoint n
  · exact qmaFourTensorPhysical_symmetric r K hK
  · exact qmaFourTensorPhysical_low r K
  · intro p
    exact qmaFourTensorRestriction_high n _
  · exact qmaFourTensorPhysical_high r K

end ContinuumCoulomb

end

end OAI
