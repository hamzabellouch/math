import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorError

namespace OAI

/-! The actual effective form approximates the calibrated tensor matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {n : ℕ}

def qmaFourTensorPerturbation (r : ℝ)
    (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) :
    EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16) :=
  r • (qmaMatrixOperator V).restrictScalars ℝ+(qmaMatrixOperator C).restrictScalars ℝ

def qmaFourTensorEffectiveMatrix (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ) :=
  (qmaFourTensorEncoding n).conjTranspose*C*qmaFourTensorEncoding n-
    (1/8:ℂ) • ((V*qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n))

theorem qmaFourTensor_restrict_column (V : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    (hV : (qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n) = 0)
    (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    qmaFourTensorRestriction n (qmaMatrixOperator V (qmaFourTensorInclusion n p)) = 0 := by
  change qmaMatrixOperator _ (qmaMatrixOperator _ (qmaMatrixOperator _ p)) = 0
  rw [← ContinuousLinearMap.comp_apply,← qmaMatrixOperator_mul,
    ← ContinuousLinearMap.comp_apply,← qmaMatrixOperator_mul,Matrix.mul_assoc,hV]
  ext s
  simp only [qmaMatrixOperator_apply,Matrix.zero_apply,zero_mul,Finset.sum_const_zero,PiLp.zero_apply]

theorem qmaFourTensorOff_split (r : ℝ) (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    (hV : (qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n) = 0)
    (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    qmaFourTensorOff (qmaFourTensorPerturbation r V C) p =
      r • qmaMatrixOperator V (qmaFourTensorInclusion n p)+
        qmaFourTensorHigh n (qmaMatrixOperator C (qmaFourTensorInclusion n p)) := by
  change qmaFourTensorHigh n (r • qmaMatrixOperator V (qmaFourTensorInclusion n p)+
    qmaMatrixOperator C (qmaFourTensorInclusion n p)) = _
  rw [map_add,map_smul,qmaFourTensorHigh_fixed _ (qmaFourTensor_restrict_column V hV p)]

theorem qmaQuadratic_operator_gram {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq τ]
    (W : Matrix σ τ ℂ) (p : EuclideanSpace ℂ τ) :
    qmaQuadratic (W.conjTranspose*W) (fun i => p i) = ‖qmaMatrixOperator W p‖^2 := by
  rw [qmaQuadratic_operator,qmaMatrixOperator_mul,ContinuousLinearMap.comp_apply,
    ← qmaMatrixOperator_real_adjoint,real_inner_self_eq_norm_sq]

theorem qmaFourTensorEffectiveMatrix_form
    (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    qmaQuadratic (qmaFourTensorEffectiveMatrix V C) (fun i => p i) =
      ⟪qmaFourTensorInclusion n p,qmaMatrixOperator C (qmaFourTensorInclusion n p)⟫_ℝ-
        (1/8)*‖qmaMatrixOperator V (qmaFourTensorInclusion n p)‖^2 := by
  rw [qmaFourTensorEffectiveMatrix,qmaQuadratic_sub,
    show (1/8:ℂ) = ((1/8:ℝ):ℂ) from by norm_num,qmaQuadratic_smul,
    qmaQuadratic_sandwich,qmaQuadratic_operator_gram,qmaMatrixOperator_mul,ContinuousLinearMap.comp_apply]
  rfl

theorem qmaFourTensorLow_form (r : ℝ) (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    (hV : (qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n) = 0)
    (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    ⟪p,qmaFourTensorLow (qmaFourTensorPerturbation r V C) p⟫_ℝ =
      ⟪qmaFourTensorInclusion n p,qmaMatrixOperator C (qmaFourTensorInclusion n p)⟫_ℝ := by
  change ⟪p,qmaFourTensorRestriction n (qmaFourTensorPerturbation r V C (qmaFourTensorInclusion n p))⟫_ℝ = _
  rw [← qmaFourTensor_inclusion_adjoint]
  change ⟪qmaFourTensorInclusion n p,r • qmaMatrixOperator V (qmaFourTensorInclusion n p)+
    qmaMatrixOperator C (qmaFourTensorInclusion n p)⟫_ℝ = _
  rw [inner_add_right,inner_smul_right,qmaFourTensor_inclusion_adjoint,
    qmaFourTensor_restrict_column V hV p,inner_zero_right,mul_zero,zero_add]

theorem qmaFourTensor_column_norm (M : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    {b : ℝ} (hb : ‖spinMatrixOperator M‖ ≤ b) (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    ‖qmaMatrixOperator M (qmaFourTensorInclusion n p)‖ ≤ b*‖p‖ := by
  apply ((qmaMatrixOperator M).le_opNorm _).trans
  rw [qmaMatrixOperator_square,qmaFourTensor_inclusion_norm]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg p)

theorem qmaFourTensorEffective_error (r : ℝ) (hr : 0 < r)
    (V C : Matrix (Fin n → Fin 16) (Fin n → Fin 16) ℂ)
    (hV : (qmaFourTensorEncoding n).conjTranspose*(V*qmaFourTensorEncoding n) = 0)
    (hH : qmaFourTensorPenalty n*(V*qmaFourTensorEncoding n) = (8:ℂ) • (V*qmaFourTensorEncoding n))
    (T : EuclideanSpace ℂ (Fin n → Fin 16) →L[ℝ] EuclideanSpace ℂ (Fin n → Fin 16))
    (hAT : ∀ x, qmaFourTensorPadded n r (T x) = x) (hTA : ∀ x, T (qmaFourTensorPadded n r x) = x)
    (hTn : ‖T‖ ≤ 1/(4*r^2)) {v c : ℝ} (hv : 0 ≤ v) (hc : 0 ≤ c)
    (hVn : ‖spinMatrixOperator V‖ ≤ v) (hCn : ‖spinMatrixOperator C‖ ≤ c)
    (p : EuclideanSpace ℂ (Fin n → Fin 2)) :
    |Perturbation.effectiveForm (qmaFourTensorLow (qmaFourTensorPerturbation r V C)) T
        (qmaFourTensorOff (qmaFourTensorPerturbation r V C)) p-
      qmaQuadratic (qmaFourTensorEffectiveMatrix V C) (fun i => p i)| ≤
      (v*c/(4*r)+c^2/(4*r^2))*‖p‖^2 := by
  let w := qmaMatrixOperator V (qmaFourTensorInclusion n p)
  let z := qmaFourTensorHigh n (qmaMatrixOperator C (qmaFourTensorInclusion n p))
  have hw : T w = (8*r^2)⁻¹ • w := by
    have h := qmaFourTensorInverse_column hr T hTA (V*qmaFourTensorEncoding n) hV hH p
    simpa only [qmaMatrixOperator_mul,ContinuousLinearMap.comp_apply,w,qmaFourTensorInclusion,
      ContinuousLinearMap.coe_restrictScalars'] using h
  have hwn : ‖w‖ ≤ v*‖p‖ := qmaFourTensor_column_norm V hVn p
  have hzn : ‖z‖ ≤ c*‖p‖ := by
    apply ((qmaFourTensorHigh n).le_opNorm _).trans
    exact (mul_le_mul (qmaFourTensorHigh_norm n) (qmaFourTensor_column_norm C hCn p)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have h := qmaSecondOrder_column_error T hr hv hc (norm_nonneg p)
    (qmaInverse_symmetric _ T hAT (qmaFourTensorPadded_symmetric n r)) hTn w z hw hwn hzn
  rw [Perturbation.effectiveForm,Perturbation.inverseForm,qmaFourTensorLow_form r V C hV p,
    qmaFourTensorEffectiveMatrix_form,qmaFourTensorOff_split r V C hV p]
  convert h using 1
  rw [show (⟪qmaFourTensorInclusion n p,qmaMatrixOperator C (qmaFourTensorInclusion n p)⟫_ℝ-
      ⟪r • w+z,T (r • w+z)⟫_ℝ)-
      (⟪qmaFourTensorInclusion n p,qmaMatrixOperator C (qmaFourTensorInclusion n p)⟫_ℝ-(1/8)*‖w‖^2) =
        -(⟪r • w+z,T (r • w+z)⟫_ℝ-(1/8)*‖w‖^2) by ring,abs_neg]

end ContinuumCoulomb

end

end OAI
