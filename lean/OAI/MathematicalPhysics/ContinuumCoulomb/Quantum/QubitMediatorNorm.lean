import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliAlgebra
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.SpinMatrixNorm

namespace OAI

/-! Spectator-independent norm estimates for the physical mediator terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι κ σ α : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype σ] [DecidableEq σ]
  [Fintype α] [DecidableEq α]

theorem qmaPauliWord_operator_norm (w : ι → Fin 4) :
    ‖spinMatrixOperator (qmaPauliWord w)‖ ≤ 1 :=
  spinMatrixOperator_unitary_norm _ (qmaPauliWord_gram w)

theorem qmaBitFlipMatrix_square (e : κ) : qmaBitFlipMatrix e*qmaBitFlipMatrix e = 1 := by
  ext s t
  simp [qmaBitFlipMatrix,Matrix.mul_apply,mul_ite,qmaBitFlip_involutive e t,Matrix.one_apply]

theorem qmaBitFlipMatrix_star (e : κ) : (qmaBitFlipMatrix e).conjTranspose = qmaBitFlipMatrix e := by
  ext s t
  have he : t = qmaBitFlip e s ↔ s = qmaBitFlip e t := by
    constructor <;> intro h <;> rw [h,qmaBitFlip_involutive]
  simp [Matrix.conjTranspose_apply,qmaBitFlipMatrix,he]

theorem qmaKronecker_unitary_norm (M : Matrix σ σ ℂ) (N : Matrix α α ℂ)
    (hM : M.conjTranspose*M = 1) (hN : N.conjTranspose*N = 1) :
    ‖spinMatrixOperator (M ⊗ₖ N)‖ ≤ 1 := by
  apply spinMatrixOperator_unitary_norm
  rw [Matrix.conjTranspose_kronecker,← Matrix.mul_kronecker_mul,hM,hN,Matrix.one_kronecker_one]

theorem qmaPauliFlip_operator_norm (w : ι → Fin 4) (e : κ) :
    ‖spinMatrixOperator (qmaPauliWord w ⊗ₖ qmaBitFlipMatrix e)‖ ≤ 1 := by
  apply qmaKronecker_unitary_norm _ _ (qmaPauliWord_gram w)
  rw [qmaBitFlipMatrix_star,qmaBitFlipMatrix_square]

omit [DecidableEq σ] in
theorem qmaOccupation_mulVec (M : Matrix σ σ ℂ) (e : κ)
    (u : (σ × (κ → Fin 2)) → ℂ) (s : σ) (a : κ → Fin 2) :
    (M ⊗ₖ qmaAncillaOccupation e).mulVec u (s,a) =
      if a e = 1 then M.mulVec (fun t => u (t,a)) s else 0 := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.kronecker_apply,
    qmaAncillaOccupation,Matrix.diagonal_apply]
  by_cases ha : a e = 1
  · simp [ha]
  · simp [ha]

theorem qmaKronecker_occupation_norm (M : Matrix σ σ ℂ) (hM : M.conjTranspose*M = 1)
    (e : κ) : ‖spinMatrixOperator (M ⊗ₖ qmaAncillaOccupation e)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  let y : EuclideanSpace ℂ σ := WithLp.toLp 2 (fun s => x (s,a))
  have heq : ∑ s, ‖(spinMatrixOperator M y) s‖^2 = ∑ s, ‖x (s,a)‖^2 := by
    have h := congrArg (fun r : ℝ => r^2) (spinMatrixOperator_unitary_norm_map M hM y)
    simpa only [EuclideanSpace.norm_sq_eq,y] using h
  by_cases ha : a e = 1
  · convert le_of_eq heq using 1
    apply Finset.sum_congr rfl
    intro s _
    change ‖(M ⊗ₖ qmaAncillaOccupation e).mulVec (fun t => x t) (s,a)‖^2 =
      ‖(spinMatrixOperator M y) s‖^2
    rw [qmaOccupation_mulVec,ite_eq_left ha]
    rfl
  · have hz : ∑ s, ‖spinMatrixOperator (M ⊗ₖ qmaAncillaOccupation e) x (s,a)‖^2 = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      change ‖(M ⊗ₖ qmaAncillaOccupation e).mulVec (fun t => x t) (s,a)‖^2 = 0
      rw [qmaOccupation_mulVec,ite_eq_right ha]
      norm_num
    rw [hz]
    positivity

theorem qmaPauliOccupation_operator_norm (w : ι → Fin 4) (e : κ) :
    ‖spinMatrixOperator (qmaPauliWord w ⊗ₖ qmaAncillaOccupation e)‖ ≤ 1 :=
  qmaKronecker_occupation_norm _ (qmaPauliWord_gram w) e

end ContinuumCoulomb

end

end OAI
