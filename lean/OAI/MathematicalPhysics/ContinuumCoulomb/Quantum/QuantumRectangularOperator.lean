import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorNorm

namespace OAI

/-! Rectangular Euclidean operators for the actual mediator columns. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace Classical

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

def qmaMatrixOperator (M : Matrix α β ℂ) : EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ α :=
  LinearMap.toContinuousLinearMap M.toEuclideanLin

@[simp] theorem qmaMatrixOperator_apply (M : Matrix α β ℂ) (x : EuclideanSpace ℂ β) (a : α) :
    qmaMatrixOperator M x a = ∑ b, M a b*x b := rfl

theorem qmaMatrixOperator_add (M N : Matrix α β ℂ) :
    qmaMatrixOperator (M+N) = qmaMatrixOperator M+qmaMatrixOperator N := by
  unfold qmaMatrixOperator
  rw [map_add,map_add]

theorem qmaMatrixOperator_smul (c : ℂ) (M : Matrix α β ℂ) :
    qmaMatrixOperator (c • M) = c • qmaMatrixOperator M := by
  unfold qmaMatrixOperator
  rw [map_smul,map_smul]

theorem qmaMatrixOperator_sum {δ : Type*} (s : Finset δ) (M : δ → Matrix α β ℂ) :
    qmaMatrixOperator (∑ a ∈ s, M a) = ∑ a ∈ s, qmaMatrixOperator (M a) := by
  unfold qmaMatrixOperator
  rw [map_sum,map_sum]

theorem qmaMatrixOperator_mul [DecidableEq γ] (M : Matrix α β ℂ) (N : Matrix β γ ℂ) :
    qmaMatrixOperator (M*N) = (qmaMatrixOperator M).comp (qmaMatrixOperator N) := by
  ext x a
  change Matrix.toLpLin 2 2 (M*N) x a = Matrix.toLpLin 2 2 M (Matrix.toLpLin 2 2 N x) a
  rw [Matrix.toLpLin_mul_same,LinearMap.comp_apply]

theorem qmaMatrixOperator_star (M : Matrix α β ℂ) :
    qmaMatrixOperator M.conjTranspose = (qmaMatrixOperator M).adjoint := by
  unfold qmaMatrixOperator
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint,LinearMap.adjoint_toContinuousLinearMap]

theorem qmaMatrixOperator_square [DecidableEq α] (M : Matrix α α ℂ) :
    qmaMatrixOperator M = spinMatrixOperator M := rfl

theorem qmaEuclidean_real_inner (x y : EuclideanSpace ℂ α) :
    ⟪x,y⟫_ℝ = (⟪x,y⟫_ℂ).re := by
  simp only [PiLp.inner_apply,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  rfl

variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]
variable [DecidableEq α]

theorem qmaSliceColumn_operator_norm_map (a : α) (M : Matrix σ σ ℂ)
    (x : EuclideanSpace ℂ σ) :
    ‖qmaMatrixOperator (qmaSliceColumn a M) x‖ = ‖spinMatrixOperator M x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type,qmaMatrixOperator_apply,qmaSliceColumn]
  have hentry (s : σ) (b : α) :
      (∑ t, (if b = a then M s t else 0)*x t) =
        if b = a then spinMatrixOperator M x s else 0 := by
    by_cases hb : b = a <;> simp [hb,spinMatrixOperator_apply]
  simp only [hentry]
  simp [apply_ite]

theorem qmaSliceColumn_operator_norm (a : α) (M : Matrix σ σ ℂ) :
    ‖qmaMatrixOperator (qmaSliceColumn a M)‖ ≤ ‖spinMatrixOperator M‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [qmaSliceColumn_operator_norm_map]
  exact (spinMatrixOperator M).le_opNorm x

omit [DecidableEq κ] in
theorem qmaSliceFamily_operator_norm (a : κ → α) (V : κ → Matrix σ σ ℂ) :
    ‖qmaMatrixOperator (∑ e, qmaSliceColumn (a e) (V e))‖ ≤
      ∑ e, ‖spinMatrixOperator (V e)‖ := by
  rw [qmaMatrixOperator_sum]
  calc
    _ ≤ ∑ e, ‖qmaMatrixOperator (qmaSliceColumn (a e) (V e))‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro e _
      exact qmaSliceColumn_operator_norm (a e) (V e)

theorem qmaAncillaColumn_operator_norm (V : κ → Matrix σ σ ℂ) :
    ‖qmaMatrixOperator (qmaAncillaColumn V)‖ ≤ ∑ e, ‖spinMatrixOperator (V e)‖ :=
  qmaSliceFamily_operator_norm qmaAncillaSingle V

end ContinuumCoulomb

end

end OAI
