import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRectangularOperator

namespace OAI

/-! Matrix quadratic forms agree with the real forms of their actual
complex Euclidean operators, including rectangular compressions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped InnerProductSpace
variable {α β : Type*} [Fintype α] [Fintype β]

theorem qmaMatrixOperator_real_adjoint (B : Matrix α β ℂ)
    (p : EuclideanSpace ℂ β) (y : EuclideanSpace ℂ α) :
    ⟪qmaMatrixOperator B p,y⟫_ℝ = ⟪p,qmaMatrixOperator B.conjTranspose y⟫_ℝ := by
  rw [qmaEuclidean_real_inner,qmaEuclidean_real_inner]
  have h := ContinuousLinearMap.adjoint_inner_right (qmaMatrixOperator B) p y
  rw [← qmaMatrixOperator_star] at h
  exact congrArg Complex.re h.symm

theorem qmaQuadratic_operator (M : Matrix α α ℂ) (p : EuclideanSpace ℂ α) :
    qmaQuadratic M (fun i => p i) = ⟪p,qmaMatrixOperator M p⟫_ℝ := by
  rw [qmaEuclidean_real_inner]
  simp only [qmaQuadratic,PiLp.inner_apply,RCLike.inner_apply',qmaMatrixOperator_apply,
    Matrix.mulVec,dotProduct,Pi.star_apply,starRingEnd_apply]

theorem qmaQuadratic_sandwich [DecidableEq α] [DecidableEq β] (B : Matrix α β ℂ) (M : Matrix α α ℂ)
    (p : EuclideanSpace ℂ β) :
    qmaQuadratic (B.conjTranspose*M*B) (fun i => p i) =
      ⟪qmaMatrixOperator B p,qmaMatrixOperator M (qmaMatrixOperator B p)⟫_ℝ := by
  rw [qmaQuadratic_operator,qmaMatrixOperator_mul,qmaMatrixOperator_mul]
  simp only [ContinuousLinearMap.comp_apply]
  exact (qmaMatrixOperator_real_adjoint B p _).symm

theorem qmaQuadratic_sub (M N : Matrix α α ℂ) (p : α → ℂ) :
    qmaQuadratic (M-N) p = qmaQuadratic M p-qmaQuadratic N p := by
  have hn : qmaQuadratic (-N) p = -qmaQuadratic N p := by
    have h := qmaQuadratic_smul N (-1) p
    simpa using h
  simp only [sub_eq_add_neg,qmaQuadratic_add,hn]

theorem qmaQuadratic_real_smul (M : Matrix α α ℂ) (a : ℝ) (p : α → ℂ) :
    qmaQuadratic (a • M) p = a*qmaQuadratic M p := by
  have he : a • M = (a:ℂ) • M := rfl
  rw [he,qmaQuadratic_smul]

end ContinuumCoulomb

end

end OAI
