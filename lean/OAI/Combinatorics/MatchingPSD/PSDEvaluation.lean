import Mathlib

namespace OAI

namespace AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

noncomputable def evaluation (B : I → Matrix R R ℝ) : Matrix R R ℝ →ₗ[ℝ] (I → ℝ) where
  toFun A := fun i => (A * B i).trace
  map_add' A C := by ext i; simp [add_mul, Matrix.trace_add]
  map_smul' t A := by ext i; simp [Matrix.trace_smul]

omit [Fintype I] in
@[simp] lemma evaluation_apply (B : I → Matrix R R ℝ) (A : Matrix R R ℝ) (i : I) :
    evaluation B A i = (A * B i).trace := rfl

noncomputable def evaluationCone (B : I → Matrix R R ℝ) : Set (I → ℝ) :=
  evaluation B '' {A | A.PosSemidef}

end AffinePSD

end OAI
