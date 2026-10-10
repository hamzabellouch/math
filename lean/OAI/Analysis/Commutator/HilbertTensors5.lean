import Mathlib
import OAI.Analysis.Commutator.HilbertTensors4

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem constant_operator_right_coefficient_zero [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℂ] F) (v : ℕ → E) (hv : Orthonormal ℂ v)
    (x : F) (c : ℂ) (hc : ∀ n, inner ℂ x (T (v n)) = c) : c = 0 := by
  apply constant_right_orthonormal_coefficient_zero v hv (T.adjoint x) c
  intro n
  rw [ContinuousLinearMap.adjoint_inner_left, hc]

end Kadison
end

end OAI
