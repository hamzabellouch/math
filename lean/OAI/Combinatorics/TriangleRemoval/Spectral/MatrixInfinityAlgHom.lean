import Mathlib
import OAI.Combinatorics.TriangleRemoval.Stability.Volterra

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave
noncomputable def matrixInfinityAlgHom {I : Type*} [Fintype I] [DecidableEq I] :
    Matrix I I ℝ →ₐ[ℝ] ((I → ℝ) →L[ℝ] (I → ℝ)) :=
  (Matrix.toLinAlgEquiv'.trans (Module.End.toContinuousLinearMap (I → ℝ))).toAlgHom

@[simp] theorem matrixInfinityAlgHom_apply {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (z : I → ℝ) (i : I) :
    matrixInfinityAlgHom A z i = ∑ j, A i j * z j := rfl

open scoped Matrix.Norms.Operator in

@[simp] theorem matrixInfinityAlgHom_norm {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) : ‖matrixInfinityAlgHom A‖ = ‖A‖ :=
  (Matrix.linfty_opNorm_eq_opNorm A).symm

open scoped Matrix.Norms.Operator in

theorem matrixInfinityAlgHom_exp_norm {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (s : ℝ) :
    ‖NormedSpace.exp ((-s) • matrixInfinityAlgHom A)‖ =
      ‖NormedSpace.exp ((-s) • A)‖ := by
  have hc : Continuous (matrixInfinityAlgHom (I := I)) :=
    (matrixInfinityAlgHom (I := I)).toLinearMap.continuous_of_finiteDimensional
  rw [← map_smul,← continuous_algHom_map_exp (matrixInfinityAlgHom (I := I)) hc,
    matrixInfinityAlgHom_norm]
  rfl
end SharpTerminalLeave

end

end OAI
