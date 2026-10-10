import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexifiedLieAutomorphism
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealNormedLieAlgebra

namespace OAI

/-! # Exponentials commute with the concrete complexification of operators -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable (L : Type) [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
local instance : ComplexNormedLieAlgebra (ℂ ⊗[ℝ] L) := complexificationNormedLie L

def continuousComplexifiedEnd :
    (L →L[ℝ] L) →ₐ[ℝ] ((ℂ ⊗[ℝ] L) →L[ℂ] (ℂ ⊗[ℝ] L)) :=
  ((Module.End.toContinuousLinearMap (𝕜 := ℂ) (ℂ ⊗[ℝ] L)).restrictScalars ℝ).toAlgHom.comp
    ((Module.End.baseChangeHom ℝ ℂ L).comp
      (Module.End.toContinuousLinearMap (𝕜 := ℝ) L).symm.toAlgHom)

theorem complexifiedEnd_exp (D : Module.End ℝ L) :
    ((NormedSpace.exp (LinearMap.toContinuousLinearMap D)).toLinearMap).baseChange ℂ =
      (NormedSpace.exp (LinearMap.toContinuousLinearMap (D.baseChange ℂ))).toLinearMap := by
  let := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  let := NormedAlgebra.restrictScalars ℚ ℂ ((ℂ ⊗[ℝ] L) →L[ℂ] (ℂ ⊗[ℝ] L))
  have h := NormedSpace.map_exp (continuousComplexifiedEnd L)
    (continuousComplexifiedEnd L).toLinearMap.continuous_of_finiteDimensional
    (LinearMap.toContinuousLinearMap D)
  exact congrArg
    (fun T : (ℂ ⊗[ℝ] L) →L[ℂ] (ℂ ⊗[ℝ] L) => T.toLinearMap) h

omit [FiniteDimensional ℝ L] in
theorem realEnd_baseChange_injective : Function.Injective (Module.End.baseChangeHom ℝ ℂ L) := by
  intro A B h
  apply LinearMap.ext
  intro x
  apply complexificationLieHom_injective L
  exact congrArg (fun T : Module.End ℂ (ℂ ⊗[ℝ] L) => T ((1 : ℂ) ⊗ₜ[ℝ] x)) h

end PolycyclicRecognition

end

end OAI
