import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentCodimensionOneCriterion
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentSemidirectTangent

namespace OAI

/-! # Nilpotence of the constructed derivation semidirect Lie group -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

theorem derivationSemidirect_tangent_nilpotent :
    letI := derivationSemidirectGroup D hD
    letI := derivationSemidirectLieGroup D hD
    LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)) := by
  let := derivationSemidirectGroup D hD
  let := derivationSemidirectLieGroup D hD
  let T := GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)
  let e : T ≃ₗ[ℝ] L × ℝ := LinearEquiv.refl ℝ (L × ℝ)
  apply nilpotent_derivation_extension e D.toLinearMap hD
  intro x y
  exact semidirect_tangent_bracket D hD (derivationSemidirect_one D hD)
    (derivationSemidirect_mul D hD) x.1 y.1 x.2 y.2

end PolycyclicRecognition

end

end OAI
