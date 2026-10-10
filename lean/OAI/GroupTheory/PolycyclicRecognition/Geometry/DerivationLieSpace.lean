import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentSemidirectNilpotence
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentLieModel
import Mathlib.Analysis.Convex.Contractible

namespace OAI

/-! # The actual tangent algebra of the derivation extension

The type synonym keeps exponential group coordinates distinct from the raw
semidirect group on the product vector space.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

def DerivationLieSpace (D : LieDerivation ℝ L L) (_hD : IsNilpotent D.toLinearMap) : Type _ :=
  L × ℝ

instance derivationLieSpaceRealNormed
    (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap) :
    RealNormedLieAlgebra (DerivationLieSpace D hD) := by
  let := derivationSemidirectGroup D hD
  let := derivationSemidirectLieGroup D hD
  let T := GroupLieAlgebra (𝓘(ℝ, L × ℝ)) (L × ℝ)
  let lr : LieRing (L × ℝ) := inferInstanceAs (LieRing T)
  let la : @LieAlgebra ℝ (L × ℝ) _ lr := inferInstanceAs (LieAlgebra ℝ T)
  change RealNormedLieAlgebra (L × ℝ)
  exact { (inferInstance : NormedAddCommGroup (L × ℝ)), lr,
    (inferInstance : NormedSpace ℝ (L × ℝ)), la with }

instance derivationLieSpaceFiniteDimensional
    (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap) :
    FiniteDimensional ℝ (DerivationLieSpace D hD) :=
  inferInstanceAs (FiniteDimensional ℝ (L × ℝ))

def derivationLieSpaceSplit (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap) :
    DerivationLieSpace D hD ≃ₗ[ℝ] L × ℝ := LinearEquiv.refl ℝ (L × ℝ)

theorem derivationLieSpace_nilpotent [LieRing.IsNilpotent L]
    (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap) :
    LieRing.IsNilpotent (DerivationLieSpace D hD) :=
  derivationSemidirect_tangent_nilpotent D hD

def derivationNilpotentLieModel
    (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap) :
    NilpotentLieModel (DerivationLieSpace D hD) := by
  let := derivationSemidirectGroup D hD
  let := derivationSemidirectLieGroup D hD
  let : MeasurableSpace (L × ℝ) := borel (L × ℝ)
  let : BorelSpace (L × ℝ) := ⟨rfl⟩
  let V := L × ℝ
  exact {
    modelSpace := V
    carrier := V
    equiv := LieEquiv.refl }

end PolycyclicRecognition

end

end OAI
