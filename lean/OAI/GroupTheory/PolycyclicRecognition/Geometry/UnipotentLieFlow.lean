import OAI.GroupTheory.PolycyclicRecognition.Geometry.UnipotentLieLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentDerivationFlow

namespace OAI

/-! # A real Lie-automorphism flow through a given unipotent automorphism -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
local instance unipotentFlowRationalModule : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)

theorem unipotentLieLogarithm_toLinearMap (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : IsNilpotent (A.toLinearMap - 1)) :
    (unipotentLieLogarithm A hA).toLinearMap = nilpotentLog (A.toLinearMap - 1) := rfl

theorem unipotentLieLogarithm_nilpotent (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : IsNilpotent (A.toLinearMap - 1)) :
    IsNilpotent (unipotentLieLogarithm A hA).toLinearMap := by
  rw [unipotentLieLogarithm_toLinearMap]
  exact nilpotentLog_nilpotent _ hA

theorem exp_unipotentLieLogarithm (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : IsNilpotent (A.toLinearMap - 1)) :
    IsNilpotent.exp (unipotentLieLogarithm A hA).toLinearMap = A.toLinearMap := by
  rw [unipotentLieLogarithm_toLinearMap, exp_nilpotentLog _ hA]
  abel

def unipotentLieFlow (A : L ≃ₗ⁅ℝ⁆ L) (hA : IsNilpotent (A.toLinearMap - 1))
    (t : ℝ) : L ≃ₗ⁅ℝ⁆ L :=
  nilpotentDerivationFlow (unipotentLieLogarithm A hA)
    (unipotentLieLogarithm_nilpotent A hA) t

theorem unipotentLieFlow_zero (A : L ≃ₗ⁅ℝ⁆ L) (hA : IsNilpotent (A.toLinearMap - 1))
    (x : L) : unipotentLieFlow A hA 0 x = x :=
  nilpotentDerivationFlow_zero _ _ x

theorem unipotentLieFlow_add (A : L ≃ₗ⁅ℝ⁆ L) (hA : IsNilpotent (A.toLinearMap - 1))
    (s t : ℝ) (x : L) :
    unipotentLieFlow A hA (s + t) x = unipotentLieFlow A hA s (unipotentLieFlow A hA t x) :=
  nilpotentDerivationFlow_add _ _ s t x

theorem unipotentLieFlow_one (A : L ≃ₗ⁅ℝ⁆ L) (hA : IsNilpotent (A.toLinearMap - 1)) :
    unipotentLieFlow A hA 1 = A := by
  ext x
  change IsNilpotent.exp (1 • (unipotentLieLogarithm A hA).toLinearMap) x = A x
  rw [one_smul, exp_unipotentLieLogarithm]
  rfl

end PolycyclicRecognition

end

end OAI
