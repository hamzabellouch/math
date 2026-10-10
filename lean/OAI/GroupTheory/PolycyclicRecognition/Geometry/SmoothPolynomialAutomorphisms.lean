import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialDerivationAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelHom

namespace OAI

/-! # The subgroup of smooth automorphisms of a polynomial Lie group -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

def smoothPolynomialAutomorphisms : Subgroup (MulAut L) where
  carrier := {A | ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ A ∧
    ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ A.symm}
  one_mem' := ⟨contMDiff_id, contMDiff_id⟩
  mul_mem' := by
    intro A B hA hB
    exact ⟨hA.1.comp hB.1, hB.2.comp hA.2⟩
  inv_mem' := by
    intro A hA
    exact ⟨hA.2, hA.1⟩

theorem groupAutomorphism_mem_smooth (A : L ≃ₗ⁅ℝ⁆ L) :
    PolynomialExponentialCoordinates.groupAutomorphism (P := P) A ∈
      smoothPolynomialAutomorphisms :=
  ⟨A.toLinearEquiv.toContinuousLinearEquiv.contDiff.contMDiff,
    A.symm.toLinearEquiv.toContinuousLinearEquiv.contDiff.contMDiff⟩

end PolycyclicRecognition

end

end OAI
