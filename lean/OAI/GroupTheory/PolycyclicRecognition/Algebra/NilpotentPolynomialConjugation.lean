import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelDifference
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialDerivationAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentAutomorphismDifference

namespace OAI

/-! # Unipotence of smooth kernel conjugation in a nilpotent extension -/

noncomputable section
namespace PolycyclicRecognition
variable {L H : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group H] [Group.IsNilpotent H]

theorem nilpotent_polynomial_conjugation_unipotent (j : L →* H)
    (hj : Function.Injective j) (A : L ≃ₗ⁅ℝ⁆ L) (t : H)
    (hA : ∀ x, j (A x) = t * j x * t⁻¹) : IsNilpotent (A.toLinearMap - 1) := by
  apply nilpotent_linear_of_group_difference A.toLinearMap (Group.nilpotencyClass H)
  intro x
  have hh := automorphism_difference_iterate_one j hj
    (PolynomialExponentialCoordinates.groupAutomorphism A) t hA x
  change (fun y : L => A y * (-y))^[Group.nilpotencyClass H] x = 0
  simpa only [PolynomialExponentialCoordinates.groupAutomorphism_apply,
    P.inv_eq_neg, P.one_eq_zero] using hh

end PolycyclicRecognition

end

end OAI
