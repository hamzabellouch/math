import OAI.GroupTheory.PolycyclicRecognition.Geometry.AbelianLieModel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.AbelianDynkinInput
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialExponentialCoordinates

namespace OAI

/-! # Explicit additive polynomial coordinates for an abelian Lie algebra -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold
variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L] [IsLieAbelian L]

@[instance_reducible]
def abelianPolynomialCoordinates : PolynomialExponentialCoordinates L := by
  let N := abelianLieModel (V := L)
  refine
    { group := inferInstanceAs (Group (Multiplicative L))
      lieGroup := N.lieGroup
      one_eq_zero := rfl
      inv_eq_neg := fun _ => rfl
      degree := 1
      coefficients := abelianDynkinCoefficients 1 2
      mul_eq := ?_
      tangentEquiv := N.equiv
      tangentEquiv_apply := fun _ => rfl }
  intro x y
  change x + y = finiteDynkinPolynomial (abelianDynkinCoefficients 1 2) ![x, y]
  rw [finiteDynkinPolynomial_abelian (by decide)]
  simp

end PolycyclicRecognition

end

end OAI
