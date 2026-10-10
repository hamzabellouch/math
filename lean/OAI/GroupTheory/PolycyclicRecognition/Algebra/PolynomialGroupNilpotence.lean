import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialSubalgebraNilpotence

namespace OAI

/-! # Nilpotence of the polynomial group of a nilpotent Lie algebra -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] polynomialSubalgebraGroup
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

theorem polynomial_group_nilpotent : Group.IsNilpotent L := by
  let K : LieSubalgebra ℝ L := ⊤
  let : LieRing.IsNilpotent K := Function.Injective.lieAlgebra_isNilpotent
    (f := K.incl) Subtype.val_injective
  let : Group.IsNilpotent K := polynomialSubalgebra_group_nilpotent K
  apply Group.nilpotent_of_surjective (polynomialSubalgebraHom K K.incl)
  intro x
  exact ⟨⟨x, trivial⟩, rfl⟩

end PolycyclicRecognition

end

end OAI
