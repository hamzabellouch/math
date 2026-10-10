import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnconditionalNilpotentCoordinates

namespace OAI

/-! # Simply connected nilpotent model existence without published inputs -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

def polynomialCoordinateLieModel (L : Type*) [RealNormedLieAlgebra L]
    [FiniteDimensional ℝ L] [P : PolynomialExponentialCoordinates L] : NilpotentLieModel L := by
  let : MeasurableSpace L := borel L
  let : BorelSpace L := ⟨rfl⟩
  exact { modelSpace := L, carrier := L, equiv := P.tangentEquiv }

theorem nilpotentLieModel_exists (L : Type) [RealNormedLieAlgebra L]
    [FiniteDimensional ℝ L] (hnil : LieRing.IsNilpotent L) : Nonempty (NilpotentLieModel L) := by
  obtain ⟨P⟩ := polynomialExponentialCoordinates_nilpotent L hnil
  let := P
  exact ⟨polynomialCoordinateLieModel L⟩

theorem nilpotentLieExistenceInput (L : Type) [LieRing L] [LieAlgebra ℝ L]
    [FiniteDimensional ℝ L] : NilpotentLieExistenceInput L := by
  let b := Module.finBasis ℝ L
  let : NormedAddCommGroup L := NormedAddCommGroup.induced L _ b.equivFun b.equivFun.injective
  let : NormedSpace ℝ L := NormedSpace.induced ℝ L _ b.equivFun
  let : RealNormedLieAlgebra L :=
    { (inferInstance : NormedAddCommGroup L), (inferInstance : LieRing L),
      (inferInstance : NormedSpace ℝ L), (inferInstance : LieAlgebra ℝ L) with }
  exact nilpotentLieModel_exists L

end PolycyclicRecognition

end

end OAI
