import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnconditionalNilpotentModel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelDynkin
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarConstruction

namespace OAI

/-! # Constructed nilpotent models with their BCH and Haar data

Polynomial exponential coordinates give nilpotent Lie models together
with their finite BCH expansion and exponential Haar measure.
-/

noncomputable section
namespace PolycyclicRecognition

variable (L : Type) [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem polynomialCoordinateLieModel_dynkin :
    NilpotentDynkinExpansionInput (polynomialCoordinateLieModel L).modelSpace
      (polynomialCoordinateLieModel L).carrier := by
  change NilpotentDynkinExpansionInput L L
  exact nilpotentDynkinExpansionInput_polynomial

theorem polynomialCoordinateLieModel_haar :
    NilpotentExponentialHaarInput (polynomialCoordinateLieModel L).modelSpace
      (polynomialCoordinateLieModel L).carrier := by
  have hd := polynomialCoordinateLieModel_dynkin L
  exact ((nilpotentGlobalExponentialChart_of_dynkin hd).toCoordinates hd).toHaar

omit P in
theorem exists_nilpotent_model_with_inputs (hnil : LieRing.IsNilpotent L) :
    ∃ N : NilpotentLieModel L, NilpotentDynkinExpansionInput N.modelSpace N.carrier ∧
      NilpotentExponentialHaarInput N.modelSpace N.carrier := by
  obtain ⟨Q⟩ := polynomialExponentialCoordinates_nilpotent L hnil
  let := Q
  exact ⟨polynomialCoordinateLieModel L, polynomialCoordinateLieModel_dynkin L,
    polynomialCoordinateLieModel_haar L⟩

theorem exists_nilpotent_model_with_inputs_of_finite
    (K : Type) [LieRing K] [LieAlgebra ℝ K] [FiniteDimensional ℝ K]
    (hnil : LieRing.IsNilpotent K) :
    ∃ N : NilpotentLieModel K, NilpotentDynkinExpansionInput N.modelSpace N.carrier ∧
      NilpotentExponentialHaarInput N.modelSpace N.carrier := by
  let b := Module.finBasis ℝ K
  let : NormedAddCommGroup K := NormedAddCommGroup.induced K _ b.equivFun b.equivFun.injective
  let : NormedSpace ℝ K := NormedSpace.induced ℝ K _ b.equivFun
  let : RealNormedLieAlgebra K :=
    { (inferInstance : NormedAddCommGroup K), (inferInstance : LieRing K),
      (inferInstance : NormedSpace ℝ K), (inferInstance : LieAlgebra ℝ K) with }
  exact exists_nilpotent_model_with_inputs K hnil

end PolycyclicRecognition

end

end OAI
