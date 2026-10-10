import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommonDynkinFormula
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinIntegration
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentCoordinatesInput
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieIntegrationNaturality

namespace OAI

/-! # Integration between the nilpotent models used by the application

Global exponential coordinates and one application of the finite Dynkin
identity to the product construct the homomorphism. Its smoothness and
actual differential are proved by exponential curves. The target is
explicitly nilpotent; integration into the ambient solvable group remains
a separate input.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

attribute [local instance] productSelfChartedSpace

variable {E G F H : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [T2Space G] [SimplyConnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H]
  [T2Space H] [SimplyConnectedSpace H] [MeasurableSpace H] [BorelSpace H]

omit [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H] in
theorem nilpotentSmoothIntegration_of_coordinates
    (coordinatesG : NilpotentGlobalExponentialChartInput E G)
    (coordinatesH : NilpotentGlobalExponentialChartInput F H)
    (dynkin : ∀ (L : Type) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
      (P : NilpotentLieModel L), NilpotentDynkinExpansionInput P.modelSpace P.carrier)
    (hnilH : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, F)) H)) :
    NilpotentSmoothIntegrationInput (EN := E) (N := G) (EG := F) (G := H) := by
  intro _ hnilG j
  obtain ⟨cG, hcG⟩ := coordinatesG groupExponential groupExponential_isGroupExponential hnilG
  obtain ⟨cH, hcH⟩ := coordinatesH groupExponential groupExponential_isGroupExponential hnilH
  have hG : IsGroupExponential cG := by
    have heq : (cG : GroupLieAlgebra (𝓘(ℝ, E)) G → G) = groupExponential := funext hcG
    rw [heq]
    exact groupExponential_isGroupExponential
  have hH : IsGroupExponential cH := by
    have heq : (cH : GroupLieAlgebra (𝓘(ℝ, F)) H → H) = groupExponential := funext hcH
    rw [heq]
    exact groupExponential_isGroupExponential
  have hp : NilpotentDynkinExpansionInput (E × F) (G × H) :=
    dynkin _ (exponentialProductLieModel cG cH)
  obtain ⟨c, coeff, hprodG, hprodH⟩ := exists_common_dynkin_formula hnilG hnilH hp hG hH
  refine ⟨exponentialHomOfDynkin cG cH hG hH coeff hprodG hprodH j,
    contMDiff_exponentialHomOfDynkin cG cH hG hH coeff hprodG hprodH j, ?_⟩
  exact mfderiv_exponentialHomOfDynkin cG cH hG hH coeff hprodG hprodH j

end PolycyclicRecognition

end

end OAI
