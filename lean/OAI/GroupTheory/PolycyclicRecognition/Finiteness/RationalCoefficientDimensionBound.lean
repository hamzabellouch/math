import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalFiniteResolution
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalGroupHomology
import OAI.GroupTheory.PolycyclicRecognition.Geometry.HeightKernelTorsionBound

namespace OAI

/-! # Rational homology bounds from the actual rational-coefficient resolution -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits ThompsonNonamenability
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem rationalHomologyDimension_of_rational_representation (d : ℕ)
    (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d) :
    RationalHomologyDimensionLE G d := by
  let := hd
  intro A i hi
  exact (RationalResolution.groupHomology_isZero_above_dimension d
    (rationalizeRepresentation A) i hi).of_iso (rationalizeGroupHomologyIso A i).symm

theorem rationalHomologyDimension_of_rational_coefficient (d : ℕ)
    (hd : HasProjectiveDimensionLE (Rep.trivial ℤ G ℚ) d) :
    RationalHomologyDimensionLE G d :=
  rationalHomologyDimension_of_rational_representation d
    (rationalGroup_dimension_le_of_integral_rational d hd)

theorem TypeFPInfinity.heightKernel_rationalHomologyDimension [Countable G]
    (hG : TypeFPInfinity G) (M : InvariantMean G) (N : Subgroup G) [N.Normal]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsVirtuallyNilpotent J) :
    ∃ d : ℕ, RationalHomologyDimensionLE G d := by
  obtain ⟨d, hd⟩ := hG.heightKernel_rationalCoefficient_finite_dimension M N hQ hN
  exact ⟨d, rationalHomologyDimension_of_rational_coefficient d hd⟩

end PolycyclicRecognition

end

end OAI
