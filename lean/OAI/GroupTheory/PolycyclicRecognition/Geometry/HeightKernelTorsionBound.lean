import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HeightKernelCoefficientDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SmallCoefficientRationalRetract
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalCompleteIdentity

namespace OAI

/-! # Bounded finite subgroup orders for the height-kernel extension

The coefficient-ring dimension theorem and the actual invariant mean give
finite integral projective dimension of the rational coefficient. FP-infinity
then detects a nonzero factorial annihilator of the complete integral identity.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory ThompsonNonamenability
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] [Countable G]

theorem TypeFPInfinity.heightKernel_rationalCoefficient_finite_dimension
    (hG : TypeFPInfinity G) (M : InvariantMean G) (N : Subgroup G) [N.Normal]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsVirtuallyNilpotent J) :
    ∃ d : ℕ, HasProjectiveDimensionLE (Rep.trivial ℤ G ℚ) d := by
  obtain ⟨d, hd⟩ := hG.heightKernel_smallCoefficient_finite_dimension N hQ hN
  exact ⟨d + 1, rationalCoefficient_dimension_of_smallCoefficient M d hd⟩

theorem TypeFPInfinity.heightKernel_boundedFiniteSubgroupOrders
    (hG : TypeFPInfinity G) (M : InvariantMean G) (N : Subgroup G) [N.Normal]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsVirtuallyNilpotent J) :
    HasBoundedFiniteSubgroupOrders G := by
  obtain ⟨d, hd⟩ := hG.heightKernel_rationalCoefficient_finite_dimension M N hQ hN
  let := hd
  exact hG.boundedFiniteSubgroupOrders_of_rational_projectiveDimension G d

end PolycyclicRecognition

end

end OAI
