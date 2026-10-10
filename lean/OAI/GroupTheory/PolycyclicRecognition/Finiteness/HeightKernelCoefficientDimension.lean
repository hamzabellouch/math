import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalQuotientCompleteVanishing
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.LocalVirtualPolycyclicVanishing
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SmallCoefficientCompletedUnit

namespace OAI

/-! # Finite dimension of the coefficient ring for the height-kernel extension

The kernel may contain torsion and its finitely generated subgroups may have
unbounded ranks. The quotient alone is assumed to have finite integral dimension.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G] [Countable G]

theorem TypeFPInfinity.heightKernel_smallCoefficient_vanishing
    (hG : TypeFPInfinity G) (N : Subgroup G) [N.Normal]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsVirtuallyNilpotent J)
    (p : ℕ) :
    Subsingleton (ShiftedCompletedCohomology p (smallCoefficientRepresentation G)) := by
  exact hG.normalQuotient_complete_vanishing N (smallCoefficientRepresentation G) hQ
    (fun r => hG.locallyVirtuallyNilpotent_smallCoefficient_induction_vanishing N r hN) p

theorem TypeFPInfinity.heightKernel_smallCoefficient_finite_dimension
    (hG : TypeFPInfinity G) (N : Subgroup G) [N.Normal]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsVirtuallyNilpotent J) :
    ∃ d : ℕ, HasProjectiveDimensionLE (smallCoefficientRepresentation G) d :=
  smallCoefficient_finite_dimension_of_complete_vanishing G
    (hG.heightKernel_smallCoefficient_vanishing N hQ hN 0)

end PolycyclicRecognition

end

end OAI
