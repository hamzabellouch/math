import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalRecognitionEndgame
import OAI.GroupTheory.PolycyclicRecognition.Geometry.HeightKernelVirtualSolvable
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteIndexFiniteness

namespace OAI

/-! # The finiteness and duality endgame for the actual height extension -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory ThompsonNonamenability
open scoped IsMulCommutative
variable {P G : Type} [Group P] [Group G] [Group.FG P] [Group.FG G]

theorem TypeFPInfinity.heightKernel_virtuallyPolycyclic
    (hG : TypeFPInfinity G) (e : GroupCoarseEquivalence P G)
    (hP : IsVirtuallyPolycyclic P) (M : InvariantMean G)
    (N : Subgroup G) [N.Normal] [IsMulCommutative (G ⧸ N)]
    (hQ : HasFiniteIntegralCohomologicalDimension (G ⧸ N))
    (hN : ∀ J : Subgroup G, J ≤ N → J.FG → Group.IsVirtuallyNilpotent J) :
    IsVirtuallyPolycyclic G := by
  let : Countable G := countable_of_group_fg G
  obtain ⟨d, hd⟩ := hG.heightKernel_rationalCoefficient_finite_dimension M N hQ hN
  exact virtuallyPolycyclic_of_coarse_rational_bounds e hP d
    (rationalGroup_dimension_le_of_integral_rational d hd)
    (hG.heightKernel_boundedFiniteSubgroupOrders M N hQ hN)
    (hG.heightKernel_virtualSolvable M N hQ hN)

end PolycyclicRecognition

end

end OAI
