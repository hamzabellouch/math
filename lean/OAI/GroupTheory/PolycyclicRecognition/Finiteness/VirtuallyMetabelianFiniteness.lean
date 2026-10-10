import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianNormalFinitenessEndgame
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteIndexRestriction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.VirtualSolvableDimension

namespace OAI

/-! # FP-infinity and virtual metabelianity give finite virtual dimension -/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {G : Type} [Group G] [Group.FG G]

theorem metabelian_virtual_finite_dimension [IsMulCommutative (commutator G)]
    (h : TypeFPInfinity G) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V :=
  abelian_normal_virtual_finite_dimension (commutator G) h

theorem virtually_metabelian_virtual_finite_dimension (H : Subgroup G) [H.FiniteIndex]
    [IsMulCommutative (commutator H)] (h : TypeFPInfinity G) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V :=
  exists_solvable_finiteDimension_of_finiteIndex H
    (metabelian_virtual_finite_dimension (h.finiteIndex_subgroup H))

end PolycyclicRecognition

end

end OAI
