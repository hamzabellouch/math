import OAI.Analysis.Pureness.GroupAlgebra.FreeGroupTensorTrace
import OAI.Analysis.Pureness.States.RegularizedStateSpatialFaithful

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
universe u

lemma faithfulHilbertSpace_nontrivial (B : Type*) [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] [Nontrivial B] :
    Nontrivial (FaithfulHilbertSpace B) := by
  by_contra h
  let : Subsingleton (FaithfulHilbertSpace B) := not_nontrivial_iff_subsingleton.mp h
  have he : faithfulHilbertRepresentation B (0 : B) = faithfulHilbertRepresentation B 1 :=
    Subsingleton.elim _ _
  exact zero_ne_one (faithfulHilbertRepresentation_injective B he)

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A))
variable (hy : y ≠ 0) (f : StateSpace y) (hA : IsNuclear.{u,0} A)

lemma regularizedStateCauchyQuotient_nontrivial :
    Nontrivial (RegularizedStateCauchyQuotient hsimple y hy f 0) :=
  (regularizedStateCauchyEmbedding_injective hsimple y hy f 0).nontrivial

include hA in

theorem regularizedStateCauchyQuotient_has_tracialState :
    Nonempty (TracialState (RegularizedStateCauchyQuotient hsimple y hy f 0)) := by
  let T := regularizedStateCauchyPositive hsimple y hy f
  let ht := regularizedStateCauchyTriangle hsimple y hy f
  let : Nontrivial (T.CauchyQuotient ht) := regularizedStateCauchyQuotient_nontrivial hsimple y hy f
  let : Nontrivial (FaithfulHilbertSpace (T.CauchyQuotient ht)) :=
    faithfulHilbertSpace_nontrivial (T.CauchyQuotient ht)
  exact tracialState_of_finite_freeGroup_tensor (T.cauchyTargetGNS ht)
    (regularizedStateSpatialTensor_finite hsimple y hy f hA)
end CuntzPureness

end

end OAI
