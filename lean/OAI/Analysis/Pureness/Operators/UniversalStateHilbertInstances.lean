import OAI.Analysis.Pureness.Operators.UniversalStateGNS

namespace OAI
noncomputable section
namespace CuntzPureness
variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[instance_reducible]
def universalStateHilbertNormedAddCommGroup :
    NormedAddCommGroup (UniversalStateHilbert A) := inferInstance

attribute [local instance] universalStateHilbertNormedAddCommGroup

@[instance_reducible]
def universalStateHilbertInnerProductSpace :
    InnerProductSpace ℂ (UniversalStateHilbert A) := inferInstance

theorem universalStateHilbertCompleteSpace :
    CompleteSpace (UniversalStateHilbert A) := inferInstance
end CuntzPureness

end

end OAI
