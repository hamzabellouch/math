import OAI.Analysis.Pureness.Operators.UniversalStateHilbertInstances

namespace OAI
noncomputable section
namespace CuntzPureness
variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def StateHilbertSpace := UniversalStateHilbert A

instance stateHilbertNormedAddCommGroup : NormedAddCommGroup (StateHilbertSpace A) :=
  inferInstanceAs (NormedAddCommGroup (UniversalStateHilbert A))

instance stateHilbertInnerProductSpace : InnerProductSpace ℂ (StateHilbertSpace A) :=
  inferInstanceAs (InnerProductSpace ℂ (UniversalStateHilbert A))

instance stateHilbertCompleteSpace : CompleteSpace (StateHilbertSpace A) :=
  inferInstanceAs (CompleteSpace (UniversalStateHilbert A))

def stateHilbertRepresentation : A →⋆ₐ[ℂ]
    (StateHilbertSpace A →L[ℂ] StateHilbertSpace A) :=
  universalStateGNS A

theorem stateHilbertRepresentation_injective :
    Function.Injective (stateHilbertRepresentation A) := universalStateGNS_injective A
end CuntzPureness

end

end OAI
