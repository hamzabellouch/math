import OAI.Analysis.Pureness.Operators.BundledUniversalGNS

namespace OAI
noncomputable section
namespace CuntzPureness
universe u

structure FaithfulHilbertRepresentation (A : Type u) [CStarAlgebra A] where
  carrier : Type u
  [normed : NormedAddCommGroup carrier]
  [inner : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]
  hom : A →⋆ₐ[ℂ] (carrier →L[ℂ] carrier)
  injective : Function.Injective hom

attribute [instance] FaithfulHilbertRepresentation.normed
  FaithfulHilbertRepresentation.inner FaithfulHilbertRepresentation.complete

variable (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem nonempty_faithfulHilbertRepresentation : Nonempty (FaithfulHilbertRepresentation A) := by
  exact ⟨{
    carrier := StateHilbertSpace A
    hom := stateHilbertRepresentation A
    injective := stateHilbertRepresentation_injective A
  }⟩

def chosenFaithfulHilbertRepresentation : FaithfulHilbertRepresentation A :=
  Classical.choice (nonempty_faithfulHilbertRepresentation A)

abbrev FaithfulHilbertSpace := (chosenFaithfulHilbertRepresentation A).carrier

def faithfulHilbertRepresentation : A →⋆ₐ[ℂ]
    (FaithfulHilbertSpace A →L[ℂ] FaithfulHilbertSpace A) :=
  (chosenFaithfulHilbertRepresentation A).hom

theorem faithfulHilbertRepresentation_injective :
    Function.Injective (faithfulHilbertRepresentation A) :=
  (chosenFaithfulHilbertRepresentation A).injective
end CuntzPureness

end

end OAI
