import OAI.NumberTheory.Ostmann.Characters.TemplateParityActionsAnchors
import OAI.NumberTheory.Ostmann.Characters.TemplateParityActionsPrior

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template.ParityActions
attribute [local instance] Classical.propDecidable

def genericReassignmentEquiv (k n m : ℕ) :
    Reassignments k n m ≃ Characters.ParityReassignments n m :=
  Fintype.equivOfCardEq ((reassignments_card k n m).trans
    (Characters.card_parityReassignments n m).symm)

end Ostmann.Characters.Template.ParityActions

end

end OAI
