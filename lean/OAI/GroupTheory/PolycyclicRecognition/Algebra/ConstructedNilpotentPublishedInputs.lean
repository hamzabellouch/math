import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntrinsicGroupDynkin
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentPublishedInputs

namespace OAI

/-! # Discharging the nilpotent published-input family

The finite BCH formula holds for every nilpotent Lie model. Together
with the model construction, global chart, integration, and Haar identities,
this proves the nilpotent input record without additional hypotheses.
-/

noncomputable section
namespace PolycyclicRecognition

/-- The nilpotent BCH expansion holds without additional hypotheses. -/
theorem nilpotentPublishedInputs : NilpotentPublishedInputs where
  dynkin := fun _ _ _ _ _ => nilpotentDynkinExpansionInput

end PolycyclicRecognition

end

end OAI
