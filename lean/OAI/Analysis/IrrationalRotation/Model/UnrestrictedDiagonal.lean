import OAI.Analysis.IrrationalRotation.Model.Diagonal

namespace OAI

noncomputable section

namespace Invariant233.SequenceHilbert

variable {I : Type*}

def boundedDiagonal (a : I → ℂ) : SequenceHilbert I →L[ℂ] SequenceHilbert I := by
  classical
  exact if h : ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖a i‖ ≤ C then
    diagonal a h.choose h.choose_spec.1 h.choose_spec.2
  else 0

end Invariant233.SequenceHilbert

end

end OAI
