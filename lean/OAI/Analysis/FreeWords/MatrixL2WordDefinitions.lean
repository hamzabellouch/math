import Mathlib
import OAI.Analysis.FreeWords.MatrixL2Definitions

namespace OAI

noncomputable section

namespace KKMatrixL2

open KKTraceTransfer Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def EntryBound {I : Type*} {M : VonNeumannAlgebra H} {n : ℕ}
    (f : I → MatrixAlg M n) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ t i j, ‖f t i j‖ ≤ C

end

end KKMatrixL2
end

end OAI
