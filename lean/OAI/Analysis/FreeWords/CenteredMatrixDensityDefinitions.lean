import Mathlib
import OAI.Analysis.FreeWords.TraceTransferDefinitions

namespace OAI

noncomputable section

namespace KKTraceTransfer

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def amplifiedTrace (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M) (n : ℕ)
    (x : Matrix (Fin n) (Fin n) (ConcreteAlgebra M)) : ℂ :=
  (n : ℂ)⁻¹ * ∑ i, τ.map (x i i)

end

end KKTraceTransfer
end

end OAI
