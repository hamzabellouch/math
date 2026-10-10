import Mathlib
import OAI.Analysis.FreeWords.TraceTransferDefinitions

namespace OAI

noncomputable section

namespace KKMatrixL2

open KKTraceTransfer

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev MatrixAlg (M : VonNeumannAlgebra H) (n : ℕ) :=
  Matrix (Fin n) (Fin n) (ConcreteAlgebra M)

end

end KKMatrixL2
end

end OAI
