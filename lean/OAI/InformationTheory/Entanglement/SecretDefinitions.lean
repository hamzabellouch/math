import OAI.Analysis.Quantum.PPTSquare.ChannelModel
import OAI.Analysis.Quantum.PPTSquare.Compression
import OAI.Analysis.Quantum.PPTSquare.TensorModel
import OAI.Analysis.Quantum.PPTSquare.TensorPositivity
import OAI.Analysis.Quantum.PPTSquare.SymmetricVectors
import OAI.Analysis.Quantum.PPTSquare.QuadraticCriterion

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {n m : Type} [Fintype n] [Fintype m]

noncomputable def traceNorm (A : Matrix n m ℂ) : ℝ := by
  classical
  exact (Matrix.trace (CFC.sqrt (Aᴴ * A))).re

def Represented (R : Mat (n × m)) : Prop :=
  R.PosSemidef ∧ Matrix.trace R = 1 ∧
  ∃ r s : ℕ, 0 < r ∧ 0 < s ∧
    ∃ (L : Map (Fin r) n) (M : Map (Fin s) m) (χ : Fin r × Fin s → ℂ),
      CP L ∧ CP (L.comp transposeMap) ∧ CP M ∧ CP (M.comp transposeMap) ∧
      R = tensorMap L M (Matrix.vecMulVec χ (star χ))

end SecretKey

end

end OAI
