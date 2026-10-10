import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicRealIdentity

namespace OAI

noncomputable section
open scoped TensorProduct Topology MatrixGroups
open Matrix Module Set
namespace PrimeDegreePackets.Adelic
 
def CanonicalRealDiagonalizerAllowed {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K) (σ : OrderedEmbeddings n K) : Prop :=
  AllowedRealDiagonalizer b (ProjGenLinGroup.mk (realBasisGL hn b σ))
end PrimeDegreePackets.Adelic

end

end OAI
