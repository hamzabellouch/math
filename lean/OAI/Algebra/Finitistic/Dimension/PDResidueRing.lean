import OAI.Algebra.Finitistic.Dimension.PDResidueTensor
import OAI.Algebra.Finitistic.Dimension.PDSquareZero
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace OAI
noncomputable section
namespace LittleFinitistic.PDTensor
universe u
variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- The right-module quotient used by tensor detection is the underlying
vector space of the usual quotient ring A/rad A. -/
def residueRingEquiv : Residue (A := A) ≃ₗ[k] A ⧸ Ring.jacobson A :=
  LinearEquiv.refl k _
end LittleFinitistic.PDTensor

end

end OAI
