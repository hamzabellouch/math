import OAI.Analysis.OperatorAlgebra.GNSHilbertStructure

namespace OAI

/-! Algebra vectors are dense in the bundled GNS space. -/
noncomputable section
open scoped ComplexOrder Topology
namespace WeakPureInfiniteness

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def gnsVector (φ : A →ₚ[ℂ] ℂ) (a : A) : gnsHilbert φ :=
  (φ.toPreGNS a : φ.GNS)

lemma gnsVector_induction_on (φ : A →ₚ[ℂ] ℂ) (x : gnsHilbert φ)
    {p : gnsHilbert φ → Prop} (hp : IsClosed {x | p x})
    (h : ∀ a : A, p (gnsVector φ a)) : p x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact hp
  | ih y =>
    have hy := h (φ.ofPreGNS y)
    simpa only [gnsVector, PositiveLinearMap.toPreGNS_ofPreGNS] using hy

end WeakPureInfiniteness

end

end OAI
