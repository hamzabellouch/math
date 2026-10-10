import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.Inner

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section Endpoint
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma HasQuadraticExpansion.sub {f g : E → ℝ} {p q : E} {H K : E →L[ℝ] E}
    (hf : HasQuadraticExpansion f p H) (hg : HasQuadraticExpansion g q K) :
    HasQuadraticExpansion (fun d => f d-g d) (p-q) (H-K) := by
  rw [hasQuadraticExpansion_iff_isLittleO] at hf hg ⊢
  convert! hf.sub hg using 1
  funext d
  simp only [quadraticTaylor,inner_sub_left,sub_apply]
  ring
end Endpoint
end WeakMTWTransport

end

end

end

end OAI
