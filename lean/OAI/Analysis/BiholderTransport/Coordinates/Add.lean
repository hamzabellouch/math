import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.Inner

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma HasQuadraticExpansion.add {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : E → ℝ} {p q : E} {H K : E →L[ℝ] E}
    (hf : HasQuadraticExpansion f p H) (hg : HasQuadraticExpansion g q K) :
    HasQuadraticExpansion (fun d => f d+g d) (p+q) (H+K) := by
  rw [hasQuadraticExpansion_iff_isLittleO] at hf hg ⊢
  convert! hf.add hg using 1
  funext d
  simp only [quadraticTaylor,inner_add_left,add_apply]
  ring

end WeakMTWTransport
end
end
end

end OAI
