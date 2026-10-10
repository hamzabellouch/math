import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.TensorProducts.SpatialIdentification
import OAI.Analysis.JiangSu.Traceless.TracelessCanonicalPure

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain
open scoped CStarAlgebra

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def canonicalStabilizationEquiv :
    CornerCompletion A ≃⋆ₐ[ℂ] Traceless.CanonicalStabilization A :=
  Pureness.completedSpatialEquiv (stateHilbertRepresentation A).toNonUnitalStarAlgHom
    (stateHilbertRepresentation_injective A)

theorem StrictComparison.empty_trace [IsEmpty (TracialState A)]
    (hcmp : StrictComparison A) : Traceless.EmptyTraceComparison A := by
  intro a b ha hb hb0
  let e := canonicalStabilizationEquiv (A := A)
  have hpos (x : Traceless.CanonicalStabilization A) (hx : 0 ≤ x) : 0 ≤ e.symm x := by
    simpa only [map_zero] using OrderHomClass.mono e.symm hx
  have h := hcmp (e.symm a) (e.symm b) (hpos a ha) (hpos b hb)
    (fun hz => hb0 (e.symm.injective (hz.trans (map_zero _).symm)))
    (fun τ => isEmptyElim τ)
  apply (cuntzSubequiv_iff_norm a b).mpr
  intro ε hε
  obtain ⟨v,hv⟩ := (cuntzSubequiv_iff_norm _ _).mp h ε hε
  refine ⟨e v, ?_⟩
  have hstar : e (star v) = star (e v) := e.map_star' v
  have heq : e (e.symm a-star v*e.symm b*v)=a-star (e v)*b*e v := by
    rw [map_sub e,map_mul e,map_mul e,hstar,
      StarAlgEquiv.apply_symm_apply,StarAlgEquiv.apply_symm_apply]
  rw [←heq]
  have henorm (x : CornerCompletion A) : ‖e x‖=‖x‖ :=
    Pureness.completedSpatialEquiv_norm _ _ x
  rw [henorm]
  exact hv

end DirectComparison

end
end

end OAI
