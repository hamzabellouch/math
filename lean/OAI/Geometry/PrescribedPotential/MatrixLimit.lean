import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus

namespace OAI

/-! Matrix Limit. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ComplexOrder
namespace CompactMatrixPositivity
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma posSemidef_of_tendsto {M : ℕ → Matrix n n ℂ} {L : Matrix n n ℂ}
    (hL : L.IsHermitian) (hM : ∀ j, (M j).PosSemidef)
    (ht : Tendsto M atTop (𝓝 L)) : L.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hL
  intro v
  apply Complex.nonneg_iff.mpr
  refine ⟨?_,(hL.im_star_dotProduct_mulVec_self v).symm⟩
  have hc : Continuous (fun B : Matrix n n ℂ => (star v ⬝ᵥ (B *ᵥ v)).re) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  exact ge_of_tendsto (hc.tendsto L |>.comp ht)
    (Filter.Eventually.of_forall (fun j => (hM j).re_dotProduct_nonneg v))

lemma posDef_of_tendsto_det_ne_zero {M : ℕ → Matrix n n ℂ} {L : Matrix n n ℂ}
    (hL : L.IsHermitian) (hM : ∀ j, (M j).PosDef)
    (ht : Tendsto M atTop (𝓝 L)) (hd : L.det ≠ 0) : L.PosDef :=
  (posSemidef_of_tendsto hL (fun j => (hM j).posSemidef) ht).posDef_iff_det_ne_zero.mpr hd

end CompactMatrixPositivity

end
end

end OAI
