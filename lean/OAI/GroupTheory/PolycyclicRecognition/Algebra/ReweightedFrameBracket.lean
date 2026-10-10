import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

namespace OAI

/-! # The bracket of a frame after a varying linear change -/

noncomputable section
namespace PolycyclicRecognition
open VectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- At a point where both frames are the identity, the correction to the
bracket is precisely the antisymmetric part of the changing frame. -/
theorem lieBracket_reweighted_frame
    {F R : E → E →L[ℝ] E} {dF dR : E →L[ℝ] E →L[ℝ] E} {x : E}
    (hF : HasFDerivAt F dF x) (hR : HasFDerivAt R dR x)
    (hF₀ : F x = ContinuousLinearMap.id ℝ E)
    (hR₀ : R x = ContinuousLinearMap.id ℝ E) (v w : E) :
    lieBracket ℝ (fun y => F y (R y v)) (fun y => F y (R y w)) x =
      lieBracket ℝ (fun y => F y v) (fun y => F y w) x + dR v w - dR w v := by
  have hv := hF.clm_apply (hR.clm_apply (hasFDerivAt_const v x))
  have hw := hF.clm_apply (hR.clm_apply (hasFDerivAt_const w x))
  have hv₀ := hF.clm_apply (hasFDerivAt_const v x)
  have hw₀ := hF.clm_apply (hasFDerivAt_const w x)
  unfold lieBracket
  rw [hw.fderiv,hv.fderiv,hw₀.fderiv,hv₀.fderiv]
  simp only [hF₀,hR₀,ContinuousLinearMap.id_apply,add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    zero_apply,map_zero,zero_add]
  abel

end PolycyclicRecognition

end

end OAI
