import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.StationaryPullback

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section CenteredQuadratic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma centered_half_norm_sq_c2 (z : E) :
    ContDiff ℝ 2 (fun w : E => ‖w-z‖^2/2) :=
  (half_norm_sq_contDiff.comp (contDiff_id.sub contDiff_const)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

lemma centered_half_norm_sq_fderiv (z : E) :
    fderiv ℝ (fun w : E => ‖w-z‖^2/2) z=0 := by
  have hq := (half_norm_sq_hasFDerivAt (z-z)).comp (f := fun w:E => w-z) z ((hasFDerivAt_id z).sub_const z)
  simpa only [Function.comp_def,sub_self,map_zero,ContinuousLinearMap.zero_comp] using hq.fderiv

lemma centered_half_norm_sq_second (z d : E) :
    fderiv ℝ (fderiv ℝ (fun w : E => ‖w-z‖^2/2)) z d d=‖d‖^2 := by
  have hc : ContDiffAt ℝ 2 (fun w:E => ‖w‖^2/2) (z-z) :=
    (half_norm_sq_contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt
  have H := second_fderiv_comp_stationary hc (g := fun w:E => w-z)
    (contDiffAt_id.sub contDiffAt_const)
    (by rw [sub_self,half_norm_sq_fderiv,map_zero]) d d
  have hid : fderiv ℝ (fun w:E => w-z) z=ContinuousLinearMap.id ℝ E :=
    ((hasFDerivAt_id z).sub_const z).fderiv
  simpa only [sub_self,hid,ContinuousLinearMap.id_apply,
    half_norm_sq_second_fderiv,real_inner_self_eq_norm_sq] using H
end CenteredQuadratic

end WeakMTWTransport
end
end
end

end OAI
