import Mathlib

namespace OAI

section
noncomputable section
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E F G:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma fderiv_contact_jet {g:E × F → G} {f:E → F} {x:E}
    (hg:DifferentiableAt ℝ g (x,f x)) (hf:DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y=>g (y,f y)) x=(fderiv ℝ g (x,f x)).comp
      ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ f x)) := by
  exact (hg.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hf.hasFDerivAt)).fderiv
lemma fderiv_contact_c2 {g:E × (E →L[ℝ] ℝ) → G} {φ:E → ℝ} {x:E}
    (hg:ContDiffAt ℝ ∞ g (x,fderiv ℝ φ x)) (hφ:ContDiffAt ℝ 2 φ x) :
    fderiv ℝ (fun y=>g (y,fderiv ℝ φ y)) x=(fderiv ℝ g (x,fderiv ℝ φ x)).comp
      ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ (fderiv ℝ φ) x)) := by
  exact fderiv_contact_jet (hg.differentiableAt (by simp))
    ((hφ.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num))
lemma continuous_contact_jet_det (J:E × F →L[ℝ] E) (H Q:E →L[ℝ] F) :
    Continuous (fun δ:ℝ=>|(J.comp ((ContinuousLinearMap.id ℝ E).prod (H-δ • Q))).det|) := by
  have hH:Continuous (fun δ:ℝ=>H-δ • Q):=continuous_const.sub (continuous_id.smul continuous_const)
  have hP:Continuous (fun δ:ℝ=>(ContinuousLinearMap.id ℝ E).prod (H-δ • Q)):=
    (ContinuousLinearMap.prodL ℝ).continuous.comp (continuous_const.prodMk hH)
  exact (ContinuousLinearMap.continuous_det.comp (continuous_const.clm_comp hP)).abs
lemma continuous_linearized_det (J:F →L[ℝ] E) (H Q:E →L[ℝ] F) :
    Continuous (fun δ:ℝ=>|(J.comp (H-δ • Q)).det|) := by
  have hH:Continuous (fun δ:ℝ=>H-δ • Q):=continuous_const.sub (continuous_id.smul continuous_const)
  exact (ContinuousLinearMap.continuous_det.comp (continuous_const.clm_comp hH)).abs
end WeakMTWTransport

end
end

end OAI
