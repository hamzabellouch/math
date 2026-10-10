import Mathlib

namespace OAI



noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma bilinear_differentiable_substitution
    (K : F →L[ℝ] F →L[ℝ] ℝ) {r : E → F} {R : E →L[ℝ] F}
    (hr0 : r 0 = 0) (hr : HasFDerivAt r R 0) :
    (fun h => K (r h) (r h) - K (R h) (R h)) =o[𝓝 0] (fun h : E => ‖h‖^2) := by
  have he : (fun h => r h-R h) =o[𝓝 0] (fun h : E => h) := by
    simpa only [hr0,sub_zero] using hr.isLittleO
  have hro : r =O[𝓝 0] (fun h : E => h) := by
    simpa only [hr0,sub_zero] using hr.isBigO_sub
  have hRo : (fun h => R h) =O[𝓝 0] (fun h : E => h) := R.isBigO_comp _ _
  have h₁ : (fun h => K (r h-R h) (r h)) =o[𝓝 0] (fun h : E => ‖h‖*‖h‖) :=
    K.isBoundedBilinearMap.isBigO_comp.trans_isLittleO (he.norm_norm.mul_isBigO hro.norm_norm)
  have h₂ : (fun h => K (R h) (r h-R h)) =o[𝓝 0] (fun h : E => ‖h‖*‖h‖) :=
    K.isBoundedBilinearMap.isBigO_comp.trans_isLittleO (hRo.norm_norm.mul_isLittleO he.norm_norm)
  convert! h₁.add h₂ using 1
  · funext h
    simp only [map_sub,sub_apply]
    ring
  · funext h
    ring

lemma second_order_substitution_exact_linear
    {f : F → ℝ} {D : F →L[ℝ] ℝ} {K : F →L[ℝ] F →L[ℝ] ℝ}
    (hf : (fun z => f z-f 0-D z-K z z/2) =o[𝓝 0] (fun z : F => ‖z‖^2))
    {r : E → F} {R : E →L[ℝ] F} (hr0 : r 0 = 0) (hr : HasFDerivAt r R 0) :
    (fun h => f (r h)-f 0-D (r h)-K (R h) (R h)/2)
      =o[𝓝 0] (fun h : E => ‖h‖^2) := by
  have hro : r =O[𝓝 0] (fun h : E => h) := by
    simpa only [hr0,sub_zero] using hr.isBigO_sub
  have hn : (fun h => ‖r h‖^2) =O[𝓝 0] (fun h : E => ‖h‖^2) := by
    simpa only [← sq] using hro.norm_norm.mul hro.norm_norm
  have hc : Tendsto r (𝓝 0) (𝓝 0) := by simpa only [ContinuousAt,hr0] using hr.continuousAt
  have H := (hf.comp_tendsto hc).trans_isBigO hn
  have HQ := (bilinear_differentiable_substitution K hr0 hr).const_mul_left (1/2:ℝ)
  convert! H.add HQ using 1
  funext h
  simp only [Function.comp_def]
  ring

end WeakMTWTransport

end

end OAI
