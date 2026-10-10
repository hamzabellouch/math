import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianPerturbation
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianCoefficientBounds

namespace OAI


noncomputable section
namespace TamingCompatibility.ExteriorForms
open Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma extDeriv_dc_translate (J : E → E →L[ℝ] E) (f : E → ℝ) (b y : E) :
    extDeriv (dc J (fun x => f (x-b))) y =
      extDeriv (dc (fun z => J (b+z)) f) (y-b) := by
  have he : dc J (fun x => f (x-b)) = fun x => dc (fun z => J (b+z)) f (x-b) := by
    funext x
    simp only [dc,fderiv_comp_sub]
    congr 3
    abel_nf
  rw [he,extDeriv,fderiv_comp_sub]
  rfl

lemma extDeriv_dc_congr_germ {J K : E → E →L[ℝ] E} {f g : E → ℝ} {y : E}
    (hJ : J =ᶠ[𝓝 y] K) (hf : f =ᶠ[𝓝 y] g) :
    extDeriv (dc J f) y = extDeriv (dc K g) y := by
  have he : dc J f =ᶠ[𝓝 y] dc K g := by
    filter_upwards [hJ,hf.fderiv (𝕜 := ℝ)] with x hx hf
    simp only [dc,hx,hf]
  exact congrArg ContinuousAlternatingMap.alternatizeUncurryFin he.fderiv_eq
end TamingCompatibility.ExteriorForms

namespace TamingCompatibility.RadialPotential
open Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology SchwartzMap RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma schwartz_hermitianLog_lower (W : 𝓢(E,E →L[ℝ] E)) {s : ℝ} (hs : 0 < s)
    (b y v : E) (hWy : ∀ w, W y (W y w) = -w) (hWb : ∀ w, W b (W b w) = -w) :
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    2*s^2*(‖v‖^2+‖W b v‖^2)/(s^2+‖y-b‖^2+‖W b (y-b)‖^2)^2 -
      ((1+M)^2*(16*L*M/(s+‖y-b‖)))*‖v‖^2 ≤
      extDeriv (ExteriorForms.dc W (fun x => hermitianLogPotential (W b) s (x-b))) y ![v,W y v] := by
  dsimp only
  rw [ExteriorForms.extDeriv_dc_translate]
  have hJ : DifferentiableAt ℝ (fun z => W (b+z)) (y-b) :=
    ((W.smooth ⊤).comp (contDiff_const.add contDiff_id)).differentiable (by simp) _
  have he : b+(y-b)=y := by abel
  have h := hermitianLog_variable_ddc_lower (W b) hs (y-b) v hJ
    (by simpa only [he] using hWy) hWb
    (apply_nonneg _ _) (apply_nonneg _ _)
    (by simpa only [he] using GeometricChart.schwartz_difference_bound W y b)
    (by simpa only [fderiv_comp_add_left,he] using GeometricChart.schwartz_fderiv_bound W y)
    (by simpa only [he] using W.norm_le_seminorm ℝ y) (W.norm_le_seminorm ℝ b)
  simpa only [he] using h

lemma schwartz_hermitianSqrt_lower (W : 𝓢(E,E →L[ℝ] E)) {s : ℝ} (hs : 0 < s)
    (b y v : E) (hWy : ∀ w, W y (W y w) = -w) (hWb : ∀ w, W b (W b w) = -w) :
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    ‖v‖^2/((1+M)*(s+‖y-b‖)) - ((1+M)^2*(10*L*M))*‖v‖^2 ≤
      extDeriv (ExteriorForms.dc W (fun x => hermitianSqrtPotential (W b) s (x-b))) y ![v,W y v] := by
  dsimp only
  rw [ExteriorForms.extDeriv_dc_translate]
  have hJ : DifferentiableAt ℝ (fun z => W (b+z)) (y-b) :=
    ((W.smooth ⊤).comp (contDiff_const.add contDiff_id)).differentiable (by simp) _
  have he : b+(y-b)=y := by abel
  have h := hermitianSqrt_variable_ddc_lower (W b) hs (y-b) v hJ
    (by simpa only [he] using hWy) hWb
    (apply_nonneg _ _) (apply_nonneg _ _)
    (by simpa only [he] using GeometricChart.schwartz_difference_bound W y b)
    (by simpa only [fderiv_comp_add_left,he] using GeometricChart.schwartz_fderiv_bound W y)
    (by simpa only [he] using W.norm_le_seminorm ℝ y) (W.norm_le_seminorm ℝ b)
  simpa only [he] using h
end TamingCompatibility.RadialPotential

end

end OAI
