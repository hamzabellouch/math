import Mathlib
import OAI.Geometry.WeakMTW.Variations.HessianNull

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace DiscreteVariational
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem null_endpoint_null_momentum {f : ℝ × E → ℝ} {c : ℝ → E}
    {p : ℝ → E →L[ℝ] ℝ} {p' : E →L[ℝ] ℝ} {R : E → E →L[ℝ] ℝ}
    (hf : ContDiffAt ℝ 2 f (0,c 0)) (hm : IsLocalMin f (0,c 0))
    (hc : HasDerivAt c 0 0) (hp : HasDerivAt p p' 0) (hR : DifferentiableAt ℝ R (c 0))
    (hstat : ∀ᶠ s in 𝓝 (0 : ℝ), fderiv ℝ f (s,c s) (1,0) = 0)
    (hmom : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ w : E,
      fderiv ℝ f (s,c s) (0,w) = p s w + R (c s) w) : p' = 0 := by
  let q : ℝ × E := (0,c 0)
  let H := fderiv ℝ (fderiv ℝ f) q
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) q :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hpath : HasDerivAt (fun s : ℝ => (s,c s)) (1,0) 0 := (hasDerivAt_id 0).prodMk hc
  have hpathdf := hdf.hasFDerivAt.comp_hasDerivAt 0 hpath
  have hdiag : H (1,0) (1,0) = 0 := by
    have hh := hpathdf.clm_apply (hasDerivAt_const (0 : ℝ) (1, (0 : E)))
    have hz := hh.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hstat)
    simpa using hz
  have hnull : ∀ w : E, H (1,0) (0,w) = 0 := fun w => hessian_null_pair hf hm hdiag (0,w)
  have hRc : HasDerivAt (R ∘ c) 0 0 := by
    simpa using hR.hasFDerivAt.comp_hasDerivAt 0 hc
  ext w
  have h1 := hpathdf.clm_apply (hasDerivAt_const (0 : ℝ) ((0 : ℝ),w))
  have h2 := (hp.clm_apply (hasDerivAt_const (0 : ℝ) w)).add
    (hRc.clm_apply (hasDerivAt_const (0 : ℝ) w))
  have he : (fun s => fderiv ℝ f (s,c s) (0,w)) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => p s w + R (c s) w) := hmom.mono (fun _ hs => hs w)
  have hh := h1.unique (h2.congr_of_eventuallyEq he)
  simp only [map_zero,zero_apply,add_zero] at hh
  exact hh.symm.trans (hnull w)

end
end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
