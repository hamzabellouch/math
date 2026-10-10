import Mathlib
import OAI.Geometry.WeakMTW.Variations.HessianNull
import OAI.Geometry.WeakMTW.Variations.MajorantHessian
import OAI.Geometry.WeakMTW.Variations.GeneratingFocalCalculus

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace DiscreteVariational
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem fderiv_partial_fst {f : E × F → ℝ} {a : E} {b : F}
    (hf : DifferentiableAt ℝ f (a,b)) (ξ : E) :
    fderiv ℝ (fun z : E => f (z,b)) a ξ = fderiv ℝ f (a,b) (ξ,0) := by
  have hc : HasFDerivAt (fun z : E => (z,b))
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] F)) a :=
    (hasFDerivAt_id a).prodMk (hasFDerivAt_const (c := b) a)
  change fderiv ℝ (f ∘ (fun z : E => (z,b))) a ξ = _
  rw [(hf.hasFDerivAt.comp a hc).fderiv]
  rfl

 theorem horizontal_hessian_positive {f : E × F → ℝ} {a : E} {b : F}
    (hf : ContDiffAt ℝ 2 f (a,b)) (hm : IsLocalMin f (a,b))
    (ξ : E) (κ : F) {c : ℝ} (hc : c ≠ 0)
    (hcross : HasDerivAt (fun t : ℝ => fderiv ℝ f (a,b+t•κ) (ξ,0)) c 0) :
    0 < fderiv ℝ (fderiv ℝ (fun z : E => f (z,b))) a ξ ξ := by
  let L : E →L[ℝ] E × F := (ContinuousLinearMap.id ℝ E).prod 0
  have hd : fderiv ℝ (fderiv ℝ (fun z : E => f (z,b))) a ξ ξ =
      fderiv ℝ (fderiv ℝ f) (a,b) (ξ,0) (ξ,0) := by
    have hf' : ContDiffAt ℝ 2 f ((0,b)+L a) := by simpa [L] using hf
    convert hessian_affine_pullback L ((0,b) : E × F) hf' ξ using 1 <;> simp [L]
  rw [hd]
  have hnonneg := hessian_nonneg hf hm ((ξ,0) : E × F)
  by_contra hn
  have hzero := le_antisymm (not_lt.mp hn) hnonneg
  have hnull := hessian_null_pair hf hm hzero ((0,κ) : E × F)
  have hcurve : HasDerivAt (fun t : ℝ => (a,b+t•κ)) ((0,κ) : E × F) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) a).prodMk (((hasDerivAt_id (0 : ℝ)).smul_const κ).const_add b) using 1
    simp
  have hf' : ContDiffAt ℝ 2 f (a,b+(0 : ℝ)•κ) := by simpa using hf
  have he := (derivative_hessian_along_curve hf' hcurve ((ξ,0) : E × F)).unique hcross
  simp only [zero_smul,add_zero] at he
  rw [(hf.isSymmSndFDerivAt (by norm_num)).eq (0,κ) (ξ,0),hnull] at he
  exact hc he.symm

end
end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
