import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.NormalDifferential
import OAI.Geometry.WeakMTW.Coordinates.NormalFlowLength
import OAI.Geometry.WeakMTW.Coordinates.NormalNeighborhood
import OAI.Geometry.WeakMTW.Coordinates.RadialRigidity

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry
variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

omit [FiniteDimensional ℝ E] in
 theorem normalAt_fderiv_injective (N : NormalFlow G S x₀) {x v : E}
    (hv : v ∈ (N.normalAt x).source) : Function.Injective (fderiv ℝ (N.normalAt x) v) := by
  let e := N.normalAt x
  have he := ((N.normalAt_smooth x v hv).contDiffAt (e.open_source.mem_nhds hv)).differentiableAt (by simp)
  have hi := ((N.normalAt_inverse_smooth x (e v) (e.map_source hv)).contDiffAt
    (e.open_target.mem_nhds (e.map_source hv))).differentiableAt (by simp)
  have hcomp := hi.hasFDerivAt.comp v he.hasFDerivAt
  have hh : HasFDerivAt (fun w : E => w) ((fderiv ℝ e.symm (e v)).comp (fderiv ℝ e v)) v := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hv] with w hw
    exact (e.left_inv hw).symm
  have hid := hh.unique (hasFDerivAt_id v)
  apply Function.LeftInverse.injective (f := fderiv ℝ e v) (g := fderiv ℝ e.symm (e v))
  intro w
  exact congrArg (fun A : E →L[ℝ] E => A w) hid

 theorem normal_radial_curve (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ z ∈ S, ∀ v w, G z v w = G z w v)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x : E} (hzero : (0 : E) ∈ (N.normalAt x).source)
    {U : Set ℝ} (hU : IsOpen U) (hUc : Convex ℝ U)
    {c : ℝ → E} (hc : DifferentiableOn ℝ c U)
    (hct : ∀ t ∈ U, c t ∈ (N.normalAt x).target)
    {a C : ℝ} (ha : a ∈ U) (hca : c a = x)
    (hsp : ∀ t ∈ U, G (c t) (deriv c t) (deriv c t) = C ^ 2)
    (hr : ∀ t ∈ U, N.time ^ 2 * G x ((N.normalAt x).symm (c t))
      ((N.normalAt x).symm (c t)) = C ^ 2 * (t - a) ^ 2) :
    ∀ t ∈ U, c t = N.normalAt x (((t - a) / N.time) • deriv c a) := by
  let e := N.normalAt x
  let ν : ℝ → E := fun t => e.symm (c t)
  have hc' : ∀ t ∈ U, HasDerivAt c (deriv c t) t :=
    fun t ht => ((hc t ht).differentiableAt (hU.mem_nhds ht)).hasDerivAt
  have hνd : ∀ t ∈ U, DifferentiableAt ℝ ν t := by
    intro t ht
    exact (((N.normalAt_inverse_smooth x (c t) (hct t ht)).contDiffAt
      (e.open_target.mem_nhds (hct t ht))).differentiableAt (by simp)).comp t (hc' t ht).differentiableAt
  have hνt : ∀ t ∈ U, ν t ∈ e.source := fun t ht => e.map_target (hct t ht)
  have hν₀ : ν a = 0 := by
    dsimp only [ν]
    rw [hca]
    have hz := N.normalAt_zero hS hG hpos hzero
    have hh := e.left_inv hzero
    change (N.normalAt x).symm (N.normalAt x 0) = 0 at hh
    rwa [hz] at hh
  have hνa : deriv ν a = N.time⁻¹ • deriv c a := by
    have hh := (N.normalAt_inverse_hasFDerivAt_center hS hG hpos hzero)
    have hd := (show HasFDerivAt e.symm (N.time⁻¹ • ContinuousLinearMap.id ℝ E) (c a) by
      rw [hca]; exact hh).comp_hasDerivAt a (hc' a ha)
    exact hd.deriv
  have hrad : ∀ t ∈ U, (t - a) • deriv ν t = ν t := by
    intro t ht
    have hv := hνt t ht
    have hx := N.base_mem hzero
    have heq : e (ν t) = c t := e.right_inv (hct t ht)
    have he := ((N.normalAt_smooth x (ν t) hv).contDiffAt (e.open_source.mem_nhds hv)).differentiableAt (by simp)
    have hcd : deriv c t = fderiv ℝ e (ν t) (deriv ν t) := by
      have hh := he.hasFDerivAt.comp_hasDerivAt t (hνd t ht).hasDerivAt
      have hh' : HasDerivAt c (fderiv ℝ e (ν t) (deriv ν t)) t := by
        apply hh.congr_of_eventuallyEq
        filter_upwards [hU.mem_nhds ht] with s hs
        exact (e.right_inv (hct s hs)).symm
      exact hh'.deriv
    have hq := ((G x).hasFDerivAt.comp_hasDerivAt t (hνd t ht).hasDerivAt).clm_apply
      (hνd t ht).hasDerivAt
    have hq' := hq.const_mul (N.time ^ 2)
    have hp := (((hasDerivAt_id t).sub_const a).pow 2).const_mul (C ^ 2)
    have hh : N.time ^ 2 * (G x (deriv ν t) (ν t) + G x (ν t) (deriv ν t)) =
        C ^ 2 * (2 * (t - a)) := by
      have hq'' : HasDerivAt (fun s => C ^ 2 * (s - a) ^ 2)
          (N.time ^ 2 * (G x (deriv ν t) (ν t) + G x (ν t) (deriv ν t))) t := by
        apply hq'.congr_of_eventuallyEq
        filter_upwards [hU.mem_nhds ht] with s hs
        exact (hr s hs).symm
      simpa using hq''.unique hp
    rw [hsym x hx (deriv ν t) (ν t)] at hh
    have hrd : N.time ^ 2 * G x (ν t) (deriv ν t) = C ^ 2 * (t - a) := by linarith
    apply RadialRigidity.gauss_equality (B₀ := G x) (B₁ := G (e (ν t)))
      (L := fderiv ℝ e (ν t)) (T := N.time) (C := C)
      (hsym _ (N.normalAt_mem hv)) (hpos _ (N.normalAt_mem hv))
      (N.normalAt_fderiv_injective hv)
      (fun w => N.normalAt_gauss hS hG hsym hpos hv w) (hr t ht) hrd
    rw [heq, ← hcd]
    exact hsp t ht
  have hlin := RadialRigidity.radial_linear hU hUc ha hν₀
    (fun t ht => (hνd t ht).hasDerivAt) hrad
  intro t ht
  have hh := e.right_inv (hct t ht)
  change e (ν t) = c t at hh
  rw [hlin t ht, hνa, smul_smul] at hh
  simpa only [div_eq_mul_inv] using hh.symm
end
end NormalNeighborhood.NormalFlow
end

end WeakMTWGlobalSupport

end OAI
