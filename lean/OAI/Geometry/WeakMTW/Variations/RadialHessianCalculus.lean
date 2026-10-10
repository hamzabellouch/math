import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.CoordinateGeometry
import OAI.Geometry.WeakMTW.Variations.QuadraticHessian

namespace OAI

namespace WeakMTWGlobalSupport

section

open Filter Set
open scoped Topology ContDiff
namespace RadialHessianCalculus
open CoordinateGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

 omit [FiniteDimensional ℝ E] in
 theorem coordinate_radial (G : E → MetricTensor E) (ν : E → E) (f : E → ℝ) {a : E}
    (hG : DifferentiableAt ℝ G a) (hν : DifferentiableAt ℝ ν a)
    (hf : ContDiffAt ℝ 2 f a)
    (hsym : ∀ v w, G a v w = G a w v)
    (henergy : f =ᶠ[𝓝 a] (fun r => G r (ν r) (ν r) / 2))
    (hgrad : ∀ᶠ r in 𝓝 a, ∀ w, fderiv ℝ f r w = -G r (ν r) w) (ξ : E) :
    fderiv ℝ (fderiv ℝ f) a ξ (ν a) =
      G a (ν a) ξ - fderiv ℝ G a ξ (ν a) (ν a) / 2 := by
  have hD := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have he : fderiv ℝ f a = fderiv ℝ (fun r => G r (ν r) (ν r) / 2) a := henergy.fderiv_eq
  have hQ := ((hG.clm_apply hν).clm_apply hν)
  have hQD : HasFDerivAt (fun r => G r (ν r) (ν r) / 2)
      ((1/2 : ℝ) • fderiv ℝ (fun r => G r (ν r) (ν r)) a) a := by
    convert! hQ.hasFDerivAt.const_smul (1/2 : ℝ) using 1
    ext r
    simp [smul_eq_mul,div_eq_mul_inv,mul_comm]
  have heval := congrArg (fun L : E →L[ℝ] ℝ => L ξ) he
  rw [hQD.fderiv, smul_apply,smul_eq_mul,
    QuadraticHessian.first G ν hG hν, hgrad.self_of_nhds] at heval
  rw [hsym (fderiv ℝ ν a ξ) (ν a)] at heval
  have hge : (fun r => fderiv ℝ f r (ν a)) =ᶠ[𝓝 a]
      (fun r => -G r (ν r) (ν a)) := hgrad.mono (fun _ h => h (ν a))
  have hleft := hD.hasFDerivAt.clm_apply (hasFDerivAt_const (ν a) a)
  have hright := ((hG.hasFDerivAt.clm_apply hν.hasFDerivAt).clm_apply
    (hasFDerivAt_const (ν a) a)).neg
  have hEq := congrArg (fun L : E →L[ℝ] ℝ => L ξ)
    (hleft.unique (hright.congr_of_eventuallyEq hge))
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, neg_apply,
    zero_apply, map_zero, zero_add] at hEq
  rw [hsym (fderiv ℝ ν a ξ) (ν a)] at hEq
  linarith

 theorem covariant_radial (G : E → MetricTensor E) (ν : E → E) (f : E → ℝ)
    {S : Set E} (hS : IsOpen S) (hG : DifferentiableOn ℝ G S)
    (hsym : ∀ r ∈ S, ∀ v w, G r v w = G r w v)
    {a : E} (ha : a ∈ S) (hpos : ∀ v : E, v ≠ 0 → 0 < G a v v)
    (hν : DifferentiableAt ℝ ν a) (hf : ContDiffAt ℝ 2 f a)
    (henergy : f =ᶠ[𝓝 a] (fun r => G r (ν r) (ν r) / 2))
    (hgrad : ∀ᶠ r in 𝓝 a, ∀ w, fderiv ℝ f r w = -G r (ν r) w) (ξ : E) :
    fderiv ℝ (fderiv ℝ f) a ξ (ν a) +
        G a (ν a) (christoffel G a ξ (ν a)) = G a ξ (ν a) := by
  have hr := coordinate_radial G ν f ((hG a ha).differentiableAt (hS.mem_nhds ha))
    hν hf (hsym a ha) henergy hgrad ξ
  have hc := metric_christoffel hpos ξ (ν a) (ν a)
  rw [derivative_metric_symmetric hS hG hsym ha (ν a) ξ (ν a)] at hc
  rw [hsym a ha (ν a) (christoffel G a ξ (ν a)),hc,hsym a ha ξ (ν a)]
  linarith

end RadialHessianCalculus
end

end WeakMTWGlobalSupport

end OAI
