import OAI.Geometry.Relativity.CKS.SchwarzschildAdvancedTime

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
lemma radial_field_derivative {f : ℝ → ℝ} {x : E3} (hx : x ≠ 0)
    (hf : DifferentiableAt ℝ f ‖x‖) (a : E3) :
    fderiv ℝ (fun y : E3 => f ‖y‖ • radialUnit y) x a =
      (deriv f ‖x‖ * ⟪radialUnit x,a⟫_ℝ) • radialUnit x +
        (f ‖x‖ / ‖x‖) • tangentProjection x a := by
  have hn := (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) x).differentiableAt one_ne_zero
  have h := (hf.hasDerivAt.hasFDerivAt.comp x hn.hasFDerivAt).smul
    ((radialUnit_smoothAt hx).differentiableAt (by simp)).hasFDerivAt
  rw [show fderiv ℝ (fun y : E3 => f ‖y‖ • radialUnit y) x = _ from h.fderiv]
  simp only [_root_.add_apply,ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  rw [norm_derivative hx,radialUnit_derivative hx]
  simp only [tangentProjection,smul_smul,div_eq_mul_inv,Function.comp_def]
  module
lemma futureNormal_derivative {m : ℝ} (hm : 0 < m) {z : Spacetime} (hr : m < ‖z.2‖) (a : Spacetime) :
    fderiv ℝ (futureNormal m) z a =
    (((deriv (velocity m) ‖z.2‖-deriv (lapse m) ‖z.2‖)/(lapse m ‖z.2‖-velocity m ‖z.2‖)^2) * ⟪radialUnit z.2,a.2⟫_ℝ,
      (deriv (velocity m) ‖z.2‖ * ⟪radialUnit z.2,a.2⟫_ℝ) • radialUnit z.2 +
        (velocity m ‖z.2‖ / ‖z.2‖) • tangentProjection z.2 a.2) := by
  have hx := norm_pos_iff.mp (lt_trans hm hr)
  have hn := (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) z.2).differentiableAt one_ne_zero
  have hu := (lapse_smooth_extended hm hr).differentiableAt (by simp)
  have hv := (velocity_smooth m).differentiable (by simp) ‖z.2‖
  have hq := (hu.hasDerivAt.sub hv.hasDerivAt).inv (ne_of_gt (lapse_sub_velocity_pos hm hr))
  have hF := (hq.hasFDerivAt.comp z.2 hn.hasFDerivAt).comp z spacePart.hasFDerivAt
  have hS := ((hv.comp z.2 hn).smul
    ((radialUnit_smoothAt hx).differentiableAt (by simp))).hasFDerivAt.comp z spacePart.hasFDerivAt
  have h := hF.prodMk hS
  rw [show fderiv ℝ (futureNormal m) z = _ from h.fderiv]
  simp only [ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  change ((spacePart a |> fderiv ℝ (fun y : E3 => ‖y‖) z.2) *
      (-(deriv (lapse m) ‖z.2‖-deriv (velocity m) ‖z.2‖)/(lapse m ‖z.2‖-velocity m ‖z.2‖)^2),
    fderiv ℝ (fun y : E3 => velocity m ‖y‖ • radialUnit y) z.2 a.2) = _
  rw [radial_field_derivative hx hv,norm_derivative hx]
  apply Prod.ext
  · change ⟪radialUnit z.2,a.2⟫_ℝ * _ = _
    ring
  · rfl
end CKSSchwarzschild

end

end OAI
