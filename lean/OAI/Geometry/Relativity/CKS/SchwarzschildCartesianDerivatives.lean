import OAI.Geometry.Relativity.CKS.SchwarzschildMetric
import OAI.Geometry.Relativity.CKS.SchwarzschildConnectionDefinitions

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma norm_derivative {x : E3} (hx : x ≠ 0) (a : E3) :
    fderiv ℝ (fun y : E3 => ‖y‖) x a = ⟪radialUnit x,a⟫_ℝ := by
  have hn := (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) x).differentiableAt one_ne_zero
  have he := congrArg (fun L : E3 →L[ℝ] ℝ => L a) (hn.hasFDerivAt.pow 2).fderiv
  rw [fderiv_norm_sq_apply] at he
  simp only [smul_apply,smul_eq_mul,innerSL_apply_apply,
    show (2:ℕ)-1=1 by norm_num,pow_one,nsmul_eq_mul,Nat.cast_ofNat] at he
  change 2 * ⟪x,a⟫_ℝ = 2 * ‖x‖ * (fderiv ℝ (fun y : E3 => ‖y‖) x) a at he
  simp only [radialUnit,real_inner_smul_left]
  have hp := norm_pos_iff.mpr hx
  field_simp
  nlinarith

lemma radialUnit_derivative {x : E3} (hx : x ≠ 0) (a : E3) :
    fderiv ℝ radialUnit x a = ‖x‖⁻¹ • (a-⟪radialUnit x,a⟫_ℝ • radialUnit x) := by
  have hn := (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) x).differentiableAt one_ne_zero
  have h := ((hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).hasFDerivAt.comp x hn.hasFDerivAt).smul (hasFDerivAt_id x)
  rw [show fderiv ℝ radialUnit x = _ from h.fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,
    smul_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  rw [norm_derivative hx,radialUnit]
  simp only [Function.comp_def,id_eq]
  module

lemma radial_inner_derivative {x : E3} (hx : x ≠ 0) (a b : E3) :
    fderiv ℝ (fun y => ⟪radialUnit y,b⟫_ℝ) x a =
      (⟪a,b⟫_ℝ - ⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ)/‖x‖ := by
  rw [fderiv_inner_apply ℝ ((radialUnit_smoothAt hx).differentiableAt (by simp)) (differentiableAt_const b)]
  simp only [fderiv_const_apply,zero_apply,inner_zero_right,zero_add]
  rw [radialUnit_derivative hx,real_inner_smul_left,inner_sub_left,real_inner_smul_left]
  simp only [div_eq_mul_inv]
  ring

lemma radial_metric_derivative {x : E3} (hx : x ≠ 0) (c : E3 → ℝ)
    (hc : DifferentiableAt ℝ c x) (a b d : E3) :
    fderiv ℝ (fun y => ⟪a,b⟫_ℝ + c y*(⟪radialUnit y,a⟫_ℝ * ⟪radialUnit y,b⟫_ℝ)) x d =
      fderiv ℝ c x d * (⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ) +
      c x / ‖x‖ * ((⟪d,a⟫_ℝ - ⟪radialUnit x,d⟫_ℝ * ⟪radialUnit x,a⟫_ℝ)*⟪radialUnit x,b⟫_ℝ +
        ⟪radialUnit x,a⟫_ℝ * (⟪d,b⟫_ℝ - ⟪radialUnit x,d⟫_ℝ * ⟪radialUnit x,b⟫_ℝ)) := by
  have ha := ((radialUnit_smoothAt hx).differentiableAt (by simp)).inner ℝ (differentiableAt_const (c := a))
  have hb := ((radialUnit_smoothAt hx).differentiableAt (by simp)).inner ℝ (differentiableAt_const (c := b))
  have h := (hasFDerivAt_const (⟪a,b⟫_ℝ) x).add (hc.hasFDerivAt.mul (ha.hasFDerivAt.mul hb.hasFDerivAt))
  rw [show fderiv ℝ (fun y => ⟪a,b⟫_ℝ + c y*(⟪radialUnit y,a⟫_ℝ * ⟪radialUnit y,b⟫_ℝ)) x = _ from h.fderiv]
  simp only [add_apply,smul_apply,zero_add,smul_eq_mul]
  rw [radial_inner_derivative hx,radial_inner_derivative hx]
  simp only [Pi.mul_apply]
  ring

lemma radialNormal_derivative {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) (a : E3) :
    fderiv ℝ (radialNormal m) x a =
      (deriv (lapse m) ‖x‖ * ⟪radialUnit x,a⟫_ℝ) • radialUnit x +
        (lapse m ‖x‖ / ‖x‖) • tangentProjection x a := by
  have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hr)
  have hn := (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) x).differentiableAt one_ne_zero
  have hu := (lapse_smoothAt hm hr).differentiableAt (by simp)
  have h := (hu.hasDerivAt.hasFDerivAt.comp x hn.hasFDerivAt).smul
    ((radialUnit_smoothAt hx).differentiableAt (by simp)).hasFDerivAt
  rw [show fderiv ℝ (radialNormal m) x = _ from h.fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,
    smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  rw [norm_derivative hx,radialUnit_derivative hx]
  simp only [tangentProjection,smul_smul,div_eq_mul_inv]
  simp only [Function.comp_def]
  module
end CKSSchwarzschild

end

end OAI
