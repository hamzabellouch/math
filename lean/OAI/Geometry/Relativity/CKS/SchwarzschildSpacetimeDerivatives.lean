import OAI.Geometry.Relativity.CKS.SchwarzschildSpacetimeAlgebra

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
lemma H_hasDerivAt {m r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (schwarzschildH m) (2*m/r^2) r := by
  have h : HasDerivAt (fun s : ℝ => 1-2*m/s) (0-(0*r-2*m*1)/r^2) r :=
    (hasDerivAt_const r (1:ℝ)).sub ((hasDerivAt_const r (2*m)).div (hasDerivAt_id r) hr)
  convert h using 1 <;> try rfl
  ring
lemma H_radial_derivative {m : ℝ} {x : E3} (hx : x ≠ 0) (a : E3) :
    fderiv ℝ (fun y : E3 => schwarzschildH m ‖y‖) x a =
      (2*m/‖x‖^2) * ⟪radialUnit x,a⟫_ℝ := by
  have hn := (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) x).differentiableAt one_ne_zero
  have h := (H_hasDerivAt (m := m) (norm_ne_zero_iff.mpr hx)).hasFDerivAt.comp x hn.hasFDerivAt
  rw [show fderiv ℝ (fun y : E3 => schwarzschildH m ‖y‖) x = _ from h.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,norm_derivative hx]
  ring
lemma lapse_deriv_identity {m r : ℝ} (hm : 0 < m) (hr : m < r) :
    lapse m r * deriv (lapse m) r = m/r^2 + velocity m r*deriv (velocity m) r := by
  have hu := (lapse_smooth_extended hm hr).differentiableAt (by simp)
  have hv := (velocity_smooth m).differentiable (by simp) r
  have h1 := hu.hasDerivAt.pow 2
  have h2 := (H_hasDerivAt (m := m) (ne_of_gt (lt_trans hm hr))).add (hv.hasDerivAt.pow 2)
  have he : (fun s => (lapse m s)^2) =ᶠ[𝓝 r] (fun s => schwarzschildH m s+(velocity m s)^2) := by
    filter_upwards [lt_mem_nhds hr] with s hs
    exact Real.sq_sqrt (lapseSquared_pos_extended hm hs).le
  have hh := (h1.congr_of_eventuallyEq he.symm).unique h2
  norm_num at hh
  linear_combination hh/2
lemma advancedMetric_spatial_derivative {m : ℝ} {x : E3} (hx : x ≠ 0) (a b : Spacetime) (d : E3) :
    fderiv ℝ (fun y : E3 => advancedMetric m (0,y) a b) x d =
      -(2*m/‖x‖^2) * ⟪radialUnit x,d⟫_ℝ * a.1*b.1 +
      (a.1- ⟪radialUnit x,a.2⟫_ℝ)/‖x‖ * (⟪d,b.2⟫_ℝ - ⟪radialUnit x,d⟫_ℝ * ⟪radialUnit x,b.2⟫_ℝ) +
      (b.1- ⟪radialUnit x,b.2⟫_ℝ)/‖x‖ * (⟪d,a.2⟫_ℝ - ⟪radialUnit x,d⟫_ℝ * ⟪radialUnit x,a.2⟫_ℝ) := by
  have hn := (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) x).differentiableAt one_ne_zero
  have hh := (H_hasDerivAt (m := m) (norm_ne_zero_iff.mpr hx)).differentiableAt.comp x hn
  have ha := ((radialUnit_smoothAt hx).differentiableAt (by simp)).inner ℝ (differentiableAt_const a.2)
  have hb := ((radialUnit_smoothAt hx).differentiableAt (by simp)).inner ℝ (differentiableAt_const b.2)
  have h := (((hh.hasFDerivAt.neg.mul_const a.1).mul_const b.1).add
    (hb.hasFDerivAt.const_mul a.1) |>.add (ha.hasFDerivAt.const_mul b.1) |>.add
    (hasFDerivAt_const (⟪a.2,b.2⟫_ℝ) x)).sub (ha.hasFDerivAt.mul hb.hasFDerivAt)
  have he : (fun y : E3 => advancedMetric m (0,y) a b) =
    (fun y => -schwarzschildH m ‖y‖ * a.1*b.1 + a.1 * ⟪radialUnit y,b.2⟫_ℝ +
      b.1 * ⟪radialUnit y,a.2⟫_ℝ + ⟪a.2,b.2⟫_ℝ - ⟪radialUnit y,a.2⟫_ℝ * ⟪radialUnit y,b.2⟫_ℝ) := by
    funext y
    exact advancedMetric_apply m _ _ _
  change HasFDerivAt (fun y : E3 => -schwarzschildH m ‖y‖ * a.1*b.1 + a.1 * ⟪radialUnit y,b.2⟫_ℝ +
      b.1 * ⟪radialUnit y,a.2⟫_ℝ + ⟪a.2,b.2⟫_ℝ - ⟪radialUnit y,a.2⟫_ℝ * ⟪radialUnit y,b.2⟫_ℝ) _ x at h
  rw [he, h.fderiv]
  simp only [sub_apply,add_apply,neg_apply,smul_apply,add_zero,smul_eq_mul,Function.comp_def]
  rw [H_radial_derivative hx,radial_inner_derivative hx,radial_inner_derivative hx]
  ring
lemma advancedMetric_derivative {m : ℝ} {z : Spacetime} (hx : z.2 ≠ 0) (a b d : Spacetime) :
    fderiv ℝ (fun y => advancedMetric m y a b) z d =
      -(2*m/‖z.2‖^2) * ⟪radialUnit z.2,d.2⟫_ℝ * a.1*b.1 +
      (a.1- ⟪radialUnit z.2,a.2⟫_ℝ)/‖z.2‖ * (⟪d.2,b.2⟫_ℝ - ⟪radialUnit z.2,d.2⟫_ℝ * ⟪radialUnit z.2,b.2⟫_ℝ) +
      (b.1- ⟪radialUnit z.2,b.2⟫_ℝ)/‖z.2‖ * (⟪d.2,a.2⟫_ℝ - ⟪radialUnit z.2,d.2⟫_ℝ * ⟪radialUnit z.2,a.2⟫_ℝ) := by
  have hn := (contDiffAt_norm ℝ hx : ContDiffAt ℝ 1 (fun y : E3 => ‖y‖) z.2).differentiableAt one_ne_zero
  have hh := (H_hasDerivAt (m := m) (norm_ne_zero_iff.mpr hx)).differentiableAt.comp z.2 hn
  have ha := ((radialUnit_smoothAt hx).differentiableAt (by simp)).inner ℝ (differentiableAt_const a.2)
  have hb := ((radialUnit_smoothAt hx).differentiableAt (by simp)).inner ℝ (differentiableAt_const b.2)
  have hs : DifferentiableAt ℝ (fun y : E3 => advancedMetric m (0,y) a b) z.2 := by
    simp_rw [advancedMetric_apply]
    exact ((((hh.neg.mul_const a.1).mul_const b.1).add (hb.const_mul a.1)).add (ha.const_mul b.1) |>.add (differentiableAt_const (⟪a.2,b.2⟫_ℝ))).sub (ha.mul hb)
  have h := hs.hasFDerivAt.comp z (spacePart.hasFDerivAt)
  rw [show fderiv ℝ (fun y => advancedMetric m y a b) z = _ from h.fderiv]
  change fderiv ℝ (fun y : E3 => advancedMetric m (0,y) a b) z.2 d.2 = _
  exact advancedMetric_spatial_derivative hx a b d.2
end CKSSchwarzschild

end

end OAI
