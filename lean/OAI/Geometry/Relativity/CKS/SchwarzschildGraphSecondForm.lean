import OAI.Geometry.Relativity.CKS.SchwarzschildSpacetimeDerivatives
import OAI.Geometry.Relativity.CKS.SchwarzschildNormalDerivative

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

lemma second_coefficient {u v du dv c : ℝ} (hu : u ≠ 0) (hq : u-v ≠ 0)
    (hid : u*du = c+v*dv) :
    -((u-v)*(u+v))*((dv-du)/(u-v)^2)*(u*(u-v))⁻¹ +
      (dv-du)/(u-v)^2 + (u*(u-v))⁻¹*dv-c*v*((u*(u-v))⁻¹)^2 = dv/u^2 := by
  field_simp
  linear_combination v * hid

lemma graph_metric_cross_derivatives {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) (a b : E3) :
    fderiv ℝ (fun y => advancedMetric m y (futureNormal m (advancedGraph m x)) (graphTangent m x b))
      (advancedGraph m x) (graphTangent m x a) =
    fderiv ℝ (fun y => advancedMetric m y (graphTangent m x a) (futureNormal m (advancedGraph m x)))
      (advancedGraph m x) (graphTangent m x b) := by
  have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hr)
  rw [advancedMetric_derivative hx,advancedMetric_derivative hx]
  simp only [advancedGraph,graphTangent,futureNormal,inner_smul_right,
    radialUnit_inner_self hx,mul_one,real_inner_comm a (radialUnit x),real_inner_comm b (radialUnit x),real_inner_comm b a]
  ring

lemma graph_metric_normal_derivative {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) (a b : E3) :
    fderiv ℝ (fun y => advancedMetric m y (graphTangent m x a) (graphTangent m x b))
      (advancedGraph m x) (futureNormal m (advancedGraph m x)) =
      -(2*m/‖x‖^2)*velocity m ‖x‖*(advancedSlope m ‖x‖)^2 *
        (⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ) := by
  have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hr)
  rw [advancedMetric_derivative hx]
  simp only [advancedGraph,graphTangent,futureNormal,inner_smul_right,real_inner_smul_left,
    radialUnit_inner_self hx,mul_one]
  ring

lemma advancedMetric_radial_pair {m : ℝ} {z : Spacetime} (hx : z.2 ≠ 0)
    (a b : E3) (A B C s : ℝ) :
    advancedMetric m z (A * ⟪radialUnit z.2,a⟫_ℝ,
        (B * ⟪radialUnit z.2,a⟫_ℝ) • radialUnit z.2 + C • tangentProjection z.2 a)
      (s * ⟪radialUnit z.2,b⟫_ℝ,b) =
      (-schwarzschildH m ‖z.2‖*A*s+A+s*B) * (⟪radialUnit z.2,a⟫_ℝ * ⟪radialUnit z.2,b⟫_ℝ) +
        C * (⟪a,b⟫_ℝ - ⟪radialUnit z.2,a⟫_ℝ * ⟪radialUnit z.2,b⟫_ℝ) := by
  rw [advancedMetric_apply]
  simp only [tangentProjection,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    inner_smul_right,real_inner_smul_left,radialUnit_inner_self hx,mul_one]
  ring

lemma futureNormal_graph_derivative {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) (a : E3) :
    fderiv ℝ (futureNormal m) (advancedGraph m x) (graphTangent m x a) =
    (((deriv (velocity m) ‖x‖-deriv (lapse m) ‖x‖)/(lapse m ‖x‖-velocity m ‖x‖)^2) * ⟪radialUnit x,a⟫_ℝ,
      (deriv (velocity m) ‖x‖ * ⟪radialUnit x,a⟫_ℝ) • radialUnit x +
        (velocity m ‖x‖ / ‖x‖) • tangentProjection x a) := by
  have hmx : m < ‖x‖ := lt_of_lt_of_le (by linarith) hr
  simpa only [advancedGraph, graphTangent] using
    (futureNormal_derivative hm (z := advancedGraph m x) hmx (graphTangent m x a))

lemma graph_normal_derivative_pair {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) (a b : E3) :
    advancedMetric m (advancedGraph m x)
      (fderiv ℝ (futureNormal m) (advancedGraph m x) (graphTangent m x a)) (graphTangent m x b) =
      (-schwarzschildH m ‖x‖*((deriv (velocity m) ‖x‖-deriv (lapse m) ‖x‖)/(lapse m ‖x‖-velocity m ‖x‖)^2)*advancedSlope m ‖x‖ +
        (deriv (velocity m) ‖x‖-deriv (lapse m) ‖x‖)/(lapse m ‖x‖-velocity m ‖x‖)^2 +
        advancedSlope m ‖x‖*deriv (velocity m) ‖x‖) * (⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ) +
      (velocity m ‖x‖ / ‖x‖) * (⟪a,b⟫_ℝ - ⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ) := by
  have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hr)
  rw [futureNormal_graph_derivative hm hr]
  simpa only [advancedGraph, graphTangent] using
    (advancedMetric_radial_pair (m := m) (z := advancedGraph m x) hx a b
      ((deriv (velocity m) ‖x‖-deriv (lapse m) ‖x‖)/(lapse m ‖x‖-velocity m ‖x‖)^2)
      (deriv (velocity m) ‖x‖) (velocity m ‖x‖ / ‖x‖) (advancedSlope m ‖x‖))

lemma graph_induced_second_form {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) (a b : E3) :
    covariantPair (advancedMetric m) (futureNormal m) (advancedGraph m x)
      (graphTangent m x a) (graphTangent m x b) = cartTensor m x a b := by
  rw [covariantPair,graph_metric_cross_derivatives hm hr,graph_metric_normal_derivative hm hr,
    graph_normal_derivative_pair hm hr]
  have hc := second_coefficient (ne_of_gt (lapse_pos hm hr))
    (ne_of_gt (lapse_sub_velocity_pos hm (lt_of_lt_of_le (by linarith) hr)))
    (lapse_deriv_identity hm (lt_of_lt_of_le (by linarith) hr))
  rw [← H_factor hm hr] at hc
  change -schwarzschildH m ‖x‖ * _ * advancedSlope m ‖x‖ + _ + advancedSlope m ‖x‖ * deriv (velocity m) ‖x‖ -
    m/‖x‖^2 * velocity m ‖x‖ * (advancedSlope m ‖x‖)^2 = deriv (velocity m) ‖x‖/(lapse m ‖x‖)^2 at hc
  change _ = velocity m ‖x‖ / ‖x‖ * ⟪a,b⟫_ℝ +
      (deriv (velocity m) ‖x‖ / lapseSquared m ‖x‖ - velocity m ‖x‖ / ‖x‖) *
      (⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ)
  rw [← lapse_sq hm hr]
  linear_combination (⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ) * hc
end CKSSchwarzschild

end

end OAI
