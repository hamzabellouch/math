import OAI.Geometry.Relativity.CKS.SchwarzschildAdvancedTime
import OAI.Geometry.Relativity.CKS.SchwarzschildConnection

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
lemma advancedMetric_apply (m : ℝ) (z a b : Spacetime) :
    advancedMetric m z a b = -schwarzschildH m ‖z.2‖ * a.1*b.1 +
      a.1 * ⟪radialUnit z.2,b.2⟫_ℝ + b.1 * ⟪radialUnit z.2,a.2⟫_ℝ +
      ⟪a.2,b.2⟫_ℝ - ⟪radialUnit z.2,a.2⟫_ℝ * ⟪radialUnit z.2,b.2⟫_ℝ := by
  change -schwarzschildH m ‖z.2‖ * (a.1*b.1) + a.1 * ⟪radialUnit z.2,b.2⟫_ℝ +
    ⟪radialUnit z.2,a.2⟫_ℝ * b.1 + ⟪a.2,b.2⟫_ℝ - ⟪radialUnit z.2,a.2⟫_ℝ * ⟪radialUnit z.2,b.2⟫_ℝ = _
  ring
lemma H_lapse {m r : ℝ} (hm : 0 < m) (hr : 2*m ≤ r) :
    schwarzschildH m r = (lapse m r)^2-(velocity m r)^2 := by
  rw [lapse_sq hm hr]
  simp only [schwarzschildH,lapseSquared]
  ring
lemma H_factor {m r : ℝ} (hm : 0 < m) (hr : 2*m ≤ r) :
    schwarzschildH m r = (lapse m r-velocity m r)*(lapse m r+velocity m r) := by
  rw [H_lapse hm hr]
  ring
lemma advancedSlope_identity {m r : ℝ} (hm : 0 < m) (hr : 2*m ≤ r) :
    -schwarzschildH m r*(advancedSlope m r)^2+2*advancedSlope m r = (lapseSquared m r)⁻¹ := by
  have hh : m < r := lt_of_lt_of_le (by linarith) hr
  have hu := ne_of_gt (lapse_pos hm hr)
  have hq := ne_of_gt (lapse_sub_velocity_pos hm hh)
  rw [H_factor hm hr,advancedSlope,← lapse_sq hm hr]
  field_simp
  ring
lemma graph_induced_metric {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) (a b : E3) :
    advancedMetric m (advancedGraph m x) (graphTangent m x a) (graphTangent m x b) = cartMetric m x a b := by
  rw [advancedMetric_apply,cartMetric_apply]
  change -schwarzschildH m ‖x‖*(advancedSlope m ‖x‖ * ⟪radialUnit x,a⟫_ℝ)*(advancedSlope m ‖x‖ * ⟪radialUnit x,b⟫_ℝ) +
    advancedSlope m ‖x‖ * ⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ +
    advancedSlope m ‖x‖ * ⟪radialUnit x,b⟫_ℝ * ⟪radialUnit x,a⟫_ℝ + ⟪a,b⟫_ℝ -
    ⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ = _
  linear_combination (⟪radialUnit x,a⟫_ℝ * ⟪radialUnit x,b⟫_ℝ) * advancedSlope_identity hm hr
lemma futureNormal_unit {m : ℝ} (hm : 0 < m) {z : Spacetime} (hr : 2*m ≤ ‖z.2‖) :
    advancedMetric m z (futureNormal m z) (futureNormal m z) = -1 := by
  have hx : z.2 ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hr)
  have hq := ne_of_gt (lapse_sub_velocity_pos hm (lt_of_lt_of_le (by linarith) hr))
  rw [advancedMetric_apply]
  simp only [futureNormal,inner_smul_right,real_inner_smul_left,radialUnit_inner_self hx,mul_one]
  rw [H_factor hm hr]
  field_simp
  ring
lemma futureNormal_orthogonal {m : ℝ} (hm : 0 < m) {x : E3} (hr : 2*m ≤ ‖x‖) (a : E3) :
    advancedMetric m (advancedGraph m x) (futureNormal m (advancedGraph m x)) (graphTangent m x a) = 0 := by
  have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hr)
  have hq := ne_of_gt (lapse_sub_velocity_pos hm (lt_of_lt_of_le (by linarith) hr))
  have hu := ne_of_gt (lapse_pos hm hr)
  rw [advancedMetric_apply]
  simp only [futureNormal,advancedGraph,graphTangent,inner_smul_right,real_inner_smul_left,radialUnit_inner_self hx,mul_one]
  rw [H_factor hm hr,advancedSlope]
  field_simp
  ring
lemma futureNormal_future {m : ℝ} (hm : 0 < m) {z : Spacetime} (hr : 2*m ≤ ‖z.2‖) :
    0 < (futureNormal m z).1 := by
  exact inv_pos.mpr (lapse_sub_velocity_pos hm (lt_of_lt_of_le (by linarith) hr))
end CKSSchwarzschild

end

end OAI
