import OAI.Geometry.Relativity.CKS.SchwarzschildGraphSecondForm

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface

theorem future_horizon_realization {m : ℝ} (hm : 0 < m) :
    ContDiffOn ℝ ∞ (advancedTime m) (Ioi m) ∧
    (∀ x : E3, m < ‖x‖ → fderiv ℝ (advancedGraph m) x =
      ((ContinuousLinearMap.toSpanSingleton ℝ (advancedSlope m ‖x‖)).comp
        (innerSL ℝ (radialUnit x)) ).prod (ContinuousLinearMap.id ℝ E3)) ∧
    (∀ x : E3, 2*m ≤ ‖x‖ → ∀ a b : E3,
      advancedMetric m (advancedGraph m x) (graphTangent m x a) (graphTangent m x b) = cartMetric m x a b) ∧
    (∀ x : E3, 2*m ≤ ‖x‖ →
      advancedMetric m (advancedGraph m x) (futureNormal m (advancedGraph m x))
        (futureNormal m (advancedGraph m x)) = -1) ∧
    (∀ x : E3, 2*m ≤ ‖x‖ → ∀ a b : E3,
      covariantPair (advancedMetric m) (futureNormal m) (advancedGraph m x)
        (graphTangent m x a) (graphTangent m x b) = cartTensor m x a b) := by
  refine ⟨advancedTime_smooth hm,?_,fun _ h => graph_induced_metric hm h,
    fun _ h => futureNormal_unit hm h,fun _ h => graph_induced_second_form hm h⟩
  intro x hx
  apply ContinuousLinearMap.ext
  intro a
  rw [advancedGraph_derivative hm hx]
  apply Prod.ext
  · change advancedSlope m ‖x‖ * ⟪radialUnit x,a⟫_ℝ =
      ⟪radialUnit x,a⟫_ℝ * advancedSlope m ‖x‖
    ring
  · rfl

lemma radialNormal_unit {m : ℝ} (hm : 0 < m) {x : E3} (hx : 2*m ≤ ‖x‖) :
    cartMetric m x (radialNormal m x) (radialNormal m x) = 1 := by
  have hn : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hx)
  rw [cartMetric_apply]
  simp only [radialNormal,inner_smul_right,real_inner_smul_left,radialUnit_inner_self hn,mul_one]
  rw [← lapse_sq hm hx]
  have hu := ne_of_gt (lapse_pos hm hx)
  field_simp
  ring
lemma radialNormal_points_out {m : ℝ} (hm : 0 < m) {x : E3} (hx : 2*m ≤ ‖x‖) :
    0 < fderiv ℝ (fun y : E3 => ‖y‖) x (radialNormal m x) := by
  have hn : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hx)
  rw [norm_derivative hn]
  simp only [radialNormal,inner_smul_right,radialUnit_inner_self hn,mul_one]
  exact lapse_pos hm hx
lemma radialNormal_orthogonal (m : ℝ) {x a : E3} (ha : ⟪radialUnit x,a⟫_ℝ = 0) :
    cartMetric m x (radialNormal m x) a = 0 := by
  rw [cartMetric_apply]
  simp only [radialNormal,real_inner_smul_left,ha,mul_zero,zero_add]
end CKSSchwarzschild

end

end OAI
