import OAI.Geometry.RCD.Transport.RenyiTransportNode

namespace OAI

/-! # The two children of a fixed maximal transport midpoint -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [CompleteSpace X]
attribute [local instance] pathBorel pathBorelSpace

noncomputable def RenyiNodeSplit.children {n : ℕ} {K q : ℝ}
    {a : RenyiTransportNode n X} (s : RenyiNodeSplit K q a) :
    RenyiTransportNode n X × RenyiTransportNode n X := by
  let : Nonempty X := ⟨a.center⟩
  let := a.left_probability
  let := a.right_probability
  let := s.probability
  let νm := s.plan.map (fun γ => γ midpointTime)
  have hνm : IsProbabilityMeasure νm := inferInstance
  have he := optimalPlan_endpoints a.left a.right s.plan s.optimal
  have hp : IsOptimalCoupling (s.plan.map (fun γ => γ 0)) (s.plan.map (fun γ => γ 1))
      (s.plan.map (fun γ => (γ 0,γ 1))) := by
    rw [he.1,he.2]
    exact s.optimal
  have hm0 := finiteSecondMoment_of_bounded a.left a.center a.left_support
  have hm1 := finiteSecondMoment_of_bounded a.right a.center a.right_support
  have hfin := finite_second_moment_cost hm0 hm1 s.optimal.1 s.optimal.2.1
  have hD : OptimalPlanDistanceBound (s.plan.map (fun γ => γ 0)) (s.plan.map (fun γ => γ 1))
      a.distance := by
    rw [he.1,he.2]
    exact a.distance_bound
  have hdists := OptimalPlanDistanceBound.midpoint_halves s.plan s.geodesic hp hfin hD
  have hDl := hdists.1
  have hDr := hdists.2
  rw [he.1] at hDl
  rw [he.2] at hDr
  let C := compressionStep K n a.distance a.capacity
  have hC : C ≠ ∞ := compressionStep_ne_top K n a.distance a.capacity_finite
  have hinc : a.capacity ≤ C := le_compressionStep K n a.distance a.capacity
    (Nat.cast_nonneg n) a.distance_nonneg
  have h0 : a.left ≤ C • hausdorff n X := a.left_bound.trans (by
    intro S
    exact mul_le_mul_left hinc _)
  have h1 : a.right ≤ C • hausdorff n X := a.right_bound.trans (by
    intro S
    exact mul_le_mul_left hinc _)
  have hm : νm ≤ C • hausdorff n X := s.compressed.trans (by
    intro S
    exact mul_le_mul_left (midpointCapacity_le_compressionStep K n a.distance a.capacity
      (Nat.cast_nonneg n) a.distance_nonneg) _)
  have hsm : ∀ᵐ x ∂νm, dist x a.center ≤ 3*a.radius := by
    apply (ae_map_iff (measurable_path_eval midpointTime).aemeasurable
      (measurableSet_le (measurable_id.dist measurable_const) measurable_const)).mpr
    exact (optimal_geodesic_plan_bounded a.left a.right s.plan s.geodesic s.optimal
      a.center a.radius_nonneg a.left_support a.right_support).mono (fun _ h => h.2 midpointTime)
  have hs0 : ∀ᵐ x ∂a.left, dist x a.center ≤ 3*a.radius := a.left_support.mono
    (fun _ h => by linarith [a.radius_nonneg])
  have hs1 : ∀ᵐ x ∂a.right, dist x a.center ≤ 3*a.radius := a.right_support.mono
    (fun _ h => by linarith [a.radius_nonneg])
  exact (⟨a.left,νm,a.left_probability,hνm,a.center,3*a.radius,mul_nonneg (by norm_num) a.radius_nonneg,hs0,hsm,
    C,hC,h0,hm,a.distance/2,div_nonneg a.distance_nonneg (by norm_num),hDl⟩,
    ⟨νm,a.right,hνm,a.right_probability,a.center,3*a.radius,mul_nonneg (by norm_num) a.radius_nonneg,hsm,hs1,
    C,hC,hm,h1,a.distance/2,div_nonneg a.distance_nonneg (by norm_num),hDr⟩)

noncomputable def RenyiNodeSplit.leftNode {n : ℕ} {K q : ℝ}
    {a : RenyiTransportNode n X} (s : RenyiNodeSplit K q a) : RenyiTransportNode n X := s.children.1

noncomputable def RenyiNodeSplit.rightNode {n : ℕ} {K q : ℝ}
    {a : RenyiTransportNode n X} (s : RenyiNodeSplit K q a) : RenyiTransportNode n X := s.children.2

@[simp] theorem RenyiNodeSplit.leftNode_left {n : ℕ} {K q : ℝ} {a : RenyiTransportNode n X}
    (s : RenyiNodeSplit K q a) : s.leftNode.left=a.left := rfl
@[simp] theorem RenyiNodeSplit.leftNode_right {n : ℕ} {K q : ℝ} {a : RenyiTransportNode n X}
    (s : RenyiNodeSplit K q a) : s.leftNode.right=s.plan.map (fun γ => γ midpointTime) := rfl
@[simp] theorem RenyiNodeSplit.rightNode_left {n : ℕ} {K q : ℝ} {a : RenyiTransportNode n X}
    (s : RenyiNodeSplit K q a) : s.rightNode.left=s.plan.map (fun γ => γ midpointTime) := rfl
@[simp] theorem RenyiNodeSplit.rightNode_right {n : ℕ} {K q : ℝ} {a : RenyiTransportNode n X}
    (s : RenyiNodeSplit K q a) : s.rightNode.right=a.right := rfl
@[simp] theorem RenyiNodeSplit.leftNode_capacity {n : ℕ} {K q : ℝ} {a : RenyiTransportNode n X}
    (s : RenyiNodeSplit K q a) : s.leftNode.capacity=compressionStep K n a.distance a.capacity := rfl
@[simp] theorem RenyiNodeSplit.rightNode_capacity {n : ℕ} {K q : ℝ} {a : RenyiTransportNode n X}
    (s : RenyiNodeSplit K q a) : s.rightNode.capacity=compressionStep K n a.distance a.capacity := rfl
@[simp] theorem RenyiNodeSplit.leftNode_distance {n : ℕ} {K q : ℝ} {a : RenyiTransportNode n X}
    (s : RenyiNodeSplit K q a) : s.leftNode.distance=a.distance/2 := rfl
@[simp] theorem RenyiNodeSplit.rightNode_distance {n : ℕ} {K q : ℝ} {a : RenyiTransportNode n X}
    (s : RenyiNodeSplit K q a) : s.rightNode.distance=a.distance/2 := rfl

end RegularPointCoordinates

end

end OAI
