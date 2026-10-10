import OAI.Geometry.RCD.Transport.MaximalMidpointCompression

namespace OAI

/-! # Actual half nodes with their sharper inherited compression budget -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.maximal_compression_children
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    (a : RenyiTransportNode n X) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {q : ℝ} (hq0 : 0<q) (hq1 : q<1)
    (hm : RenyiMaximizingPlan (hausdorff n X) a.left a.right π midpointTime q) :
    ∃ a₀ a₁ : RenyiTransportNode n X,
      a₀.left=π.map (fun γ => γ 0) ∧ a₀.right=π.map (fun γ => γ midpointTime) ∧
      a₁.left=π.map (fun γ => γ midpointTime) ∧ a₁.right=π.map (fun γ => γ 1) ∧
      a₀.distance=a.distance/2 ∧ a₁.distance=a.distance/2 ∧
      a₀.capacity=compressionStep K n a.distance a.capacity ∧
      a₁.capacity=compressionStep K n a.distance a.capacity := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  let : Nonempty X := ⟨a.center⟩
  let := a.left_probability
  let := a.right_probability
  have he := optimalPlan_endpoints a.left a.right π hp
  have hpp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))) := by rw [he.1,he.2]; exact hp
  have hfin := finite_second_moment_cost
    (finiteSecondMoment_of_bounded a.left a.center a.left_support)
    (finiteSecondMoment_of_bounded a.right a.center a.right_support) hp.1 hp.2.1
  have hDa : OptimalPlanDistanceBound (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1)) a.distance := by
    rw [he.1,he.2]; exact a.distance_bound
  have hD := OptimalPlanDistanceBound.midpoint_halves π hg hpp hfin hDa
  let C := compressionStep K n a.distance a.capacity
  have hC : C≠∞ := compressionStep_ne_top K n a.distance a.capacity_finite
  have hinc : a.capacity≤C := le_compressionStep K n a.distance a.capacity (Nat.cast_nonneg _) a.distance_nonneg
  have h0 : π.map (fun γ => γ 0)≤C • hausdorff n X := by
    rw [he.1]
    exact a.left_bound.trans (by intro B; exact mul_le_mul' hinc le_rfl)
  have h1 : π.map (fun γ => γ 1)≤C • hausdorff n X := by
    rw [he.2]
    exact a.right_bound.trans (by intro B; exact mul_le_mul' hinc le_rfl)
  have hmid : π.map (fun γ => γ midpointTime)≤C • hausdorff n X :=
    (hX.maximal_midpoint_compressed K n hn a π hg hp hq0 hq1 hm).trans
      (by intro B; exact mul_le_mul' (midpointCapacity_le_compressionStep K n a.distance a.capacity
        (Nat.cast_nonneg _) a.distance_nonneg) le_rfl)
  have hs (t : Time) : ∀ᵐ x ∂π.map (fun γ => γ t), dist x a.center≤3*a.radius := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable
      (measurableSet_le (measurable_id.dist measurable_const) measurable_const)).mpr
    exact (optimal_geodesic_plan_bounded a.left a.right π hg hp a.center a.radius_nonneg
      a.left_support a.right_support).mono (fun γ hγ => hγ.2 t)
  let a₀ : RenyiTransportNode n X :=
    ⟨π.map (fun γ => γ 0),π.map (fun γ => γ midpointTime),inferInstance,inferInstance,
      a.center,3*a.radius,mul_nonneg (by norm_num) a.radius_nonneg,hs 0,hs midpointTime,
      C,hC,h0,hmid,a.distance/2,div_nonneg a.distance_nonneg (by norm_num),hD.1⟩
  let a₁ : RenyiTransportNode n X :=
    ⟨π.map (fun γ => γ midpointTime),π.map (fun γ => γ 1),inferInstance,inferInstance,
      a.center,3*a.radius,mul_nonneg (by norm_num) a.radius_nonneg,hs midpointTime,hs 1,
      C,hC,hmid,h1,a.distance/2,div_nonneg a.distance_nonneg (by norm_num),hD.2⟩
  exact ⟨a₀,a₁,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end RegularPointCoordinates

end

end OAI
