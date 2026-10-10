import OAI.Geometry.RCD.Coordinates.NormalizedOptimalSubplan
import OAI.Geometry.RCD.Transport.MaximalScalarMidpoint

namespace OAI

/-! # Bounded transport nodes for the actual normalized length components

Uniform compression of the parent controls both half-nodes. Their
transport-distance bounds are inherited at exactly half the parent scale.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [CompleteSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem exists_normalized_subplan_half_nodes {n : ℕ} (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X)
    (κ : Measure C(Time,X)) (hκ : κ≤π) (hκ0 : κ univ≠0) :
    ∃ a₀ a₁ : RenyiTransportNode n X,
      a₀.left=(κ univ)⁻¹ • κ.map (fun γ => γ 0) ∧
      a₀.right=(κ univ)⁻¹ • κ.map (fun γ => γ midpointTime) ∧
      a₁.left=(κ univ)⁻¹ • κ.map (fun γ => γ midpointTime) ∧
      a₁.right=(κ univ)⁻¹ • κ.map (fun γ => γ 1) ∧
      a₀.distance=a.distance/2 ∧ a₁.distance=a.distance/2 := by
  let : Nonempty X := ⟨a.center⟩
  let : IsProbabilityMeasure a.left := a.left_probability
  let : IsProbabilityMeasure a.right := a.right_probability
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le π hκ
  have hc : κ univ≠∞ := measure_ne_top κ univ
  have hi : (κ univ)⁻¹≠∞ := ENNReal.inv_ne_top.mpr hκ0
  have he := optimalPlan_endpoints a.left a.right π hp
  have hpp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))) := by rw [he.1,he.2]; exact hp
  have hfin := finite_second_moment_cost
    (finiteSecondMoment_of_bounded a.left a.center a.left_support)
    (finiteSecondMoment_of_bounded a.right a.center a.right_support) hp.1 hp.2.1
  let πn := (κ univ)⁻¹ • κ
  obtain ⟨hπn,hgn,hpn,hfn⟩ := normalized_optimal_subplan π hg hpp hfin κ hκ hκ0
  let : IsProbabilityMeasure πn := hπn
  have heval (t : Time) : πn.map (fun γ => γ t)=(κ univ)⁻¹ • κ.map (fun γ => γ t) :=
    Measure.map_smul _ (measurable_path_eval t).aemeasurable
  have hDn : OptimalPlanDistanceBound (πn.map (fun γ => γ 0))
      (πn.map (fun γ => γ 1)) a.distance := by
    rw [heval,heval]
    exact a.distance_bound.normalized_subplan π hg hp κ hκ hκ0
  have hD := OptimalPlanDistanceBound.midpoint_halves πn hgn hpn hfn hDn
  let c := (κ univ)⁻¹*C
  have hcf : c≠∞ := ENNReal.mul_ne_top hi hC
  have hcn (t : Time) : πn.map (fun γ => γ t)≤c • hausdorff n X := by
    rw [heval]
    intro B
    change (κ univ)⁻¹ * (κ.map (fun γ => γ t)) B ≤ c * (hausdorff n X) B
    calc
      _ ≤ (κ univ)⁻¹ * (π.map (fun γ => γ t)) B :=
        mul_le_mul' le_rfl (Measure.map_mono hκ (measurable_path_eval t) B)
      _ ≤ (κ univ)⁻¹ * (C*(hausdorff n X) B) := mul_le_mul' le_rfl (hcomp t B)
      _ = _ := (mul_assoc _ _ _).symm
  have hstay (t : Time) : ∀ᵐ x ∂πn.map (fun γ => γ t), dist x a.center≤3*a.radius := by
    rw [heval]
    have hs : ∀ᵐ x ∂π.map (fun γ => γ t), dist x a.center≤3*a.radius := by
      apply (ae_map_iff (measurable_path_eval t).aemeasurable
        (measurableSet_le (measurable_id.dist measurable_const) measurable_const)).mpr
      exact (optimal_geodesic_plan_bounded a.left a.right π hg hp a.center a.radius_nonneg
        a.left_support a.right_support).mono (fun γ hγ => hγ.2 t)
    exact (hs.filter_mono (Measure.map_mono hκ (measurable_path_eval t)).absolutelyContinuous.ae_le).filter_mono
      Measure.smul_absolutelyContinuous.ae_le
  let a₀ : RenyiTransportNode n X :=
    ⟨πn.map (fun γ => γ 0),πn.map (fun γ => γ midpointTime),inferInstance,inferInstance,
      a.center,3*a.radius,mul_nonneg (by norm_num) a.radius_nonneg,hstay 0,hstay midpointTime,
      c,hcf,hcn 0,hcn midpointTime,a.distance/2,div_nonneg a.distance_nonneg (by norm_num),hD.1⟩
  let a₁ : RenyiTransportNode n X :=
    ⟨πn.map (fun γ => γ midpointTime),πn.map (fun γ => γ 1),inferInstance,inferInstance,
      a.center,3*a.radius,mul_nonneg (by norm_num) a.radius_nonneg,hstay midpointTime,hstay 1,
      c,hcf,hcn midpointTime,hcn 1,a.distance/2,div_nonneg a.distance_nonneg (by norm_num),hD.2⟩
  exact ⟨a₀,a₁,heval 0,heval midpointTime,heval midpointTime,heval 1,rfl,rfl⟩

end RegularPointCoordinates

end

end OAI
