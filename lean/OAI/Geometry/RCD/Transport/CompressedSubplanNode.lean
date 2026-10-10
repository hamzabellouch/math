import OAI.Geometry.RCD.Transport.OptimalInitialSubmeasure
import OAI.Geometry.RCD.Coordinates.NormalizedOptimalSubplan

namespace OAI

/-! # A transport node at the actual length scale of a compressed component -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem normalized_subplan_compression [SeparableSpace X]
    (π κ : Measure C(Time,X)) (hκ : κ≤π) {C : ℝ≥0∞} {μ : Measure X}
    (hc : ∀ t : Time, π.map (fun γ => γ t)≤C • μ) :
    ∀ t : Time, ((κ univ)⁻¹ • κ).map (fun γ => γ t)≤((κ univ)⁻¹*C) • μ := by
  intro t
  rw [Measure.map_smul _ (measurable_path_eval t).aemeasurable]
  intro B
  change (κ univ)⁻¹*(κ.map (fun γ => γ t)) B≤((κ univ)⁻¹*C)*μ B
  calc
    _ ≤ (κ univ)⁻¹*(π.map (fun γ => γ t)) B :=
      mul_le_mul' le_rfl (Measure.map_mono hκ (measurable_path_eval t) B)
    _ ≤ (κ univ)⁻¹*(C*μ B) := mul_le_mul' le_rfl (hc t B)
    _ = _ := (mul_assoc _ _ _).symm

theorem NoncollapsedRCD.compressed_subplan_node
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    (a : RenyiTransportNode n X) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hc : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X)
    (κ : Measure C(Time,X)) (hκ : κ≤π) (hκ0 : κ univ≠0)
    {D : ℝ} (hD0 : 0≤D) (hD : ∀ᵐ γ ∂κ, dist (γ 0) (γ 1)≤D) :
    ∃ b : RenyiTransportNode n X,
      b.left=(κ univ)⁻¹ • κ.map (fun γ => γ 0) ∧
      b.right=(κ univ)⁻¹ • κ.map (fun γ => γ 1) ∧ b.distance=D := by
  let : SeparableSpace X := hX.separable
  let := a.left_probability
  let := a.right_probability
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le π hκ
  have hi : (κ univ)⁻¹≠∞ := ENNReal.inv_ne_top.mpr hκ0
  have he := optimalPlan_endpoints a.left a.right π hp
  have hpp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))) := by rw [he.1,he.2]; exact hp
  have hfin := finite_second_moment_cost
    (finiteSecondMoment_of_bounded a.left a.center a.left_support)
    (finiteSecondMoment_of_bounded a.right a.center a.right_support) hp.1 hp.2.1
  let πn := (κ univ)⁻¹ • κ
  obtain ⟨hπn,hgn,hpn,_⟩ := normalized_optimal_subplan π hg hpp hfin κ hκ hκ0
  let : IsProbabilityMeasure πn := hπn
  have heval (t : Time) : πn.map (fun γ => γ t)=(κ univ)⁻¹ • κ.map (fun γ => γ t) :=
    Measure.map_smul _ (measurable_path_eval t).aemeasurable
  let c := (κ univ)⁻¹*C
  have hcf : c≠∞ := ENNReal.mul_ne_top hi hC
  have hcn (t : Time) : πn.map (fun γ => γ t)≤c • hausdorff n X :=
    normalized_subplan_compression π κ hκ hc t
  have hstay (t : Time) (ht : t=0 ∨ t=1) :
      ∀ᵐ x ∂πn.map (fun γ => γ t), dist x a.center≤a.radius := by
    rw [heval]
    have hs : ∀ᵐ x ∂π.map (fun γ => γ t), dist x a.center≤a.radius := by
      rcases ht with rfl | rfl
      · rw [he.1]; exact a.left_support
      · rw [he.2]; exact a.right_support
    exact (hs.filter_mono (Measure.map_mono hκ (measurable_path_eval t)).absolutelyContinuous.ae_le).filter_mono
      Measure.smul_absolutelyContinuous.ae_le
  let b : RenyiTransportNode n X :=
    ⟨πn.map (fun γ => γ 0),πn.map (fun γ => γ 1),inferInstance,inferInstance,
      a.center,a.radius,a.radius_nonneg,hstay 0 (Or.inl rfl),hstay 1 (Or.inr rfl),
      c,hcf,hcn 0,hcn 1,2*a.radius,mul_nonneg (by norm_num) a.radius_nonneg,
      optimalPlanDistanceBound_of_bounded _ _ a.center (hstay 0 (Or.inl rfl)) (hstay 1 (Or.inr rfl))⟩
  have hDn : ∀ᵐ γ ∂πn, dist (γ 0) (γ 1)≤D :=
    hD.filter_mono Measure.smul_absolutelyContinuous.ae_le
  have hbD := hX.compressed_optimal_distance_bound K n hn b πn hgn hpn hcf hcn hDn
  let bD : RenyiTransportNode n X := { b with distance:=D, distance_nonneg:=hD0, distance_bound:=hbD }
  exact ⟨bD,heval 0,heval 1,rfl⟩

end RegularPointCoordinates

end

end OAI
