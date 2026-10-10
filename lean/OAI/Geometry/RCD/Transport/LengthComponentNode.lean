import OAI.Geometry.RCD.Transport.CompressedSubplanNode

namespace OAI

/-! # Component nodes retain the original endpoint density budget -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.compressed_subplan_node_capacity
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    (a : RenyiTransportNode n X) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hc : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X)
    (κ : Measure C(Time,X)) (hκ : κ≤π) (hκ0 : κ univ≠0)
    {D : ℝ} (hD0 : 0≤D) (hD : ∀ᵐ γ ∂κ, dist (γ 0) (γ 1)≤D) :
    ∃ b : RenyiTransportNode n X,
      b.left=(κ univ)⁻¹ • κ.map (fun γ => γ 0) ∧
      b.right=(κ univ)⁻¹ • κ.map (fun γ => γ 1) ∧ b.distance=D ∧
      b.capacity=(κ univ)⁻¹*a.capacity := by
  let : SeparableSpace X := hX.separable
  obtain ⟨b,hb0,hb1,hbD⟩ := hX.compressed_subplan_node K n hn a π hg hp hC hc κ hκ hκ0 hD0 hD
  have he := optimalPlan_endpoints a.left a.right π hp
  let c := (κ univ)⁻¹*a.capacity
  have hcf : c≠∞ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hκ0) a.capacity_finite
  have hend (t : Time) (ht : t=0 ∨ t=1) : π.map (fun γ => γ t)≤a.capacity • hausdorff n X := by
    rcases ht with rfl | rfl
    · rw [he.1]; exact a.left_bound
    · rw [he.2]; exact a.right_bound
  have hcκ (t : Time) (ht : t=0 ∨ t=1) :
      (κ univ)⁻¹ • κ.map (fun γ => γ t)≤c • hausdorff n X := by
    intro B
    change (κ univ)⁻¹*(κ.map (fun γ => γ t)) B≤c*(hausdorff n X) B
    calc
      _ ≤ (κ univ)⁻¹*(π.map (fun γ => γ t)) B :=
        mul_le_mul' le_rfl (Measure.map_mono hκ (measurable_path_eval t) B)
      _ ≤ (κ univ)⁻¹*(a.capacity*(hausdorff n X) B) := mul_le_mul' le_rfl (hend t ht B)
      _ = _ := (mul_assoc _ _ _).symm
  let bC : RenyiTransportNode n X := { b with
    capacity:=c, capacity_finite:=hcf,
    left_bound:=by rw [hb0]; exact hcκ 0 (Or.inl rfl),
    right_bound:=by rw [hb1]; exact hcκ 1 (Or.inr rfl) }
  exact ⟨bC,hb0,hb1,hbD,rfl⟩

end RegularPointCoordinates

end

end OAI
