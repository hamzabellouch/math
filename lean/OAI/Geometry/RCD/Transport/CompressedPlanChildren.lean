import OAI.Geometry.RCD.Coordinates.NormalizedSubplanNodes

namespace OAI

/-! # Half nodes for an actual compressed plan -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [CompleteSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem compressed_plan_children {n : ℕ} (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C≠∞) (hc : ∀ t : Time, π.map (fun γ => γ t)≤C • hausdorff n X) :
    ∃ a₀ a₁ : RenyiTransportNode n X,
      a₀.left=π.map (fun γ => γ 0) ∧ a₀.right=π.map (fun γ => γ midpointTime) ∧
      a₁.left=π.map (fun γ => γ midpointTime) ∧ a₁.right=π.map (fun γ => γ 1) ∧
      a₀.distance=a.distance/2 ∧ a₁.distance=a.distance/2 := by
  simpa only [measure_univ,inv_one,one_smul] using
    exists_normalized_subplan_half_nodes a π hg hp hC hc π le_rfl (by simp)

end RegularPointCoordinates

end

end OAI
