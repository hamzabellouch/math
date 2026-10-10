import OAI.Geometry.RCD.Transport.BoundedOptimalRecovery

namespace OAI

/-! # Transport nodes of bounded recovered endpoints -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

def boundedEndpointNode (n : ℕ) (ρ : ProbabilityMeasure C(Time,X)) (p : X)
    {R : ℝ} (hR : 0≤R)
    (hs : ∀ᵐ γ ∂(ρ : Measure C(Time,X)), ∀ t : Time, dist (γ t) p≤R)
    {C : ℝ≥0∞} (hC : C≠∞)
    (h0 : (ρ : Measure C(Time,X)).map (fun γ => γ 0)≤C • hausdorff n X)
    (h1 : (ρ : Measure C(Time,X)).map (fun γ => γ 1)≤C • hausdorff n X) :
    RenyiTransportNode n X := by
  have he (t : Time) : ∀ᵐ x ∂(ρ : Measure C(Time,X)).map (fun γ => γ t), dist x p≤R := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_closedBall).mpr
    exact hs.mono fun _ hγ => hγ t
  exact ⟨(ρ : Measure C(Time,X)).map (fun γ => γ 0),
    (ρ : Measure C(Time,X)).map (fun γ => γ 1),inferInstance,inferInstance,
    p,R,hR,he 0,he 1,C,hC,h0,h1,2*R,mul_nonneg (by norm_num) hR,
    optimalPlanDistanceBound_of_bounded _ _ p (he 0) (he 1)⟩

omit [SeparableSpace X] in
theorem bounded_recovery_endpoint_bound
    (n : ℕ) (ρ τ : Measure C(Time,X))
    (hle : τ≤(2 : ℝ≥0∞) • ρ) {C : ℝ≥0∞} (t : Time)
    (hc : ρ.map (fun γ => γ t)≤C • hausdorff n X) :
    τ.map (fun γ => γ t)≤((2 : ℝ≥0∞)*C) • hausdorff n X := by
  have hh := Measure.map_mono hle (measurable_path_eval t)
  rw [Measure.map_smul _ (measurable_path_eval t).aemeasurable] at hh
  intro B
  exact (hh B).trans (by
    change (2 : ℝ≥0∞)*(ρ.map (fun γ => γ t)) B≤((2 : ℝ≥0∞)*C)*(hausdorff n X) B
    have hcb : (ρ.map (fun γ => γ t)) B≤C*(hausdorff n X) B := hc B
    exact (mul_le_mul' (le_refl (2 : ℝ≥0∞)) hcb).trans_eq (mul_assoc 2 C _).symm)

end RegularPointCoordinates

end

end OAI
