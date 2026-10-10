import OAI.Geometry.RCD.Transport.CompressedFiniteUnique
import OAI.Geometry.RCD.Transport.ReducedInterpolation

namespace OAI

/-! # Exact reduced interpolation on every bounded compressed optimal plan

The entropy-maximizing plan has the finite-dimensional reduced
bound. Uniqueness now transfers that bound to the prescribed actual plan.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem all_compressed_reduced_interpolation (hn : 2 ≤ n) (hK : K ≤ 0)
    {N : ℝ} (hN : (n:ℝ) ≤ N) (a : RenyiTransportNode n X)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X) :
    ∀ t, ReducedRenyiChordBound (hausdorff n X) K N π t := by
  obtain ⟨ρ,hρ,hgρ,hpρ,hcρ,hr⟩ :=
    hX.exists_compressed_reduced_interpolation K n hn hK hN a
  let : IsProbabilityMeasure ρ := hρ
  have he : π=ρ := hX.compressed_plan_unique_finite hn a.center a.radius_nonneg π ρ hg hgρ hp hpρ
    hC (compressionBudget_ne_top K n a.distance a.capacity_finite) hc hcρ a.left_support a.right_support
  rwa [he]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
