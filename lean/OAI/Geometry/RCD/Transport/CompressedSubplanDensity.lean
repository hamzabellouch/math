import OAI.Geometry.RCD.Transport.CompressedAllInverse
import OAI.Geometry.RCD.Transport.ObservableSubplanDensity

namespace OAI

/-! # Exact original densities for every measurable restriction of a compressed plan -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem restricted_plan_density (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    {S : Set C(Time,X)} (hS : MeasurableSet S) (t : Time) :
    ∀ᵐ γ ∂π.restrict S,
      ((π.restrict S).map (fun γ => γ t)).rnDeriv (hausdorff n X) (γ t)=
        (π.map (fun γ => γ t)).rnDeriv (hausdorff n X) (γ t) := by
  obtain ⟨g,hg,hgi⟩ := hX.compressed_time_inverse hn p hR π hg hp hC hc hs₀ hs₁ t
  exact rnDeriv_restricted_map_ae π (hausdorff n X) (measurable_path_eval t) hg hgi
    (Measure.absolutelyContinuous_of_le_smul (hc t)) hS

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
