import OAI.Geometry.RCD.Transport.StrongEntropy
import OAI.Geometry.RCD.Metric.BoundedDensityLp

namespace OAI

/-! # The strong entropy inequality for actual bounded probability measures -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX

theorem bounded_entropy_geodesic_measure (hn : 2 ≤ n) (p : X)
    (ν₀ ν₁ ν : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν]
    {C : ℝ≥0} (hν₀ : ν₀ ≤ ENNReal.ofReal C • hausdorff n X)
    (hν₁ : ν₁ ≤ ENNReal.ofReal C • hausdorff n X) (hν : ν ≤ ENNReal.ofReal C • hausdorff n X)
    {R₀ R₁ R : ℝ} (hs₀ : ∀ᵐ x ∂ν₀, dist x p ≤ R₀) (hs₁ : ∀ᵐ x ∂ν₁, dist x p ≤ R₁)
    (hs : ∀ᵐ x ∂ν, dist x p ≤ R) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hd₀ : (wassersteinSq ν ν₀).toReal=θ^2*(wassersteinSq ν₀ ν₁).toReal)
    (hd₁ : (wassersteinSq ν ν₁).toReal=(1-θ)^2*(wassersteinSq ν₀ ν₁).toReal) :
    boltzmannEntropy (hausdorff n X) ν ≤
      (1-θ)*boltzmannEntropy (hausdorff n X) ν₀+θ*boltzmannEntropy (hausdorff n X) ν₁-
      (K/2)*θ*(1-θ)*(wassersteinSq ν₀ ν₁).toReal := by
  obtain ⟨f,hf0,hfC,hfm,hfs,he⟩ := exists_bounded_probability_density (hausdorff n X)
    hX.quadratic ν hν p hs
  have h := hX.bounded_entropy_geodesic_point hn p f C hf0 hfC hfm hfs ν₀ ν₁ hν₀ hν₁ hs₀ hs₁
    hθ0 hθ1 (by rwa [he]) (by rwa [he])
  rwa [he] at h

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
