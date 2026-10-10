import OAI.Geometry.RCD.Heat.CompactHeatDensityMoments
import OAI.Geometry.RCD.Harmonic.RadialMomentBound

namespace OAI

/-! # Uniform reduction of weighted moments to the density powers -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem interpolationDensity_power_moment_bound (hε1 : ∀ k, ε k ≤ 1)
    (z : X) {R : ℝ} (hR : 1 ≤ R)
    (hS : ∀ a : S, dist z a ≤ R) (hT : ∀ b : T, dist z b ≤ R) :
    ∃ L : ℝ, 0 < L ∧ ∀ (k : ℕ) (t : Ioo (0:ℝ) 1) (q : ℕ), 2 ≤ q →
      (∫ x, (D.interpolationDensity k t x)^q*(1+(dist x z)^2) ∂hausdorff n X) ≤
        (1+L^2)*(∫ x, (D.interpolationDensity k t x)^q ∂hausdorff n X)+1 := by
  obtain ⟨L,hL,hbound⟩ := D.interpolationDensity_tail_moments hε1 z hR hS hT
  refine ⟨L,hL,?_⟩
  intro k t q hq
  exact weighted_moment_le_of_tail z L (fun x => pow_nonneg (D.interpolationDensity_pos k t x).le q)
    (D.interpolationDensity_power_integrable hε1 z hR hS hT k t hq)
    (D.interpolationDensity_weighted_power_integrable hε1 z hR hS hT k t hq)
    (hbound k t q hq).2

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
