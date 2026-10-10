import OAI.Geometry.RCD.Heat.CompactHeatDensityTailMoments
import OAI.Geometry.RCD.Harmonic.ContinuousRadialMoment

namespace OAI

/-! # Finite weighted power moments of every actual interpolation density -/

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

theorem interpolationDensity_weighted_power_integrable (hε1 : ∀ k, ε k ≤ 1)
    (z : X) {R : ℝ} (hR : 1 ≤ R)
    (hS : ∀ a : S, dist z a ≤ R) (hT : ∀ b : T, dist z b ≤ R)
    (k : ℕ) (t : Ioo (0:ℝ) 1) {q : ℕ} (hq : 2 ≤ q) :
    Integrable (fun x => (D.interpolationDensity k t x)^q*(1+(dist x z)^2))
      (hausdorff n X) := by
  obtain ⟨L,hL,hbound⟩ := D.interpolationDensity_tail_moments hε1 z hR hS hT
  exact integrable_one_add_sq_of_tail ((D.interpolationDensity_continuous k t).pow q)
    (fun x => pow_nonneg (D.interpolationDensity_pos k t x).le q) z hL
    (hbound k t q hq).1

theorem interpolationDensity_power_integrable (hε1 : ∀ k, ε k ≤ 1)
    (z : X) {R : ℝ} (hR : 1 ≤ R)
    (hS : ∀ a : S, dist z a ≤ R) (hT : ∀ b : T, dist z b ≤ R)
    (k : ℕ) (t : Ioo (0:ℝ) 1) {q : ℕ} (hq : 2 ≤ q) :
    Integrable (fun x => (D.interpolationDensity k t x)^q) (hausdorff n X) := by
  apply (D.interpolationDensity_weighted_power_integrable hε1 z hR hS hT k t hq).mono'
  · exact ((D.interpolationDensity_continuous k t).pow q).aestronglyMeasurable
  · apply Eventually.of_forall
    intro x
    have hpos := pow_nonneg (D.interpolationDensity_pos k t x).le q
    rw [Real.norm_eq_abs,abs_of_nonneg hpos]
    nlinarith [mul_nonneg hpos (sq_nonneg (dist x z))]

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
