import OAI.Geometry.RCD.Heat.CompactHeatPowerGronwall
import OAI.Geometry.RCD.Metric.PowerGrowthGeometricBound
import OAI.Geometry.RCD.Sobolev.GeometricMomentPointwiseBound

namespace OAI

/-! # Uniform density bound on the first half of the interpolation -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal
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

theorem interpolationDensity_half_bound (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (z : X) {R : ℝ} (hR : 1 ≤ R)
    (hS : ∀ a : S, dist z a ≤ R) (hT : ∀ b : T, dist z b ≤ R) :
    ∃ B : ℝ, 0 < B ∧ ∀ (k : ℕ) (t : Ioo (0:ℝ) 1), (t:ℝ) ≤ 1/2 →
      ∀ x, D.interpolationDensity k t x ≤ B := by
  obtain ⟨C,hC,hbound⟩ := D.interpolation_power_gronwall hK hε1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁
    hC₀ hC₁ hμ hν z hR hS hT
  let B := max 1 (C₀:ℝ)*Real.exp C
  have hB : 0 < B := mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (Real.exp_pos _)
  refine ⟨B,hB,?_⟩
  intro k t ht
  let : (hausdorff n X).IsOpenPosMeasure := hX.openPos K n
  apply continuous_le_of_geometric_moments (hausdorff n X) (D.interpolationDensity_continuous k t)
    (fun x => (D.interpolationDensity_pos k t x).le) (M := 2) hB
    (fun j => D.interpolationDensity_power_integrable hε1 z hR hS hT k t (by omega))
  intro j
  exact power_growth_geometric_bound hC C₀.coe_nonneg t.property.2.le j (hbound k j t ht)

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
