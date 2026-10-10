import OAI.Geometry.RCD.Heat.CompactHeatHalfDensityBound
import OAI.Geometry.RCD.Heat.CompactHeatTimeReverse

namespace OAI

/-! # Uniform bounded compression for the actual heat interpolation

The bound holds at every point, time and noise index. It is constructed
from the original endpoint densities, not supplied as an additional input.
-/

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

theorem interpolationDensity_uniform_bound (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (z : X) {R : ℝ} (hR : 1 ≤ R)
    (hS : ∀ a : S, dist z a ≤ R) (hT : ∀ b : T, dist z b ≤ R) :
    ∃ B : ℝ, 0 < B ∧ ∀ (k : ℕ) (t : Ioo (0:ℝ) 1) (x : X),
      D.interpolationDensity k t x ≤ B := by
  obtain ⟨A,hA,ha⟩ := D.interpolationDensity_half_bound hK hε1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁
    hC₀ hC₁ hμ hν z hR hS hT
  obtain ⟨B,hB,hb⟩ := D.reverse.interpolationDensity_half_bound hK hε1 ρ₁ ρ₀ hm₁ hm₀ hp₁ hp₀
    hC₁ hC₀ hν hμ z hR hT hS
  refine ⟨max A B,hA.trans_le (le_max_left _ _),?_⟩
  intro k t x
  by_cases ht : (t:ℝ) ≤ 1/2
  · exact (ha k t ht x).trans (le_max_left _ _)
  · let s : Ioo (0:ℝ) 1 := ⟨1-t,by constructor <;> linarith [t.property.1,t.property.2]⟩
    have hs : (s:ℝ) ≤ 1/2 := by dsimp only [s]; linarith
    have he := D.reverse_density k t x
    exact (he ▸ hb k s hs x).trans (le_max_right _ _)

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
