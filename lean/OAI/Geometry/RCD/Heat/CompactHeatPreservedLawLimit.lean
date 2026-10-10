import OAI.Geometry.RCD.Heat.CompactHeatContinuousLawLimit

namespace OAI

/-! # The law limit preserves both originally selected heat actions -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal BoundedContinuousFunction
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

theorem preserved_action_law_limit (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R : ℝ} (hR : 1 ≤ R)
    (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R) :
    ∃ (C : ℝ) (Q : Ioo (0:ℝ) 1 → ProbabilityMeasure X) (j : ℕ → ℕ),
      0 < C ∧ StrictMono j ∧ Continuous Q ∧
      hX.CompactHeatConverges hn p μ D.left ε hε p (D.index ∘ j) D.forward.potential ∧
      hX.CompactHeatConverges hn p ν D.right ε hε p (D.index ∘ j) D.backward.potential ∧ ∀ t,
      Tendsto (fun k => D.interpolationLaw (D.index (j k)) t) atTop (𝓝 (Q t)) ∧
      (Q t : Measure X) ≤ ENNReal.ofReal C • hausdorff n X ∧
      ∀ f : X → ℝ, Integrable f (hausdorff n X) →
        Tendsto (fun k => ∫ x, D.interpolationDensity (D.index (j k)) t x*f x ∂hausdorff n X)
          atTop (𝓝 (∫ x, f x ∂(Q t : Measure X))) := by
  obtain ⟨C,Q,j,hC,hj,hQ,hlim⟩ := D.interpolationLaw_continuous_limit hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν p hR hS hT D.index
  exact ⟨C,Q,j,hC,hj,hQ,D.forward_limit.subsequence hX hn p hj,
    D.backward_limit.subsequence hX hn p hj,hlim⟩

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
