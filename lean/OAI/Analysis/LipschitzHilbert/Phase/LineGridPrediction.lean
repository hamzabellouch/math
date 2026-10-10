import OAI.Analysis.LipschitzHilbert.Trees.FiniteLineGrid
import OAI.Analysis.LipschitzHilbert.Phase.GraphPredictionFactor
import OAI.Analysis.LipschitzHilbert.Fourier.FourierAveragingConvolution

namespace OAI

/-! The snapshot prediction factor on the actual finite line-cell mesh. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

attribute [local instance] Classical.propDecidable

theorem intervalProbability_ae_mem_Ico (a b : ℝ) :
    ∀ᵐ x ∂intervalProbability a b, x ∈ Ico a b := by
  apply Measure.ae_smul_measure
  have hmem : ∀ᵐ x ∂volume.restrict (Icc a b), x ∈ Icc a b :=
    ae_restrict_mem measurableSet_Icc
  have hne : ∀ᵐ x ∂volume.restrict (Icc a b), x ≠ b :=
    (show ∀ᵐ x : ℝ ∂volume, x ≠ b by
      rw [ae_iff]
      have hs : {x : ℝ | ¬x ≠ b} = {b} := by ext x; simp
      rw [hs]
      exact measure_singleton b).filter_mono (ae_mono Measure.restrict_le_self)
  filter_upwards [hmem, hne] with x hx hxb
  exact ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩

namespace FiniteLineGrid

/-- Apply the constructed graph predictor to a finite uniform line grid.
There is no free measurable partition or cell-diameter hypothesis here. -/
theorem graph_prediction_step {ι κ : Type*} [Fintype ι] [Fintype κ]
    (grid : FiniteLineGrid) (level : ℕ) (hlevel : level ≤ grid.depth)
    (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i)
    (w m : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : ∀ i, orderMass w (closedNeighborhood G i) ≤ m i)
    (τ : Measure ℝ) [IsProbabilityMeasure τ]
    (frequency : ι → κ → ℝ) (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
    (lambda : ι → ℂ) (i₀ : ι)
    {η gap D p K u freqBound θ : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hgap : 0 < gap)
    (hν : FourierGap (predictionMixture
      (intervalProbability grid.origin (grid.origin + grid.width)) τ η) gap)
    (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hfrequency : ∀ i j, i ≠ j → ¬G i j → ∀ k, gap ≤ |frequency i k - frequency j k|)
    (hcard : ∀ S : Finset ι, (S : Set ι).Pairwise (fun i j => ¬G i j) → (S.card : ℝ) ≤ D)
    (hl : ∀ i, 0 ≤ l i) (htotal : ∑ i, l i ≤ 1)
    (hlambda : ∀ i, ‖lambda i‖ ≤ (w i / m i) ^ phaseMu D p)
    (hK : 0 ≤ K) (hu : 0 ≤ u) (hfreqBound : 0 ≤ freqBound)
    (hmass : (∑ i : RemainderIndex i₀, ‖predictionCoefficients l X lambda D p i‖) ≤ K * u)
    (hfrequencyBound : ∀ i : RemainderIndex i₀, ∀ j,
      |frequency i j - frequency i₀ j| ≤ freqBound)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ Γ : ℝ → ℝ, Measurable Γ ∧
      Integrable Γ (intervalProbability grid.origin (grid.origin + grid.width)) ∧
      (∀ t, 0 ≤ Γ t) ∧
      (∫ t, Γ t ∂intervalProbability grid.origin (grid.origin + grid.width)) ≤ 1 ∧
      (∀ s t, grid.index level s = grid.index level t → Γ s = Γ t) ∧
      ∀ t ∈ grid.root, (1 - θ) * graphPredictionValue frequency l X lambda D p t + θ ≤
        Real.exp (((η / (1 - η) * (2 * p * K)) +
          p * freqBound * K * (grid.width / (grid.branching : ℝ) ^ level)) * u) * Γ t := by
  let : IsProbabilityMeasure (intervalProbability grid.origin (grid.origin + grid.width)) :=
    intervalProbability_isProbability (by linarith [grid.width_pos])
  exact graph_prediction_step_factor G hG w m hw hm
    (intervalProbability grid.origin (grid.origin + grid.width)) τ frequency l X lambda
    i₀ grid.root (grid.index level) hη0 hη1 hgap hν hD hp hfrequency hcard hl htotal hlambda
    hK hu hfreqBound (div_nonneg grid.width_pos.le (pow_nonneg (Nat.cast_nonneg _) _))
    hmass hfrequencyBound hθ0 hθ1 (grid.measurable_index_fiber level)
    (intervalProbability_ae_mem_Ico _ _) (fun s hs t ht hst =>
      grid.same_index_distance hlevel ht hs hst)

end FiniteLineGrid
end LipschitzHilbert

end

end OAI
