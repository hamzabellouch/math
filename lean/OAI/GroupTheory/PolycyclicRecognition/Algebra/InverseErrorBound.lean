import OAI.GroupTheory.PolycyclicRecognition.Algebra.InverseAverageL2
import OAI.GroupTheory.PolycyclicRecognition.Algebra.InverseDefectControl

namespace OAI

/-! # The normalized inverse-transfer error bound

The actual error of the averaged inverse transfer is controlled by the
original stationary defect on one compact increment region. Every factor
in the bound is independent of the chosen evaluation point in that region.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  {Λ : ℝ≥0} [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [SecondCountableTopology W]
  [MeasurableSpace W] [BorelSpace W]

/-- Quantitative whole-fiber estimate for the actual averaged inverse error.
The original defect bound is used only on the displayed increment set. -/
theorem inverseAverageError_lintegral_le
    (m : Measure G) [m.IsHaarMeasure]
    (μ ν : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SMulInvariantMeasure G (NormalizedPair G Λ) ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : MemLp φ 2 μ) (hφm : Measurable φ)
    {B C T : Set G} (hB : IsCompact B) (hB0 : m B ≠ 0) (hTm : MeasurableSet T)
    (hT : ∀ x₂ ∈ B, ∀ x₁ ∈ C, x₂⁻¹ * x₁ ∈ T)
    (y : G) (hC : ∀ p : NormalizedPair G Λ, ∀ x ∈ B, p.val.1 y * x ∈ C)
    {c : ℝ≥0∞}
    (hc : ∀ t ∈ T, (∫⁻ p, ‖pairTransferDefect π l φ t p‖ₑ ^ 2 ∂μ) ≤ c) :
    (∫⁻ p, ‖inverseAverageError (normalizedRestriction m B) π l φ y p‖ₑ ^ 2 ∂ν) ≤
      ((m B)⁻¹) ^ 2 * ((m (inverseStripBase (Λ := Λ) B) * c) * m T) := by
  let β := normalizedRestriction m B
  let := normalizedRestriction_probability m hB0 hB.measure_ne_top
  have hD := inverseFiberTransfer_memLp_normalized m μ ν hprod π l hπ hl hφ hB hB0
  have hS := inverseFiberTransfer_shift_memLp ν β π l hl φ hD y
  have hAvg := fiber_average_error_lintegral_le ν β hS hD
  change (∫⁻ p, ‖inverseAverageError β π l φ y p‖ₑ ^ 2 ∂ν) ≤ _ at hAvg
  simp_rw [inverseFiberTransfer_sub] at hAvg
  rw [lintegral_normalizedRestriction_two ν m hB0] at hAvg
  refine hAvg.trans ?_
  exact mul_le_mul_right (inverse_defect_oscillation_bound m μ ν hprod π l hπ hl hφm
    hB.measurableSet hTm hT y hC hc) _

/-- Compact-uniform vanishing of the original defects implies uniform
vanishing of the squared inverse-average errors on the chosen region. -/
theorem inverseAverageError_tendsto_uniform
    (m : Measure G) [m.IsHaarMeasure]
    (μ ν : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SMulInvariantMeasure G (NormalizedPair G Λ) ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (φ : ℕ → NormalizedPair G Λ → W)
    (hφ : ∀ n, MemLp (φ n) 2 μ) (hφm : ∀ n, Measurable (φ n))
    {B C T Q : Set G} (hB : IsCompact B) (hB0 : m B ≠ 0) (hTc : IsCompact T)
    (hT : ∀ x₂ ∈ B, ∀ x₁ ∈ C, x₂⁻¹ * x₁ ∈ T)
    (hC : ∀ y ∈ Q, ∀ p : NormalizedPair G Λ, ∀ x ∈ B, p.val.1 y * x ∈ C)
    {c : ℕ → ℝ≥0∞} (hc : Filter.Tendsto c Filter.atTop (nhds 0))
    (hbound : ∀ n t, t ∈ T → (∫⁻ p, ‖pairTransferDefect π l (φ n) t p‖ₑ ^ 2 ∂μ) ≤ c n) :
    Filter.Tendsto (fun n => ⨆ y ∈ Q,
      ∫⁻ p, ‖inverseAverageError (normalizedRestriction m B) π l (φ n) y p‖ₑ ^ 2 ∂ν)
      Filter.atTop (nhds 0) := by
  let K : ℝ≥0∞ := ((m B)⁻¹) ^ 2 * m (inverseStripBase (Λ := Λ) B) * m T
  have hK : K ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hB0))
      (inverseStripBase_compact hB).measure_ne_top) hTc.measure_ne_top
  have ht : Filter.Tendsto (fun n => K * c n) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hc (Or.inr hK)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
  · intro n
    exact zero_le
  · intro n
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    have h := inverseAverageError_lintegral_le m μ ν hprod π l hπ hl
      (hφ n) (hφm n) hB hB0 hTc.measurableSet hT y (hC y hy) (hbound n)
    convert h using 1
    dsimp [K]
    ac_rfl

end PolycyclicRecognition

end

end OAI
