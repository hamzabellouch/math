import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProbeSectionRestrictions
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePathConcatenation

namespace OAI

/-! # The measured regions produced by the two-path construction -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set
open scoped Topology

/-- One section and three containing regions, with their actual measure
bounds. The ideal exponent is fixed while the loss is subexponential. -/
structure MeasuredProbeRegions {N D Q : Type*} [Group N] [Group Q]
    [TopologicalSpace N] [TopologicalSpace Q]
    [MeasurableSpace Q] [MeasurableSpace N] [MeasurableSpace D]
    (π : N →* Q) (μQ : Measure Q) (μI : Measure π.ker) (ν : Measure D)
    (scale : ℕ → ℝ) (P : ℝ) where
  sectionMap : C(Q, N)
  section_rightInverse : ∀ q, π (sectionMap q) = q
  quotientRegion : ℕ → Set Q
  idealRegion : ℕ → Set π.ker
  cartanRegion : ℕ → Set D
  idealLoss : ℕ → ℝ
  quotient_finite : ∀ n, μQ (quotientRegion n) ≠ ⊤
  ideal_finite : ∀ n, μI (idealRegion n) ≠ ⊤
  cartan_finite : ∀ n, ν (cartanRegion n) ≠ ⊤
  quotient_subexponential : HasSubexponentialUpperBoundSeq scale
    (fun n => (μQ (quotientRegion n)).toReal)
  ideal_subexponential : HasSubexponentialUpperBoundSeq scale idealLoss
  idealLoss_nonneg : ∀ n, 0 ≤ idealLoss n
  cartan_subexponential : HasSubexponentialUpperBoundSeq scale
    (fun n => (ν (cartanRegion n)).toReal)
  ideal_volume : ∀ n, (μI (idealRegion n)).toReal = idealLoss n * Real.exp (P * scale n)

variable {N D G Q W : Type*} [Group N] [Group D] [Group G] [Group Q]
  [TopologicalSpace N] [TopologicalSpace Q]
  [MeasurableSpace Q] [MeasurableSpace N] [MeasurableSpace D]
  [MetricSpace G] [NormedAddCommGroup W] [NormedSpace ℝ W]
  {π : N →* Q} {μQ : Measure Q} {μI : Measure π.ker} {ν : Measure D}
  {scale : ℕ → ℝ} {P : ℝ}

/-- The path property proved for the measured regions. This records
geometric input paths and the single fixed lift controlling the whole
right cell, without choosing points or tile frames. -/
def MeasuredProbeRegions.ControlsTwoPaths
    (R : MeasuredProbeRegions π μQ μI ν scale P)
    (project : N → D → G) (φ : D →* MulAut N) (act : G → Q → Q)
    (height : G →* Multiplicative W) (cell : Set (N × D))
    (E₁ E₂ : Set W) (η : ℕ → ℝ) (A B δ : ℝ) (n : ℕ) : Prop :=
  ∀ (base anchor first second : G)
    (path₁ : Path (1 : G) (base⁻¹ * first))
    (path₂ : Path (1 : G) (anchor⁻¹ * second)),
    PathMetricBound path₁ (A * scale n) (B * (1 + Real.log (2 + scale n))) →
    PathMetricBound path₂ (A * scale n) (B * (1 + Real.log (2 + scale n))) →
    (∀ t, ∃ w ∈ E₁, ‖(height (path₁ t)).toAdd - scale n • w‖ ≤
      2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
    (∀ t, ∃ w ∈ E₂, ‖(height (path₂ t)).toAdd - scale n • w‖ ≤
      2 * scale n * η n + A * (1 + Real.log (2 + scale n))) →
    ‖(height (anchor⁻¹ * second)).toAdd‖ ≤ δ * scale n →
    dist second first ≤ δ * scale n →
    ∃ (u : N) (d : D), project u d = anchor⁻¹ * first ∧ ∀ z ∈ cell,
      act (base⁻¹ * (first * project z.1 z.2)) 1 ∈ R.quotientRegion n ∧
      quotientSectionResidual π R.sectionMap R.section_rightInverse (u * φ d z.1) ∈
        R.idealRegion n ∧ d * z.2 ∈ R.cartanRegion n

end PolycyclicRecognition

end

end OAI
