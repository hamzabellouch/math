import OAI.Geometry.RCD.Metric.BallMassFubini
import Mathlib.MeasureTheory.Covering.Besicovitch

namespace OAI

/-! # Local measure domination from arbitrarily small closed-ball bounds

The Vitali family is taken for the source measure itself, so absolute
continuity is a conclusion rather than an assumption.
-/

open Set Metric Filter MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem local_ball_measure_order {n : ℕ}
    (μ : Measure (Euclidean n)) [IsFiniteMeasure μ]
    (c : ℝ≥0) {U : Set (Euclidean n)} {R : ℝ} (hR : 0 < R)
    (hb : ∀ x ∈ U, ∀ r : ℝ, 0 < r → r ≤ R →
      μ (closedBall x r) ≤ (c : ℝ≥0∞)*volume (closedBall x r)) :
    ∀ A : Set (Euclidean n), A ⊆ U → μ A ≤ (c • volume) A := by
  intro A hA
  apply (Besicovitch.vitaliFamily μ).measure_le_of_frequently_le (c • volume)
    Measure.AbsolutelyContinuous.rfl A
  intro x hx
  rw [VitaliFamily.frequently_filterAt_iff]
  intro ε hε
  let r := min R ε
  have hr : 0 < r := lt_min hR hε
  refine ⟨closedBall x r,?_,closedBall_subset_closedBall (min_le_right _ _),?_⟩
  · exact mem_image_of_mem _ hr
  · simpa only [Measure.coe_nnreal_smul_apply] using hb x (hA hx) r hr (min_le_left _ _)

theorem local_ball_absolutelyContinuous {n : ℕ}
    (μ : Measure (Euclidean n)) [IsFiniteMeasure μ]
    (c : ℝ≥0) {U : Set (Euclidean n)} (hU : MeasurableSet U)
    {R : ℝ} (hR : 0 < R)
    (hb : ∀ x ∈ U, ∀ r : ℝ, 0 < r → r ≤ R →
      μ (closedBall x r) ≤ (c : ℝ≥0∞)*volume (closedBall x r)) :
    μ.restrict U ≪ volume := by
  intro A hA
  rw [Measure.restrict_apply' hU]
  apply le_antisymm _ bot_le
  change μ (A ∩ U) ≤ 0
  have hh := local_ball_measure_order μ c hR hb (A ∩ U) inter_subset_right
  have hz : volume (A ∩ U)=0 := measure_mono_null inter_subset_left hA
  simpa only [Measure.coe_nnreal_smul_apply,hz,mul_zero] using hh

end RegularPointCoordinates

end

end OAI
