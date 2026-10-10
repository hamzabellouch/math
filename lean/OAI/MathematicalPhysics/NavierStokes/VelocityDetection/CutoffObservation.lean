import Mathlib

namespace OAI

noncomputable section
namespace VelocityDetection.CutoffObservation
open scoped BigOperators Topology ContDiff
open Set Function Filter
open MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {ρ φ ψ : α → ℝ} {s : Set α}

theorem integrable_capture (hρ : Integrable ρ μ)
    (hφ : AEStronglyMeasurable φ μ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1) :
    Integrable (fun x => φ x * ρ x) μ := by
  apply hρ.bdd_mul hφ
  exact Filter.Eventually.of_forall (fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hφ0 x)] using hφ1 x)

theorem capture_le_setIntegral (hs : MeasurableSet s) (hρ : Integrable ρ μ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hφ : AEStronglyMeasurable φ μ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (hoff : ∀ x, x ∉ s → φ x = 0) :
    (∫ x, φ x * ρ x ∂μ) ≤ ∫ x in s, ρ x ∂μ := by
  rw [← integral_indicator hs]
  apply integral_mono (integrable_capture hρ hφ hφ0 hφ1) (hρ.indicator hs)
  intro x
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx]
    exact mul_le_of_le_one_left (hρ0 x) (hφ1 x)
  · simp [hx, hoff x hx]

theorem setIntegral_le_total_sub_capture (hs : MeasurableSet s) (hρ : Integrable ρ μ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hφ : AEStronglyMeasurable φ μ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (hon : ∀ x, x ∈ s → φ x = 0) :
    (∫ x in s, ρ x ∂μ) ≤ (∫ x, ρ x ∂μ) - ∫ x, φ x * ρ x ∂μ := by
  have hi := integrable_capture hρ hφ hφ0 hφ1
  rw [← integral_sub hρ hi, ← integral_indicator hs]
  apply integral_mono (hρ.indicator hs) (hρ.sub hi)
  intro x
  by_cases hx : x ∈ s
  · simp [hx, hon x hx]
  · simp only [Set.indicator_of_notMem hx]
    exact sub_nonneg.mpr (mul_le_of_le_one_left (hρ0 x) (hφ1 x))

theorem capture_monotone_at_change (hρ : Integrable ρ μ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hφ : AEStronglyMeasurable φ μ) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (hψ : AEStronglyMeasurable ψ μ) (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∀ x, ψ x ≤ 1)
    (hchange : ∀ x, φ x ≠ 0 → ψ x = 1) :
    (∫ x, φ x * ρ x ∂μ) ≤ ∫ x, ψ x * ρ x ∂μ := by
  apply integral_mono (integrable_capture hρ hφ hφ0 hφ1)
    (integrable_capture hρ hψ hψ0 hψ1)
  intro x
  apply mul_le_mul_of_nonneg_right _ (hρ0 x)
  by_cases hx : φ x = 0
  · simpa only [hx] using hψ0 x
  · simpa only [hchange x hx] using hφ1 x

theorem positive_margin (hs : MeasurableSet s) (hρ : Integrable ρ μ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hφ : AEStronglyMeasurable φ μ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (hoff : ∀ x, x ∉ s → φ x = 0) (hmass : ∫ x, ρ x ∂μ = 1)
    {δ : ℝ} (hδ : δ < 1 / 24) (hretained : (∫ x, ρ x ∂μ) - δ ≤ ∫ x, φ x * ρ x ∂μ) :
    (3 / 4 : ℝ) < ∫ x in s, ρ x ∂μ := by
  have h := capture_le_setIntegral hs hρ hρ0 hφ hφ0 hφ1 hoff
  rw [hmass] at hretained
  linarith

theorem negative_margin (hs : MeasurableSet s) (hρ : Integrable ρ μ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hφ : AEStronglyMeasurable φ μ)
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (hon : ∀ x, x ∈ s → φ x = 0)
    {δ : ℝ} (hδ : δ < 1 / 24) (hretained : (∫ x, ρ x ∂μ) - δ ≤ ∫ x, φ x * ρ x ∂μ) :
    (∫ x in s, ρ x ∂μ) < (1 / 4 : ℝ) := by
  have h := setIntegral_le_total_sub_capture hs hρ hρ0 hφ hφ0 hφ1 hon
  linarith

end VelocityDetection.CutoffObservation
end

end OAI
