import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem hausdorff_measure_le_of_shrinking_finite_covers {d : ℕ}
    (n : ℕ) (A : Set (Ambient d)) (ι : ℕ → Type*) [∀ t, Fintype (ι t)]
    (r : ℕ → ℝ≥0∞) (hr : Tendsto r atTop (𝓝 0))
    (B : ∀ t : ℕ, ι t → Set (Ambient d))
    (hdiam : ∀ t i, ediam (B t i) ≤ r t)
    (hcover : ∀ t, A ⊆ ⋃ i, B t i) (K : ℝ≥0∞)
    (hcost : ∀ t, (∑ i, ediam (B t i) ^ n) ≤ K) :
    (μH[(n : ℝ)] : Measure (Ambient d)) A ≤ K := by
  have h := Measure.hausdorffMeasure_le_liminf_sum (n : ℝ) A r hr B
    (Filter.Eventually.of_forall hdiam) (Filter.Eventually.of_forall hcover)
  simp only [ENNReal.rpow_natCast] at h
  have hc : (fun t => ∑ i, ediam (B t i) ^ n) ≤ᶠ[atTop] (fun _ => K) :=
    Filter.Eventually.of_forall hcost
  have hlim : (liminf (fun t => ∑ i, ediam (B t i) ^ n) atTop) ≤ K := by
    simpa only [liminf_const] using! Filter.liminf_le_liminf hc
  exact h.trans hlim

end

end RieszRectifiability

end OAI
