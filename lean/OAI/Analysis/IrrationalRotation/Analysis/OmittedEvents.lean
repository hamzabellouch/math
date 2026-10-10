import OAI.Analysis.IrrationalRotation.Model.ConditionalConvolution
import OAI.Analysis.IrrationalRotation.Model.LaurentConvolution
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib

namespace OAI

noncomputable section

namespace InvariantProjection.ConditionalConvolution

open MeasureTheory

@[simp] theorem mem_window_iff (K n : ℕ) (v : ℤ) :
    v ∈ window K n ↔ |v| ≤ (K : ℤ) ∧ |(n : ℤ) + v| ≤ (K : ℤ) := by
  simp only [window, Finset.mem_filter, Finset.mem_Icc, abs_le]

theorem selector_outside (K n : ℕ) (v : ℤ) (hv : v ∉ window K n) :
    (K : ℤ) < |selector K n v| := by
  unfold selector
  split_ifs with h
  · exact h
  · have hv' := mt (mem_window_iff K n v).mpr hv
    push Not at hv'
    exact hv' (le_of_not_gt h)

theorem truncated_eq_convolution (K n : ℕ) (A B : ℤ → ℂ) :
    truncated K n A B = Invariant233.FiniteWindow.convolution K A B n := rfl

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem measurableSet_omittedEvent (H : ℤ → Set Ω) (K n : ℕ)
    (hH : ∀ k : ℤ, (K : ℤ) < |k| → MeasurableSet (H k)) (v : ℤ) :
    MeasurableSet (omittedEvent H K n v) := by
  unfold omittedEvent
  split_ifs with hv
  · exact MeasurableSet.empty
  · exact hH _ (selector_outside K n v hv)

theorem measurableSet_omittedMask (H : ℤ → Set Ω) (K n : ℕ)
    (hH : ∀ k : ℤ, (K : ℤ) < |k| → MeasurableSet (H k)) :
    MeasurableSet {z : Ω × ℤ | z.1 ∈ omittedEvent H K n z.2} := by
  have he : {z : Ω × ℤ | z.1 ∈ omittedEvent H K n z.2} =
      ⋃ v : ℤ, (omittedEvent H K n v) ×ˢ ({v} : Set ℤ) := by
    ext z
    simp
  rw [he]
  exact MeasurableSet.iUnion (fun v =>
    (measurableSet_omittedEvent H K n hH v).prod (measurableSet_singleton v))

theorem condExp_omittedEvent_le (μ : Measure Ω) (m : MeasurableSpace Ω)
    (H : ℤ → Set Ω) (K n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hH : ∀ k : ℤ, (K : ℤ) < |k| →
      μ[(H k).indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[μ] fun _ => δ) :
    ∀ v : ℤ, μ[(omittedEvent H K n v).indicator (fun _ => (1 : ℝ)) | m]
      ≤ᵐ[μ] fun _ => δ := by
  intro v
  by_cases hv : v ∈ window K n
  · simp only [omittedEvent, ite_eq_left hv, Set.indicator_empty]
    change μ[(0 : Ω → ℝ) | m] ≤ᵐ[μ] fun _ => δ
    rw [condExp_zero]
    exact Filter.Eventually.of_forall (fun _ => hδ)
  · simpa only [omittedEvent, ite_eq_right hv] using hH _ (selector_outside K n v hv)

theorem condExp_omittedMask_section_le (μ : Measure Ω) (m : MeasurableSpace Ω)
    (H : ℤ → Set Ω) (K n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hH : ∀ k : ℤ, (K : ℤ) < |k| →
      μ[(H k).indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[μ] fun _ => δ) :
    ∀ v : ℤ,
      μ[({ω | (ω, v) ∈ {z : Ω × ℤ | z.1 ∈ omittedEvent H K n z.2}}).indicator
        (fun _ => (1 : ℝ)) | m] ≤ᵐ[μ] fun _ => δ := by
  let : MeasurableSpace Ω := mΩ
  exact condExp_omittedEvent_le (mΩ := mΩ) μ m H K n hδ hH

end InvariantProjection.ConditionalConvolution

end

end OAI
