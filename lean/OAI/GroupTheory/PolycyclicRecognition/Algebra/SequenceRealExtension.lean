import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponential

namespace OAI

/-! # Extending a scale sequence without regularity assumptions

The geometric box lemmas use real scales. Arbitrary data on a strictly
increasing scale sequence extend by zero off that sequence, preserving
vanishing errors and subexponential upper bounds.
-/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- No interpolation or regularity of the envelope is required. -/
def sequenceRealExtension (scale : ℕ → ℝ) (f : ℕ → ℝ) (r : ℝ) : ℝ := by
  classical
  exact if h : ∃ n, scale n = r then f h.choose else 0

theorem sequenceRealExtension_apply (scale : ℕ → ℝ) (hs : StrictMono scale)
    (f : ℕ → ℝ) (n : ℕ) : sequenceRealExtension scale f (scale n) = f n := by
  classical
  have h : ∃ k, scale k = scale n := ⟨n, rfl⟩
  rw [sequenceRealExtension, dite_eq_left h, hs.injective h.choose_spec]

theorem sequenceRealExtension_nonneg (scale f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    ∀ r, 0 ≤ sequenceRealExtension scale f r := by
  classical
  intro r
  unfold sequenceRealExtension
  split_ifs with h
  · exact hf _
  · exact le_rfl

/-- A vanishing sequence of errors remains vanishing on the real scale. -/
theorem tendsto_sequenceRealExtension_zero (scale : ℕ → ℝ) (hs : StrictMono scale)
    (f : ℕ → ℝ) (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (sequenceRealExtension scale f) atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hf ε hε
  refine ⟨scale N, ?_⟩
  intro r hr
  unfold sequenceRealExtension
  split_ifs with h
  · have hn : N ≤ h.choose := hs.le_iff_le.mp (by rwa [h.choose_spec])
    exact hN _ hn
  · simpa using hε

/-- A sequential subexponential envelope is enough for the real-scale
box estimates. Its zero extension imposes no restriction between samples. -/
theorem HasSubexponentialUpperBoundSeq.realExtension
    {scale f : ℕ → ℝ} (hf : HasSubexponentialUpperBoundSeq scale f)
    (hs : StrictMono scale) : HasSubexponentialUpperBound (sequenceRealExtension scale f) := by
  classical
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hf ε hε)
  filter_upwards [eventually_ge_atTop (scale N)] with r hr
  unfold sequenceRealExtension
  split_ifs with h
  · have hn : N ≤ h.choose := hs.le_iff_le.mp (by rwa [h.choose_spec])
    simpa only [h.choose_spec] using hN _ hn
  · exact (Real.exp_pos _).le

/-- The same extension transports the exponentially bounded inside-letter
parameters, together with their actual vanishing errors. -/
theorem sequenceRealExtension_eventually_abs_le_exp
    (scale : ℕ → ℝ) (hs : StrictMono scale) (t ε : ℕ → ℝ) (a : ℝ)
    (ht : ∀ᶠ n in atTop, |t n| ≤ Real.exp ((a + ε n) * scale n)) :
    ∀ᶠ r in atTop, |sequenceRealExtension scale t r| ≤
      Real.exp ((a + sequenceRealExtension scale ε r) * r) := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp ht
  filter_upwards [eventually_ge_atTop (scale N)] with r hr
  by_cases h : ∃ n, scale n = r
  · obtain ⟨n, rfl⟩ := h
    rw [sequenceRealExtension_apply scale hs, sequenceRealExtension_apply scale hs]
    exact hN n (hs.le_iff_le.mp hr)
  · simp only [sequenceRealExtension, dite_eq_right h, abs_zero]
    exact (Real.exp_pos _).le

end PolycyclicRecognition

end

end OAI
