import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.TruncationLinear

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal ENNReal

theorem truncated_restriction_eq_indicator_function {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (s : Set (Ambient d)) (hs : MeasurableSet s)
    (ε : ℝ) (f : Ambient d → ℝ) :
    truncated m (μ.restrict s) ε f = truncated m μ ε (s.indicator f) := by
  classical
  funext x
  have ht : MeasurableSet {y : Ambient d | ε < dist x y} :=
    measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable
  have heq : (fun y => s.indicator f y • kernel m x y) =
      s.indicator (fun y => f y • kernel m x y) := by
    funext y
    by_cases hy : y ∈ s
    · simp only [indicator_of_mem hy]
    · simp only [indicator_of_notMem hy, zero_smul]
  unfold truncated
  rw [heq, integral_indicator hs, Measure.restrict_restrict ht,
    Measure.restrict_restrict hs, inter_comm]

theorem native_truncation_bound_restrict {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (D : ℝ≥0)
    (hB : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated m μ ε f) 2 μ ∧
        eLpNorm (truncated m μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (s : Set (Ambient d)) (hs : MeasurableSet s) :
    ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (μ.restrict s) →
      MemLp (truncated m (μ.restrict s) ε f) 2 (μ.restrict s) ∧
        eLpNorm (truncated m (μ.restrict s) ε f) 2 (μ.restrict s) ≤
          (D : ℝ≥0∞) * eLpNorm f 2 (μ.restrict s) := by
  intro ε hε f hf
  have hi : MemLp (s.indicator f) 2 μ := (memLp_indicator_iff_restrict hs).mpr hf
  obtain ⟨hT, hN⟩ := hB ε hε (s.indicator f) hi
  rw [truncated_restriction_eq_indicator_function m μ s hs ε f]
  refine ⟨hT.restrict s, ?_⟩
  calc
    _ ≤ eLpNorm (truncated m μ ε (s.indicator f)) 2 μ :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ (D : ℝ≥0∞) * eLpNorm (s.indicator f) 2 μ := hN
    _ = _ := by rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]

end

end RieszRectifiability

end OAI
