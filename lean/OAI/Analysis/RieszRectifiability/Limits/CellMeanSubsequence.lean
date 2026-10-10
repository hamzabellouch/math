import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.CellMeanBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter Topology

theorem bounded_of_eventually_abs_le (a : ℕ → ℝ) (B : ℝ)
    (h : ∀ᶠ j in atTop, |a j| ≤ B) : ∃ C : ℝ, ∀ j, |a j| ≤ C := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨max B (∑ j ∈ Finset.range N, |a j|), ?_⟩
  intro j
  by_cases hj : N ≤ j
  · exact (hN j hj).trans (le_max_left _ _)
  · exact (Finset.single_le_sum (fun i _ => abs_nonneg (a i))
      (Finset.mem_range.mpr (lt_of_not_ge hj))).trans (le_max_right _ _)

theorem exists_common_subsequence_of_eventual_bounds {ι : Type*} [Countable ι]
    (a : ℕ → ι → ℝ) (h : ∀ i, ∃ B : ℝ, ∀ᶠ j in atTop, |a j i| ≤ B) :
    ∃ b : ι → ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, Tendsto (fun j => a (φ j) i) atTop (𝓝 (b i)) := by
  classical
  have hb : ∀ i, ∃ B : ℝ, ∀ j, |a j i| ≤ B := by
    intro i
    obtain ⟨B, hB⟩ := h i
    exact bounded_of_eventually_abs_le (fun j => a j i) B hB
  choose B hB using hb
  have hc : IsCompact {b : ι → ℝ | ∀ i, b i ∈ Icc (-B i) (B i)} :=
    isCompact_pi_infinite (fun i => isCompact_Icc)
  obtain ⟨b, _, φ, hφ, hlim⟩ := hc.tendsto_subseq
    (fun j i => abs_le.mp (hB i j))
  exact ⟨b, φ, hφ, fun i => (continuous_apply i).tendsto b |>.comp hlim⟩

theorem exists_subsequence_cellMeans {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (μ : ℕ → Measure X) [∀ j, IsFiniteMeasure (μ j)]
    (w : ℕ → X → ℝ) (hw : ∀ j, MemLp (w j) 2 (μ j))
    (s : ι → Set X) (B : ℝ) (hB : ∀ j, (∫ x, w j x ^ 2 ∂μ j) ≤ B)
    (hmass : ∀ i, ∃ c : ℝ, 0 < c ∧ ∀ᶠ j in atTop, c ≤ (μ j).real (s i)) :
    ∃ b : ι → ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, Tendsto (fun j => cellMean ((μ (φ j)).restrict (s i)) (w (φ j)))
        atTop (𝓝 (b i)) := by
  apply exists_common_subsequence_of_eventual_bounds
    (fun j i => cellMean ((μ j).restrict (s i)) (w j))
  intro i
  obtain ⟨c, hc, hmass⟩ := hmass i
  refine ⟨B / c + 1, ?_⟩
  filter_upwards [hmass] with j hj
  apply cellMean_abs_bound ((μ j).restrict (s i)) (w j) ((hw j).restrict (s i)) c B hc
  · simpa only [Measure.real, Measure.restrict_apply_univ] using! hj
  · exact (setIntegral_le_integral (hw j).integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg (w j x))).trans (hB j)

end

end RieszRectifiability

end OAI
