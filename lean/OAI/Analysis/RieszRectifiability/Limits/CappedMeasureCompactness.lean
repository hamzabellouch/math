import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.CappedLowerGrowth
import OAI.Analysis.RieszRectifiability.Limits.OriginalGrowthLimit

namespace OAI

/-!
# Compactness under capped lower growth

Uniform upper growth and capped lower growth yield a nonzero compact-test limit.
The limit retains the origin in its support and quantitative growth bounds, with
the upper and lower constants enlarged by `2 ^ n` and `4 ^ n` respectively.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem exists_capped_lower_measure_limit {d : ℕ} (n : ℕ) (C G H : ℝ)
    (μ : ℕ → Measure (Ambient d)) (hC : 0 < C) (hH : 0 < H)
    (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlower : ∀ j, CappedLowerGrowth n C H (μ j)) (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => μ (ρ j)) ν ∧ GlobalUpperGrowth n (G * 2 ^ n) ν ∧
      CappedLowerGrowth n (C * 4 ^ n) H ν ∧ (0 : Ambient d) ∈ ν.support := by
  let (j : ℕ) : IsFiniteMeasureOnCompacts (μ j) := globalGrowth_finite_on_compacts G (μ j) (hg j)
  let t := min 1 H
  have ht : 0 < t := lt_min zero_lt_one hH
  have hmass (j : ℕ) : t ^ n / C ≤ (μ j).real (ball (0 : Ambient d) 1) := by
    apply (CappedLowerGrowth.real_bound n C H (μ j) hC (hlower j) 0 (hzero j) t ht (min_le_right _ _)).trans
    exact measureReal_mono (ball_subset_ball (min_le_left 1 H))
      ((hg j).2 0 1 zero_lt_one |>.trans_lt ENNReal.ofReal_lt_top).ne
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν⟩ :=
    exists_original_growth_limit n μ G (t ^ n / C) (by positivity) hg hmass
  let := hfinite
  refine ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, ?_, ?_⟩
  · exact CappedLowerGrowth.compact_limit n C H (fun j => μ (ρ j)) ν hC hlocal (fun j => hlower (ρ j))
  · exact CappedLowerGrowth.limit_origin n C H (fun j => μ (ρ j)) ν hC hH hlocal
      (fun j => hlower (ρ j)) (fun j => hzero (ρ j))

end

end RieszRectifiability

end OAI
