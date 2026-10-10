import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitGrowth
import OAI.Analysis.RieszRectifiability.Limits.OriginalMeasureCompactness

namespace OAI

/-!
# Nonzero compact-test limits with upper growth

A uniform lower bound on unit-ball mass prevents the compact-test subsequential
limit from vanishing. The upper growth estimate passes to this limit with the
explicit factor `2 ^ n` in its constant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_original_growth_limit {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C c : ℝ) (hc : 0 < c) (hg : ∀ j, GlobalUpperGrowth n C (μ j))
    (hm : ∀ j, c ≤ (μ j).real (ball (0 : Ambient d) 1)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => μ (ρ j)) ν ∧ GlobalUpperGrowth n (C * 2 ^ n) ν := by
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlimit⟩ :=
    exists_original_measure_compact_subsequence n μ C c hc hg hm
  let := hfinite
  exact ⟨ρ, hρ, ν, hfinite, hne, hlimit,
    compactTestConvergence_upper_growth n (fun j => μ (ρ j)) ν hlimit C (fun j => hg (ρ j))⟩

end

end RieszRectifiability

end OAI
