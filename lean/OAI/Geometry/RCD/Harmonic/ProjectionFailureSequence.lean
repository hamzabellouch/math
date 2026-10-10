import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace OAI

/-! # Selecting the normalized counterexample sequence for sharp projection -/

open Filter
open scoped Topology

noncomputable section
namespace RegularPointCoordinates

/-- Failure of every uniform late-space bound gives increasingly
Euclidean configurations whose source error is negligible relative to
the residual. Positivity of the source floor guarantees valid division. -/
theorem projection_failure_sequence_with_ratio_bound {I : Type*} (epsilon residual source : I → ℝ)
    (hε : ∀ i, 0 ≤ epsilon i) (hs : ∀ i, 0 < source i)
    (hfail : ¬∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ i, epsilon i < δ → residual i ≤ C * source i) :
    ∃ q : ℕ → I, (∀ j, 0 < residual (q j)) ∧
      Tendsto (epsilon ∘ q) atTop (𝓝 0) ∧
      Tendsto (fun j => source (q j) / residual (q j)) atTop (𝓝 0) ∧
      (∀ j, source (q j) / residual (q j) ≤ 1) := by
  classical
  push Not at hfail
  have hchoice (j : ℕ) : ∃ i, epsilon i < 1 / ((j : ℝ) + 1) ∧
      ((j : ℝ) + 1) * source i < residual i :=
    hfail ((j : ℝ) + 1) (by positivity) (1 / ((j : ℝ) + 1)) (by positivity)
  choose q hqε hq using hchoice
  have hpos (j : ℕ) : 0 < residual (q j) :=
    (mul_pos (by positivity) (hs (q j))).trans (hq j)
  have hb (j : ℕ) : source (q j) / residual (q j) ≤ 1 / ((j : ℝ) + 1) := by
    apply le_of_lt
    apply (div_lt_div_iff₀ (hpos j) (by positivity : 0 < (j : ℝ) + 1)).mpr
    nlinarith only [hq j]
  refine ⟨q, hpos, ?_, ?_, ?_⟩
  · exact squeeze_zero (fun j => hε (q j)) (fun j => (hqε j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · exact squeeze_zero (fun j => div_nonneg (hs (q j)).le (hpos j).le) hb
      tendsto_one_div_add_atTop_nhds_zero_nat
  · intro j
    exact (hb j).trans ((div_le_one (by positivity : 0 < (j : ℝ) + 1)).mpr (by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ)); linarith))

/-- The failure sequence without the additional pointwise ratio bound. -/
theorem projection_failure_sequence {I : Type*} (epsilon residual source : I → ℝ)
    (hε : ∀ i, 0 ≤ epsilon i) (hs : ∀ i, 0 < source i)
    (hfail : ¬∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ i, epsilon i < δ → residual i ≤ C * source i) :
    ∃ q : ℕ → I, (∀ j, 0 < residual (q j)) ∧
      Tendsto (epsilon ∘ q) atTop (𝓝 0) ∧
      Tendsto (fun j => source (q j) / residual (q j)) atTop (𝓝 0) := by
  obtain ⟨q, hq, hlimit, hratio, _⟩ :=
    projection_failure_sequence_with_ratio_bound epsilon residual source hε hs hfail
  exact ⟨q, hq, hlimit, hratio⟩

end RegularPointCoordinates

end

end OAI
