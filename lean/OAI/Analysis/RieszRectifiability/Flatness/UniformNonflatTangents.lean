import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.GlobalLowerDiameter
import OAI.Analysis.RieszRectifiability.Limits.UniformNonflatLimits

namespace OAI

/-!
Uniform bilateral nonflatness persists, with a fixed loss, under compact-test limits and blowups.
Global lower growth supplies infinite support diameter for the limiting argument.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem GlobalBilateralLower.compact_limit_global {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hne : ∀ j, μ j ≠ 0) (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ n / C) ≤ (μ j) (ball x t))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbad : ∀ᶠ j in atTop, GlobalBilateralLower n (μ j) ε) :
    GlobalBilateralLower n ν (ε / 64) := by
  apply GlobalBilateralLower.compact_limit hnd μ ν hlocal C hC
    (fun j x hx t ht => hlower j x hx t ht.1) _ ε hε hε1 hbad
  intro t _
  apply Eventually.of_forall
  intro j
  rw [global_lower_growth_support_ediam_top n hn (μ j) (hne j) C hC (hlower j)]
  exact le_top

theorem GlobalBilateralLower.tangent {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (μ ν : Measure (Ambient d)) [IsFiniteMeasureOnCompacts ν]
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ n / C) ≤ μ (ball x t))
    (a : Ambient d) (ha : a ∈ μ.support) (s : ℕ → ℝ) (hs : ∀ j, 0 < s j)
    (hlocal : CompactTestConvergence (fun j => blowupMeasure n μ a (s j)) ν)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hbad : GlobalBilateralLower n μ ε) :
    GlobalBilateralLower n ν (ε / 64) := by
  let μj := fun j => blowupMeasure n μ a (s j)
  let : ∀ j, IsFiniteMeasureOnCompacts (μj j) := fun j =>
    globalGrowth_finite_on_compacts G (μj j) (blowupMeasure_growth n μ a (s j) G (hs j) hg)
  have hne (j : ℕ) : μj j ≠ 0 := by
    have hz := blowupMeasure_origin_mem_support n μ a (s j) (hs j) ha
    intro hj
    change (0 : Ambient d) ∈ (μj j).support at hz
    rw [hj] at hz
    simp only [Measure.support_zero, mem_empty_iff_false] at hz
  apply GlobalBilateralLower.compact_limit_global hn hnd μj ν hne hlocal C hC
    (fun j => blowupMeasure_lower_global n μ a (s j) C (hs j) hlower) ε hε hε1
  exact Eventually.of_forall fun j => GlobalBilateralLower.blowup n μ ε hbad a (s j) (hs j)

end

end RieszRectifiability

end OAI
