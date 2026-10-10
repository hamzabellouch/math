import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.BilateralLowerLimit
import OAI.Analysis.RieszRectifiability.Foundations.BlowupBilateralCenters

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

def GlobalBilateralLower {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (ε : ℝ) : Prop :=
  ∀ a ∈ μ.support, ∀ r : ℝ, 0 < r → ε ≤ bilateralBeta n μ a r

theorem GlobalBilateralLower.blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (ε : ℝ) (hε : GlobalBilateralLower n μ ε) (a : Ambient d) (s : ℝ) (hs : 0 < s) :
    GlobalBilateralLower n (blowupMeasure n μ a s) ε := by
  intro b hb R hR
  rw [bilateralBeta_blowup_at n μ a b s R hs]
  exact hε _ ((blowupMeasure_support_iff n μ a b s hs).mp hb) _ (mul_pos hs hR)

theorem GlobalBilateralLower.compact_limit {n d : ℕ} (hnd : n ≤ d)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ t : ℝ, AdmissibleRadius (μ j) t →
      ENNReal.ofReal (t ^ n / C) ≤ (μ j) (ball x t))
    (hdiam : ∀ t : ℝ, 0 < t → ∀ᶠ j in atTop, ENNReal.ofReal t ≤ ediam (μ j).support)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbad : ∀ᶠ j in atTop, GlobalBilateralLower n (μ j) ε) :
    GlobalBilateralLower n ν (ε / 64) := by
  intro a ha R hR
  have hb : ∀ᶠ j in atTop, ∀ b ∈ (μ j).support, b ∈ (univ : Set (Ambient d)) →
      ε ≤ bilateralBeta n (μ j) b (R / 2) := by
    filter_upwards [hbad] with j hj
    exact fun b hb _ => hj b hb (R / 2) (by positivity)
  have ht := compactTestConvergence_bilateralBeta_lower hnd μ ν hlocal C hC hlower hdiam
    univ isOpen_univ ε hε hε1 (R / 2) (by positivity) hb a ha (mem_univ a)
  simpa only [mul_div_cancel₀ R (by norm_num : (2 : ℝ) ≠ 0)] using! ht

end

end RieszRectifiability

end OAI
