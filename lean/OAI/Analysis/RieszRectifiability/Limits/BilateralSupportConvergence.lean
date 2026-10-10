import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.BoundedBoxHeight
import OAI.Analysis.RieszRectifiability.Limits.CompactReverseSupportTube

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem compactTestConvergence_support_tube_of_AD_lower {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (a : Ambient d) (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ x ∈ ball a R, x ∈ (μ j).support → infDist x ν.support < ε := by
  obtain ⟨c, hc, hbc⟩ := eventual_lower_ball_mass_of_AD_lower n μ C hC hlower hdiam
    (ε / 2) (half_pos hε)
  have hzero : ∀ᵐ x ∂ν, infDist x ν.support = 0 := by
    filter_upwards [ν.support_mem_ae] with x hx
    exact infDist_zero_of_mem hx
  apply compactTestConvergence_support_tube μ ν hlocal (fun x => infDist x ν.support)
    1 (lipschitz_infDist_pt ν.support) hzero a R ε (ε / 2) c hε hc (by simp)
  filter_upwards [hbc] with j hj
  exact fun x _ hx => hj x hx

theorem compactTestConvergence_bilateral_support_tubes {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (a : Ambient d) (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop,
      (∀ x ∈ ball a R, x ∈ (μ j).support → infDist x ν.support < ε) ∧
      (∀ x ∈ ball a R, x ∈ ν.support → infDist x (μ j).support < ε) :=
  (compactTestConvergence_support_tube_of_AD_lower n μ ν hlocal C hC hlower hdiam a R ε hε).and
    (compactTestConvergence_reverse_support_tube μ ν hlocal a R ε hε)

end

end RieszRectifiability

end OAI
