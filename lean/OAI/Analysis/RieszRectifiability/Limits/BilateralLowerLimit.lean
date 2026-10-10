import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.BilateralBetaWitnesses
import OAI.Analysis.RieszRectifiability.Flatness.LocalFlatBallExclusion

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem compactTestConvergence_bilateralBeta_lower {n d : ℕ} (hnd : n ≤ d)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ t : ℝ, AdmissibleRadius (μ j) t →
      ENNReal.ofReal (t ^ n / C) ≤ (μ j) (ball x t))
    (hdiam : ∀ t : ℝ, 0 < t → ∀ᶠ j in atTop, ENNReal.ofReal t ≤ ediam (μ j).support)
    (U : Set (Ambient d)) (hU : IsOpen U) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (r : ℝ) (hr : 0 < r)
    (hbad : ∀ᶠ j in atTop, ∀ b ∈ (μ j).support, b ∈ U → ε ≤ bilateralBeta n (μ j) b r)
    (a : Ambient d) (ha : a ∈ ν.support) (haU : a ∈ U) :
    ε / 64 ≤ bilateralBeta n ν a (2 * r) := by
  by_contra hnot
  obtain ⟨S, hS, he⟩ := exists_bilateral_plane_error_lt hnd ν a (2 * r) (ε / 64) (lt_of_not_ge hnot)
  have hp := bilateralPlaneError_lt_pointwise ν ⟨a, ha⟩ a (2 * r) (ε / 64) (by positivity) S hS he
  apply compactTestConvergence_excludes_local_flat_ball n μ ν hlocal C hC hlower hdiam
    U hU ε hε hε1 r hr hbad a ha haU
  refine ⟨S, hS, ?_, ?_⟩
  · intro x hx hxs
    have ht := hp.1 x hx hxs
    nlinarith [mul_pos hε hr]
  · intro x hx hxs
    have ht := hp.2 x hx hxs
    nlinarith [mul_pos hε hr]

end

end RieszRectifiability

end OAI
