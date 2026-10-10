import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitSupport

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal CompactlySupported

theorem compactTestConvergence_lower_ball_mass {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (x : Ambient d) (hx : x ∈ ν.support)
    (r b : ℝ) (hr : 0 < r)
    (hlower : ∀ᶠ j in atTop, ∀ y ∈ (μ j).support, b ≤ (μ j).real (ball y (r / 4))) :
    b ≤ ν.real (ball x r) := by
  have hsub : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
  obtain ⟨f, hone, hzero, hcomp, hbounds⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall x (r / 2)) isOpen_ball.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hsub)
  let F : C_c(Ambient d, ℝ) := ⟨f, hcomp⟩
  have hbound : ∀ᶠ j in atTop, b ≤ ∫ z, F z ∂μ j := by
    filter_upwards [hlower, compactTestConvergence_nearby_support μ ν hlocal x hx
      (r / 4) (by positivity)] with j hj hnear
    obtain ⟨y, hysupp, hyball⟩ := hnear
    apply (hj y hysupp).trans
    apply ball_mass_le_compact_test_integral (μ j) F y (r / 4) (fun z => (hbounds z).1)
    intro z hz
    apply hone
    have htri := dist_triangle z y x
    have hzy : dist z y < r / 4 := hz
    have hyx : dist y x < r / 4 := hyball
    exact mem_closedBall.mpr (by linarith)
  have hlimit : b ≤ ∫ z, F z ∂ν := ge_of_tendsto (hlocal F) hbound
  exact hlimit.trans (compact_test_integral_le_ball_mass ν F x r
    (fun z => (hbounds z).2) (fun _ hz => hzero hz))

theorem compactTestConvergence_AD_lower {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support) :
    ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / (C * 4 ^ n)) ≤ ν (ball x r) := by
  intro x hx r hr
  have hquarter : 0 < r / 4 := by positivity
  have heq : (r / 4) ^ n / C = r ^ n / (C * 4 ^ n) := by
    rw [div_pow]
    ring
  have hbound : ∀ᶠ j in atTop, ∀ y ∈ (μ j).support,
      r ^ n / (C * 4 ^ n) ≤ (μ j).real (ball y (r / 4)) := by
    filter_upwards [hdiam (r / 4) hquarter] with j hj
    intro y hy
    have hfinite : (μ j) (ball y (r / 4)) ≠ ∞ :=
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall y (r / 4)).measure_lt_top).ne
    have h := ENNReal.toReal_mono hfinite (hlower j y hy (r / 4) ⟨hquarter, hj⟩)
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (r / 4) ^ n / C)] at h
    simpa only [heq, Measure.real] using! h
  have hreal := compactTestConvergence_lower_ball_mass μ ν hlocal x hx r _ hr hbound
  calc
    _ ≤ ENNReal.ofReal (ν.real (ball x r)) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := ENNReal.ofReal_toReal
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top).ne

end

end RieszRectifiability

end OAI
