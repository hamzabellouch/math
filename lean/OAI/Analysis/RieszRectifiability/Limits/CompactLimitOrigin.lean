import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitGrowth
import OAI.Analysis.RieszRectifiability.Kernel.BoundedBoxHeight

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal CompactlySupported

theorem compactTestConvergence_mem_support_of_ball_masses {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (x : Ambient d)
    (hmass : ∀ r : ℝ, 0 < r → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ j in atTop, c ≤ (μ j).real (ball x r)) : x ∈ ν.support := by
  have hball : ∀ r : ℝ, 0 < r → 0 < ν (ball x r) := by
    intro r hr
    have hsub : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
    obtain ⟨f, hone, hzero, hcomp, hbounds⟩ := exists_continuous_one_zero_of_isCompact
      (isCompact_closedBall x (r / 2)) isOpen_ball.isClosed_compl
        (disjoint_compl_right_iff_subset.mpr hsub)
    let F : C_c(Ambient d, ℝ) := ⟨f, hcomp⟩
    obtain ⟨c, hc, hmassc⟩ := hmass (r / 2) (by positivity)
    have hbound : ∀ᶠ j in atTop, c ≤ ∫ y, F y ∂μ j := by
      filter_upwards [hmassc] with j hj
      exact hj.trans (ball_mass_le_compact_test_integral (μ j) F x (r / 2)
        (fun y => (hbounds y).1) (fun _ hy => hone (ball_subset_closedBall hy)))
    have hlimit : c ≤ ∫ y, F y ∂ν := ge_of_tendsto (hlocal F) hbound
    have hpos : 0 < ν.real (ball x r) := hc.trans_le (hlimit.trans
      (compact_test_integral_le_ball_mass ν F x r (fun y => (hbounds y).2) (fun _ hy => hzero hy)))
    exact (ENNReal.toReal_pos_iff.mp hpos).1
  apply (ν.mem_support_iff_forall x).mpr
  intro U hU
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hU
  exact (hball r hr).trans_le (measure_mono hsub)

theorem compactTestConvergence_origin_mem_support {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support) : (0 : Ambient d) ∈ ν.support := by
  apply compactTestConvergence_mem_support_of_ball_masses μ ν hlocal 0
  intro r hr
  obtain ⟨c, hc, hmass⟩ := eventual_lower_ball_mass_of_AD_lower n μ C hC hlower hdiam r hr
  refine ⟨c, hc, ?_⟩
  filter_upwards [hmass] with j hj
  exact hj 0 (hzero j)

end

end RieszRectifiability

end OAI
