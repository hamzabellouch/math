import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitGrowth

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal CompactlySupported

theorem compactTestConvergence_nearby_support {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (x : Ambient d) (hx : x ∈ ν.support)
    (r : ℝ) (hr : 0 < r) :
    ∀ᶠ j in atTop, ∃ y, y ∈ (μ j).support ∧ y ∈ ball x r := by
  have hsub : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
  obtain ⟨f, hone, hzero, hcomp, hbounds⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall x (r / 2)) isOpen_ball.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hsub)
  let F : C_c(Ambient d, ℝ) := ⟨f, hcomp⟩
  have hmass : 0 < ν.real (ball x (r / 2)) := by
    apply ENNReal.toReal_pos
    · exact ne_of_gt ((ν.mem_support_iff_forall x).mp hx (ball x (r / 2))
        (ball_mem_nhds x (by positivity)))
    · exact ((measure_mono ball_subset_closedBall).trans_lt
        (isCompact_closedBall x (r / 2)).measure_lt_top).ne
  have hpos : 0 < ∫ y, F y ∂ν := hmass.trans_le
    (ball_mass_le_compact_test_integral ν F x (r / 2) (fun y => (hbounds y).1)
      (fun _ hy => hone (ball_subset_closedBall hy)))
  filter_upwards [(hlocal F).eventually (lt_mem_nhds hpos)] with j hj
  by_contra hnone
  have hzeroae : ∀ᵐ y ∂μ j, F y = 0 := by
    filter_upwards [(μ j).support_mem_ae] with y hy
    exact hzero (show y ∈ (ball x r)ᶜ from fun hball => hnone ⟨y, hy, hball⟩)
  have heq : (∫ y, F y ∂μ j) = 0 := integral_eq_zero_of_ae hzeroae
  rw [heq] at hj
  exact (lt_irrefl 0) hj

theorem compactTestConvergence_support_zero_of_tubes {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (q : Ambient d → ℝ) (hq : Continuous q)
    (hqnn : ∀ x, 0 ≤ q x)
    (htube : ∀ R ε : ℝ, 0 < R → 0 < ε →
      ∀ᶠ j in atTop, ∀ x ∈ ball (0 : Ambient d) R, x ∈ (μ j).support → q x < ε) :
    ∀ x ∈ ν.support, q x = 0 := by
  intro x hx
  by_contra hne
  have hpos : 0 < q x := lt_of_le_of_ne (hqnn x) (Ne.symm hne)
  let ε := q x / 2
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hnhds : {y | ε < q y} ∈ 𝓝 x :=
    (isOpen_lt continuous_const hq).mem_nhds (show ε < q x by dsimp only [ε]; linarith)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hR : 0 < ‖x‖ + r := by linarith [norm_nonneg x]
  obtain ⟨j, hjnear, hjtube⟩ := ((compactTestConvergence_nearby_support μ ν hlocal x hx r hr).and
    (htube (‖x‖ + r) ε hR hε)).exists
  obtain ⟨y, hysupport, hyball⟩ := hjnear
  have hy0 : y ∈ ball (0 : Ambient d) (‖x‖ + r) := by
    have htri := dist_triangle y x (0 : Ambient d)
    have hyr : dist y x < r := hyball
    simp only [mem_ball, dist_zero_right] at htri ⊢
    linarith
  exact (not_lt_of_ge (hball hyball).le) (hjtube y hy0 hysupport)

theorem compactTestConvergence_ae_zero_of_tubes {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (q : Ambient d → ℝ) (hq : Continuous q)
    (hqnn : ∀ x, 0 ≤ q x)
    (htube : ∀ R ε : ℝ, 0 < R → 0 < ε →
      ∀ᶠ j in atTop, ∀ x ∈ ball (0 : Ambient d) R, x ∈ (μ j).support → q x < ε) :
    ∀ᵐ x ∂ν, q x = 0 := by
  filter_upwards [ν.support_mem_ae] with x hx
  exact compactTestConvergence_support_zero_of_tubes μ ν hlocal q hq hqnn htube x hx

end

end RieszRectifiability

end OAI
