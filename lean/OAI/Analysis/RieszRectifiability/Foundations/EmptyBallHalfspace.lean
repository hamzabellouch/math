import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitSupport

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem exists_nearest_point_to_hole {d : ℕ} (E : Set (Ambient d))
    (hclosed : IsClosed E) (hne : E.Nonempty) (c : Ambient d) (hc : c ∉ E) :
    ∃ a ∈ E, a ≠ c ∧ ∀ y ∈ E, dist a c ≤ dist y c := by
  obtain ⟨a, ha, heq⟩ := hclosed.exists_infDist_eq_dist hne c
  refine ⟨a, ha, (fun hac => hc (hac ▸ ha)), ?_⟩
  intro y hy
  rw [dist_comm a c, ← heq, dist_comm y c]
  exact infDist_le_dist_of_mem hy

theorem nearest_point_quadratic_constraint {d : ℕ} (a c y : Ambient d)
    (hmin : dist a c ≤ dist y c) :
    0 ≤ 2 * inner ℝ (a - c) (y - a) + ‖y - a‖ ^ 2 := by
  have hs := pow_le_pow_left₀ (dist_nonneg : 0 ≤ dist a c) hmin 2
  have heq : y - c = (a - c) + (y - a) := by abel
  simp only [dist_eq_norm] at hs
  rw [heq, norm_add_sq_real] at hs
  linarith

theorem nearest_point_rescaled_constraint {d : ℕ} (a c x : Ambient d)
    (r : ℝ) (hr : 0 < r) (hmin : dist a c ≤ dist (a + r • x) c) :
    0 ≤ 2 * inner ℝ (a - c) x + r * ‖x‖ ^ 2 := by
  have h := nearest_point_quadratic_constraint a c (a + r • x) hmin
  have heq : a + r • x - a = r • x := by abel
  rw [heq, inner_smul_right, norm_smul, Real.norm_of_nonneg hr.le] at h
  have hp : 0 ≤ r * (2 * inner ℝ (a - c) x + r * ‖x‖ ^ 2) := by nlinarith
  exact nonneg_of_mul_nonneg_right hp hr

theorem compactTestConvergence_halfspace_of_quadratic_constraint {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (e : Ambient d)
    (r : ℕ → ℝ) (hr : ∀ j, 0 ≤ r j) (hr0 : Tendsto r atTop (𝓝 0))
    (hside : ∀ j x, x ∈ (μ j).support → 0 ≤ 2 * inner ℝ e x + r j * ‖x‖ ^ 2) :
    ∀ x ∈ ν.support, 0 ≤ inner ℝ e x := by
  have hzero : ∀ x ∈ ν.support, max 0 (-inner ℝ e x) = 0 := by
    apply compactTestConvergence_support_zero_of_tubes μ ν hlocal
      (fun x => max 0 (-inner ℝ e x)) (by fun_prop) (fun _ => le_max_left _ _)
    intro R ε hR hε
    have hconv : Tendsto (fun j => r j * R ^ 2) atTop (𝓝 0) := by
      simpa only [zero_mul] using! hr0.mul_const (R ^ 2)
    filter_upwards [hconv.eventually (gt_mem_nhds (by linarith : 0 < 2 * ε))] with j hj
    intro x hx hxsupport
    have hxR : ‖x‖ ≤ R := (mem_ball_zero_iff.mp hx).le
    have hs : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hxR 2
    have hp := mul_le_mul_of_nonneg_left hs (hr j)
    have h := hside j x hxsupport
    apply max_lt_iff.mpr
    exact ⟨hε, by linarith⟩
  intro x hx
  have h := le_max_right (0 : ℝ) (-inner ℝ e x)
  rw [hzero x hx] at h
  linarith

end

end RieszRectifiability

end OAI
