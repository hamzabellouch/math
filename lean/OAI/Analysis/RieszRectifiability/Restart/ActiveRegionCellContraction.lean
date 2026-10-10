import Mathlib
import OAI.Analysis.RieszRectifiability.Surfaces.ConvexChartContraction
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLimitCharts

namespace OAI

/-!
# Contractions inside active-region cells

The local chart for an active cell captures a small ball in the limiting surface.
Contracting in its convex parameter ball gives a contraction within the limiting image,
with the chart's location estimate controlling the ambient displacement.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology

theorem exists_active_region_cell_ball_contraction {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (t : ℕ) (q : SupportCellDescendant μ R hR k z)
    (hq : q ∈ activeLevelIndex μ R hR k z Good t)
    (p : Ambient d) (hp : p ∈ Set.range f)
    (hpnear : dist p q.center ≤ (17 / 8 : ℝ) * q.radius)
    (r : ℝ) (hr : 0 < r) (hrsmall : r ≤ q.radius / 16) :
    ∃ F : unitInterval × ↥(Set.range f ∩ closedBall p r) → Ambient d,
      Continuous F ∧ (∀ x, F (0, x) = x.val) ∧ (∀ x, F (1, x) = p) ∧
      (∀ s, F (s, ⟨p, ⟨hp, mem_closedBall_self hr.le⟩⟩) = p) ∧
      (∀ w, F w ∈ Set.range f ∩ closedBall p (6 * q.radius)) := by
  let B := (17039360 * ε) / 63
  have hB : B ≤ 1 / 16 := by dsimp [B]; linarith
  have hBm := mul_le_mul_of_nonneg_right hB q.radius_pos.le
  obtain ⟨H, hHembed, hHrange, _, hHball, hcapture⟩ :=
    exists_active_region_limit_cell_chart μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit f hmodel t q hq
  have hcap : Set.range f ∩ closedBall p r ⊆ Set.range H := by
    intro x hx
    have hxball : x ∈ closedBall q.center (((9 / 4 : ℝ) - B) * q.radius) := by
      have hxp : dist x p ≤ r := hx.2
      have ht := dist_triangle x p q.center
      change dist x q.center ≤ ((9 / 4 : ℝ) - B) * q.radius
      nlinarith
    exact (hcapture ▸ (show x ∈ Set.range f ∩
      closedBall q.center (((9 / 4 : ℝ) - B) * q.radius) from ⟨hx.1, hxball⟩)).1
  have hpA : p ∈ Set.range f ∩ closedBall p r := ⟨hp, mem_closedBall_self hr.le⟩
  obtain ⟨F, hF, hzero, hone, hfixed, hFrange⟩ := exists_contraction_in_convex_chart
    (closedBall ((S q).direction.orthogonalProjectionOnto q.center) ((5 / 2 : ℝ) * q.radius))
    (convex_closedBall _ _) H hHembed.isEmbedding (Set.range f ∩ closedBall p r) hcap p hpA
  refine ⟨F, hF, hzero, hone, hfixed, ?_⟩
  intro w
  refine ⟨hHrange (hFrange w), ?_⟩
  obtain ⟨a, ha⟩ := hFrange w
  rw [← ha]
  have hqball : dist (H a) q.center ≤ (3 + B) * q.radius := hHball a
  have ht := dist_triangle (H a) q.center p
  rw [dist_comm q.center p] at ht
  change dist (H a) p ≤ 6 * q.radius
  have hrq := q.radius_pos
  nlinarith

end

end RieszRectifiability

end OAI
