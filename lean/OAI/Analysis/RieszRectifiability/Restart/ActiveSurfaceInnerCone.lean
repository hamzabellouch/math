import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveSurfaceCharts

namespace OAI

/-!
# Inner-ball cone bounds for active surfaces

The capture property places surface points in the inner ball inside an active chart.
Its normal-component Lipschitz bound and the contraction of orthogonal coordinates
control normal increments by ambient distances.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem HasActiveCellSurfaceChart.normal_increment_on_inner_ball {d : ℕ}
    {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R} {k : ℕ}
    {z : (supportLatticeNets μ R hR k).points}
    (q : SupportCellDescendant μ R hR k z) (S : AffineSubspace ℝ (Ambient d))
    (ε : ℝ) (hε : 0 ≤ ε) (A : Set (Ambient d)) (hchart : HasActiveCellSurfaceChart q S ε A)
    (x y : Ambient d) (hx : x ∈ A) (hy : y ∈ A)
    (hxnear : x ∈ closedBall q.center ((9 / 4 : ℝ) * q.radius))
    (hynear : y ∈ closedBall q.center ((9 / 4 : ℝ) * q.radius)) :
    ‖(S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (x - y)‖ ≤
      (4 * activeProjectionError d ε) * dist x y := by
  obtain ⟨g, _, hnormal, hcoords, hcapture⟩ := hchart
  have hxg : x ∈ Set.range g := (hcapture ▸ (show x ∈ A ∩
    closedBall q.center ((9 / 4 : ℝ) * q.radius) from ⟨hx, hxnear⟩)).1
  have hyg : y ∈ Set.range g := (hcapture ▸ (show y ∈ A ∩
    closedBall q.center ((9 / 4 : ℝ) * q.radius) from ⟨hy, hynear⟩)).1
  obtain ⟨u, hu⟩ := hxg
  obtain ⟨v, hv⟩ := hyg
  have hnonneg : 0 ≤ 4 * activeProjectionError d ε := by unfold activeProjectionError; positivity
  have hn := hnormal.dist_le_mul u v
  rw [Real.coe_toNNReal _ hnonneg, hu, hv] at hn
  have hux : S.direction.orthogonalProjectionOnto x = u.val := by rw [← hu]; exact (hcoords u).2.1
  have hvy : S.direction.orthogonalProjectionOnto y = v.val := by rw [← hv]; exact (hcoords v).2.1
  have huv : dist u v ≤ dist x y := by
    change dist u.val v.val ≤ dist x y
    rw [← hux, ← hvy]
    have hp := S.direction.norm_starProjection_apply_le (x - y)
    rw [map_sub, ← dist_eq_norm (S.direction.starProjection x) (S.direction.starProjection y),
      ← dist_eq_norm x y] at hp
    exact hp
  rw [map_sub, ← dist_eq_norm]
  exact hn.trans (mul_le_mul_of_nonneg_left huv hnonneg)

end

end RieszRectifiability

end OAI
