import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveScaleBallSelection
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionPositiveScaleBiCharts
import OAI.Analysis.RieszRectifiability.Surfaces.PlaneChartBallArea

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (f : S (supportCellRoot μ R hR k z) → Ambient d)
  (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)

include hε hεtiny hsmall hfit hmodel

theorem active_region_chart_subset_ball_area_le
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (A : Set (Ambient d))
    (hnear : A ⊆ closedBall q.center ((17 / 8 : ℝ) * q.radius))
    (hscale : ∀ x ∈ A, q.radius / 8192 ≤ cellRegionStoppingScale μ R hR k z Good x)
    (p : Ambient d) (r : ℝ) (hr : 0 < r) (hball : A ⊆ closedBall p r) :
    (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ A) ≤
      planeChartBallAreaConstant n 16 64 * (ENNReal.ofReal r) ^ n := by
  obtain ⟨H, hLip, hsep, _, hcover⟩ :=
    exists_active_region_positive_scale_bilipschitz_chart μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit f hmodel q hq A hnear hscale
  have hsub : Set.range f ∩ A ⊆ Set.range H ∩ closedBall p r :=
    fun _ hx => ⟨hcover hx, hball hx.2⟩
  exact (measure_mono hsub).trans
    (plane_chart_ball_hausdorffMeasure_le (S q).direction (hS q).2 _ H 16 64
      (by norm_num) hLip hsep p r hr)

theorem active_region_positive_scale_local_ball_area_le
    (p : Ambient d)
    (hDpos : 0 < cellRegionStoppingScale μ R hR k z Good p)
    (hDsmall : cellRegionStoppingScale μ R hR k z Good p < latticeRadius R (k + 1))
    (r : ℝ) (hr : 0 < r)
    (hrsmall : r ≤ cellRegionStoppingScale μ R hR k z Good p / 16) :
    (μH[(n : ℝ)] : Measure (Ambient d)) (Set.range f ∩ closedBall p r) ≤
      planeChartBallAreaConstant n 16 64 * (ENNReal.ofReal r) ^ n := by
  obtain ⟨q, hq, hqhi, hqlo, hnear⟩ :=
    exists_active_parent_at_stopping_scale μ R hR k z Good p hDpos hDsmall
  obtain ⟨hball, hscale⟩ := active_stopping_ball_chart_geometry μ R hR k z Good p q hqhi hqlo hnear
  have hsub := closedBall_subset_closedBall hrsmall (x := p)
  exact active_region_chart_subset_ball_area_le μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hmodel q hq (closedBall p r)
    (hsub.trans hball) (fun x hx => hscale x (hsub hx)) p r hr Set.Subset.rfl

end

end RieszRectifiability

end OAI
