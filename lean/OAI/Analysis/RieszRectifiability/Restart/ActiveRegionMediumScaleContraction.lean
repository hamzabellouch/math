import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionPositiveScaleContraction
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLowScaleContraction

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology

theorem exists_active_region_below_first_scale_ball_contraction {n d : ℕ}
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
    (p : Ambient d) (hp : p ∈ Set.range f)
    (hDsmall : cellRegionStoppingScale μ R hR k z Good p < latticeRadius R (k + 1))
    (r : ℝ) (hr : 0 < r) (hrtop : r ≤ latticeRadius R k / 16) :
    ∃ F : unitInterval × ↥(Set.range f ∩ closedBall p r) → Ambient d,
      Continuous F ∧ (∀ x, F (0, x) = x.val) ∧ (∀ x, F (1, x) = p) ∧
      (∀ s, F (s, ⟨p, ⟨hp, mem_closedBall_self hr.le⟩⟩) = p) ∧
      (∀ w, F w ∈ Set.range f ∩ closedBall p (50331648 * r)) := by
  by_cases hlow : cellRegionStoppingScale μ R hR k z Good p < r / 4
  · obtain ⟨F, hF, hzero, hone, hfixed, hball⟩ :=
      exists_active_region_low_scale_ball_contraction μ R hR k z Good S hS
        ε hε hεtiny hsmall hfit f hmodel p hp r hr hrtop hlow
    refine ⟨F, hF, hzero, hone, hfixed, ?_⟩
    intro w
    refine ⟨(hball w).1, ?_⟩
    have hb : dist (F w) p ≤ 6144 * r := (hball w).2
    change dist (F w) p ≤ 50331648 * r
    linarith
  have hDpos : 0 < cellRegionStoppingScale μ R hR k z Good p := by linarith
  by_cases hsmallr : r ≤ cellRegionStoppingScale μ R hR k z Good p / 2048
  · obtain ⟨F, hF, hzero, hone, hfixed, hball⟩ :=
      exists_active_region_positive_scale_small_ball_contraction μ R hR k z Good S hS
        ε hε hεtiny hsmall hfit f hmodel p hp hDpos hDsmall r hr hsmallr
    refine ⟨F, hF, hzero, hone, hfixed, ?_⟩
    intro w
    refine ⟨(hball w).1, ?_⟩
    have hb : dist (F w) p ≤ 1024 * r := (hball w).2
    change dist (F w) p ≤ 50331648 * r
    linarith
  obtain ⟨q, hq, hqhi, hqlo, hnear⟩ :=
    exists_active_parent_at_stopping_scale μ R hR k z Good p hDpos hDsmall
  have hqF : q ∈ activeLevelIndex μ R hR k z Good q.depth :=
    (mem_activeLevelIndex μ R hR k z Good q.depth q).mpr ⟨rfl, hq⟩
  obtain ⟨F, hF, hzero, hone, hfixed, hball⟩ :=
    exists_active_region_cell_ball_contraction μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit f hmodel q.depth q hqF p hp
      (by have hqr := q.radius_pos; linarith) r hr (by linarith)
  refine ⟨F, hF, hzero, hone, hfixed, ?_⟩
  intro w
  refine ⟨(hball w).1, ?_⟩
  have hb : dist (F w) p ≤ 6 * q.radius := (hball w).2
  change dist (F w) p ≤ 50331648 * r
  linarith

end

end RieszRectifiability

end OAI
