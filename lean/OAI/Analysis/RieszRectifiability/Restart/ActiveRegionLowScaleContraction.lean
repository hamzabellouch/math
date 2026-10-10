import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionCellContraction
import OAI.Analysis.RieszRectifiability.Restart.ActiveRequestedScaleSelection

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology

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

include hS hε hεtiny hsmall hfit hmodel

theorem exists_active_region_low_scale_ball_contraction
    (p : Ambient d) (hp : p ∈ Set.range f)
    (r : ℝ) (hr : 0 < r) (hrtop : r ≤ latticeRadius R k / 16)
    (hD : cellRegionStoppingScale μ R hR k z Good p < r / 4) :
    ∃ F : unitInterval × ↥(Set.range f ∩ closedBall p r) → Ambient d,
      Continuous F ∧ (∀ x, F (0, x) = x.val) ∧ (∀ x, F (1, x) = p) ∧
      (∀ s, F (s, ⟨p, ⟨hp, mem_closedBall_self hr.le⟩⟩) = p) ∧
      (∀ w, F w ∈ Set.range f ∩ closedBall p (6144 * r)) := by
  obtain ⟨t, q, hq, hrlo, hrhi, hnear⟩ :=
    exists_active_cell_at_requested_radius μ R hR k z Good p r hr hrtop hD
  obtain ⟨F, hF, hzero, hone, hfixed, hball⟩ :=
    exists_active_region_cell_ball_contraction μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit f hmodel t q hq p hp
      (by have hqr := q.radius_pos; linarith) r hr (by linarith)
  refine ⟨F, hF, hzero, hone, hfixed, ?_⟩
  intro w
  refine ⟨(hball w).1, ?_⟩
  have hw : dist (F w) p ≤ 6 * q.radius := (hball w).2
  change dist (F w) p ≤ 6144 * r
  linarith

theorem exists_active_region_zero_scale_ball_contraction
    (p : Ambient d) (hzero : p ∈ cellRegionZeroSet μ R hR k z Good)
    (r : ℝ) (hr : 0 < r) (hrtop : r ≤ latticeRadius R k / 16) :
    ∃ F : unitInterval × ↥(Set.range f ∩ closedBall p r) → Ambient d,
      Continuous F ∧ (∀ x, F (0, x) = x.val) ∧ (∀ x, F (1, x) = p) ∧
      (∀ w, F w ∈ Set.range f ∩ closedBall p (6144 * r)) := by
  have hp : p ∈ Set.range f := hmodel.2.2.2.2.1 hzero
  have hD : cellRegionStoppingScale μ R hR k z Good p < r / 4 := by
    rw [show cellRegionStoppingScale μ R hR k z Good p = 0 from hzero]
    positivity
  obtain ⟨F, hF, hstart, hend, _, hball⟩ :=
    exists_active_region_low_scale_ball_contraction μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit f hmodel p hp r hr hrtop hD
  exact ⟨F, hF, hstart, hend, hball⟩

end

end RieszRectifiability

end OAI
