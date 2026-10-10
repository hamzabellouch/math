import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLimitCharts
import OAI.Analysis.RieszRectifiability.Surfaces.ContinuousPerturbedBallCoverage

namespace OAI

/-!
# Projection coverage of active-region limit charts

Continuous perturbation coverage turns the displacement bound for a cell chart
into a projected disk contained in the limit image. The quantitative smallness
assumption gives a disk of twice the cell radius inside a four-radius image ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology

theorem active_region_limit_cell_projection_covers_disk {n d : ℕ}
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
    (hq : q ∈ activeLevelIndex μ R hR k z Good t) :
    let B := (17039360 * ε) / 63
    closedBall ((S q).direction.orthogonalProjectionOnto q.center)
        (((5 / 2 : ℝ) - B) * q.radius) ⊆
      (S q).direction.orthogonalProjectionOnto ''
        (Set.range f ∩ closedBall q.center ((3 + B) * q.radius)) := by
  dsimp only
  let B := (17039360 * ε) / 63
  obtain ⟨H, hH, hHrange, hdisp, hlocal, _⟩ :=
    exists_active_region_limit_cell_chart μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit f hmodel t q hq
  have hcontinuous : Continuous (fun u => (S q).direction.orthogonalProjectionOnto (H u)) :=
    (S q).direction.orthogonalProjectionOnto.continuous.comp hH.continuous
  have hcover := closedBall_covered_by_continuous_perturbation
    ((S q).direction.orthogonalProjectionOnto q.center)
    ((5 / 2 : ℝ) * q.radius) (B * q.radius)
    (mul_nonneg (by norm_num) q.radius_pos.le)
    (fun u => (S q).direction.orthogonalProjectionOnto (H u)) hcontinuous hdisp
  intro a ha
  have ha' : a ∈ closedBall ((S q).direction.orthogonalProjectionOnto q.center)
      ((5 / 2 : ℝ) * q.radius - B * q.radius) := by
    change dist a ((S q).direction.orthogonalProjectionOnto q.center) ≤
      ((5 / 2 : ℝ) - B) * q.radius at ha
    change dist a ((S q).direction.orthogonalProjectionOnto q.center) ≤ _
    nlinarith
  obtain ⟨u, hu⟩ := hcover ha'
  exact ⟨H u, ⟨hHrange ⟨u, rfl⟩, hlocal u⟩, hu⟩

theorem active_region_limit_cell_projection_covers_double_disk {n d : ℕ}
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
    (hq : q ∈ activeLevelIndex μ R hR k z Good t) :
    closedBall ((S q).direction.orthogonalProjectionOnto q.center) (2 * q.radius) ⊆
      (S q).direction.orthogonalProjectionOnto ''
        (Set.range f ∩ closedBall q.center (4 * q.radius)) := by
  let B := (17039360 * ε) / 63
  have hB : B ≤ 1 / 2 := by dsimp [B]; nlinarith
  have hcover := active_region_limit_cell_projection_covers_disk μ R hR k z
    Good S hS ε hε hεtiny hsmall hfit f hmodel t q hq
  intro a ha
  have ha' : a ∈ closedBall ((S q).direction.orthogonalProjectionOnto q.center)
      (((5 / 2 : ℝ) - B) * q.radius) := by
    change dist a ((S q).direction.orthogonalProjectionOnto q.center) ≤ 2 * q.radius at ha
    change dist a ((S q).direction.orthogonalProjectionOnto q.center) ≤ _
    nlinarith [q.radius_pos]
  obtain ⟨x, hx, hxa⟩ := hcover ha'
  refine ⟨x, ⟨hx.1, ?_⟩, hxa⟩
  have hdist : dist x q.center ≤ (3 + B) * q.radius := hx.2
  change dist x q.center ≤ 4 * q.radius
  nlinarith [q.radius_pos]

end

end RieszRectifiability

end OAI
