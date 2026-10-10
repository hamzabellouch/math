import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionSurfaces
import OAI.Analysis.RieszRectifiability.Restart.ActiveCellSurfaceApproximation

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)

include hε hεtiny hsmall hfit

theorem activeRegionSurface_approximates_region_limit (t : ℕ)
    (x : Ambient d) (hx : x ∈ cellRegionLimit μ R hR k z Good) :
    ∃ y ∈ activeRegionSurface μ R hR k z Good S hS t,
      dist x y ≤ (263168 * ε) * latticeRadius R (k + t) := by
  obtain ⟨q, hq, _⟩ := exists_unique_support_descendant_at_point μ R hR k z x hx.1 t
  have hqA := activeRegionCell_of_region_limit Good x hx q hq.2
  have hqF : q ∈ activeLevelIndex μ R hR k z Good t :=
    (mem_activeLevelIndex μ R hR k z Good t q).mpr ⟨hq.1, hqA⟩
  have hrad : q.radius = latticeRadius R (k + t) := by simp only [SupportCellDescendant.radius, hq.1]
  have hcharts := activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit t
  have hxμ := supportLatticeCell_subset_support μ R hR k z hx.1.1
  obtain ⟨y, hy, hxy⟩ := active_cell_support_point_near_surface μ R hR k z q (S q) (hS q)
    ε (hfit q hqA) (activeRegionSurface μ R hR k z Good S hS t) (hcharts q hqF)
    x hxμ (q.dist_center_of_mem x hq.2)
  exact ⟨y, hy, by simpa only [hrad] using! hxy⟩

theorem activeRegionSurface_near_support_in_active_ball (t : ℕ)
    (q : SupportCellDescendant μ R hR k z)
    (hq : q ∈ activeLevelIndex μ R hR k z Good t)
    (x : Ambient d) (hx : x ∈ activeRegionSurface μ R hR k z Good S hS t)
    (hnear : x ∈ closedBall q.center ((9 / 4 : ℝ) * latticeRadius R (k + t))) :
    infDist x μ.support ≤ (263168 * ε) * latticeRadius R (k + t) := by
  have hqA := (mem_activeLevelIndex μ R hR k z Good t q).mp hq
  have hrad : q.radius = latticeRadius R (k + t) := by simp only [SupportCellDescendant.radius, hqA.1]
  have hcharts := activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit t
  have h := active_cell_surface_point_near_support μ R hR k z q (S q) (hS q) ε
    (hfit q hqA.2) (activeRegionSurface μ R hR k z Good S hS t) (hcharts q hq)
    (by linarith : ε ≤ 1 / 524288) x hx (by simpa only [hrad] using! hnear)
  simpa only [hrad] using! h

end

end RieszRectifiability

end OAI
