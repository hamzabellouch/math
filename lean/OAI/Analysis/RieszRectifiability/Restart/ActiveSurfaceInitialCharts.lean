import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveSurfaceCharts
import OAI.Analysis.RieszRectifiability.Nets.SupportCellRoot
import OAI.Analysis.RieszRectifiability.Surfaces.FittingPlaneInputChart

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem active_surface_charts_initial {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 2048)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) :
    HasActiveSurfaceCharts μ R hR k z Good 0 S ε
      (S (supportCellRoot μ R hR k z) : Set (Ambient d)) := by
  intro q hq
  have hqA := (mem_activeLevelIndex μ R hR k z Good 0 q).mp hq
  have heq := q.eq_root_of_zero_depth hqA.1
  have hplane : (S (supportCellRoot μ R hR k z) : Set (Ambient d)) = (S q : Set (Ambient d)) := by
    rw [heq]
  rw [hplane]
  obtain ⟨g, hgLip, hgNormal, hgCoords, hgRange⟩ := exists_fitting_plane_input_chart μ
    q.center q.center_mem_support q.radius q.radius_pos ε hεsmall (S q) (hS q) (hfit q hqA.2)
  refine ⟨g, hgLip, hgNormal.weaken (zero_le), ?_, ?_⟩
  · intro u
    refine ⟨(hgCoords u).1, (hgCoords u).2.1, ?_, (hgCoords u).2.2⟩
    rw [infDist_zero_of_mem (hgCoords u).1]
    exact mul_nonneg (mul_nonneg (by norm_num) hε.le) q.radius_pos.le
  · ext x
    constructor
    · intro hx
      refine ⟨?_, hx.2⟩
      rw [hgRange]
      refine ⟨hx.1, ?_⟩
      have hp := (S q).direction.norm_starProjection_apply_le (x - q.center)
      rw [map_sub, ← dist_eq_norm, ← dist_eq_norm] at hp
      have hx' : dist x q.center ≤ (9 / 4 : ℝ) * q.radius := hx.2
      have hr := q.radius_pos
      change dist ((S q).direction.starProjection x) ((S q).direction.starProjection q.center) ≤
        (5 / 2 : ℝ) * q.radius
      linarith
    · rintro ⟨⟨u, rfl⟩, hx⟩
      exact ⟨(hgCoords u).1, hx⟩

end

end RieszRectifiability

end OAI
