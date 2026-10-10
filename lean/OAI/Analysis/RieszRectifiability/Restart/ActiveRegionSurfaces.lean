import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveSurfaceInitialCharts
import OAI.Analysis.RieszRectifiability.Restart.ActiveSurfaceChartInductionStep

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i))

def activeRegionSurface : ℕ → Set (Ambient d)
  | 0 => (S (supportCellRoot μ R hR k z) : Set (Ambient d))
  | t + 1 => (activeLevelProjectionMap μ R hR k z Good (t + 1) S hS) ''
      activeRegionSurface t

def activeRegionParameterMap : ℕ → Ambient d → Ambient d
  | 0 => id
  | t + 1 => activeLevelProjectionMap μ R hR k z Good (t + 1) S hS ∘
      activeRegionParameterMap t

theorem activeRegionSurface_eq_image (t : ℕ) :
    activeRegionSurface μ R hR k z Good S hS t =
      (activeRegionParameterMap μ R hR k z Good S hS t) ''
        (S (supportCellRoot μ R hR k z) : Set (Ambient d)) := by
  induction t with
  | zero => simp only [activeRegionSurface, activeRegionParameterMap, Set.image_id]
  | succ t ih =>
    simp only [activeRegionSurface, activeRegionParameterMap, ih, Set.image_image, Function.comp_def]

theorem activeRegionParameterMap_continuous (t : ℕ) :
    Continuous (activeRegionParameterMap μ R hR k z Good S hS t) := by
  induction t with
  | zero => exact continuous_id
  | succ t ih =>
    exact (activeLevelProjectionMap_continuous μ R hR k z Good (t + 1) S hS).comp ih

theorem activeRegionSurface_charts (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) (t : ℕ) :
    HasActiveSurfaceCharts μ R hR k z Good t S ε
      (activeRegionSurface μ R hR k z Good S hS t) := by
  induction t with
  | zero =>
    exact active_surface_charts_initial μ R hR k z Good S hS ε hε (by linarith) hfit
  | succ t ih =>
    exact active_surface_charts_successor μ R hR k z Good t S hS ε hε hεtiny hsmall hfit
      (activeRegionSurface μ R hR k z Good S hS t) ih

theorem activeRegionSurface_successor_displacement (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) (t : ℕ) :
    ∀ x ∈ activeRegionSurface μ R hR k z Good S hS t,
      dist (activeLevelProjectionMap μ R hR k z Good (t + 1) S hS x) x ≤
        (17039360 * ε) * latticeRadius R (k + (t + 1)) := by
  have hcharts := activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit t
  apply activeLevelProjectionMap_successor_surface_displacement μ R hR k z Good t
    S hS ε hε (by linarith) hfit (activeRegionSurface μ R hR k z Good S hS t)
  intro q hq x hx hnear
  have hqA := (mem_activeLevelIndex μ R hR k z Good t q).mp hq
  have hrad : q.radius = latticeRadius R (k + t) := by
    simp only [SupportCellDescendant.radius, hqA.1]
  have h := HasActiveCellSurfaceChart.height_on_inner_ball q (S q) ε
    (activeRegionSurface μ R hR k z Good S hS t) (hcharts q hq) x hx
      (by simpa only [hrad] using! hnear)
  simpa only [hrad] using! h

end

end RieszRectifiability

end OAI
