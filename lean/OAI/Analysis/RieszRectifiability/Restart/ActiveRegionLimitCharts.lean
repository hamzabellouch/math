import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionLimitEmbedding
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionChartLift

namespace OAI

/-!
# Local charts for active-region limits

Finite-stage charts lift to the limiting model to give closed embedded charts on active
cells. Their projection error and ambient location remain quantitatively controlled,
and each chart agrees locally with the image of the full limiting map.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Topology
open scoped NNReal

theorem exists_active_region_limit_cell_chart {n d : ℕ}
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
    ∃ H : closedBall ((S q).direction.orthogonalProjectionOnto q.center)
        ((5 / 2 : ℝ) * q.radius) → Ambient d,
      IsClosedEmbedding H ∧ Set.range H ⊆ Set.range f ∧
      (∀ u, dist ((S q).direction.orthogonalProjectionOnto (H u)) u.val ≤ B * q.radius) ∧
      (∀ u, H u ∈ closedBall q.center ((3 + B) * q.radius)) ∧
      Set.range f ∩ closedBall q.center (((9 / 4 : ℝ) - B) * q.radius) =
        Set.range H ∩ closedBall q.center (((9 / 4 : ℝ) - B) * q.radius) := by
  let B := (17039360 * ε) / 63
  have hqdepth := ((mem_activeLevelIndex μ R hR k z Good t q).mp hq).1
  have hqr : q.radius = latticeRadius R (k + t) := by
    simp only [SupportCellDescendant.radius, hqdepth]
  have hcharts := activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit t
  obtain ⟨g, hg, _, hcoords, hcapture⟩ := hcharts q hq
  obtain ⟨j, hj, hjF⟩ := exists_active_region_finite_chart_lift μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit t g 2 hg (by rintro _ ⟨a, rfl⟩; exact (hcoords a).1)
  let H := fun a => f (j a)
  have hHcont : Continuous H := hmodel.1.comp hj.continuous
  have hginj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    have hp := congrArg (S q).direction.orthogonalProjectionOnto hab
    rwa [(hcoords a).2.1, (hcoords b).2.1] at hp
  have hjinj : Function.Injective j := by
    intro a b hab
    apply hginj
    rw [← hjF a, ← hjF b, hab]
  have hfinj := active_region_limit_injective μ R hR k z Good S hS
    ε hε hεtiny hsmall hfit f hmodel
  have hHinj : Function.Injective H := hfinj.comp hjinj
  have hHembed : IsClosedEmbedding H := hHcont.isClosedEmbedding hHinj
  have hHrange : Set.range H ⊆ Set.range f := by
    rintro _ ⟨a, rfl⟩
    exact ⟨j a, rfl⟩
  have hdisp : ∀ a, dist (H a) (g a) ≤ B * q.radius := by
    intro a
    have h := hmodel.2.2.2.1 t (j a)
    rw [hjF a, ← hqr] at h
    exact (dist_comm (H a) (g a)) ▸ h
  refine ⟨H, hHembed, hHrange, ?_, ?_, ?_⟩
  · intro a
    rw [← (hcoords a).2.1]
    have hp := (S q).direction.norm_starProjection_apply_le (H a - g a)
    rw [map_sub] at hp
    exact hp.trans (hdisp a)
  · intro a
    have ht := dist_triangle (H a) (g a) q.center
    have hgball : dist (g a) q.center ≤ 3 * q.radius := (hcoords a).2.2.2
    change dist (H a) q.center ≤ (3 + B) * q.radius
    linarith [hdisp a]
  · apply Set.Subset.antisymm
    · rintro x ⟨⟨u, rfl⟩, hx⟩
      have hy : activeRegionParameterMap μ R hR k z Good S hS t u ∈
          activeRegionSurface μ R hR k z Good S hS t := by
        rw [activeRegionSurface_eq_image]
        exact ⟨u.val, u.property, rfl⟩
      have htail := hmodel.2.2.2.1 t u
      rw [← hqr] at htail
      have hynear : activeRegionParameterMap μ R hR k z Good S hS t u ∈
          closedBall q.center ((9 / 4 : ℝ) * q.radius) := by
        have ht := dist_triangle (activeRegionParameterMap μ R hR k z Good S hS t u)
          (f u) q.center
        change dist (f u) q.center ≤ ((9 / 4 : ℝ) - B) * q.radius at hx
        change dist (activeRegionParameterMap μ R hR k z Good S hS t u) (f u) ≤
          B * q.radius at htail
        change dist (activeRegionParameterMap μ R hR k z Good S hS t u) q.center ≤
          (9 / 4 : ℝ) * q.radius
        nlinarith
      have hgin : activeRegionParameterMap μ R hR k z Good S hS t u ∈ Set.range g :=
        (hcapture ▸ (show activeRegionParameterMap μ R hR k z Good S hS t u ∈
          activeRegionSurface μ R hR k z Good S hS t ∩
          closedBall q.center ((9 / 4 : ℝ) * q.radius) from ⟨hy, hynear⟩)).1
      obtain ⟨a, ha⟩ := hgin
      have hju : j a = u :=
        (activeRegionParameterMap_antilipschitz μ R hR k z Good S hS
          ε hε hεtiny hsmall hfit t).injective ((hjF a).trans ha)
      exact ⟨⟨a, by dsimp [H]; rw [hju]⟩, hx⟩
    · intro x hx
      exact ⟨hHrange hx.1, hx.2⟩

end

end RieszRectifiability

end OAI
