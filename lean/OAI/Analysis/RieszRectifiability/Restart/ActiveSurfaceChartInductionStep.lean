import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveSurfaceCharts
import OAI.Analysis.RieszRectifiability.Restart.ActiveSurfaceTransitionTools

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (A : Set (Ambient d)) (hcharts : HasActiveSurfaceCharts μ R hR k z Good t S ε A)

include hS hε hεtiny hsmall hfit hcharts

theorem active_surface_successor_input_chart
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ activeLevelIndex μ R hR k z Good (t + 1)) :
    HasActiveCellInputChart i (S i) A := by
  have hiA := (mem_activeLevelIndex μ R hR k z Good (t + 1) i).mp hi
  obtain ⟨q, hqdepth, hsub, hc⟩ := i.exists_ancestor_at_depth t (by rw [hiA.1]; omega)
  have hqA : activeRegionCell Good q :=
    activeRegionCell_ancestor Good i q hiA.2 (by rw [hqdepth, hiA.1]; omega) hsub
  have hq : q ∈ activeLevelIndex μ R hR k z Good t :=
    (mem_activeLevelIndex μ R hR k z Good t q).mpr ⟨hqdepth, hqA⟩
  have hscale : q.radius = 64 * i.radius := by
    simp only [SupportCellDescendant.radius, hqdepth, hiA.1]
    rw [← Nat.add_assoc, latticeRadius_succ]
    ring
  have hnear := q.dist_center_of_mem i.center hc
  obtain ⟨g, hgLip, hgNormal, hgCoords, hgCapture⟩ := hcharts q hq
  let L := Real.toNNReal (4 * activeProjectionError d ε)
  obtain ⟨hη, _⟩ := activeProjectionError_small_parameters d ε hε (by linarith)
  have hL : (L : ℝ) + 2048 * ε ≤ 1 / 8 := by
    change (Real.toNNReal (4 * activeProjectionError d ε) : ℝ) + 2048 * ε ≤ 1 / 8
    rw [Real.coe_toNNReal _ (mul_nonneg (by norm_num) hη)]
    linarith
  obtain ⟨g', hg'Lip, _, hg'Coords, hg'Range⟩ :=
    exists_parent_to_child_input_chart μ R hR k z i q hscale hnear ε hε hεtiny
      (S i) (S q) (hS i) (hS q) (hfit i hiA.2) (hfit q hqA) g L hL
      (fun u => (hgCoords u).2.1) hgNormal
      (fun u => (hgCoords u).2.2.1) (fun u => (hgCoords u).2.2.2)
  refine ⟨g', hg'Lip, (fun u => (hg'Coords u).2.1),
    (fun u => (hg'Coords u).2.2), ?_, ?_⟩
  · rintro x ⟨u, rfl⟩
    obtain ⟨v, hv⟩ := (hg'Coords u).1
    rw [← hv]
    exact (hgCoords v).1
  · intro x hx
    have hri := i.radius_pos
    have hxq : x ∈ closedBall q.center ((9 / 4 : ℝ) * q.radius) := by
      have ht := dist_triangle x i.center q.center
      have hxi : dist x i.center ≤ (5 / 2 : ℝ) * i.radius := hx.2
      change dist x q.center ≤ (9 / 4 : ℝ) * q.radius
      nlinarith
    have hxg : x ∈ Set.range g := (hgCapture ▸ (show x ∈ A ∩
      closedBall q.center ((9 / 4 : ℝ) * q.radius) from ⟨hx.1, hxq⟩)).1
    rw [hg'Range]
    refine ⟨hxg, ?_⟩
    have hp := (S i).direction.norm_starProjection_apply_le (x - i.center)
    rw [map_sub, ← dist_eq_norm, ← dist_eq_norm] at hp
    have hxi : dist x i.center ≤ (5 / 2 : ℝ) * i.radius := hx.2
    change dist ((S i).direction.starProjection x) ((S i).direction.starProjection i.center) ≤
      (11 / 4 : ℝ) * i.radius
    linarith

theorem active_surface_charts_successor :
    HasActiveSurfaceCharts μ R hR k z Good (t + 1) S ε
      ((activeLevelProjectionMap μ R hR k z Good (t + 1) S hS) '' A) := by
  have hprevious : ∀ q ∈ activeLevelIndex μ R hR k z Good t, ∀ x ∈ A,
      x ∈ closedBall q.center ((9 / 4 : ℝ) * latticeRadius R (k + t)) →
        infDist x (S q : Set (Ambient d)) ≤ (262144 * ε) * latticeRadius R (k + t) := by
    intro q hq x hx hnear
    have hqA := (mem_activeLevelIndex μ R hR k z Good t q).mp hq
    have hrad : q.radius = latticeRadius R (k + t) := by
      simp only [SupportCellDescendant.radius, hqA.1]
    have h := HasActiveCellSurfaceChart.height_on_inner_ball q (S q) ε A (hcharts q hq) x hx
      (by simpa only [hrad] using! hnear)
    simpa only [hrad] using! h
  have hmove := activeLevelProjectionMap_successor_surface_displacement_small μ R hR k z Good t
    S hS ε hε (by linarith) hfit A hprevious (by linarith : ε ≤ 1 / 68157440)
  intro i hi
  have hiA := (mem_activeLevelIndex μ R hR k z Good (t + 1) i).mp hi
  have hrad : i.radius = latticeRadius R (k + (t + 1)) := by
    simp only [SupportCellDescendant.radius, hiA.1]
  have hin := active_surface_successor_input_chart μ R hR k z Good t S hS ε hε hεtiny
    hsmall hfit A hcharts i hi
  unfold HasActiveCellInputChart at hin
  rw [hrad] at hin
  obtain ⟨g, hg, hcoords, hlocal, hsubset, hcapture⟩ := hin
  have h := exists_active_surface_chart_step μ R hR k z Good (t + 1) S hS ε hε
    (by linarith) (fun j hj => hfit j ((mem_activeLevelIndex μ R hR k z Good (t + 1) j).mp hj).2)
    i hi A g hg hcoords hlocal hsubset hcapture hmove
  unfold HasActiveCellSurfaceChart
  rw [hrad]
  exact h

end

end RieszRectifiability

end OAI
