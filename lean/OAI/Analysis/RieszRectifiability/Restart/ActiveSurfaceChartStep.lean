import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveProjectionReplacementChart
import OAI.Analysis.RieszRectifiability.Restart.ActiveProjectionSurfaceBounds
import OAI.Analysis.RieszRectifiability.Surfaces.RecenteredDiskCharts
import OAI.Analysis.RieszRectifiability.Foundations.LocalImageCapture
import OAI.Analysis.RieszRectifiability.Projections.ProjectionTubeLocation

namespace OAI

/-!
# One active surface chart step

A local chart capturing the original surface near an active cell gives a chart for its projected
image. Shrinking the tangential disk leaves room for the projection displacement while retaining
exact local image capture. The new chart has controlled normal slope, stays in the reference
plane tube, and remains inside the prescribed ambient ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_active_surface_chart_step {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hsmall : activeProjectionError d ε ≤ 1 / 4)
    (hfit : ∀ i ∈ activeLevelIndex μ R hR k z Good t,
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (q : SupportCellDescendant μ R hR k z)
    (hq : q ∈ activeLevelIndex μ R hR k z Good t)
    (A : Set (Ambient d))
    (g : closedBall ((S q).direction.orthogonalProjectionOnto q.center)
      ((11 / 4 : ℝ) * latticeRadius R (k + t)) → Ambient d)
    (hg : LipschitzWith 2 g)
    (hcoordinates : ∀ u, (S q).direction.orthogonalProjectionOnto (g u) = u.val)
    (hlocal : ∀ u, g u ∈ closedBall q.center (3 * latticeRadius R (k + t)))
    (hsubset : Set.range g ⊆ A)
    (hcapture : A ∩ closedBall q.center ((5 / 2 : ℝ) * latticeRadius R (k + t)) ⊆ Set.range g)
    (hmove : ∀ x ∈ A,
      dist (activeLevelProjectionMap μ R hR k z Good t S hS x) x ≤
        latticeRadius R (k + t) / 4) :
    ∃ h : closedBall ((S q).direction.orthogonalProjectionOnto q.center)
        ((5 / 2 : ℝ) * latticeRadius R (k + t)) → Ambient d,
      LipschitzWith 2 h ∧
      LipschitzWith (Real.toNNReal (4 * activeProjectionError d ε))
        (fun u => ((S q).directionᗮ : Submodule ℝ (Ambient d)).starProjection (h u)) ∧
      (∀ u, h u ∈ (activeLevelProjectionMap μ R hR k z Good t S hS) '' A ∧
        (S q).direction.orthogonalProjectionOnto (h u) = u.val ∧
        infDist (h u) (S q : Set (Ambient d)) ≤
          (262144 * ε) * latticeRadius R (k + t) ∧
        h u ∈ closedBall q.center (3 * latticeRadius R (k + t))) ∧
      ((activeLevelProjectionMap μ R hR k z Good t S hS) '' A) ∩
          closedBall q.center ((9 / 4 : ℝ) * latticeRadius R (k + t)) =
        Set.range h ∩ closedBall q.center ((9 / 4 : ℝ) * latticeRadius R (k + t)) := by
  let r := latticeRadius R (k + t)
  let P := (S q).direction
  let a := P.orthogonalProjectionOnto q.center
  let δ := (262144 * ε) * r
  let L := Real.toNNReal (4 * activeProjectionError d ε)
  let σ := activeLevelProjectionMap μ R hR k z Good t S hS
  have hr : 0 < r := latticeRadius_pos R hR (k + t)
  obtain ⟨hη, hεsmall⟩ := activeProjectionError_small_parameters d ε hε hsmall
  have hpow : (1 : ℝ) ≤ (9 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hpow hε.le
  have hδcoeff : 262144 * ε ≤ 1 / 4 := by
    unfold activeProjectionError at hsmall
    nlinarith
  have hδ : δ ≤ r / 4 := by
    have h := mul_le_mul_of_nonneg_right hδcoeff hr.le
    dsimp [δ]
    linarith
  have hεfit : 1024 * ε ≤ 1 / 4 := by linarith
  have hqA := (mem_activeLevelIndex μ R hR k z Good t q).mp hq
  have hrad : q.radius = r := by simp only [SupportCellDescendant.radius, hqA.1, r]
  have hqr := q.radius_pos
  have hcenter := (bilateralPlaneError_lt_pointwise μ ⟨q.center, q.center_mem_support⟩
    q.center (1024 * q.radius) ε (by positivity) (S q) (hS q) (hfit q hq)).1
      q.center (mem_ball_self (by positivity)) q.center_mem_support
  have hcenterBound : infDist q.center (S q : Set (Ambient d)) ≤ r / 4 := by
    rw [hrad] at hcenter
    have h := mul_le_mul_of_nonneg_right hεfit hr.le
    nlinarith
  obtain ⟨j, hjLip, hjNormal, hjCoords, hjRange⟩ :=
    exists_active_level_replacement_chart μ R hR k z Good t S hS ε hε hsmall hfit q hq
      a ((11 / 4 : ℝ) * r) (by positivity) g hg hcoordinates hlocal
  obtain ⟨h, hhLip, hhNormal, hhCoords, hhRange⟩ :=
    exists_recentered_disk_chart P a (((11 / 4 : ℝ) * r) - δ) j L
      (fun u => (hjCoords u).2) hjNormal a ((5 / 2 : ℝ) * r)
      (by rw [dist_self]; linarith)
  have hL : 1 + L ≤ (2 : ℝ≥0) := by
    have hreal : ((1 + L : ℝ≥0) : ℝ) ≤ 2 := by
      change 1 + (Real.toNNReal (4 * activeProjectionError d ε) : ℝ) ≤ 2
      rw [Real.coe_toNNReal _ (mul_nonneg (by norm_num) hη)]
      linarith
    exact_mod_cast hreal
  have hheight : ∀ u, infDist (h u) (S q : Set (Ambient d)) ≤ δ := by
    intro u
    obtain ⟨v, hv⟩ := (hhCoords u).1
    have hin : h u ∈ σ '' Set.range g := by
      rw [← hv]
      exact (hjCoords v).1
    exact activeLevelProjectionMap_image_plane_height μ R hR k z Good t S hS
      ε hε hεsmall hfit q hq (Set.range g) (by rintro x ⟨v, rfl⟩; exact hlocal v)
      (h u) hin
  have hphysical : ∀ u, h u ∈ closedBall q.center (3 * r) := by
    intro u
    have hloc := plane_chart_location_of_height (S q) (hS q).1 q.center
      ((5 / 2 : ℝ) * r) δ h (fun v => (hhCoords v).2) hheight u
    change dist (h u) q.center ≤ 3 * r
    linarith
  have hexact : Set.range h = (σ '' Set.range g) ∩
      P.orthogonalProjectionOnto ⁻¹' closedBall a ((5 / 2 : ℝ) * r) := by
    rw [hhRange, hjRange]
    ext y
    constructor
    · intro hy
      exact ⟨hy.1.1, hy.2⟩
    · intro hy
      refine ⟨⟨hy.1, ?_⟩, hy.2⟩
      have hy' : dist (P.orthogonalProjectionOnto y) a ≤ (5 / 2 : ℝ) * r := hy.2
      change dist (P.orthogonalProjectionOnto y) a ≤ (11 / 4 : ℝ) * r - δ
      linarith
  refine ⟨h, hhLip.weaken hL, hhNormal, ?_, ?_⟩
  · intro u
    refine ⟨?_, (hhCoords u).2, hheight u, hphysical u⟩
    have hin : h u ∈ σ '' Set.range g := (hexact ▸ (show h u ∈ Set.range h from ⟨u, rfl⟩)).1
    exact Set.image_mono hsubset hin
  · have hpre : ∀ x ∈ A, dist x q.center ≤ (9 / 4 : ℝ) * r + r / 4 → x ∈ Set.range g := by
      intro x hx hnear
      apply hcapture
      exact ⟨hx, by change dist x q.center ≤ (5 / 2 : ℝ) * r; linarith⟩
    have hproject : closedBall q.center ((9 / 4 : ℝ) * r) ⊆
        P.orthogonalProjectionOnto ⁻¹' closedBall a ((5 / 2 : ℝ) * r) := by
      intro x hx
      have hp := P.norm_starProjection_apply_le (x - q.center)
      rw [map_sub, ← dist_eq_norm, ← dist_eq_norm] at hp
      have hx' : dist x q.center ≤ (9 / 4 : ℝ) * r := hx
      change dist (P.orthogonalProjectionOnto x) a ≤ (5 / 2 : ℝ) * r
      change dist (P.starProjection x) (P.starProjection q.center) ≤ (5 / 2 : ℝ) * r
      linarith
    exact image_chart_captures_closedBall σ A g h P (closedBall a ((5 / 2 : ℝ) * r))
      q.center ((9 / 4 : ℝ) * r) (r / 4) hsubset hpre hmove hexact hproject

end

end RieszRectifiability

end OAI
