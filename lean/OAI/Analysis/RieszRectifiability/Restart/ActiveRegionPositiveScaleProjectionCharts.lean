import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionPositiveScaleCharts
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionTransitionResidual

namespace OAI

/-!
# Projection charts at positive stopping scales

Transporting a local surface chart through three active-region transitions gives
a bi-Lipschitz chart containing the limit surface where the stopping scale stays
positive. Its tangential displacement and normal component retain quantitative
Lipschitz bounds controlled by the active projection error.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_active_region_positive_scale_projection_chart {n d : ℕ}
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
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (A : Set (Ambient d))
    (hnear : A ⊆ closedBall q.center ((17 / 8 : ℝ) * q.radius))
    (hscale : ∀ x ∈ A, q.radius / 8192 ≤ cellRegionStoppingScale μ R hR k z Good x) :
    ∃ H : closedBall ((S q).direction.orthogonalProjectionOnto q.center)
        ((5 / 2 : ℝ) * q.radius) → Ambient d,
      LipschitzWith 16 H ∧ AntilipschitzWith 64 H ∧
      LipschitzWith (Real.toNNReal (1008 * activeProjectionError d ε))
        (fun u => (S q).direction.orthogonalProjectionOnto (H u) - u.val) ∧
      LipschitzWith (Real.toNNReal (1012 * activeProjectionError d ε))
        (fun u => ((S q).directionᗮ : Submodule ℝ (Ambient d)).starProjection (H u)) ∧
      (∀ u, dist ((S q).direction.orthogonalProjectionOnto (H u)) u.val ≤
        (2 * ((17039360 * ε) / 63)) * q.radius) ∧
      Set.range H ⊆ activeRegionSurface μ R hR k z Good S hS (q.depth + 3) ∧
      Set.range f ∩ A ⊆ Set.range H := by
  have hqF : q ∈ activeLevelIndex μ R hR k z Good q.depth :=
    (mem_activeLevelIndex μ R hR k z Good q.depth q).mpr ⟨rfl, hq⟩
  have hcharts := activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit q.depth
  obtain ⟨g, hgLip, hgNormal, hcoords, hgCapture⟩ := hcharts q hqF
  let T := activeRegionTransitionMap μ R hR k z Good S hS q.depth 3
  let P := (S q).direction
  have hη : 0 ≤ activeProjectionError d ε := by unfold activeProjectionError; positivity
  have hres (u v) : ‖(T (g u) - T (g v)) - (g u - g v)‖ ≤
      (1008 * activeProjectionError d ε) * dist u v := by
    have h := activeRegionTransitionMap_surface_residual_le μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit q.depth 3 (g u) (g v) (hcoords u).1 (hcoords v).1
    have hb := hgLip.dist_le_mul u v
    norm_num at h hb
    change ‖(T (g u) - T (g v)) - (g u - g v)‖ ≤ _ at h
    nlinarith [mul_le_mul_of_nonneg_left hb
      (show 0 ≤ 504 * activeProjectionError d ε by positivity)]
  have hprojected : LipschitzWith (Real.toNNReal (1008 * activeProjectionError d ε))
      (fun u => P.orthogonalProjectionOnto (T (g u)) - u.val) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
    change ‖(P.starProjection (T (g u)) - (u.val : Ambient d)) -
      (P.starProjection (T (g v)) - (v.val : Ambient d))‖ ≤ _
    have hpu : P.starProjection (g u) = (u.val : Ambient d) :=
      congrArg (fun w : P => (w : Ambient d)) (hcoords u).2.1
    have hpv : P.starProjection (g v) = (v.val : Ambient d) :=
      congrArg (fun w : P => (w : Ambient d)) (hcoords v).2.1
    have hid : (P.starProjection (T (g u)) - (u.val : Ambient d)) -
        (P.starProjection (T (g v)) - (v.val : Ambient d)) =
        P.starProjection ((T (g u) - T (g v)) - (g u - g v)) := by
      rw [map_sub, map_sub, map_sub, hpu, hpv]
      abel
    rw [hid]
    exact (P.norm_starProjection_apply_le _).trans (hres u v)
  have hnormal : LipschitzWith (Real.toNNReal (1012 * activeProjectionError d ε))
      (fun u => (Pᗮ : Submodule ℝ (Ambient d)).starProjection (T (g u))) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, ← map_sub]
    have hb := hgNormal.dist_le_mul u v
    rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, ← map_sub] at hb
    let e := (T (g u) - T (g v)) - (g u - g v)
    have hid : T (g u) - T (g v) = e + (g u - g v) := by dsimp [e]; abel
    calc
      _ ≤ ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection e‖ +
          ‖(Pᗮ : Submodule ℝ (Ambient d)).starProjection (g u - g v)‖ := by
        rw [hid, map_add]
        exact norm_add_le _ _
      _ ≤ ‖e‖ + (4 * activeProjectionError d ε) * dist u v :=
        add_le_add ((Pᗮ : Submodule ℝ (Ambient d)).norm_starProjection_apply_le e) hb
      _ ≤ (1012 * activeProjectionError d ε) * dist u v := by
        have h := hres u v
        change ‖e‖ ≤ _ at h
        linarith
  have hdist (u v) :
      (1 / 64 : ℝ) * dist (g u) (g v) ≤ dist (T (g u)) (T (g v)) ∧
      dist (T (g u)) (T (g v)) ≤ 8 * dist (g u) (g v) := by
    have h := activeRegionTransitionMap_surface_dist_bounds μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit q.depth 3 (g u) (g v) (hcoords u).1 (hcoords v).1
    norm_num at h
    exact h
  have hLip : LipschitzWith 16 (T ∘ g) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have hbase := hgLip.dist_le_mul u v
    norm_num at hbase ⊢
    have h := (hdist u v).2
    change dist (T (g u)) (T (g v)) ≤ 16 * dist u v
    linarith
  have hsep : AntilipschitzWith 64 (T ∘ g) := by
    apply AntilipschitzWith.of_le_mul_dist
    intro u v
    have hproj : dist u v ≤ dist (g u) (g v) := by
      change dist u.val v.val ≤ dist (g u) (g v)
      rw [← (hcoords u).2.1, ← (hcoords v).2.1]
      have h := (S q).direction.norm_starProjection_apply_le (g u - g v)
      rw [map_sub] at h
      exact h
    have h := (hdist u v).1
    norm_num
    change dist u v ≤ 64 * dist (T (g u)) (T (g v))
    linarith
  have hinto : Set.range (T ∘ g) ⊆ activeRegionSurface μ R hR k z Good S hS (q.depth + 3) := by
    rintro _ ⟨u, rfl⟩
    rw [activeRegionSurface_add]
    exact ⟨g u, (hcoords u).1, rfl⟩
  have hdisplacement (u) : dist (P.orthogonalProjectionOnto (T (g u))) u.val ≤
      (2 * ((17039360 * ε) / 63)) * q.radius := by
    have h := active_region_transition_surface_movement μ R hR k z Good S hS ε hε.le
      f hmodel q.depth 3 (g u) (hcoords u).1
    change dist (T (g u)) (g u) ≤ (2 * ((17039360 * ε) / 63)) * q.radius at h
    rw [← (hcoords u).2.1]
    have hp := P.norm_starProjection_apply_le (T (g u) - g u)
    rw [map_sub] at hp
    exact hp.trans h
  have hrq := q.radius_pos
  have hB : (17039360 * ε) / 63 ≤ 1 / 16 := by linarith
  have hrad : latticeRadius R (k + (q.depth + 3)) = q.radius / 262144 := by
    rw [← Nat.add_assoc, latticeRadius_add]
    change q.radius * (1 / 64 : ℝ) ^ 3 = _
    norm_num
    ring
  have hstable := active_region_limit_eq_finite_of_tail_small μ R hR k z Good S hS f
    (fun u => hmodel.2.2.1.tendsto_at u) ((17039360 * ε) / 63) (by positivity)
    hmodel.2.2.2.1 A (q.radius / 8192) hscale (q.depth + 3) (by
      rw [hrad]
      have hBm := mul_le_mul_of_nonneg_right hB hrq.le
      nlinarith)
  refine ⟨T ∘ g, hLip, hsep, hprojected, hnormal, hdisplacement, hinto, ?_⟩
  intro x hx
  have hxN : x ∈ activeRegionSurface μ R hR k z Good S hS (q.depth + 3) :=
    (hstable ▸ hx).1
  rw [activeRegionSurface_add] at hxN
  obtain ⟨y, hy, hTy⟩ := hxN
  change T y = x at hTy
  have hmove := active_region_transition_surface_movement μ R hR k z Good S hS ε hε.le
    f hmodel q.depth 3 y hy
  change dist (T y) y ≤ (2 * ((17039360 * ε) / 63)) * q.radius at hmove
  rw [hTy] at hmove
  have hBm := mul_le_mul_of_nonneg_right hB hrq.le
  have hyq : y ∈ closedBall q.center ((9 / 4 : ℝ) * q.radius) := by
    have hxy := dist_triangle y x q.center
    rw [dist_comm y x] at hxy
    have hxq : dist x q.center ≤ (17 / 8 : ℝ) * q.radius := hnear hx.2
    change dist y q.center ≤ (9 / 4 : ℝ) * q.radius
    nlinarith
  have hyg : y ∈ Set.range g := (hgCapture ▸ (show y ∈
    activeRegionSurface μ R hR k z Good S hS q.depth ∩
      closedBall q.center ((9 / 4 : ℝ) * q.radius) from ⟨hy, hyq⟩)).1
  obtain ⟨u, hu⟩ := hyg
  refine ⟨u, ?_⟩
  change T (g u) = x
  rw [hu]
  exact hTy

end

end RieszRectifiability

end OAI
