import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveScaleBallSelection
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionPositiveScaleBiCharts

namespace OAI

/-!
# Inner disks at positive stopping scale

A point of an active-region limit image with positive stopping scale admits
a centered disk chart inside each sufficiently small ambient ball. Selecting an
active parent and transporting its plane coordinates gives explicit Lipschitz
and antilipschitz bounds while retaining containment in the limit image.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_active_region_positive_scale_inner_disk {n d : ℕ}
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
    (hDpos : 0 < cellRegionStoppingScale μ R hR k z Good p)
    (hDsmall : cellRegionStoppingScale μ R hR k z Good p < latticeRadius R (k + 1))
    (r : ℝ) (hr : 0 < r) (hrsmall : r ≤ cellRegionStoppingScale μ R hR k z Good p / 2) :
    ∃ q : SupportCellDescendant μ R hR k z, activeRegionCell Good q ∧
      ∃ a : (S q).direction, ∃ H : closedBall a (r / 16) → Ambient d,
        LipschitzWith 16 H ∧ AntilipschitzWith 64 H ∧
        H ⟨a, mem_closedBall_self (by positivity)⟩ = p ∧
        Set.range H ⊆ Set.range f ∩ closedBall p r := by
  let δ := cellRegionStoppingScale μ R hR k z Good p
  let B := (17039360 * ε) / 63
  obtain ⟨q, hq, hqhi, hqlo, hnear⟩ :=
    exists_active_parent_at_stopping_scale μ R hR k z Good p hDpos hDsmall
  have hrq := q.radius_pos
  have hB : B ≤ 1 / 16 := by dsimp [B]; linarith
  have hBm := mul_le_mul_of_nonneg_right hB hrq.le
  have hrad : latticeRadius R (k + (q.depth + 3)) = q.radius / 262144 := by
    rw [← Nat.add_assoc, latticeRadius_add]
    change q.radius * (1 / 64 : ℝ) ^ 3 = _
    norm_num
    ring
  have hK : ∀ x ∈ closedBall p (δ / 2),
      δ / 2 ≤ cellRegionStoppingScale μ R hR k z Good x := by
    intro x hx
    have h := cellRegionStoppingScale_le_add_dist μ R hR k z Good p x
    rw [dist_comm p x] at h
    change δ ≤ cellRegionStoppingScale μ R hR k z Good x + dist x p at h
    have hx' : dist x p ≤ δ / 2 := hx
    linarith
  have hstable := active_region_limit_eq_finite_of_tail_small μ R hR k z Good S hS f
    (fun u => hmodel.2.2.1.tendsto_at u) B (by dsimp [B]; positivity)
    hmodel.2.2.2.1 (closedBall p (δ / 2)) (δ / 2) hK (q.depth + 3) (by
      rw [hrad]
      change q.radius ≤ 4096 * δ at hqhi
      change 0 < δ at hDpos
      nlinarith)
  have hpfinite : p ∈ activeRegionSurface μ R hR k z Good S hS (q.depth + 3) :=
    (hstable ▸ (show p ∈ Set.range f ∩ closedBall p (δ / 2) from
      ⟨hp, mem_closedBall_self (by dsimp [δ]; positivity)⟩)).1
  rw [activeRegionSurface_add] at hpfinite
  obtain ⟨y, hy, hTy⟩ := hpfinite
  let T := activeRegionTransitionMap μ R hR k z Good S hS q.depth 3
  change T y = p at hTy
  have hmove := active_region_transition_surface_movement μ R hR k z Good S hS
    ε hε.le f hmodel q.depth 3 y hy
  change dist (T y) y ≤ (2 * B) * q.radius at hmove
  rw [hTy] at hmove
  have hyq : y ∈ closedBall q.center ((9 / 4 : ℝ) * q.radius) := by
    have ht := dist_triangle y p q.center
    rw [dist_comm y p] at ht
    change dist y q.center ≤ (9 / 4 : ℝ) * q.radius
    nlinarith
  have hqF : q ∈ activeLevelIndex μ R hR k z Good q.depth :=
    (mem_activeLevelIndex μ R hR k z Good q.depth q).mpr ⟨rfl, hq⟩
  obtain ⟨g, hgLip, _, hcoords, hcapture⟩ :=
    activeRegionSurface_charts μ R hR k z Good S hS ε hε hεtiny hsmall hfit q.depth q hqF
  have hyg : y ∈ Set.range g := (hcapture ▸ (show y ∈
    activeRegionSurface μ R hR k z Good S hS q.depth ∩
      closedBall q.center ((9 / 4 : ℝ) * q.radius) from ⟨hy, hyq⟩)).1
  obtain ⟨a, ha⟩ := hyg
  let P := (S q).direction
  have hamargin : dist a.val (P.orthogonalProjectionOnto q.center) ≤ (9 / 4 : ℝ) * q.radius := by
    rw [← (hcoords a).2.1, ha]
    have hproj := P.norm_starProjection_apply_le (y - q.center)
    rw [map_sub] at hproj
    exact hproj.trans hyq
  have hsub : closedBall a.val (r / 16) ⊆
      closedBall (P.orthogonalProjectionOnto q.center) ((5 / 2 : ℝ) * q.radius) := by
    intro u hu
    have hu' : dist u a.val ≤ r / 16 := hu
    have ht := dist_triangle u a.val (P.orthogonalProjectionOnto q.center)
    change dist u (P.orthogonalProjectionOnto q.center) ≤ (5 / 2 : ℝ) * q.radius
    change r ≤ δ / 2 at hrsmall
    change 64 * δ < q.radius at hqlo
    linarith
  let j : closedBall a.val (r / 16) →
      closedBall (P.orthogonalProjectionOnto q.center) ((5 / 2 : ℝ) * q.radius) :=
    fun u => ⟨u.val, hsub u.property⟩
  let H := fun u : closedBall a.val (r / 16) => T (g (j u))
  have hdist (u v : closedBall a.val (r / 16)) :
      (1 / 64 : ℝ) * dist (g (j u)) (g (j v)) ≤ dist (H u) (H v) ∧
      dist (H u) (H v) ≤ 8 * dist (g (j u)) (g (j v)) := by
    have h := activeRegionTransitionMap_surface_dist_bounds μ R hR k z Good S hS
      ε hε hεtiny hsmall hfit q.depth 3 (g (j u)) (g (j v))
      (hcoords (j u)).1 (hcoords (j v)).1
    norm_num at h
    exact h
  have hLip : LipschitzWith 16 H := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have hb := hgLip.dist_le_mul (j u) (j v)
    norm_num at hb ⊢
    change dist (g (j u)) (g (j v)) ≤ 2 * dist u v at hb
    linarith [(hdist u v).2]
  have hsep : AntilipschitzWith 64 H := by
    apply AntilipschitzWith.of_le_mul_dist
    intro u v
    have hproj : dist u v ≤ dist (g (j u)) (g (j v)) := by
      change dist (j u).val (j v).val ≤ dist (g (j u)) (g (j v))
      rw [← (hcoords (j u)).2.1, ← (hcoords (j v)).2.1]
      have h := P.norm_starProjection_apply_le (g (j u) - g (j v))
      rw [map_sub] at h
      exact h
    norm_num
    linarith [(hdist u v).1]
  let a0 : closedBall a.val (r / 16) := ⟨a.val, mem_closedBall_self (by positivity)⟩
  have hcenter : H a0 = p := by
    have hja : j a0 = a := Subtype.ext rfl
    change T (g (j a0)) = p
    rw [hja, ha, hTy]
  refine ⟨q, hq, a.val, H, hLip, hsep, hcenter, ?_⟩
  rintro _ ⟨u, rfl⟩
  have hball : H u ∈ closedBall p r := by
    have h := hLip.dist_le_mul u a0
    rw [hcenter] at h
    have hu : dist u a0 ≤ r / 16 := u.property
    norm_num at h
    change dist (H u) p ≤ r
    linarith
  have hballK : H u ∈ closedBall p (δ / 2) :=
    le_trans hball hrsmall
  have hfinite : H u ∈ activeRegionSurface μ R hR k z Good S hS (q.depth + 3) := by
    rw [activeRegionSurface_add]
    exact ⟨g (j u), (hcoords (j u)).1, rfl⟩
  exact ⟨(hstable.symm ▸ (show H u ∈
    activeRegionSurface μ R hR k z Good S hS (q.depth + 3) ∩ closedBall p (δ / 2)
    from ⟨hfinite, hballK⟩)).1, hball⟩

end

end RieszRectifiability

end OAI
