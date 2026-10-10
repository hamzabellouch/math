import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveLevelCover

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_active_parent_at_stopping_scale {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (x : Ambient d)
    (hpos : 0 < cellRegionStoppingScale μ R hR k z Good x)
    (hsmall : cellRegionStoppingScale μ R hR k z Good x < latticeRadius R (k + 1)) :
    ∃ q : SupportCellDescendant μ R hR k z, activeRegionCell Good q ∧
      q.radius ≤ 4096 * cellRegionStoppingScale μ R hR k z Good x ∧
      64 * cellRegionStoppingScale μ R hR k z Good x < q.radius ∧
      dist x q.center < (131 / 64 : ℝ) * q.radius := by
  let δ := cellRegionStoppingScale μ R hR k z Good x
  let t := annularLatticeDepth R k (8 * δ) (by positivity)
  have ht : latticeRadius R (k + t) ≤ δ := by
    have h := annularLatticeDepth_radius_upper R k (8 * δ) (by positivity)
    change latticeRadius R (k + t) ≤ (8 * δ) / 8 at h
    linarith
  have htpos : 2 ≤ t := by
    by_contra h
    have hle := latticeRadius_antitone R hR.le (show k + t ≤ k + 1 by omega)
    change δ < latticeRadius R (k + 1) at hsmall
    linarith
  have hδ : δ < latticeRadius R (k + (t - 1)) := by
    by_contra h
    have hm := annularLatticeDepth_minimal R k (8 * δ) (by positivity) (t - 1)
      (by linarith [le_of_not_gt h])
    change t ≤ t - 1 at hm
    omega
  obtain ⟨i, hi, hxi⟩ := exists_active_level_center_of_small_stopping_scale μ R hR k z Good
    (t - 1) x hδ
  obtain ⟨q, hqd, hsub, hc⟩ := i.exists_ancestor_at_depth (t - 2) (by have := hi.1; omega)
  have hqA := activeRegionCell_ancestor Good i q hi.2 (by have := hi.1; omega) hsub
  have hid : i.depth = q.depth + 1 := by have := hi.1; omega
  have hri : i.radius = latticeRadius R (k + (t - 1)) := by
    simp only [SupportCellDescendant.radius, hi.1]
  have hrq : q.radius = 64 * i.radius := by
    change latticeRadius R (k + q.depth) = 64 * latticeRadius R (k + i.depth)
    rw [hid, ← Nat.add_assoc, latticeRadius_succ]
    ring
  have hrt : i.radius = 64 * latticeRadius R (k + t) := by
    rw [hri, show k + t = (k + (t - 1)) + 1 by omega, latticeRadius_succ]
    ring
  have hdist := q.dist_center_of_mem i.center hc
  have htri := dist_triangle x i.center q.center
  rw [← hri] at hxi hδ
  refine ⟨q, hqA, ?_, ?_, ?_⟩
  · change q.radius ≤ 4096 * δ
    nlinarith
  · change 64 * δ < q.radius
    nlinarith
  · nlinarith

theorem active_stopping_ball_chart_geometry {d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (x : Ambient d)
    (q : SupportCellDescendant μ R hR k z)
    (hrhi : q.radius ≤ 4096 * cellRegionStoppingScale μ R hR k z Good x)
    (hrlo : 64 * cellRegionStoppingScale μ R hR k z Good x < q.radius)
    (hnear : dist x q.center < (131 / 64 : ℝ) * q.radius) :
    closedBall x (cellRegionStoppingScale μ R hR k z Good x / 16) ⊆
      closedBall q.center ((17 / 8 : ℝ) * q.radius) ∧
    ∀ y ∈ closedBall x (cellRegionStoppingScale μ R hR k z Good x / 16),
      q.radius / 8192 ≤ cellRegionStoppingScale μ R hR k z Good y := by
  have hr := q.radius_pos
  constructor
  · intro y hy
    have hyx : dist y x ≤ cellRegionStoppingScale μ R hR k z Good x / 16 := hy
    have htri := dist_triangle y x q.center
    change dist y q.center ≤ (17 / 8 : ℝ) * q.radius
    linarith
  · intro y hy
    have hyx : dist y x ≤ cellRegionStoppingScale μ R hR k z Good x / 16 := hy
    have hD := cellRegionStoppingScale_le_add_dist μ R hR k z Good x y
    rw [dist_comm x y] at hD
    linarith

end

end RieszRectifiability

end OAI
