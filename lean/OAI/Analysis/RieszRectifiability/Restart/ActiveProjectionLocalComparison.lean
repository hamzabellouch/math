import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveLevelProjectionMaps
import OAI.Analysis.RieszRectifiability.Restart.ActiveLevelCenterPartition
import OAI.Analysis.RieszRectifiability.Projections.ProjectionAverageIncrement
import OAI.Analysis.RieszRectifiability.Projections.NeighborProjectionEstimates

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators

def activeProjectionError (d : ℕ) (ε : ℝ) : ℝ :=
  (2048 + 1048576 * (9 : ℝ) ^ d) * ε

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i))
  (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 1024)
  (hfit : ∀ i ∈ activeLevelIndex μ R hR k z Good t,
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (q : SupportCellDescendant μ R hR k z)
  (hq : q ∈ activeLevelIndex μ R hR k z Good t)

include hε hεsmall hfit hq hS

theorem active_level_used_plane_comparison (x y : Ambient d)
    (hx : x ∈ closedBall q.center (3 * latticeRadius R (k + t)))
    (hy : y ∈ closedBall q.center (3 * latticeRadius R (k + t)))
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ activeLevelIndex μ R hR k z Good t)
    (hn : activeLevelWeight μ R hR k z Good t i x ≠ 0 ∨
      activeLevelWeight μ R hR k z Good t i y ≠ 0) :
    ‖(S i).direction.starProjection - (S q).direction.starProjection‖ ≤ 2048 * ε ∧
    dist (nonemptyAffineProjection (S i) (hS i).1 y)
      (nonemptyAffineProjection (S q) (hS q).1 y) ≤
        (262144 * ε) * latticeRadius R (k + t) := by
  let r := latticeRadius R (k + t)
  have hr : 0 < r := latticeRadius_pos R hR (k + t)
  have hiA := (mem_activeLevelIndex μ R hR k z Good t i).mp hi
  have hqA := (mem_activeLevelIndex μ R hR k z Good t q).mp hq
  have hri : i.radius = r := by simp only [SupportCellDescendant.radius, hiA.1, r]
  have hrq : q.radius = r := by simp only [SupportCellDescendant.radius, hqA.1, r]
  have hnearAt (a : Ambient d) (ha : dist a q.center ≤ 3 * r)
      (hnz : activeLevelWeight μ R hR k z Good t i a ≠ 0) :
      dist i.center q.center ≤ 7 * r := by
    have hd := (activeLevelWeight_ne_zero_iff μ R hR k z Good t i a).mp hnz
    have ht := dist_triangle i.center a q.center
    rw [dist_comm i.center a] at ht
    change dist a i.center < 4 * r at hd
    linarith
  have hnear : dist i.center q.center ≤ 7 * r := by
    rcases hn with hnx | hny
    · exact hnearAt x hx hnx
    · exact hnearAt y hy hny
  have hsmall : i.radius ≤ q.radius := by rw [hri, hrq]
  have hlarge : q.radius ≤ 64 * i.radius := by rw [hri, hrq]; linarith
  have hneighbor : dist i.center q.center ≤ 128 * q.radius := by rw [hrq]; linarith
  refine ⟨neighbor_cell_projection_operator_norm_le μ R hR k z i q hsmall hlarge hneighbor
    ε hε hεsmall (S i) (S q) (hS i) (hS q) (hfit i hi) (hfit q hq), ?_⟩
  have hyi : y ∈ closedBall i.center (32 * i.radius) := by
    have hy' : dist y q.center ≤ 3 * r := hy
    have ht := dist_triangle y q.center i.center
    rw [dist_comm q.center i.center] at ht
    change dist y i.center ≤ 32 * i.radius
    rw [hri]
    linarith
  have h := neighbor_cell_affine_projections_close_on_32ball μ R hR k z i q
    hsmall hlarge hneighbor ε hε hεsmall (S i) (S q) (hS i) (hS q)
    (hfit i hi) (hfit q hq) y hyi
  simpa only [hri, r] using! h

theorem activeLevelProjectionMap_reference_displacement (x : Ambient d)
    (hx : x ∈ closedBall q.center (3 * latticeRadius R (k + t))) :
    dist (activeLevelProjectionMap μ R hR k z Good t S hS x)
      (nonemptyAffineProjection (S q) (hS q).1 x) ≤
        (262144 * ε) * latticeRadius R (k + t) := by
  apply finiteProjectionAverage_dist_reference_le
    (activeLevelIndex μ R hR k z Good t) (activeLevelWeight μ R hR k z Good t)
    (fun i => nonemptyAffineProjection (S i) (hS i).1) x _ _
    (fun i _ => activeLevelWeight_nonneg μ R hR k z Good t i x)
    (activeLevelWeight_sum_eq_one_near_center μ R hR k z Good t q hq x hx)
  intro i hi hn
  exact (active_level_used_plane_comparison μ R hR k z Good t S hS ε hε hεsmall hfit
    q hq x x hx hx i hi (Or.inl hn)).2

theorem activeLevelProjectionMap_reference_increment (x y : Ambient d)
    (hx : x ∈ closedBall q.center (3 * latticeRadius R (k + t)))
    (hy : y ∈ closedBall q.center (3 * latticeRadius R (k + t))) :
    ‖(activeLevelProjectionMap μ R hR k z Good t S hS x -
      activeLevelProjectionMap μ R hR k z Good t S hS y) -
      (S q).direction.starProjection (x - y)‖ ≤ activeProjectionError d ε * dist x y := by
  let r := latticeRadius R (k + t)
  let θ := activeLevelWeight μ R hR k z Good t
  let π := fun i => nonemptyAffineProjection (S i) (hS i).1
  have hr : 0 < r := latticeRadius_pos R hR (k + t)
  have hlinear : ∀ i ∈ activeLevelIndex μ R hR k z Good t, θ i x ≠ 0 →
      ‖(π i x - π i y) - (π q x - π q y)‖ ≤ (2048 * ε) * dist x y := by
    intro i hi hn
    have hop := (active_level_used_plane_comparison μ R hR k z Good t S hS ε hε hεsmall hfit
      q hq x y hx hy i hi (Or.inl hn)).1
    exact nonemptyAffineProjection_increment_difference_le (S i) (S q)
      (hS i).1 (hS q).1 x y (2048 * ε) hop
  have hoffset : ∀ i ∈ activeLevelIndex μ R hR k z Good t, θ i x ≠ θ i y →
      dist (π i y) (π q y) ≤ (262144 * ε) * r := by
    intro i hi hchange
    have hn : θ i x ≠ 0 ∨ θ i y ≠ 0 := by
      by_cases hz : θ i x = 0
      · right
        intro hyz
        exact hchange (hz.trans hyz.symm)
      · exact Or.inl hz
    exact (active_level_used_plane_comparison μ R hR k z Good t S hS ε hε hεsmall hfit
      q hq x y hx hy i hi hn).2
  have hvariation : (∑ i ∈ activeLevelIndex μ R hR k z Good t, |θ i x - θ i y|) ≤
      (4 * (9 : ℝ) ^ d / r) * dist x y := by
    calc
      _ ≤ (4 * (9 : ℝ) ^ d) * (dist x y / r) :=
        activeLevelWeight_sum_abs_sub_le μ R hR k z Good t x y
      _ = _ := by ring
  have h := finiteProjectionAverage_increment_bound (activeLevelIndex μ R hR k z Good t)
    θ π (π q) x y (2048 * ε) ((262144 * ε) * r) (4 * (9 : ℝ) ^ d / r)
    (by positivity) (fun i _ => activeLevelWeight_nonneg μ R hR k z Good t i x)
    (activeLevelWeight_sum_eq_one_near_center μ R hR k z Good t q hq x hx)
    (activeLevelWeight_sum_eq_one_near_center μ R hR k z Good t q hq y hy) hlinear hoffset hvariation
  have heq : 2048 * ε + ((262144 * ε) * r) * (4 * (9 : ℝ) ^ d / r) =
      activeProjectionError d ε := by
    unfold activeProjectionError
    field_simp [ne_of_gt hr]
    ring
  rw [heq] at h
  change ‖(activeLevelProjectionMap μ R hR k z Good t S hS x -
    activeLevelProjectionMap μ R hR k z Good t S hS y) -
    (nonemptyAffineProjection (S q) (hS q).1 x -
      nonemptyAffineProjection (S q) (hS q).1 y)‖ ≤ _ at h
  rwa [nonemptyAffineProjection_sub] at h

end

end RieszRectifiability

end OAI
