import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveSuccessorFiveBall
import OAI.Analysis.RieszRectifiability.Projections.ProjectionAverageResidualBound

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεsmall : ε ≤ 1 / 1024)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (A : Set (Ambient d)) (hcharts : HasActiveSurfaceCharts μ R hR k z Good t S ε A)

include hS hε hεsmall hfit hcharts

theorem activeLevelProjectionMap_surface_residual_le
    (x y : Ambient d) (hx : x ∈ A) (hy : y ∈ A) :
    ‖(activeLevelProjectionMap μ R hR k z Good (t + 1) S hS x -
      activeLevelProjectionMap μ R hR k z Good (t + 1) S hS y) - (x - y)‖ ≤
        (72 * activeProjectionError d ε) * dist x y := by
  let r := latticeRadius R (k + (t + 1))
  let F := activeLevelIndex μ R hR k z Good (t + 1)
  let θ := activeLevelWeight μ R hR k z Good (t + 1)
  let π := fun i => nonemptyAffineProjection (S i) (hS i).1
  let σ := activeLevelProjectionMap μ R hR k z Good (t + 1) S hS
  have hr : 0 < r := latticeRadius_pos R hR (k + (t + 1))
  have hri : ∀ i ∈ F, i.radius = r := by
    intro i hi
    have hiA := (mem_activeLevelIndex μ R hR k z Good (t + 1) i).mp hi
    simp only [SupportCellDescendant.radius, hiA.1, r]
  have hpow : (1 : ℝ) ≤ (9 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hpowε := mul_le_mul_of_nonneg_right hpow hε.le
  by_cases hnear : dist x y ≤ r
  · have hlinear : ∀ i ∈ F, θ i x ≠ 0 →
        ‖(π i x - x) - (π i y - y)‖ ≤
          (4 * activeProjectionError d ε + 2048 * ε) * dist x y := by
      intro i hi hn
      have hxi := (activeLevelWeight_ne_zero_iff μ R hR k z Good (t + 1) i x).mp hn
      change dist x i.center < 4 * r at hxi
      have ht := dist_triangle y x i.center
      rw [dist_comm y x] at ht
      apply active_successor_projection_residual_on_five_ball μ R hR k z Good t
        S hS ε hε hεsmall hfit A hcharts i hi x y hx hy
      · change dist x i.center ≤ 5 * i.radius
        rw [hri i hi]
        linarith
      · change dist y i.center ≤ 5 * i.radius
        rw [hri i hi]
        linarith
    have hoffset : ∀ i ∈ F, θ i x ≠ θ i y → dist (π i y) y ≤ (17039360 * ε) * r := by
      intro i hi hchange
      have hyi : dist y i.center ≤ 5 * r := by
        by_cases hny : θ i y = 0
        · have hnx : θ i x ≠ 0 := fun hx0 => hchange (hx0.trans hny.symm)
          have hxi := (activeLevelWeight_ne_zero_iff μ R hR k z Good (t + 1) i x).mp hnx
          have ht := dist_triangle y x i.center
          rw [dist_comm y x] at ht
          change dist x i.center < 4 * r at hxi
          linarith
        · have hyj := (activeLevelWeight_ne_zero_iff μ R hR k z Good (t + 1) i y).mp hny
          change dist y i.center < 4 * r at hyj
          linarith
      have h := active_successor_plane_height_on_five_ball μ R hR k z Good t
        S hS ε hε hεsmall hfit A hcharts i hi y hy
        (by change dist y i.center ≤ 5 * i.radius; rwa [hri i hi])
      change dist (nonemptyAffineProjection (S i) (hS i).1 y) y ≤ _
      rw [nonemptyAffineProjection_dist_self]
      rwa [hri i hi] at h
    have hK : 0 ≤ 4 * activeProjectionError d ε + 2048 * ε := by
      unfold activeProjectionError
      positivity
    have h := finiteProjectionAverage_residual_norm_le F θ π x y
      (4 * activeProjectionError d ε + 2048 * ε) ((17039360 * ε) * r) hK
      (fun i _ => activeLevelWeight_nonneg μ R hR k z Good (t + 1) i x)
      (activeLevelWeight_sum_le_one μ R hR k z Good (t + 1) x) hlinear hoffset
    have hvar : (∑ i ∈ F, |θ i x - θ i y|) ≤ (4 * (9 : ℝ) ^ d) * (dist x y / r) :=
      activeLevelWeight_sum_abs_sub_le μ R hR k z Good (t + 1) x y
    calc
      ‖(σ x - σ y) - (x - y)‖ ≤
          (4 * activeProjectionError d ε + 2048 * ε) * dist x y +
          ((17039360 * ε) * r) * (∑ i ∈ F, |θ i x - θ i y|) := h
      _ ≤ (4 * activeProjectionError d ε + 2048 * ε) * dist x y +
          ((17039360 * ε) * r) * ((4 * (9 : ℝ) ^ d) * (dist x y / r)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hvar (by positivity))
      _ = (4 * activeProjectionError d ε + 2048 * ε +
            68157440 * (9 : ℝ) ^ d * ε) * dist x y := by
        field_simp [ne_of_gt hr]
        ring
      _ ≤ (72 * activeProjectionError d ε) * dist x y := by
        apply mul_le_mul_of_nonneg_right _ dist_nonneg
        unfold activeProjectionError
        nlinarith
  · have hprevious : ∀ q ∈ activeLevelIndex μ R hR k z Good t, ∀ w ∈ A,
        w ∈ closedBall q.center ((9 / 4 : ℝ) * latticeRadius R (k + t)) →
        infDist w (S q : Set (Ambient d)) ≤ (262144 * ε) * latticeRadius R (k + t) := by
      intro q hq w hw hball
      have hqA := (mem_activeLevelIndex μ R hR k z Good t q).mp hq
      have hrad : q.radius = latticeRadius R (k + t) := by
        simp only [SupportCellDescendant.radius, hqA.1]
      have hp := (hcharts q hq).height_on_inner_ball q (S q) ε A w hw (by rwa [hrad])
      rwa [hrad] at hp
    have hmove := activeLevelProjectionMap_successor_surface_displacement μ R hR k z Good t
      S hS ε hε hεsmall hfit A hprevious
    have hdx : dist (σ x) x ≤ (17039360 * ε) * r := hmove x hx
    have hdy : dist (σ y) y ≤ (17039360 * ε) * r := hmove y hy
    have hid : (σ x - σ y) - (x - y) = (σ x - x) - (σ y - y) := by abel
    have hconst : 34078720 * ε ≤ 72 * activeProjectionError d ε := by
      unfold activeProjectionError
      nlinarith
    calc
      ‖(σ x - σ y) - (x - y)‖ = ‖(σ x - x) - (σ y - y)‖ := congrArg norm hid
      _ ≤ ‖σ x - x‖ + ‖σ y - y‖ := norm_sub_le _ _
      _ ≤ (17039360 * ε) * r + (17039360 * ε) * r := add_le_add hdx hdy
      _ = (34078720 * ε) * r := by ring
      _ ≤ (34078720 * ε) * dist x y := mul_le_mul_of_nonneg_left (le_of_not_ge hnear) (by positivity)
      _ ≤ (72 * activeProjectionError d ε) * dist x y :=
        mul_le_mul_of_nonneg_right hconst dist_nonneg

theorem activeLevelProjectionMap_surface_dist_bounds
    (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (x y : Ambient d) (hx : x ∈ A) (hy : y ∈ A) :
    (1 / 4 : ℝ) * dist x y ≤
        dist (activeLevelProjectionMap μ R hR k z Good (t + 1) S hS x)
          (activeLevelProjectionMap μ R hR k z Good (t + 1) S hS y) ∧
      dist (activeLevelProjectionMap μ R hR k z Good (t + 1) S hS x)
        (activeLevelProjectionMap μ R hR k z Good (t + 1) S hS y) ≤ 2 * dist x y := by
  let σ := activeLevelProjectionMap μ R hR k z Good (t + 1) S hS
  have h := activeLevelProjectionMap_surface_residual_le μ R hR k z Good t
    S hS ε hε hεsmall hfit A hcharts x y hx hy
  have hu := norm_sub_le (σ x - σ y) (x - y)
  have hl := norm_sub_norm_le (x - y) (σ x - σ y)
  have ht := norm_sub_norm_le (σ x - σ y) (x - y)
  rw [norm_sub_rev (x - y) (σ x - σ y)] at hl
  change ‖(σ x - σ y) - (x - y)‖ ≤ (72 * activeProjectionError d ε) * dist x y at h
  have hc := mul_le_mul_of_nonneg_right hsmall (dist_nonneg : 0 ≤ dist x y)
  change (1 / 4 : ℝ) * ‖x - y‖ ≤ ‖σ x - σ y‖ ∧ ‖σ x - σ y‖ ≤ 2 * ‖x - y‖
  rw [dist_eq_norm] at h hc
  constructor <;> nlinarith

end

end RieszRectifiability

end OAI
