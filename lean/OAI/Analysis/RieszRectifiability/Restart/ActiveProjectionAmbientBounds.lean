import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveLevelProjectionMaps

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hεsmall : ε ≤ 1 / 1024)
  (hfit : ∀ i ∈ activeLevelIndex μ R hR k z Good t,
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)

include hS hεsmall hfit

theorem active_level_plane_center_height_le
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ activeLevelIndex μ R hR k z Good t) :
    infDist i.center (S i : Set (Ambient d)) ≤ latticeRadius R (k + t) := by
  have hiA := (mem_activeLevelIndex μ R hR k z Good t i).mp hi
  have hrad : i.radius = latticeRadius R (k + t) := by simp only [SupportCellDescendant.radius, hiA.1]
  have hr := i.radius_pos
  have hc := (bilateralPlaneError_lt_pointwise μ ⟨i.center, i.center_mem_support⟩
    i.center (1024 * i.radius) ε (by positivity) (S i) (hS i) (hfit i hi)).1 i.center
      (mem_ball_self (by positivity)) i.center_mem_support
  have hm := mul_le_mul_of_nonneg_right hεsmall hr.le
  rw [← hrad]
  nlinarith

theorem active_level_plane_displacement_le
    (i : SupportCellDescendant μ R hR k z) (hi : i ∈ activeLevelIndex μ R hR k z Good t)
    (x : Ambient d) (A : ℝ) (hx : dist x i.center ≤ A * latticeRadius R (k + t)) :
    dist (nonemptyAffineProjection (S i) (hS i).1 x) x ≤ (A + 1) * latticeRadius R (k + t) := by
  have hc := active_level_plane_center_height_le μ R hR k z Good t S hS ε hεsmall hfit i hi
  have ht : infDist x (S i : Set (Ambient d)) ≤ infDist i.center (S i : Set (Ambient d)) +
      dist x i.center := infDist_le_infDist_add_dist
  rw [nonemptyAffineProjection_dist_self]
  nlinarith

theorem activeLevelProjectionMap_global_displacement (x : Ambient d) :
    dist (activeLevelProjectionMap μ R hR k z Good t S hS x) x ≤ 5 * latticeRadius R (k + t) := by
  have hr := latticeRadius_pos R hR (k + t)
  apply finiteProjectionAverage_dist_self_le _ _ _ x (5 * latticeRadius R (k + t)) (by positivity)
    (fun i _ => activeLevelWeight_nonneg μ R hR k z Good t i x)
    (activeLevelWeight_sum_le_one μ R hR k z Good t x)
  intro i hi hn
  have hnear := (activeLevelWeight_ne_zero_iff μ R hR k z Good t i x).mp hn
  simpa only [show (4 : ℝ) + 1 = 5 by norm_num] using!
    active_level_plane_displacement_le μ R hR k z Good t S hS ε hεsmall hfit i hi x 4 hnear.le

end

end RieszRectifiability

end OAI
