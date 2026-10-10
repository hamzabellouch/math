import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveProjectionAmbientBounds
import OAI.Analysis.RieszRectifiability.Projections.ProjectionAverageGlobalIncrement

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped BigOperators NNReal

def activeProjectionGlobalLipschitzConstant (d : ℕ) : ℝ≥0 :=
  Real.toNNReal (3 + 24 * (9 : ℝ) ^ d)

theorem activeLevelProjectionMap_global_lipschitz {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hεsmall : ε ≤ 1 / 1024)
    (hfit : ∀ i ∈ activeLevelIndex μ R hR k z Good t,
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε) :
    LipschitzWith (activeProjectionGlobalLipschitzConstant d)
      (activeLevelProjectionMap μ R hR k z Good t S hS) := by
  apply LipschitzWith.of_dist_le'
  intro x y
  let r := latticeRadius R (k + t)
  let F := activeLevelIndex μ R hR k z Good t
  let θ := activeLevelWeight μ R hR k z Good t
  let π := fun i => nonemptyAffineProjection (S i) (hS i).1
  let σ := activeLevelProjectionMap μ R hR k z Good t S hS
  have hr : 0 < r := latticeRadius_pos R hR (k + t)
  by_cases hnear : dist x y ≤ r
  · have hlinear : ∀ i ∈ F, θ i x ≠ 0 →
        ‖(π i x - x) - (π i y - y)‖ ≤ (2 : ℝ) * dist x y := by
      intro i _ _
      have hπ := (nonemptyAffineProjection_lipschitz (S i) (hS i).1).dist_le_mul x y
      simp only [NNReal.coe_one, one_mul] at hπ
      have hid : (π i x - x) - (π i y - y) = (π i x - π i y) - (x - y) := by abel
      rw [hid]
      have h := norm_sub_le (π i x - π i y) (x - y)
      rw [← dist_eq_norm (π i x) (π i y), ← dist_eq_norm x y] at h
      change dist (π i x) (π i y) ≤ dist x y at hπ
      linarith
    have hoffset : ∀ i ∈ F, θ i x ≠ θ i y → dist (π i y) y ≤ 6 * r := by
      intro i hi hchange
      have hyi : dist y i.center ≤ 5 * r := by
        by_cases hny : θ i y = 0
        · have hnx : θ i x ≠ 0 := fun hx0 => hchange (hx0.trans hny.symm)
          have hx := (activeLevelWeight_ne_zero_iff μ R hR k z Good t i x).mp hnx
          have ht := dist_triangle y x i.center
          rw [dist_comm y x] at ht
          change dist x i.center < 4 * r at hx
          linarith
        · have hy := (activeLevelWeight_ne_zero_iff μ R hR k z Good t i y).mp hny
          change dist y i.center < 4 * r at hy
          linarith
      simpa only [show (5 : ℝ) + 1 = 6 by norm_num] using!
        active_level_plane_displacement_le μ R hR k z Good t S hS ε hεsmall hfit i hi y 5 hyi
    have h := finiteProjectionAverage_dist_le_of_weight_sum_le_one F θ π x y 2 (6 * r)
      (by norm_num) (fun i _ => activeLevelWeight_nonneg μ R hR k z Good t i x)
      (activeLevelWeight_sum_le_one μ R hR k z Good t x) hlinear hoffset
    have hvar : (∑ i ∈ F, |θ i x - θ i y|) ≤ (4 * (9 : ℝ) ^ d) * (dist x y / r) :=
      activeLevelWeight_sum_abs_sub_le μ R hR k z Good t x y
    calc
      dist (σ x) (σ y) ≤ (1 + 2) * dist x y + (6 * r) * (∑ i ∈ F, |θ i x - θ i y|) := h
      _ ≤ (1 + 2) * dist x y + (6 * r) * ((4 * (9 : ℝ) ^ d) * (dist x y / r)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hvar (by positivity))
      _ = (3 + 24 * (9 : ℝ) ^ d) * dist x y := by
        field_simp [ne_of_gt hr]
        ring
  · have hx := activeLevelProjectionMap_global_displacement μ R hR k z Good t S hS ε hεsmall hfit x
    have hy := activeLevelProjectionMap_global_displacement μ R hR k z Good t S hS ε hεsmall hfit y
    have h1 := dist_triangle (σ x) x (σ y)
    have h2 := dist_triangle x y (σ y)
    rw [dist_comm y (σ y)] at h2
    change dist (σ x) x ≤ 5 * r at hx
    change dist (σ y) y ≤ 5 * r at hy
    have hpow : (1 : ℝ) ≤ (9 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    calc
      dist (σ x) (σ y) ≤ 11 * dist x y := by linarith
      _ ≤ (3 + 24 * (9 : ℝ) ^ d) * dist x y :=
        mul_le_mul_of_nonneg_right (by linarith) dist_nonneg

end

end RieszRectifiability

end OAI
