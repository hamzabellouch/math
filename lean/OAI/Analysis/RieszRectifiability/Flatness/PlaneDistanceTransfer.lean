import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.AffineTubeCover

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry
open scoped BigOperators

theorem affine_projection_norm_le {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S]
    (a : Ambient d) (ha : a ∈ S) (x : Ambient d) :
    ‖(orthogonalProjection S x : Ambient d)‖ ≤ ‖x‖ + ‖a‖ := by
  have hdist : dist (orthogonalProjection S x : Ambient d) (orthogonalProjection S 0 : Ambient d) ≤
      ‖x‖ := by simpa only [dist_zero_right] using! affine_projection_dist_le S x 0
  have hzero : ‖(orthogonalProjection S 0 : Ambient d)‖ ≤ ‖a‖ := by
    calc
      ‖(orthogonalProjection S 0 : Ambient d)‖ = dist (0 : Ambient d) (orthogonalProjection S 0) :=
        (dist_zero_left _).symm
      _ = infDist (0 : Ambient d) (S : Set (Ambient d)) := dist_orthogonalProjection_eq_infDist S 0
      _ ≤ dist (0 : Ambient d) a := infDist_le_dist_of_mem ha
      _ = ‖a‖ := dist_zero_left a
  calc
    ‖(orthogonalProjection S x : Ambient d)‖ = dist (orthogonalProjection S x : Ambient d) 0 :=
      (dist_zero_right _).symm
    _ ≤ dist (orthogonalProjection S x : Ambient d) (orthogonalProjection S 0 : Ambient d) +
        dist (orthogonalProjection S 0 : Ambient d) 0 := dist_triangle _ _ _
    _ ≤ ‖x‖ + ‖a‖ := add_le_add hdist (by simpa only [dist_zero_right] using! hzero)

theorem plane_distance_transfer {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S] (W : Set (Ambient d))
    (a : Ambient d) (ha : a ∈ S) (B C R : ℝ) (hC : 0 ≤ C) (hR : 0 < R)
    (haB : ‖a‖ ≤ B)
    (hcompare : ∀ p ∈ S, infDist p W ≤ C * (1 + ‖p‖ / R)) (x : Ambient d) :
    infDist x W ≤ infDist x (S : Set (Ambient d)) + C * (1 + (‖x‖ + B) / R) := by
  let p : Ambient d := orthogonalProjection S x
  have hp : p ∈ S := orthogonalProjection_mem x
  have hnorm : ‖p‖ ≤ ‖x‖ + B :=
    (affine_projection_norm_le S a ha x).trans (add_le_add le_rfl haB)
  have hfit : infDist p W ≤ C * (1 + (‖x‖ + B) / R) :=
    (hcompare p hp).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (div_le_div_of_nonneg_right hnorm hR.le)) hC)
  calc
    infDist x W ≤ infDist p W + dist x p := infDist_le_infDist_add_dist
    _ = infDist p W + infDist x (S : Set (Ambient d)) := by
      rw [dist_orthogonalProjection_eq_infDist]
    _ ≤ C * (1 + (‖x‖ + B) / R) + infDist x (S : Set (Ambient d)) := add_le_add hfit le_rfl
    _ = _ := add_comm _ _

theorem upper_bound_by_last_and_step_sum (d e : ℕ → ℝ) (k : ℕ)
    (hstep : ∀ i < k, d i ≤ d (i + 1) + e i) :
    d 0 ≤ d k + ∑ i ∈ Finset.range k, e i := by
  induction k with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, add_zero, le_refl]
  | succ k ih =>
    have hp := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    have hk := hstep k (Nat.lt_succ_self k)
    rw [Finset.sum_range_succ]
    linarith

end

end RieszRectifiability

end OAI
