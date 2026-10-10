import OAI.MeasureTheory.Falconer.Estimates.SuffixScales

namespace OAI

/-! # The actual cell geometry used by the far transition

The fixed separation constant may be chosen as 2000(d+1).  Comparable
point displacements at a dyadic depth then give cells satisfying that
separation, while a center displacement outside the near graph remains
large throughout both cells.
-/

namespace Falconer
open Set Metric
variable {d : ℕ}

theorem DyadicCube.point_center_bound (P : DyadicCube d) (hP : 0 < P.side)
    {ℓ : ℝ} (hside : P.side ≤ ℓ) {x : Space d} (hx : x ∈ P.carrier) :
    dist x P.center ≤ ((d:ℝ)+1)*ℓ := by
  exact (P.dist_le hP.le hx (P.center_mem hP)).trans
    ((mul_le_mul_of_nonneg_left hside (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (sqrt_dimension_le d) (hP.le.trans hside)))

theorem DyadicCube.far_centers_force_far_points (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {ℓ : ℝ}
    (hPs : P.side ≤ ℓ) (hQs : Q.side ≤ ℓ)
    (hfar : 10*((d:ℝ)+1)*ℓ < dist P.center Q.center)
    {x y : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    8*((d:ℝ)+1)*ℓ < dist x y := by
  have hpx := P.point_center_bound hP hPs hx
  have hqy := Q.point_center_bound hQ hQs hy
  have ht := (dist_triangle P.center x Q.center).trans
    (add_le_add (le_refl _) (dist_triangle x y Q.center))
  rw [dist_comm P.center x] at ht
  linarith

theorem DyadicCube.comparable_points_separate_cells (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {ℓ : ℝ}
    (hPs : P.side ≤ ℓ) (hQs : Q.side ≤ ℓ)
    {x y : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier)
    (hlo : 256*((d:ℝ)+1)*ℓ < dist x y)
    (hhi : dist x y ≤ 1024*((d:ℝ)+1)*ℓ) :
    250*((d:ℝ)+1)*ℓ ≤ dist P.center Q.center ∧
      dist P.center Q.center ≤ 1100*((d:ℝ)+1)*ℓ := by
  have hpx := P.point_center_bound hP hPs hx
  have hqy := Q.point_center_bound hQ hQs hy
  have hℓ : 0 < ℓ := hP.trans_le hPs
  have hdim : 0 < ((d:ℝ)+1)*ℓ := by positivity
  have ht₁ := (dist_triangle P.center x Q.center).trans
    (add_le_add (le_refl _) (dist_triangle x y Q.center))
  have ht₂ := (dist_triangle x P.center y).trans
    (add_le_add (le_refl _) (dist_triangle P.center Q.center y))
  rw [dist_comm P.center x] at ht₁
  rw [dist_comm Q.center y] at ht₂
  constructor <;> linarith

end Falconer

end OAI
