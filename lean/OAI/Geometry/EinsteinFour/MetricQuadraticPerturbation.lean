import OAI.Geometry.EinsteinFour.ChartVolumeDensity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

/-! A four-dimensional entrywise perturbation estimate for the metric.
It converts continuity of the chart metric into almost-isometric norm
bounds after freezing an orthonormal frame at one point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

private theorem sum_abs_sq_le_four_norm_sq (v : FourSpace) :
    (∑ i : Fin 4, |v i|) ^ 2 ≤ 4 * ‖v‖ ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 4))
    (fun _ => (1 : ℝ)) (fun i => |v i|)
  simpa [EuclideanSpace.real_norm_sq_eq, Real.norm_eq_abs] using h

/-- The factor four is exactly the dimension, so an entrywise bound
of `δ/4` controls the complete quadratic form by `δ`. -/
theorem quadraticForm_entry_bound (A : Mat4) (δ : ℝ) (hδ : 0 ≤ δ)
    (hA : ∀ i j, |A i j| ≤ δ / 4) (v : FourSpace) :
    |WithLp.ofLp v ⬝ᵥ (A *ᵥ WithLp.ofLp v)| ≤ δ * ‖v‖ ^ 2 := by
  have hsum : |∑ i : Fin 4, ∑ j : Fin 4, v i * A i j * v j| ≤
      (δ / 4) * (∑ i : Fin 4, |v i|) ^ 2 := by
    calc
      _ ≤ ∑ i : Fin 4, |∑ j : Fin 4, v i * A i j * v j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, |v i * A i j * v j| := by
        exact Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, |v i| * (δ / 4) * |v j| := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hA i j) (abs_nonneg _)) (abs_nonneg _)
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul, pow_two]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  calc
    _ = |∑ i : Fin 4, ∑ j : Fin 4, v i * A i j * v j| := by
      apply congrArg abs
      simp only [dotProduct, mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ (δ / 4) * (∑ i : Fin 4, |v i|) ^ 2 := hsum
    _ ≤ (δ / 4) * (4 * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (sum_abs_sq_le_four_norm_sq v) (by positivity)
    _ = δ * ‖v‖ ^ 2 := by ring

theorem quadraticForm_near_identity (A : Mat4) (δ : ℝ) (hδ : 0 ≤ δ)
    (hA : ∀ i j, |A i j - (1 : Mat4) i j| ≤ δ / 4) (v : FourSpace) :
    (1 - δ) * ‖v‖ ^ 2 ≤ WithLp.ofLp v ⬝ᵥ (A *ᵥ WithLp.ofLp v) ∧
      WithLp.ofLp v ⬝ᵥ (A *ᵥ WithLp.ofLp v) ≤ (1 + δ) * ‖v‖ ^ 2 := by
  have h := quadraticForm_entry_bound (A - 1) δ hδ hA v
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec] at h
  have hnorm : WithLp.ofLp v ⬝ᵥ WithLp.ofLp v = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct, pow_two]
  rw [hnorm] at h
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  constructor <;> nlinarith

end
end PositiveEinsteinFour.Geometry

end OAI
