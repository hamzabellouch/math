import OAI.Geometry.RCD.Coordinates.EuclideanCovectorIsometry

namespace OAI

/-! # A finite coordinate error controls the Euclidean distance -/

open scoped BigOperators
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_norm_le_card_mul {n : ℕ} (z : Euclidean n) {δ : ℝ}
    (h : ∀ i, |z i| ≤ δ) : ‖z‖ ≤ (n : ℝ)*δ := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  calc
    ‖z‖ = ‖∑ i : Fin n, b.repr z i • b i‖ := by rw [b.sum_repr]
    _ ≤ ∑ i : Fin n, ‖b.repr z i • b i‖ := norm_sum_le _ _
    _ = ∑ i : Fin n, |z i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul,b.norm_eq_one,mul_one]
      rfl
    _ ≤ ∑ _i : Fin n, δ := Finset.sum_le_sum (fun i _ => h i)
    _ = (n : ℝ)*δ := by simp

end RegularPointCoordinates

end

end OAI
