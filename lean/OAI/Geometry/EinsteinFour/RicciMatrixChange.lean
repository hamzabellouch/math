import OAI.Geometry.EinsteinFour.ActualRicciContraction

namespace OAI

/-! Tracing curvature after an arbitrary invertible change of coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

/-- Contract the output and first curvature-input indices. -/
def ricciMatrix (R : Fin 4 → Fin 4 → Mat4) : Mat4 :=
  fun j k => ∑ i, R i j i k

private theorem conjugate_row_contraction (J A : Mat4) (hJ : IsUnit J.det)
    (a k : Fin 4) :
    (∑ i, J a i * (J⁻¹ * A * J) i k) = (A * J) a k := by
  change (J * (J⁻¹ * A * J)) a k = _
  have he : J * (J⁻¹ * A * J) = A * J := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv J hJ,
      one_mul]
  exact congrArg (fun B : Mat4 => B a k) he

/-- Curvature conjugation in the vector slot and the two covector slots
induces precisely the ordinary covariant matrix law for Ricci. -/
theorem ricciMatrix_pullback (J : Mat4) (R S : Fin 4 → Fin 4 → Mat4)
    (hJ : IsUnit J.det)
    (hS : ∀ i j, S i j = J⁻¹ *
      (∑ a, ∑ b, (J a i * J b j) • R a b) * J) :
    ricciMatrix S = Jᵀ * (ricciMatrix R * J) := by
  have hexp (i j : Fin 4) : S i j =
      ∑ a, ∑ b, (J a i * J b j) • (J⁻¹ * R a b * J) := by
    rw [hS]
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  ext j k
  change (∑ i, S i j i k) = (Jᵀ * (ricciMatrix R * J)) j k
  simp only [hexp, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  calc
    _ = ∑ a, ∑ b, J b j *
        (∑ i, J a i * (J⁻¹ * R a b * J) i k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ a, ∑ b, J b j * (R a b * J) a k := by
      simp only [conjugate_row_contraction J _ hJ]
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, ricciMatrix,
        Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]

end
end PositiveEinsteinFour.Geometry

end OAI
