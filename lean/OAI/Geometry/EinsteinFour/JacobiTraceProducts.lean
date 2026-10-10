import OAI.Geometry.EinsteinFour.MatrixGeodesicAverage
import OAI.Geometry.EinsteinFour.JacobiMatrixLoss
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

/-! Ordered curvature products in the lower radial determinant estimate.
No curvature matrices at different times are commuted. -/

namespace PositiveEinsteinFour.Jacobi
open Matrix
open scoped Matrix.Norms.Frobenius
noncomputable section

theorem abs_trace_mul_le_frobenius (A B : NormalMatrix) :
    |(A * B).trace| ≤ ‖A‖ * ‖B‖ := by
  have h := abs_real_inner_le_norm (matrixVector Aᵀ) (matrixVector B)
  have he : inner ℝ (matrixVector Aᵀ) (matrixVector B) = (A * B).trace := by
    change inner ℝ (WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 => A ij.2 ij.1))
      (WithLp.toLp 2 (fun ij : Fin 3 × Fin 3 => B ij.1 ij.2)) = _
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
      Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [he, matrixVector.norm_map, Matrix.frobenius_norm_transpose] using h

theorem frobenius_le_three_of_posSemidef_trace {A : NormalMatrix}
    (hA : A.PosSemidef) (htr : A.trace = 3) : ‖A‖ ≤ 3 := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := hA.isHermitian.eigenvalues)
    (fun i _ => hA.eigenvalues_nonneg i)
  have ht : (∑ i, hA.isHermitian.eigenvalues i) = 3 := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq, htr] using
      hA.isHermitian.trace_eq_sum_eigenvalues.symm
  rw [ht, ← frobenius_sq_eq_sum_eigenvalues hA.isHermitian] at hs
  nlinarith [norm_nonneg A]

theorem frobenius_mul_list_le (A : NormalMatrix) (L : List NormalMatrix)
    (hL : ∀ B ∈ L, ‖B‖ ≤ 3) :
    ‖A * L.prod‖ ≤ ‖A‖ * 3 ^ L.length := by
  induction L generalizing A with
  | nil => simp
  | cons B L ih =>
      rw [List.prod_cons, ← mul_assoc]
      calc
        ‖A * B * L.prod‖ ≤ ‖A * B‖ * 3 ^ L.length :=
          ih (A * B) (fun C hC => hL C (List.mem_cons_of_mem B hC))
        _ ≤ (‖A‖ * 3) * 3 ^ L.length := by
          gcongr
          exact (Matrix.frobenius_norm_mul A B).trans
            (mul_le_mul_of_nonneg_left (hL B (List.mem_cons_self)) (norm_nonneg A))
        _ = ‖A‖ * 3 ^ (B :: L).length := by
          simp only [List.length_cons, pow_succ]
          ring

/-- This is the ordered-product bound in manuscript Lemma 4.7. The first
and last factors retain their square-integrable norms. -/
theorem abs_trace_curvature_product_le (A B : NormalMatrix) (L : List NormalMatrix)
    (hL : ∀ C ∈ L, C.PosSemidef ∧ C.trace = 3) :
    |(A * L.prod * B).trace| ≤ 3 ^ L.length * ‖A‖ * ‖B‖ := by
  calc
    _ ≤ ‖A * L.prod‖ * ‖B‖ := abs_trace_mul_le_frobenius _ _
    _ ≤ (‖A‖ * 3 ^ L.length) * ‖B‖ := by
      gcongr
      exact frobenius_mul_list_le A L (fun C hC =>
        frobenius_le_three_of_posSemidef_trace (hL C hC).1 (hL C hC).2)
    _ = _ := by ring

end
end PositiveEinsteinFour.Jacobi

end OAI
