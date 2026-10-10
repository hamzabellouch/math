import OAI.Geometry.EinsteinFour.ScalarNormalizer

namespace OAI

/-! Determinant monotonicity for the positive matrices in radial comparison. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
open scoped MatrixOrder
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem one_le_det_one_add_posSemidef {P : Matrix ι ι ℝ} (hP : P.PosSemidef) :
    1 ≤ (1 + P).det := by
  let U := star hP.isHermitian.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  have hd : φ P = diagonal hP.isHermitian.eigenvalues := by
    simpa only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
      hP.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have he : φ (1 + P) = diagonal (fun i => 1 + hP.isHermitian.eigenvalues i) := by
    rw [map_add, map_one, hd]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hdet : (φ (1 + P)).det = (1 + P).det := by
    have hu := congrArg Matrix.det (Unitary.coe_star_mul_self U)
    simp only [Matrix.det_mul, Matrix.det_one] at hu
    dsimp only [φ]
    rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul]
    calc
      _ = ((star U : Matrix ι ι ℝ).det * (U : Matrix ι ι ℝ).det) * (1 + P).det := by ring
      _ = _ := by rw [hu, one_mul]
  rw [← hdet, he, Matrix.det_diagonal]
  exact Finset.one_le_prod₀ (fun i _ => by linarith [hP.eigenvalues_nonneg i])

theorem det_le_det_of_posDef_sub_posSemidef {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hBA : (B - A).PosSemidef) : A.det ≤ B.det := by
  let U := CFC.sqrt A⁻¹
  have hU : Uᴴ = U := (CFC.sqrt_nonneg A⁻¹).posSemidef.isHermitian.eq
  have hsq : U * U = A⁻¹ := CFC.sqrt_mul_sqrt_self A⁻¹ hA.inv.posSemidef.nonneg
  have hn : U * A * U = 1 := by
    apply mul_eq_one_comm.mp
    rw [← Matrix.mul_assoc, hsq,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit)]
  have hp : (U * (B - A) * U).PosSemidef := by
    simpa only [hU] using hBA.conjTranspose_mul_mul_same U
  have he : U * B * U = 1 + U * (B - A) * U := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hn]
    abel
  have hd := one_le_det_one_add_posSemidef hp
  rw [← he, Matrix.det_mul, Matrix.det_mul] at hd
  have hn' := congrArg Matrix.det hn
  simp only [Matrix.det_mul, Matrix.det_one] at hn'
  calc
    A.det ≤ A.det * (U.det * B.det * U.det) := le_mul_of_one_le_right hA.det_pos.le hd
    _ = (U.det * A.det * U.det) * B.det := by ring
    _ = B.det := by rw [hn', one_mul]

end
end PositiveEinsteinFour.Jacobi

end OAI
