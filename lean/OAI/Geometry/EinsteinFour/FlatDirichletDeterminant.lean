import OAI.Geometry.EinsteinFour.FlatDirichletNormalizer
import OAI.Geometry.EinsteinFour.JacobiSchemeMatrix

namespace OAI

/-! Exact normalization of the flat discrete determinant. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem flatDirichlet_det (N : ℕ) : (scalarDirichlet N 2).det = N + 1 := by
  let D := fun _ : ℕ => (2 : ℝ) • (1 : NormalMatrix)
  let Y := fun n : ℕ => (n : ℝ) • (1 : NormalMatrix)
  have hrec (i : ℕ) : Y (i + 2) = D i * Y (i + 1) - Y i := by
    dsimp [D,Y]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    push_cast
    module
  have hu (i : ℕ) (hi : 1 ≤ i) (_ : i ≤ N + 1) : IsUnit (Y i).det := by
    simp only [Y, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
    apply isUnit_iff_ne_zero.mpr
    positivity
  have h := dirichlet_determinant_eq_jacobi D Y N
    (fun _ => by simp [D]) (by simp [Y]) (by simp [Y]) hrec hu
  have he : dirichletMatrix (fun i : Fin N => D i.val) =
      scalarLift (scalarDirichlet N 2) := by
    simpa only [D, smul_zero, zero_smul, sub_zero] using
      (scalarLift_sub_diagonal (N := N) 2 0 (fun _ => (0 : NormalMatrix))).symm
  rw [he, det_scalarLift] at h
  simp only [Y, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one,
    Nat.cast_add, Nat.cast_one] at h
  exact (Odd.pow_injective (by decide : Odd 3)) h

end
end PositiveEinsteinFour.Jacobi

end OAI
