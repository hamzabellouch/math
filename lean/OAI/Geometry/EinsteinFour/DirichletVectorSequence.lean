import OAI.Geometry.EinsteinFour.JacobiSchemeMatrix

namespace OAI

/-! The block Dirichlet operator on an actual vector sequence. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix
noncomputable section

theorem scalarLift_mulVec {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin 3 × Fin N → ℝ) (a : Fin 3) (i : Fin N) :
    (scalarLift G *ᵥ x) (a,i) = (G *ᵥ fun j => x (a,j)) i := by
  simp [Matrix.mulVec, dotProduct, scalarLift, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.one_apply, Fintype.sum_prod_type]

theorem blockDiagonal_mulVec {N : ℕ} (D : Fin N → NormalMatrix)
    (x : Fin 3 × Fin N → ℝ) (a : Fin 3) (i : Fin N) :
    (Matrix.blockDiagonal D *ᵥ x) (a,i) = (D i *ᵥ fun b => x (b,i)) a := by
  simp [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply, Fintype.sum_prod_type]

theorem dirichletMatrix_eq_scalarLift {N : ℕ} (D : Fin N → NormalMatrix) :
    dirichletMatrix D = scalarLift (scalarDirichlet N 2) -
      Matrix.blockDiagonal (fun i => (2 : ℝ) • (1 : NormalMatrix) - D i) := by
  have h := scalarLift_sub_diagonal (N := N) 2 1
    (fun i => (2 : ℝ) • (1 : NormalMatrix) - D i)
  simpa only [one_smul, sub_sub_cancel] using h.symm

theorem dirichlet_mulVec_sequence {N : ℕ} (D : Fin N → NormalMatrix)
    (z : ℕ → Fin 3 → ℝ) (hzero : z 0 = 0) (hend : z (N + 1) = 0)
    (a : Fin 3) (i : Fin N) :
    (dirichletMatrix D *ᵥ fun p => z (p.2.val + 1) p.1) (a,i) =
      (D i *ᵥ z (i.val + 1)) a - z i.val a - z (i.val + 2) a := by
  rw [dirichletMatrix_eq_scalarLift, Matrix.sub_mulVec, Pi.sub_apply,
    scalarLift_mulVec, blockDiagonal_mulVec]
  have h := scalarDirichlet_apply_sequence 2 (fun n => z n a)
    (by rw [hzero]; rfl) (by rw [hend]; rfl) i
  rw [h, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

end
end PositiveEinsteinFour.Jacobi

end OAI
