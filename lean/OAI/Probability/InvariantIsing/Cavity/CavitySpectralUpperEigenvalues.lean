import OAI.Probability.InvariantIsing.Cavity.CavityDiagonalFullMoment
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteCovariance

namespace OAI

/-! The actual finite compression and diagonal base obey the spectral
upper bound used by the full Gaussian moment calculation. -/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_eigenvalues_le_of_upper {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (M : ℝ)
    (hM : (M • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef) :
    ∀ i, hA.eigenvalues i ≤ M := by
  let U := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  have ha : U.transpose * A * U = Matrix.diagonal hA.eigenvalues := by
    simpa only [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def, RCLike.ofReal_real_eq_id, id_eq, U] using
      hA.conjStarAlgAut_star_eigenvectorUnitary
  have hu : U.transpose * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have he : U.transpose * (M • 1 - A) * U = Matrix.diagonal (fun i => M - hA.eigenvalues i) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hu, ha]
    rw [show M • (1 : Matrix (Fin d) (Fin d) ℝ) = Matrix.diagonal (fun _ => M) by
      ext i j; by_cases h : i = j <;> simp [h]]
    exact Matrix.diagonal_sub _ _
  have hp := hM.conjTranspose_mul_mul_same U
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, he] at hp
  intro i
  exact sub_nonneg.mp (by simpa only [Matrix.diagonal_apply_eq] using hp.diag_nonneg (i := i))

lemma cavity_compressed_eigenvalues_le {m N d : ℕ}
    (eig : Fin m → ℝ) (a : Fin m) (ha : ∀ j, eig j ≤ eig a)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hA : (B.transpose * cavityRepeatedSpectrum (n := N) eig * B).IsHermitian) :
    ∀ i, hA.eigenvalues i ≤ eig a :=
  cavity_eigenvalues_le_of_upper _ hA _ (cavity_finite_spectral_upper eig a ha B hB)

lemma cavity_diagonal_eigenvalues_le {m d : ℕ}
    (eig : Fin m → ℝ) (g : Fin d → Fin m) (a : Fin m) (ha : ∀ j, eig j ≤ eig a)
    (hA : (Matrix.diagonal (fun j => eig (g j))).IsHermitian) :
    ∀ i, hA.eigenvalues i ≤ eig a := by
  apply cavity_eigenvalues_le_of_upper _ hA
  have he : eig a • (1 : Matrix (Fin d) (Fin d) ℝ) - Matrix.diagonal (fun j => eig (g j)) =
      Matrix.diagonal (fun j => eig a - eig (g j)) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [he]
  exact Matrix.PosSemidef.diagonal (fun j => sub_nonneg.mpr (ha (g j)))

end InvariantIsing

end

end OAI
