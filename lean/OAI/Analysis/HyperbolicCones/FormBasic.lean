import OAI.Analysis.HyperbolicCones.Model

namespace OAI

/-! Exact identities for the Choi–Lam form. -/

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

universe u

namespace Paper256

theorem choiLam_expand {R : Type u} [CommRing R] (z y : Fin 3 → R) :
    choiLam z y =
      z 0 ^ 2 * y 0 ^ 2 + z 1 ^ 2 * y 1 ^ 2 + z 2 ^ 2 * y 2 ^ 2 -
      2 * (z 0 * y 0 * z 1 * y 1 + z 0 * y 0 * z 2 * y 2 +
        z 1 * y 1 * z 2 * y 2) +
      (z 0 ^ 2 * y 1 ^ 2 + z 1 ^ 2 * y 2 ^ 2 + z 2 ^ 2 * y 0 ^ 2) := by
  simp [choiLam, Fin.sum_univ_succ]
  ring

theorem qMatrix_isHermitian (y : Fin 3 → ℝ) : (qMatrix y).IsHermitian := by
  show (qMatrix y)ᴴ = qMatrix y
  ext i j
  by_cases hij : i = j
  · subst j
    simp [qMatrix, Matrix.conjTranspose_apply]
  · simp [qMatrix, Matrix.conjTranspose_apply, hij, Ne.symm hij, mul_comm]

theorem zMatrix_isHermitian (z : Fin 3 → ℝ) : (zMatrix z).IsHermitian := by
  show (zMatrix z)ᴴ = zMatrix z
  ext i j
  by_cases hij : i = j
  · subst j
    simp [zMatrix, Matrix.conjTranspose_apply]
  · simp [zMatrix, Matrix.conjTranspose_apply, hij, Ne.symm hij, mul_comm]

theorem qMatrix_quadratic (z y : Fin 3 → ℝ) :
    dotProduct z (qMatrix y *ᵥ z) = choiLam z y := by
  simp [dotProduct, Matrix.mulVec, qMatrix, choiLam, Fin.sum_univ_succ]
  ring

theorem zMatrix_quadratic (z y : Fin 3 → ℝ) :
    dotProduct y (zMatrix z *ᵥ y) = choiLam z y := by
  simp [dotProduct, Matrix.mulVec, zMatrix, choiLam, Fin.sum_univ_succ]
  ring

theorem zMatrix_diag_nonnegative (z : Fin 3 → ℝ) (i : Fin 3) :
    0 ≤ zMatrix z i i := by
  simp only [zMatrix, ↓reduceIte]
  positivity

theorem zMatrix_principal_minor_two (z : Fin 3 → ℝ) (i : Fin 3) :
    Matrix.det ((zMatrix z).submatrix
      (fun j : Fin 2 => if j = 0 then i else i + 1)
      (fun j : Fin 2 => if j = 0 then i else i + 1)) =
      (z i ^ 2) ^ 2 + z (i + 2) ^ 2 * (z i ^ 2 + z (i + 1) ^ 2) := by
  fin_cases i <;> simp [Matrix.det_fin_two, Matrix.submatrix, zMatrix,
    Fin.reduceAdd, Fin.reduceEq] <;> ring

theorem zMatrix_principal_minor_two_nonnegative (z : Fin 3 → ℝ) (i : Fin 3) :
    0 ≤ Matrix.det ((zMatrix z).submatrix
      (fun j : Fin 2 => if j = 0 then i else i + 1)
      (fun j : Fin 2 => if j = 0 then i else i + 1)) := by
  rw [zMatrix_principal_minor_two]
  positivity

theorem zMatrix_det (z : Fin 3 → ℝ) :
    Matrix.det (zMatrix z) =
      (z 0 ^ 2) ^ 2 * z 1 ^ 2 + (z 1 ^ 2) ^ 2 * z 2 ^ 2 +
        (z 2 ^ 2) ^ 2 * z 0 ^ 2 - 3 * z 0 ^ 2 * z 1 ^ 2 * z 2 ^ 2 := by
  simp [Matrix.det_fin_three, zMatrix]
  ring

theorem choiLam_nonzero :
    choiLam (![1, 0, 0] : Fin 3 → ℝ) (![1, 0, 0] : Fin 3 → ℝ) = 1 := by
  simp [choiLam_expand, Matrix.cons_val]

theorem choiLam_cyclic_zero (i : Fin 3) :
    choiLam (Pi.single i 1 : Fin 3 → ℝ) (Pi.single (i + 2) 1) = 0 := by
  fin_cases i <;> simp [choiLam_expand, Fin.reduceAdd, Fin.reduceEq]

theorem choiLam_sign_zero (σ : Fin 3 → ℝ)
    (hσ : ∀ i, σ i = 1 ∨ σ i = -1) : choiLam σ σ = 0 := by
  rcases hσ 0 with h0 | h0 <;> rcases hσ 1 with h1 | h1 <;>
    rcases hσ 2 with h2 | h2 <;> norm_num [choiLam_expand, h0, h1, h2]

theorem choiLam_curve (i : Fin 3) (s : ℝ) :
    choiLam ((Pi.single i 1 : Fin 3 → ℝ) + s • Pi.single (i + 2) 1)
      (Pi.single (i + 2) 1 + s • Pi.single i 1) = s ^ 4 := by
  fin_cases i <;> simp [choiLam_expand, Fin.reduceAdd, Fin.reduceEq] <;> ring

theorem choiLam_smul_left (z y : Fin 3 → ℝ) (s : ℝ) :
    choiLam (s • z) y = s ^ 2 * choiLam z y := by
  simp only [choiLam_expand, Pi.smul_apply, smul_eq_mul]
  ring

theorem choiLam_smul_right (z y : Fin 3 → ℝ) (s : ℝ) :
    choiLam z (s • y) = s ^ 2 * choiLam z y := by
  simp only [choiLam_expand, Pi.smul_apply, smul_eq_mul]
  ring

end Paper256

end

end OAI
