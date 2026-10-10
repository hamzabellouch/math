import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryPositiveForm

namespace OAI

/-! # Removal of the integer scaling in the boundary certificate -/

open Polynomial Matrix

namespace DefocusingNLS.BoundaryCertificate

noncomputable def boundaryQ (ell : ℕ) (b v : ℝ) : ℂ :=
  (((ell : ℝ) / 2 - 1 / 32 : ℝ) : ℂ) + Complex.I * (v - b : ℝ)

theorem inputT_eval_scaled (ell n : ℕ) (b v : ℝ) :
    (inputT ell n b).eval (v : ℂ) =
      (100000000 : ℂ) * (boundaryQ ell b v + n) := by
  simp only [inputT, eval_add, eval_C, eval_mul, eval_X, boundaryQ, inputReal]
  push_cast
  ring

attribute [local irreducible] polynomialState

theorem polynomialState_eval_scaled (ell : ℕ) (b Z v : ℝ) (N : ℕ) (i j : Fin 2) :
    ((stateMatrix (polynomialState ell b Z N)) i j).eval (v : ℂ) =
      (100000000 : ℂ) ^ N * forwardProduct (ell + 5) (Complex.I * Z)
        (boundaryQ ell b v) N i j := by
  induction N generalizing i j with
  | zero => fin_cases i <;> fin_cases j <;> simp [polynomialState, stateMatrix, forwardProduct]
  | succ N ih =>
    rw [polynomialState, polynomialStep_matrix]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, eval_add, eval_mul, ih]
    have ht := inputT_eval_scaled ell N b v
    fin_cases i <;> fin_cases j <;>
      simp [forwardProduct, forwardMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        eval_sub, eval_neg, eval_C, inputS, ht, pow_succ] <;> ring

theorem forwardProduct_conjugate (M : ℝ) (s q : ℂ) (N : ℕ) (i j : Fin 2) :
    star (forwardProduct (M : ℂ) s q N i j) =
      forwardProduct (M : ℂ) (star s) (star q) N i j := by
  induction N generalizing i j with
  | zero => fin_cases i <;> fin_cases j <;> simp [forwardProduct]
  | succ N ih =>
    simp only [forwardProduct, Matrix.mul_apply, Fin.sum_univ_two, star_add, star_mul, ih]
    have hs (a c : Fin 2) : star (forwardMatrix (M : ℂ) s (q + N) a c) =
        forwardMatrix (M : ℂ) (star s) (star q + N) a c := by
      fin_cases a <;> fin_cases c <;> simp [forwardMatrix]
    rw [hs, hs]
    ring

theorem boundaryQ_conjugate (ell : ℕ) (b v : ℝ) :
    star (boundaryQ ell b (-v)) = boundaryQ ell (-b) v := by
  simp only [boundaryQ, star_add, star_mul, Complex.star_def, Complex.conj_ofReal,
    Complex.conj_I]
  push_cast
  ring

theorem coneForm_scale_parameters (h M : ℝ) (s B C : ℂ) :
    coneForm (h * M) ((h : ℂ) * s) B C = h * coneForm M s B C := by
  simp only [coneForm, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem matrixCone_real_scaling (h a M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) ℂ) (w : Fin 2 → ℂ) :
    matrixCone (h * M) ((h : ℂ) * s) ((a : ℂ) • T) w =
      h * a ^ 2 * matrixCone M s T w := by
  simp only [matrixCone, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  rw [coneForm_scale, coneForm_scale_parameters]
  simp only [Complex.normSq_ofReal]
  ring

end DefocusingNLS.BoundaryCertificate

end OAI
