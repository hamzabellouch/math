import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryDiagonalCertificate
import Mathlib.Topology.Algebra.Polynomial

namespace OAI

/-! # Evaluation of the certified Hermitian polynomial -/

open Polynomial Matrix

namespace DefocusingNLS

theorem conjugatePolynomial_eval_real (p : Polynomial ℂ) (v : ℝ) :
    (conjugatePolynomial p).eval (v : ℂ) = star (p.eval (v : ℂ)) := by
  simpa [conjugatePolynomial] using
    (Polynomial.eval_map_apply (p := p) (starRingEnd ℂ) (v : ℂ))

theorem sharpPolynomial_eval_real (p : Polynomial ℂ) (v : ℝ) :
    (sharpPolynomial p).eval (v : ℂ) = star (p.eval ((-v : ℝ) : ℂ)) := by
  simp only [sharpPolynomial, eval_comp, eval_mul, eval_C, eval_X]
  simpa using conjugatePolynomial_eval_real p (-v)

theorem hermitianPolynomial_eval (M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (v : ℝ) (i j : Fin 2) :
    (hermitianPolynomial M s T i j).eval (v : ℂ) =
      forwardFormEntry M s (fun a b => (T a b).eval (v : ℂ)) i j := by
  simp only [hermitianPolynomial, eval_add, eval_mul, eval_sub, eval_C,
    conjugatePolynomial_eval_real, forwardFormEntry]

theorem forwardFormEntry_conjugate (M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    star (forwardFormEntry M s T i j) =
      forwardFormEntry M (star s) (fun a b => star (T a b)) i j := by
  simp only [forwardFormEntry, star_add, star_mul, star_sub,
    Complex.star_def, Complex.conj_ofReal]
  ring

/-- Reflection of the polynomial is exactly the second conjugate channel. -/
theorem reflectedHermitianPolynomial_eval (M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (v : ℝ) (i j : Fin 2) :
    (reflectedHermitianPolynomial M s T i j).eval (v : ℂ) =
      forwardFormEntry M s (fun a b => (T a b).eval (v : ℂ)) i j +
      forwardFormEntry M (star s) (fun a b => star ((T a b).eval ((-v : ℝ) : ℂ))) i j := by
  rw [reflectedHermitianPolynomial, eval_add, sharpPolynomial_eval_real,
    hermitianPolynomial_eval, hermitianPolynomial_eval]
  exact congrArg (fun z => forwardFormEntry M s (fun a b => (T a b).eval (v : ℂ)) i j + z)
    (forwardFormEntry_conjugate M s (fun a b => (T a b).eval ((-v : ℝ) : ℂ)) i j)

theorem reflectedHermitianPolynomial_eval_diagonal (M : ℝ) (s : ℂ)
    (T : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (hs : s.re = 0) (v : ℝ) (i : Fin 2) :
    (reflectedHermitianPolynomial M s T i i).eval (v : ℂ) =
      (((reflectedHermitianPolynomial M s T i i).eval (v : ℂ)).re : ℂ) := by
  have h := congrArg (fun p : Polynomial ℂ => p.eval (v : ℂ))
    (reflectedHermitian_conjugate_transpose M s T hs i i)
  rw [conjugatePolynomial_eval_real] at h
  have hi := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at hi
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]
    linarith

end DefocusingNLS

end OAI
