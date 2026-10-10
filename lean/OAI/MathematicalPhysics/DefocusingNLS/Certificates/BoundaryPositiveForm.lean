import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryFormEvaluation

namespace OAI

/-! # The certified boundary matrix is positive definite -/

open Polynomial Matrix

namespace DefocusingNLS.BoundaryCertificate

attribute [local irreducible] polynomialState state

noncomputable def rawBoundaryEntry (ell : ℕ) (b Z v : ℝ) (i j : Fin 2) : ℂ :=
  (reflectedHermitianPolynomial (scaledMass ell) (scaledShift Z)
    (stateMatrix (polynomialState ell b Z 8)) i j).eval (v : ℂ)

theorem rawBoundaryEntry_diagonal (ell : ℕ) (b Z v : ℝ) (i : Fin 2) :
    rawBoundaryEntry ell b Z v i i = ((rawBoundaryEntry ell b Z v i i).re : ℂ) :=
  reflectedHermitianPolynomial_eval_diagonal _ _ _ (by simp [scaledShift]) v i

theorem rawBoundaryEntry_continuous (ell : ℕ) (b Z : ℝ) (i j : Fin 2) :
    Continuous (fun v => rawBoundaryEntry ell b Z v i j) :=
  (reflectedHermitianPolynomial (scaledMass ell) (scaledShift Z)
    (stateMatrix (polynomialState ell b Z 8)) i j).continuous.comp Complex.continuous_ofReal

theorem rawBoundaryEntry_determinant (ell : ℕ) (b Z v : ℝ) :
    ((rawDeterminant ell b Z).eval (v : ℂ)).re =
      (rawBoundaryEntry ell b Z v 0 0).re * (rawBoundaryEntry ell b Z v 1 1).re -
        Complex.normSq (rawBoundaryEntry ell b Z v 0 1) := by
  simp only [rawDeterminant, eval_sub, eval_mul, conjugatePolynomial_eval_real]
  change (rawBoundaryEntry ell b Z v 0 0 * rawBoundaryEntry ell b Z v 1 1 -
    rawBoundaryEntry ell b Z v 0 1 * star (rawBoundaryEntry ell b Z v 0 1)).re = _
  rw [rawBoundaryEntry_diagonal ell b Z v 0, rawBoundaryEntry_diagonal ell b Z v 1]
  simp [Complex.mul_re, Complex.normSq_apply]

theorem rawBoundaryEntry_leading_pos (ell : Fin 4) (b Z : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2)
    (v : ℝ) : 0 < (rawBoundaryEntry ell b Z v 0 0).re := by
  have hdet (t : ℝ) : 0 <
      (rawBoundaryEntry ell b Z t 0 0).re * (rawBoundaryEntry ell b Z t 1 1).re -
        Complex.normSq (rawBoundaryEntry ell b Z t 0 1) := by
    rw [← rawBoundaryEntry_determinant]
    exact rawDeterminant_positive ell b Z t hb hZ
  have hzero : 0 < (rawBoundaryEntry ell b Z 0 0 0).re := by
    simpa only [rawBoundaryEntry, rawFirstDiagonal, Complex.ofReal_zero] using
      rawFirstDiagonal_at_zero_pos ell b Z hb hZ
  exact positive_leading_coefficient_of_det
    (fun t => (rawBoundaryEntry ell b Z t 0 0).re)
    (fun t => (rawBoundaryEntry ell b Z t 1 1).re)
    (fun t => rawBoundaryEntry ell b Z t 0 1)
    (Complex.continuous_re.comp (rawBoundaryEntry_continuous ell b Z 0 0)) hdet 0 hzero v

/-- The finite boundary certificate yields a strictly positive quadratic form
at every real frequency, uniformly throughout the parameter box. -/
theorem rawBoundaryEntry_pairForm_pos (ell : Fin 4) (b Z v : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2)
    (u w : ℂ) (huw : u ≠ 0 ∨ w ≠ 0) :
    0 < hermitianPairForm (rawBoundaryEntry ell b Z v 0 0).re
      (rawBoundaryEntry ell b Z v 1 1).re (rawBoundaryEntry ell b Z v 0 1) u w := by
  apply hermitianPairForm_pos _ _ _ _ _ (rawBoundaryEntry_leading_pos ell b Z hb hZ v) _ huw
  rw [← rawBoundaryEntry_determinant]
  exact rawDeterminant_positive ell b Z v hb hZ

/-- A direct positivity statement for the two actual evaluated forward forms. -/
theorem evaluated_boundary_cones_pos (ell : Fin 4) (b Z v : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2)
    (w : Fin 2 → ℂ) (hw : w ≠ 0) :
    0 < matrixCone (scaledMass ell) (scaledShift Z)
      (fun i j => ((stateMatrix (polynomialState ell b Z 8)) i j).eval (v : ℂ)) w +
      matrixCone (scaledMass ell) (star (scaledShift Z))
      (fun i j => star (((stateMatrix (polynomialState ell b Z 8)) i j).eval
        ((-v : ℝ) : ℂ))) w := by
  have he (i j : Fin 2) : rawBoundaryEntry ell b Z v i j =
      forwardFormEntry (scaledMass ell) (scaledShift Z)
        (fun a c => ((stateMatrix (polynomialState ell b Z 8)) a c).eval (v : ℂ)) i j +
      forwardFormEntry (scaledMass ell) (star (scaledShift Z))
        (fun a c => star (((stateMatrix (polynomialState ell b Z 8)) a c).eval
          ((-v : ℝ) : ℂ))) i j :=
    reflectedHermitianPolynomial_eval _ _ _ v i j
  apply positive_sum_matrixCone _ _ _ _ _ (by simp [scaledShift])
    (by simp [scaledShift]) _ _ w hw
  · simpa only [he, Complex.add_re] using rawBoundaryEntry_leading_pos ell b Z hb hZ v
  · simpa only [rawBoundaryEntry_determinant, he, Complex.add_re] using
      rawDeterminant_positive ell b Z v hb hZ

end DefocusingNLS.BoundaryCertificate

end OAI
