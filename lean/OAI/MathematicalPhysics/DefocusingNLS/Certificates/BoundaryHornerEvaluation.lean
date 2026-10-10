import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryEvenCoefficients
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryPositiveEvaluation

namespace OAI

/-! # Degree and rational-substitution identity for the chart transform -/

open Polynomial

namespace DefocusingNLS.BoundaryCertificate

noncomputable def coefficientPolynomial : List ℂ → Polynomial ℂ
  | [] => 0
  | a :: as => C a + X * coefficientPolynomial as

theorem chartNumerator_degree (U V : ℤ) : (chartNumerator U V).natDegree ≤ 1 := by
  apply natDegree_add_le_of_degree_le
  · simp
  · exact natDegree_mul_le.trans (by simp)

theorem chartDenominator_degree (J : ℤ) : (chartDenominator J).natDegree ≤ 1 := by
  apply natDegree_add_le_of_degree_le
  · simp
  · exact natDegree_mul_le.trans (by simp)

theorem homogeneousHorner_cons_degree (U V J : ℤ) (a : ℂ) (as : List ℂ) :
    (homogeneousHorner U V J (a :: as)).natDegree ≤ as.length := by
  induction as generalizing a with
  | nil => simp [homogeneousHorner]
  | cons b as ih =>
    change (C a * chartDenominator J ^ (b :: as).length +
      chartNumerator U V * homogeneousHorner U V J (b :: as)).natDegree ≤ (b :: as).length
    apply natDegree_add_le_of_degree_le
    · exact (natDegree_C_mul_le _ _).trans
        ((natDegree_pow_le_of_le _ (chartDenominator_degree J)).trans (by simp))
    · exact natDegree_mul_le.trans ((add_le_add (chartNumerator_degree U V) (ih b)).trans (by simp; omega))

theorem homogeneousHorner_degree (U V J : ℤ) (as : List ℂ) :
    (homogeneousHorner U V J as).natDegree ≤ as.length - 1 := by
  cases as with
  | nil => simp [homogeneousHorner]
  | cons a as => simpa using homogeneousHorner_cons_degree U V J a as

theorem homogeneousHorner_eval (U V J : ℤ) (as : List ℂ) (x : ℂ)
    (hd : (chartDenominator J).eval x ≠ 0) :
    (homogeneousHorner U V J as).eval x =
      (chartDenominator J).eval x ^ (as.length - 1) *
        (coefficientPolynomial as).eval ((chartNumerator U V).eval x / (chartDenominator J).eval x) := by
  induction as with
  | nil => simp [homogeneousHorner, coefficientPolynomial]
  | cons a as ih =>
    cases as with
    | nil => simp [homogeneousHorner, coefficientPolynomial]
    | cons b as =>
      conv_lhs => rw [homogeneousHorner]
      simp only [eval_add, eval_mul, eval_C, eval_pow, List.length_cons]
      rw [ih]
      simp only [coefficientPolynomial, eval_add, eval_C, eval_mul, eval_X,
        List.length_cons, Nat.add_sub_cancel]
      field_simp [hd]
      ring

attribute [local irreducible] GaussianEnclosure.EnclosesPolynomial
  homogeneousHorner evenValues transformed

/-- Each of the three exact certificate charts is strictly positive on its
nonnegative parameter half-line, throughout the actual parameter box. -/
theorem homogeneousHorner_positive (ell : Fin 4) (b Z w : ℝ)
    (hb : |100000000 * b - 33477607| ≤ 2) (hZ : |100000000 * Z - 270506819| ≤ 2)
    (hw : 0 ≤ w) (U V J : ℤ)
    (hcert : positiveFirst16 (transformed ell U V J) = true) :
    0 < ((homogeneousHorner U V J (evenValues ell b Z)).eval (w : ℂ)).re := by
  apply positive_eval_of_positiveFirst16 _ _ hcert (transformed_sound ell b Z hb hZ U V J)
  · have hd := homogeneousHorner_degree U V J (evenValues ell b Z)
    simpa [evenValues] using hd
  · exact hw

end DefocusingNLS.BoundaryCertificate

end OAI
