import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialParameter

namespace OAI

/-! Mixed derivatives of the finite outgoing expansion commute by the finite
coefficient formula, before adding the weighted correction. -/

open Polynomial
namespace DefocusingNLS

theorem circularPolynomialJet_time_hasDerivAt (P Q : ℂ[X]) (t : ℝ) :
    HasDerivAt (circularPolynomialJet (P, Q))
      (circularPolynomialJet (radialPolynomialEuler P, radialPolynomialEuler Q) t) t :=
  ((radialExteriorPolynomialFunction_hasDerivAt P t).prodMk
    (radialExteriorPolynomialFunction_hasDerivAt (radialPolynomialEuler P) t)).prodMk
    ((radialExteriorPolynomialFunction_hasDerivAt Q t).prodMk
      (radialExteriorPolynomialFunction_hasDerivAt (radialPolynomialEuler Q) t))

theorem circularPolynomialJet_mixed_hasDerivAt (P Q : ℂ → ℂ[X]) (d : ℕ) (z : ℂ)
    (hPd : ∀ lam, (P lam).natDegree ≤ d) (hQd : ∀ lam, (Q lam).natDegree ≤ d)
    (hP : ∀ k, AnalyticAt ℂ (fun lam => (P lam).coeff k) z)
    (hQ : ∀ k, AnalyticAt ℂ (fun lam => (Q lam).coeff k) z) (t : ℝ) :
    HasDerivAt (fun s => deriv (fun lam => circularPolynomialJet (P lam, Q lam) s) z)
      (deriv (fun lam => circularPolynomialJet
        (radialPolynomialEuler (P lam), radialPolynomialEuler (Q lam)) t) z) t := by
  have hEd (A : ℂ[X]) (hA : A.natDegree ≤ d) : (radialPolynomialEuler A).natDegree ≤ d := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [radialPolynomialEuler_coeff, coeff_eq_zero_of_natDegree_lt (hA.trans_lt hk), mul_zero]
  have hPe (k : ℕ) : AnalyticAt ℂ (fun lam => (radialPolynomialEuler (P lam)).coeff k) z := by
    simp only [radialPolynomialEuler_coeff]
    exact analyticAt_const.mul (hP k)
  have hQe (k : ℕ) : AnalyticAt ℂ (fun lam => (radialPolynomialEuler (Q lam)).coeff k) z := by
    simp only [radialPolynomialEuler_coeff]
    exact analyticAt_const.mul (hQ k)
  have hfun : (fun s => deriv (fun lam => circularPolynomialJet (P lam, Q lam) s) z) =
      circularPolynomialJet (polynomialParameterDerivative P d z, polynomialParameterDerivative Q d z) := by
    funext s
    exact (circularPolynomialJet_hasParameterDerivAt P Q d z hPd hQd hP hQ s).deriv
  rw [hfun, (circularPolynomialJet_hasParameterDerivAt
    (fun lam => radialPolynomialEuler (P lam)) (fun lam => radialPolynomialEuler (Q lam))
    d z (fun lam => hEd _ (hPd lam)) (fun lam => hEd _ (hQd lam)) hPe hQe t).deriv,
    polynomialParameterDerivative_euler P d z hP, polynomialParameterDerivative_euler Q d z hQ]
  exact circularPolynomialJet_time_hasDerivAt _ _ t

end DefocusingNLS

end OAI
