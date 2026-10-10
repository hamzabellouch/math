import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralBoundedPolynomialAnalytic

namespace OAI

/-! Coefficientwise parameter derivatives of the finite outgoing expansions. -/

open Polynomial
namespace DefocusingNLS

noncomputable def polynomialParameterDerivative (P : ℂ → ℂ[X]) (d : ℕ) (z : ℂ) : ℂ[X] :=
  ∑ k ∈ Finset.range (d + 1), monomial k (deriv (fun lam => (P lam).coeff k) z)

theorem polynomialParameterDerivative_coeff (P : ℂ → ℂ[X]) (d : ℕ) (z : ℂ) (k : ℕ) :
    (polynomialParameterDerivative P d z).coeff k =
      if k < d + 1 then deriv (fun lam => (P lam).coeff k) z else 0 := by
  simp [polynomialParameterDerivative, Polynomial.coeff_monomial,
    Finset.sum_ite_eq', Finset.mem_range]

theorem polynomial_eval_hasParameterDerivAt (P : ℂ → ℂ[X]) (d : ℕ) (z x : ℂ)
    (hd : ∀ lam, (P lam).natDegree ≤ d)
    (hP : ∀ k, AnalyticAt ℂ (fun lam => (P lam).coeff k) z) :
    HasDerivAt (fun lam => (P lam).eval x) (polynomialParameterDerivative P d z |>.eval x) z := by
  have he : (fun lam => (P lam).eval x) =
      fun lam => ∑ k ∈ Finset.range (d + 1), (P lam).coeff k * x ^ k := by
    funext lam
    exact Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hd lam)) x
  rw [he]
  have hh := HasDerivAt.fun_sum (u := Finset.range (d + 1))
    (fun k _ => (hP k).differentiableAt.hasDerivAt.mul_const (x ^ k))
  convert! hh using 1
  simp only [polynomialParameterDerivative, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem polynomialParameterDerivative_euler (P : ℂ → ℂ[X]) (d : ℕ) (z : ℂ)
    (hP : ∀ k, AnalyticAt ℂ (fun lam => (P lam).coeff k) z) :
    polynomialParameterDerivative (fun lam => radialPolynomialEuler (P lam)) d z =
      radialPolynomialEuler (polynomialParameterDerivative P d z) := by
  ext k
  rw [polynomialParameterDerivative_coeff, radialPolynomialEuler_coeff,
    polynomialParameterDerivative_coeff]
  by_cases hk : k < d + 1
  · simp only [hk, ite_true]
    simp_rw [radialPolynomialEuler_coeff]
    exact ((hP k).differentiableAt.hasDerivAt.const_mul _).deriv
  · simp only [hk, ite_false, mul_zero]

theorem circularPolynomialJet_hasParameterDerivAt (P Q : ℂ → ℂ[X]) (d : ℕ) (z : ℂ)
    (hPd : ∀ lam, (P lam).natDegree ≤ d) (hQd : ∀ lam, (Q lam).natDegree ≤ d)
    (hP : ∀ k, AnalyticAt ℂ (fun lam => (P lam).coeff k) z)
    (hQ : ∀ k, AnalyticAt ℂ (fun lam => (Q lam).coeff k) z) (t : ℝ) :
    HasDerivAt (fun lam => circularPolynomialJet (P lam, Q lam) t)
      (circularPolynomialJet (polynomialParameterDerivative P d z,
        polynomialParameterDerivative Q d z) t) z := by
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
  have hp := polynomial_eval_hasParameterDerivAt P d z (Real.exp (-2 * t)) hPd hP
  have hq := polynomial_eval_hasParameterDerivAt Q d z (Real.exp (-2 * t)) hQd hQ
  have hpe := polynomial_eval_hasParameterDerivAt (fun lam => radialPolynomialEuler (P lam))
    d z (Real.exp (-2 * t)) (fun lam => hEd _ (hPd lam)) hPe
  have hqe := polynomial_eval_hasParameterDerivAt (fun lam => radialPolynomialEuler (Q lam))
    d z (Real.exp (-2 * t)) (fun lam => hEd _ (hQd lam)) hQe
  rw [polynomialParameterDerivative_euler P d z hP] at hpe
  rw [polynomialParameterDerivative_euler Q d z hQ] at hqe
  exact (hp.prodMk hpe).prodMk (hq.prodMk hqe)

end DefocusingNLS

end OAI
