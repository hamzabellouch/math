import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialExpansion
import Mathlib.Analysis.Analytic.Constructions

namespace OAI

/-! Holomorphic coefficients of the finite slow-column expansions. -/

open Polynomial
namespace DefocusingNLS

theorem polynomial_mul_coeff_analytic (A : ℂ[X]) (U : ℂ → ℂ[X]) (z : ℂ)
    (hU : ∀ k, AnalyticAt ℂ (fun lam => (U lam).coeff k) z) (k : ℕ) :
    AnalyticAt ℂ (fun lam => (A*U lam).coeff k) z := by
  simp_rw [Polynomial.coeff_mul]
  exact (Finset.antidiagonal k).analyticAt_fun_sum (fun i _ => analyticAt_const.mul (hU i.2))

theorem spectralPolynomialResidual_coeff_analytic (h η : ℂ) (ν : ℂ → ℂ)
    (A B : ℂ[X]) (U V : ℂ → ℂ[X]) (z : ℂ) (hν : AnalyticAt ℂ ν z)
    (hU : ∀ k, AnalyticAt ℂ (fun lam => (U lam).coeff k) z)
    (hV : ∀ k, AnalyticAt ℂ (fun lam => (V lam).coeff k) z) (k : ℕ) :
    AnalyticAt ℂ (fun lam => (spectralPolynomialResidual h (ν lam) η A B (U lam) (V lam)).coeff k) z := by
  simp only [spectralPolynomialResidual,coeff_sub,coeff_add,coeff_C_mul,
    radialPolynomialEuler_coeff,coeff_derivative]
  exact (((((analyticAt_const.mul (analyticAt_const.mul (hU k))).add
    (((analyticAt_const.mul hν).add analyticAt_const).mul (analyticAt_const.mul (hU k)))).add
    ((hν.mul (hν.add analyticAt_const) |>.sub analyticAt_const).mul (hU k))).sub
    (analyticAt_const.mul ((hU (k+1)).mul analyticAt_const))).sub
    (polynomial_mul_coeff_analytic A U z hU k)).sub
    (polynomial_mul_coeff_analytic B V z hV k)

theorem spectralOutgoingPolynomial_coeff_analytic (νp νm : ℂ → ℂ) (η : ℂ)
    (m : ℕ) (P : ℂ[X]) (c : ℂ × ℂ) (z : ℂ)
    (hp : AnalyticAt ℂ νp z) (hm : AnalyticAt ℂ νm z) (j k : ℕ) :
    AnalyticAt ℂ (fun lam => (spectralOutgoingPolynomial (νp lam) (νm lam) η m P c j).1.coeff k) z ∧
    AnalyticAt ℂ (fun lam => (spectralOutgoingPolynomial (νp lam) (νm lam) η m P c j).2.coeff k) z := by
  induction j generalizing k with
  | zero => exact ⟨analyticAt_const,analyticAt_const⟩
  | succ j ih =>
    let Up := fun lam => (spectralOutgoingPolynomial (νp lam) (νm lam) η m P c j).1
    let Um := fun lam => (spectralOutgoingPolynomial (νp lam) (νm lam) η m P c j).2
    have hRp := spectralPolynomialResidual_coeff_analytic 1 η νp
      (spectralDiagonalPolynomial m P) (spectralCrossPolynomial m P) Up Um z hp
      (fun k => (ih k).1) (fun k => (ih k).2) j
    have hRm := spectralPolynomialResidual_coeff_analytic (-1) η νm
      (Polynomial.mapRingHom (starRingEnd ℂ) (spectralDiagonalPolynomial m P))
      (Polynomial.mapRingHom (starRingEnd ℂ) (spectralCrossPolynomial m P)) Um Up z hm
      (fun k => (ih k).2) (fun k => (ih k).1) j
    constructor
    · change AnalyticAt ℂ (fun lam => (Up lam).coeff k+
        (monomial (j+1) ((spectralPolynomialResidualPair (νp lam) (νm lam) η m P
          (Up lam,Um lam)).1.coeff j/(Complex.I*(j+1 : ℕ)))).coeff k) z
      simp only [coeff_monomial]
      by_cases he : j+1=k
      · simp only [he,ite_true]
        exact (ih k).1.add hRp.div_const
      · simp only [he,ite_false,add_zero]
        exact (ih k).1
    · change AnalyticAt ℂ (fun lam => (Um lam).coeff k+
        (monomial (j+1) ((spectralPolynomialResidualPair (νp lam) (νm lam) η m P
          (Up lam,Um lam)).2.coeff j/(-Complex.I*(j+1 : ℕ)))).coeff k) z
      simp only [coeff_monomial]
      by_cases he : j+1=k
      · simp only [he,ite_true]
        exact (ih k).2.add hRm.div_const
      · simp only [he,ite_false,add_zero]
        exact (ih k).2

end DefocusingNLS

end OAI
