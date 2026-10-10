import OAI.NumberTheory.Ostmann.ZeroDensity.DensityAbscissaSample
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityVerticalPolynomial
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityGaussianFubini

namespace OAI

/-! # Differentiating the actual Dirichlet polynomial in its real part -/

namespace Ostmann

open Complex
open scoped BigOperators

noncomputable def densityAbscissaDerivativeCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  -(Real.log n : ℂ) * a n

 theorem densityVerticalCoeff_exp (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) (hn : 0 < n) :
    densityVerticalCoeff a σ n = a n * Complex.exp (-(Real.log n : ℂ) * (σ : ℂ)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hl : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.ofReal_log (show (0 : ℝ) ≤ n by positivity)).symm
  rw [densityVerticalCoeff, Complex.cpow_def_of_ne_zero hnC, hl, div_eq_mul_inv, ← Complex.exp_neg]
  congr 2
  ring

 theorem densityVerticalCoeff_hasDerivAt (a : ℕ → ℂ) (n : ℕ) (hn : 0 < n) (σ : ℝ) :
    HasDerivAt (fun x : ℝ => densityVerticalCoeff a x n)
      (densityVerticalCoeff (densityAbscissaDerivativeCoeff a) σ n) σ := by
  have hd := ((((hasDerivAt_id σ).ofReal_comp).const_mul (-(Real.log n : ℂ))).cexp).const_mul (a n)
  simp only [id_eq, Complex.ofReal_one, mul_one] at hd
  convert hd using 1
  · funext x
    exact densityVerticalCoeff_exp a x n hn
  · rw [densityVerticalCoeff_exp _ σ n hn]
    unfold densityAbscissaDerivativeCoeff
    ring

 theorem density_abscissa_polynomial_hasDerivAt {q : ℕ} (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (t σ : ℝ) :
    HasDerivAt (fun x => densityCharacterPolynomial S (densityVerticalCoeff a x) χ t)
      (densityCharacterPolynomial S (densityVerticalCoeff (densityAbscissaDerivativeCoeff a) σ) χ t) σ := by
  unfold densityCharacterPolynomial
  exact HasDerivAt.fun_sum (fun n hn =>
    ((densityVerticalCoeff_hasDerivAt a n (hS n hn) σ).mul_const (χ (n : ZMod q))).mul_const
      (realAdditivePhase (-(Real.log n * t))))

 theorem density_abscissa_polynomial_continuous {q : ℕ} (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (t : ℝ) :
    Continuous (fun x => densityCharacterPolynomial S (densityVerticalCoeff a x) χ t) :=
  continuous_iff_continuousAt.mpr (fun x =>
    (density_abscissa_polynomial_hasDerivAt S hS a χ t x).continuousAt)

 theorem density_abscissa_polynomial_sample {q : ℕ} (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n) (a : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (t σ β : ℝ)
    (hσβ : σ ≤ β) (hβ : β ≤ 1) :
    ‖densityCharacterPolynomial S (densityVerticalCoeff a β) χ t‖ ^ 2 ≤
      2 * (∫ x in σ..2, ‖densityCharacterPolynomial S (densityVerticalCoeff a x) χ t‖ ^ 2) +
        ∫ x in σ..2, ‖densityCharacterPolynomial S
          (densityVerticalCoeff (densityAbscissaDerivativeCoeff a) x) χ t‖ ^ 2 := by
  exact density_abscissa_sample _ _
    (density_abscissa_polynomial_hasDerivAt S hS a χ t)
    (density_abscissa_polynomial_continuous S hS (densityAbscissaDerivativeCoeff a) χ t)
    σ β hσβ hβ

end Ostmann

end OAI
