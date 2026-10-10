import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.SchwartzJetCoordinates
import OAI.Analysis.RieszRectifiability.Rigidity.FourierJetMoments

namespace OAI

/-!
# Polynomial pairings for Fourier jets

A finite family of jet coefficients defines a multivariable moment polynomial.
Its pairing with a Schwartz function is integrable and equals the corresponding
linear combination of Fourier derivatives at zero.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap
open scoped FourierTransform

def jetMomentPolynomial {d N : ℕ} (c : JetCoordinateIndex d N → ℂ) :
    MvPolynomial (Fin d) ℂ :=
  ∑ i, MvPolynomial.C (c i * fourierDerivativeFactor ^ i.1.val) *
    ∏ j, MvPolynomial.X (i.2 j)

theorem jetMomentPolynomial_eval {d N : ℕ} (c : JetCoordinateIndex d N → ℂ)
    (x : Ambient d) :
    MvPolynomial.eval (fun j => (x j : ℂ)) (jetMomentPolynomial c) =
      ∑ i, c i * fourierDerivativeFactor ^ i.1.val *
        ∏ j, (inner ℝ x (EuclideanSpace.basisFun (Fin d) ℝ (i.2 j)) : ℂ) := by
  simp only [jetMomentPolynomial, map_sum, map_mul, map_prod,
    MvPolynomial.eval_C, MvPolynomial.eval_X, EuclideanSpace.inner_basisFun_real]

theorem jetMomentPolynomial_test_integrable {d N : ℕ}
    (c : JetCoordinateIndex d N → ℂ) (g : 𝓢(Ambient d, ℂ)) :
    Integrable (fun x => MvPolynomial.eval (fun j => (x j : ℂ))
      (jetMomentPolynomial c) * g x) := by
  have hi : ∀ i : JetCoordinateIndex d N, Integrable
      (fun x => c i * (fourierDerivativeFactor ^ i.1.val *
        (∏ j, (inner ℝ x (EuclideanSpace.basisFun (Fin d) ℝ (i.2 j)) : ℂ)) * g x)) :=
    fun i => (fourier_jet_moment_integrable
      (fun j => EuclideanSpace.basisFun (Fin d) ℝ (i.2 j)) g).const_mul (c i)
  convert! integrable_finsetSum Finset.univ (fun i _ => hi i) using 1
  ext x
  rw [jetMomentPolynomial_eval, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem fourier_jet_sum_eq_polynomial_pairing {d N : ℕ}
    (c : JetCoordinateIndex d N → ℂ) (g : 𝓢(Ambient d, ℂ)) :
    (∑ i, c i * iteratedFDeriv ℝ i.1.val (𝓕 g : 𝓢(Ambient d, ℂ)) 0
      (fun j => EuclideanSpace.basisFun (Fin d) ℝ (i.2 j))) =
      ∫ x, MvPolynomial.eval (fun j => (x j : ℂ)) (jetMomentPolynomial c) * g x := by
  have hi : ∀ i : JetCoordinateIndex d N, Integrable
      (fun x => c i * (fourierDerivativeFactor ^ i.1.val *
        (∏ j, (inner ℝ x (EuclideanSpace.basisFun (Fin d) ℝ (i.2 j)) : ℂ)) * g x)) :=
    fun i => (fourier_jet_moment_integrable
      (fun j => EuclideanSpace.basisFun (Fin d) ℝ (i.2 j)) g).const_mul (c i)
  calc
    _ = ∑ i, ∫ x, c i * (fourierDerivativeFactor ^ i.1.val *
        (∏ j, (inner ℝ x (EuclideanSpace.basisFun (Fin d) ℝ (i.2 j)) : ℂ)) * g x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [fourier_jet_at_zero_eq_moment]
      erw [integral_const_mul]
    _ = ∫ x, ∑ i, c i * (fourierDerivativeFactor ^ i.1.val *
        (∏ j, (inner ℝ x (EuclideanSpace.basisFun (Fin d) ℝ (i.2 j)) : ℂ)) * g x) :=
      (integral_finsetSum _ (fun i _ => hi i)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [jetMomentPolynomial_eval, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

end

end RieszRectifiability

end OAI
