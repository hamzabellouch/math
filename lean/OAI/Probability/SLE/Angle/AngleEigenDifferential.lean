import OAI.Probability.SLE.Angle.AngleEigenBounds

namespace OAI

/-! The polynomial eigenfunctions satisfy the actual centered angular
generator equation, with time measured by logarithmic conformal radius. -/
noncomputable section
open Polynomial

namespace SLEExactGauge

def anglePolynomialTest (p : ℝ[X]) (θ : ℝ) : ℝ := p.eval (Real.cos θ)

lemma anglePolynomialTest_hasDerivAt (p : ℝ[X]) (θ : ℝ) :
    HasDerivAt (anglePolynomialTest p)
      (-Real.sin θ*p.derivative.eval (Real.cos θ)) θ := by
  change HasDerivAt (fun x => p.eval (Real.cos x)) _ θ
  apply ((p.hasDerivAt (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ)).congr_deriv
  ring

lemma anglePolynomialTest_deriv (p : ℝ[X]) :
    deriv (anglePolynomialTest p)=fun θ => -Real.sin θ*p.derivative.eval (Real.cos θ) := by
  funext θ
  exact (anglePolynomialTest_hasDerivAt p θ).deriv

lemma anglePolynomialTest_second (p : ℝ[X]) (θ : ℝ) :
    deriv (deriv (anglePolynomialTest p)) θ =
      Real.sin θ^2*p.derivative.derivative.eval (Real.cos θ)-
        Real.cos θ*p.derivative.eval (Real.cos θ) := by
  rw [anglePolynomialTest_deriv]
  have hh := (Real.hasDerivAt_sin θ).neg.mul
    ((p.derivative.hasDerivAt (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ))
  change HasDerivAt (fun x => -Real.sin x*p.derivative.eval (Real.cos x))
    (-Real.cos θ*p.derivative.eval (Real.cos θ) +
      (-Real.sin θ)*(p.derivative.derivative.eval (Real.cos θ)*(-Real.sin θ))) θ at hh
  rw [hh.deriv]
  ring

lemma anglePolynomialTest_generator (κ : ℝ) (p : ℝ[X]) {θ : ℝ}
    (hθ : Real.sin θ≠0) :
    (κ/8)*deriv (deriv (anglePolynomialTest p)) θ +
      (Real.cos θ/Real.sin θ)*deriv (anglePolynomialTest p) θ =
        (anglePolynomialGenerator κ p).eval (Real.cos θ) := by
  rw [anglePolynomialTest_second,anglePolynomialTest_deriv]
  simp only [anglePolynomialGenerator,eval_sub,eval_mul,eval_C,eval_one,eval_pow,eval_X]
  have hsin : Real.sin θ^2=1-Real.cos θ^2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hsin]
  field_simp
  ring

lemma angleEigenPolynomial_differential {κ : ℝ} (hκ : 0<κ) (N : ℕ) {θ : ℝ}
    (hθ : Real.sin θ≠0) :
    (κ/8)*deriv (deriv (anglePolynomialTest (angleEigenPolynomial κ N))) θ +
      (Real.cos θ/Real.sin θ)*deriv (anglePolynomialTest (angleEigenPolynomial κ N)) θ =
      -anglePolynomialEigenvalue κ N*anglePolynomialTest (angleEigenPolynomial κ N) θ := by
  rw [anglePolynomialTest_generator κ _ hθ,angleEigenPolynomial_eigen hκ]
  simp [anglePolynomialTest]

end SLEExactGauge

end

end OAI
