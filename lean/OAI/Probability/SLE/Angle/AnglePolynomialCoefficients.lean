import OAI.Probability.SLE.Angle.AnglePolynomialGenerator

namespace OAI

/-! The exact triangular coefficient relation for the cosine generator.
This is the recurrence used to construct its polynomial eigenfunctions. -/
noncomputable section
open Polynomial

namespace SLEExactGauge

lemma anglePolynomialGenerator_coeff (κ : ℝ) (p : ℝ[X]) (n : ℕ) :
    (anglePolynomialGenerator κ p).coeff n =
      (κ/8)*((n:ℝ)+2)*((n:ℝ)+1)*p.coeff (n+2) -
        anglePolynomialEigenvalue κ n*p.coeff n := by
  have he : anglePolynomialGenerator κ p =
      C (κ/8)*p.derivative.derivative - C (κ/8)*(p.derivative.derivative*X^2) -
        C (1+κ/8)*(p.derivative*X) := by
    unfold anglePolynomialGenerator
    ring
  rw [he]
  simp only [coeff_sub,coeff_C_mul]
  rcases n with _ | (_ | n)
  · simp [coeff_derivative,anglePolynomialEigenvalue]
    ring
  · simp [coeff_derivative,coeff_mul_X_pow',anglePolynomialEigenvalue]
    ring
  · simp [coeff_derivative,coeff_mul_X_pow',anglePolynomialEigenvalue,
      show n+1+1-2=n by omega]
    ring

lemma anglePolynomial_eigen_iff_coeff (κ : ℝ) (p : ℝ[X]) (N : ℕ) :
    anglePolynomialGenerator κ p = -C (anglePolynomialEigenvalue κ N)*p ↔
      ∀ n : ℕ, (κ/8)*((n:ℝ)+2)*((n:ℝ)+1)*p.coeff (n+2) =
        (anglePolynomialEigenvalue κ n-anglePolynomialEigenvalue κ N)*p.coeff n := by
  constructor
  · intro h n
    have he := congrArg (fun q : ℝ[X] => q.coeff n) h
    rw [anglePolynomialGenerator_coeff] at he
    simp only [neg_mul,coeff_neg,coeff_C_mul] at he
    linarith
  · intro h
    ext n
    rw [anglePolynomialGenerator_coeff]
    simp only [neg_mul,coeff_neg,coeff_C_mul]
    linarith [h n]

end SLEExactGauge

end

end OAI
