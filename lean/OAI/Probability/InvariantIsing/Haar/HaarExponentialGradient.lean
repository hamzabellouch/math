import OAI.Probability.InvariantIsing.Haar.HaarExponentialPolynomial
import OAI.Probability.InvariantIsing.Haar.PositiveExponentialSum

namespace OAI

/-! Uniform logarithmic-gradient bounds for positive exponential truncations. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

lemma haarExpPolynomial_gamma {N : ℕ} (n : ℕ) (p : MatrixPolynomial N) :
    haarPolynomialGamma (haarExpPolynomial (n+1) p) (haarExpPolynomial (n+1) p) =
      (haarExpPolynomial n p)^2*haarPolynomialGamma p p := by
  simp only [haarPolynomialGamma,haarExpPolynomial_derivation,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma haarExpPolynomial_positive {N : ℕ} (n : ℕ) (p : MatrixPolynomial N)
    (M : Matrix (Fin N) (Fin N) ℝ) (hp : 0 ≤ matrixPolynomialEval M p) :
    1 ≤ matrixPolynomialEval M (haarExpPolynomial n p) := by
  rw [haarExpPolynomial_eval]
  exact positiveExpSum_one_le n hp

lemma haarExpPolynomial_log_gradient_bound {N : ℕ} (n : ℕ) (p : MatrixPolynomial N)
    (M : Matrix (Fin N) (Fin N) ℝ) (hp : 0 ≤ matrixPolynomialEval M p)
    (C : ℝ) (hC : 0 ≤ C) (hG : matrixPolynomialEval M (haarPolynomialGamma p p) ≤ C) :
    matrixPolynomialEval M (haarPolynomialGamma (haarExpPolynomial (n+1) p) (haarExpPolynomial (n+1) p)) ≤
      C*(matrixPolynomialEval M (haarExpPolynomial (n+1) p))^2 := by
  have h0 := haarExpPolynomial_positive n p M hp
  have h1 := haarExpPolynomial_positive (n+1) p M hp
  have hm : matrixPolynomialEval M (haarExpPolynomial n p) ≤
      matrixPolynomialEval M (haarExpPolynomial (n+1) p) := by
    simp only [haarExpPolynomial_eval]
    exact positiveExpSum_mono n hp
  rw [haarExpPolynomial_gamma,map_mul,map_pow]
  calc
    _ ≤ (matrixPolynomialEval M (haarExpPolynomial n p))^2*C :=
      mul_le_mul_of_nonneg_left hG (sq_nonneg _)
    _ ≤ C*(matrixPolynomialEval M (haarExpPolynomial (n+1) p))^2 := by
      rw [mul_comm _ C]
      exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (by linarith) (by linarith)).mpr hm) hC

end InvariantIsing

end

end OAI
