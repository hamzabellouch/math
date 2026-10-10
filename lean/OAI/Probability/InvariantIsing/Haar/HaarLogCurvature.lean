import OAI.Probability.InvariantIsing.Haar.HaarHessianExpansion
import OAI.Probability.InvariantIsing.Haar.HaarGammaCalculus

namespace OAI

/-! The pointwise curvature inequality with a logarithmic gradient correction. -/
noncomputable section
open Matrix MvPolynomial
open scoped BigOperators
namespace InvariantIsing

def haarGradientValue {N : ℕ} (p : MatrixPolynomial N)
    (M : Matrix (Fin N) (Fin N) ℝ) (a : Fin N × Fin N) : ℝ :=
  matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator a.1 a.2) p)

def haarHessianValue {N : ℕ} (p : MatrixPolynomial N)
    (M : Matrix (Fin N) (Fin N) ℝ) (a b : Fin N × Fin N) : ℝ :=
  matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator b.1 b.2)
    (matrixPolynomialDerivation (planeGenerator a.1 a.2) p))

lemma haarGradientValue_sq_sum {N : ℕ} (p : MatrixPolynomial N)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    (∑ a, (haarGradientValue p M a)^2) = matrixPolynomialEval M (haarPolynomialGamma p p) := by
  simp only [Fintype.sum_prod_type,haarGradientValue,haarPolynomialGamma,map_sum,map_mul,pow_two]

lemma haarGammaGammaValue {N : ℕ} (p : MatrixPolynomial N)
    (M : Matrix (Fin N) (Fin N) ℝ) :
    matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialGamma p p)) =
      2*(∑ a, ∑ b, haarHessianValue p M a b*haarGradientValue p M a*haarGradientValue p M b) := by
  have hd (a : Fin N × Fin N) : matrixPolynomialEval M
      (matrixPolynomialDerivation (planeGenerator a.1 a.2) (haarPolynomialGamma p p)) =
      2*(∑ b, haarGradientValue p M b*haarHessianValue p M b a) := by
    rw [haarPolynomialDerivation_gamma_sq]
    simp only [map_sum,map_mul,map_ofNat,Fintype.sum_prod_type,Finset.mul_sum,
      haarGradientValue,haarHessianValue]
  have hex : matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialGamma p p)) =
      ∑ a : Fin N × Fin N, haarGradientValue p M a*
        matrixPolynomialEval M (matrixPolynomialDerivation (planeGenerator a.1 a.2)
          (haarPolynomialGamma p p)) := by
    simp only [haarPolynomialGamma,map_sum,map_mul,Fintype.sum_prod_type,haarGradientValue]
  rw [hex]
  simp_rw [hd]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma haarLogCurvature {N : ℕ} (p : MatrixPolynomial N)
    (M : Matrix (Fin N) (Fin N) ℝ) (c : ℝ) :
    ((N:ℝ)-2)*matrixPolynomialEval M (haarPolynomialGamma p p) ≤
      matrixPolynomialEval M (haarPolynomialLaplacian N (haarPolynomialGamma p p))/2-
      matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialLaplacian N p))-
      c*matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialGamma p p))+
      c^2*(matrixPolynomialEval M (haarPolynomialGamma p p))^2 := by
  have hc := matrixPolynomial_corrected_hessian_bound p M c
  have he := congrArg (matrixPolynomialEval M) (haarPolynomial_bochner_identity p)
  simp only [map_mul,map_ofNat,map_add,map_sum,map_pow] at he
  have hc' : ((N:ℝ)-2)*matrixPolynomialEval M (haarPolynomialGamma p p) ≤
    ∑ a : Fin N × Fin N, ∑ b : Fin N × Fin N,
      (haarHessianValue p M a b-c*haarGradientValue p M a*haarGradientValue p M b)^2 := by
    simpa only [Fintype.sum_prod_type,haarHessianValue,haarGradientValue] using hc
  rw [sum_corrected_hessian_sq,haarGradientValue_sq_sum] at hc'
  rw [haarGammaGammaValue]
  have he' : matrixPolynomialEval M (haarPolynomialLaplacian N (haarPolynomialGamma p p)) =
    2*(matrixPolynomialEval M (haarPolynomialGamma p (haarPolynomialLaplacian N p))+
      ∑ a : Fin N × Fin N, ∑ b : Fin N × Fin N, (haarHessianValue p M a b)^2) := by
    simpa only [Fintype.sum_prod_type,haarHessianValue] using he
  linarith

end InvariantIsing

end

end OAI
