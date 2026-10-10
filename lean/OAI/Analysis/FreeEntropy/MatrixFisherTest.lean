import OAI.Analysis.FreeEntropy.GaussianScore

namespace OAI

noncomputable section
open Finset MeasureTheory
namespace FiniteEntropySeparation
variable {n d : ℕ}
 def matrixPolynomialDerivative (p : WordPolynomial n) (i : Fin n) (a : MatrixCoordinates n d) : ℂ :=
    ∑w∈p.support,p w*∑r : Fin w.length,if w[r.val]=i then
      matrixMoment a (w.take r.val)*matrixMoment a (w.drop (r.val+1)) else 0
 def matrixFisherTest (p : WordPolynomial n) (i : Fin n) (a : MatrixCoordinates n d) : ℝ :=
    2*(matrixPolynomialDerivative p i a).re-matrixPolynomialNorm p a
 def matrixRealScore (p : WordPolynomial n) (j k : Fin d) (x : MatrixIndex n d → ℝ) : ℝ :=
    (d:ℝ)*(matrixScorePolynomial p j k x).re
 theorem matrixRealScore_polynomial (p : WordPolynomial n) (j k : Fin d) :
    IsRealPolynomial (matrixRealScore p j k) := (matrixScorePolynomial_polynomial p j k).1.const_mul d
 theorem matrixRealScore_derivative (p : WordPolynomial n) (i : Fin n) (j k : Fin d) (x : MatrixIndex n d → ℝ) :
    coordinateDerivative (matrixRealScore p j k) (i,j,k) x =
      (d:ℝ)*(complexCoordinateDerivative (matrixScorePolynomial p j k) (i,j,k) x).re := by
  have hp := (matrixScorePolynomial_polynomial p j k)
  rw [hp.coordinateDerivative_eq]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,add_zero]
  exact ((hp.1.hasDerivAt (i,j,k) x).const_mul (d:ℝ)).deriv
 theorem matrixRealScore_divergence (hd : 0<d) (p : WordPolynomial n) (i : Fin n) (x : MatrixIndex n d → ℝ) :
    (∑j,∑k,coordinateDerivative (matrixRealScore p j k) (i,j,k) x) =
      (d:ℝ)^3*(matrixPolynomialDerivative p i (WithLp.toLp 2 x)).re := by
  simp_rw [matrixRealScore_derivative]
  simp_rw [← mul_sum]
  simp_rw [← Complex.re_sum]
  rw [matrixScorePolynomial_divergence]
  have hdC : (d:ℂ)≠0 := by exact_mod_cast hd.ne'
  have he : (∑w∈p.support,p w*∑r : Fin w.length,if w[r.val]=i then
        Matrix.trace (matrixWord (coordinateMatrix x) (w.take r.val))*Matrix.trace (matrixWord (coordinateMatrix x) (w.drop (r.val+1))) else 0) =
      (d:ℂ)^2*matrixPolynomialDerivative p i (WithLp.toLp 2 x) := by
    unfold matrixPolynomialDerivative matrixMoment
    simp only [mul_sum]
    apply sum_congr rfl
    intro w _
    apply sum_congr rfl
    intro r _
    split_ifs
    · dsimp [coordinateMatrix,matrixWord]
      field_simp
      ; ring_nf ; rfl
    · ring
  rw [he]
  simp only [← Complex.ofReal_natCast,← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring
 theorem matrixFisherTest_pointwise (hd : 0<d) (p : WordPolynomial n) (i : Fin n) (a : MatrixCoordinates n d) :
    (d:ℝ)^3*matrixFisherTest p i a ≤
      ∑j,∑k,(2*coordinateDerivative (matrixRealScore p j k) (i,j,k) (WithLp.ofLp a)-matrixRealScore p j k (WithLp.ofLp a)^2) := by
  have hdiv := matrixRealScore_divergence hd p i (WithLp.ofLp a)
  have hn := matrixScorePolynomial_norm_lower p (WithLp.ofLp a)
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hn' : (∑j,∑k,matrixRealScore p j k (WithLp.ofLp a)^2) ≤ (d:ℝ)^3*matrixPolynomialNorm p a := by
    simp only [matrixRealScore,mul_pow,← mul_sum]
    rw [matrixPolynomialNorm_trace]
    have he : (d:ℝ)^3*((d:ℝ)⁻¹*(Matrix.trace ((matrixPolynomial p (hermitianMatrix a)).conjTranspose*matrixPolynomial p (hermitianMatrix a))).re) =
      (d:ℝ)^2*(Matrix.trace ((matrixPolynomial p (coordinateMatrix (WithLp.ofLp a))).conjTranspose*matrixPolynomial p (coordinateMatrix (WithLp.ofLp a)))).re := by
      change (d:ℝ)^3*((d:ℝ)⁻¹*(Matrix.trace ((matrixPolynomial p (hermitianMatrix a)).conjTranspose*matrixPolynomial p (hermitianMatrix a))).re)= (d:ℝ)^2*(Matrix.trace ((matrixPolynomial p (hermitianMatrix a)).conjTranspose*matrixPolynomial p (hermitianMatrix a))).re
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left hn (sq_nonneg _)
  simp only [sum_sub_distrib,← mul_sum] at *
  rw [hdiv]
  dsimp [matrixFisherTest]
  nlinarith
end FiniteEntropySeparation

end

end OAI
