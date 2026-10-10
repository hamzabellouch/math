import OAI.Analysis.FreeEntropy.FisherLaw

namespace OAI

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem trace_conjTranspose_mul_re (D : Matrix (Fin d) (Fin d) ℂ) :
    (Matrix.trace (D.conjTranspose*D)).re = ∑j,∑k,Complex.normSq (D j k) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum,Complex.mul_re,Complex.star_def,
    Complex.conj_re,Complex.conj_im,neg_mul,sub_neg_eq_add,Complex.normSq_apply]
  exact sum_comm
 theorem matrixWord_conjTranspose (A : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀i,(A i).IsHermitian) (w : List (Fin n)) :
    (matrixWord A w).conjTranspose = matrixWord A w.reverse := by
  induction w with
  | nil => simp [matrixWord]
  | cons i w ih =>
    simp only [matrixWord_cons,Matrix.conjTranspose_mul,ih,(hA i).eq,List.reverse_cons,
      matrixWord_append,matrixWord_cons,matrixWord_nil,mul_one]
 theorem matrixScorePolynomial_norm_lower (p : WordPolynomial n) (x : MatrixIndex n d → ℝ) :
    (∑j,∑k,(matrixScorePolynomial p j k x).re^2) ≤
      (Matrix.trace ((matrixPolynomial p (coordinateMatrix x)).conjTranspose*matrixPolynomial p (coordinateMatrix x))).re := by
  rw [trace_conjTranspose_mul_re,← hermitianBasis_parseval]
  apply sum_le_sum
  intro j _
  apply sum_le_sum
  intro k _
  change (matrixScorePolynomial p j k x).re^2 ≤ Complex.normSq (matrixScorePolynomial p j k x)
  simp only [Complex.normSq_apply]
  nlinarith [sq_nonneg (matrixScorePolynomial p j k x).im]
 def matrixPolynomialNorm (p : WordPolynomial n) (a : MatrixCoordinates n d) : ℝ :=
    (∑u∈p.support,∑v∈p.support,star (p u)*p v*matrixMoment a (u.reverse++v)).re
 theorem matrixPolynomialNorm_trace (p : WordPolynomial n) (a : MatrixCoordinates n d) :
    matrixPolynomialNorm p a = (d:ℝ)⁻¹*(Matrix.trace
      ((matrixPolynomial p (hermitianMatrix a)).conjTranspose*matrixPolynomial p (hermitianMatrix a))).re := by
  have he : Matrix.trace ((matrixPolynomial p (hermitianMatrix a)).conjTranspose*matrixPolynomial p (hermitianMatrix a)) =
      ∑u∈p.support,∑v∈p.support,star (p u)*p v*Matrix.trace (matrixWord (hermitianMatrix a) (u.reverse++v)) := by
    simp only [matrixPolynomial,Finsupp.sum,Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,
      matrixWord_conjTranspose _ (hermitianMatrix_isHermitian a),sum_mul,mul_sum,
      smul_mul_assoc,mul_smul_comm,Matrix.trace_sum,Matrix.trace_smul,
      smul_eq_mul,matrixWord_append]
    rw [sum_comm]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    ring
  rw [he]
  unfold matrixPolynomialNorm matrixMoment
  have he' : (∑u∈p.support,∑v∈p.support,star (p u)*p v*((d:ℂ)⁻¹*Matrix.trace ((u.reverse++v).map (hermitianMatrix a)).prod)) =
      (d:ℂ)⁻¹*(∑u∈p.support,∑v∈p.support,star (p u)*p v*Matrix.trace (matrixWord (hermitianMatrix a) (u.reverse++v))) := by
    simp only [mul_sum,matrixWord]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    ring
  rw [he']
  simp only [← Complex.ofReal_natCast,← Complex.ofReal_inv,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
 theorem polynomialVector_norm_formula {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) (X : Fin n → H →L[ℂ] H)
    (hX : ∀i,IsSelfAdjoint (X i)) (p : WordPolynomial n) :
    ‖polynomialVector τ X p‖^2 =
      (∑u∈p.support,∑v∈p.support,star (p u)*p v*wordMoment τ X (u.reverse++v)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [polynomialVector,Finsupp.linearCombination_apply,Finsupp.sum,sum_inner,inner_sum,
    inner_smul_left,inner_smul_right,inner_wordVector τ X hX,mul_assoc,mul_sum]
  change (∑u∈p.support,∑v∈p.support,p u*(star (p v)*wordMoment τ X (v.reverse++u))).re = _
  rw [sum_comm]
  congr 1
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  ring
end FiniteEntropySeparation

end

end OAI
