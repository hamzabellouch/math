import OAI.Analysis.FreeEntropy.MatrixFisherTest

namespace OAI

noncomputable section
open MeasureTheory Finset
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem matrixMoment_polynomial (w : List (Fin n)) :
    IsComplexPolynomial (fun x : MatrixIndex n d → ℝ => matrixMoment (WithLp.toLp 2 x) w) :=
  ((IsMatrixPolynomial.word (fun i a b => coordinateMatrix_polynomial i a b) w).trace).const_mul ((d:ℂ)⁻¹)
 theorem matrixPolynomialDerivative_polynomial (p : WordPolynomial n) (i : Fin n) :
    IsComplexPolynomial (fun x : MatrixIndex n d → ℝ => matrixPolynomialDerivative p i (WithLp.toLp 2 x)) := by
  apply IsComplexPolynomial.finset_sum p.support
  intro w _
  apply IsComplexPolynomial.const_mul
  apply IsComplexPolynomial.finset_sum univ
  intro r _
  by_cases h : w[r.val]=i
  · simp only [h,ite_true]
    exact (matrixMoment_polynomial _).mul (matrixMoment_polynomial _)
  · simp only [h,ite_false]
    exact IsComplexPolynomial.const 0
 theorem matrixPolynomialNorm_polynomial (p : WordPolynomial n) :
    IsRealPolynomial (fun x : MatrixIndex n d → ℝ => matrixPolynomialNorm p (WithLp.toLp 2 x)) :=
  (IsComplexPolynomial.finset_sum p.support (fun u _ => IsComplexPolynomial.finset_sum p.support
    (fun v _ => (matrixMoment_polynomial (u.reverse++v)).const_mul (star (p u)*p v)))).1
 theorem matrixFisherTest_polynomial (p : WordPolynomial n) (i : Fin n) :
    IsRealPolynomial (fun x : MatrixIndex n d → ℝ => matrixFisherTest p i (WithLp.toLp 2 x)) :=
  ((matrixPolynomialDerivative_polynomial p i).1.const_mul 2).sub (matrixPolynomialNorm_polynomial p)
 theorem matrix_classicalFisher_lower (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsProbabilityMeasure μ]
    {K s : ℝ} (hK : 0 ≤ K) (hμ : ∀ᵐy ∂μ,‖y‖ ≤ K) (hs : 0<s)
    (p : Fin n → WordPolynomial n) :
    (d:ℝ)^3*(∑i,∫a,matrixFisherTest (p i) i a*smoothedDensity μ s a) ≤ classicalFisher μ s := by
  let f : MatrixIndex n d → (MatrixIndex n d → ℝ) → ℝ := fun q => matrixRealScore (p q.1) q.2.1 q.2.2
  have hf q : IsRealPolynomial (f q) := matrixRealScore_polynomial _ _ _
  have hc := classicalFisher_polynomial_lower μ hK hμ hs f hf
  have hi i : Integrable (fun a => matrixFisherTest (p i) i a*smoothedDensity μ s a) :=
    (matrixFisherTest_polynomial (p i) i).smoothed_integrable μ hs hK hμ
  have hj q : Integrable (fun a => (2*coordinateDerivative (f q) q (WithLp.ofLp a)-(f q (WithLp.ofLp a))^2)*smoothedDensity μ s a) :=
    (((hf q).derivative q).const_mul 2 |>.sub ((hf q).pow 2)).smoothed_integrable μ hs hK hμ
  apply le_trans _ hc
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  rw [← integral_const_mul]
  simp_rw [← integral_finsetSum _ (fun k _ => hj (i,_,k))]
  rw [← integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hj (i,j,k)))]
  apply integral_mono ((hi i).const_mul _) (integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hj (i,j,k))))
  intro a
  have hp := mul_le_mul_of_nonneg_right (matrixFisherTest_pointwise hd (p i) i a) (smoothedDensity_pos μ hs a).le
  simpa only [sum_mul,mul_assoc] using hp
end FiniteEntropySeparation

end

end OAI
