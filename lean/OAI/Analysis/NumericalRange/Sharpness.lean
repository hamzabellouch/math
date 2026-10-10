import OAI.Analysis.NumericalRange.Convexity

namespace OAI

section

section
noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator
namespace CompleteCrouzeix

def sharpMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, 2; 0, 0]

def sharpPolynomial : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ := ![0, 1]

lemma sharpPolynomial_value (z : ℂ) : polynomialValue sharpPolynomial z = z • 1 := by
  simp [polynomialValue, sharpPolynomial, Fin.sum_univ_two]

lemma sharpPolynomial_value_norm (z : ℂ) : ‖polynomialValue sharpPolynomial z‖ = ‖z‖ := by
  rw [sharpPolynomial_value, norm_smul, norm_one, mul_one]

lemma sharpMatrix_apply (x : EuclideanSpace ℂ (Fin 2)) :
    Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) sharpMatrix x = !₂[2 * x 1, 0] := by
  apply PiLp.ext
  intro i
  change (sharpMatrix *ᵥ (fun i => x i)) i = (![2 * x 1, 0] : Fin 2 → ℂ) i
  fin_cases i <;> simp [sharpMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma sharpMatrix_pairing (x : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ x (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) sharpMatrix x) =
      2 * x 1 * star (x 0) := by
  rw [sharpMatrix_apply]
  simp [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]

lemma sharpMatrix_numericalRange_le {z : ℂ} (hz : z ∈ numericalRange sharpMatrix) :
    ‖z‖ ≤ 1 := by
  obtain ⟨x, hx, rfl⟩ := hz
  rw [sharpMatrix_pairing, norm_mul, norm_mul, norm_star]
  have hnorm := EuclideanSpace.norm_sq_eq x
  simp only [Fin.sum_univ_two, hx, one_pow] at hnorm
  norm_num
  nlinarith [sq_nonneg (‖x 0‖ - ‖x 1‖)]

lemma one_mem_sharpMatrix_numericalRange : (1 : ℂ) ∈ numericalRange sharpMatrix := by
  let t : ℝ := Real.sqrt (1 / 2)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = 1 / 2 := Real.sq_sqrt (by positivity)
  let x : EuclideanSpace ℂ (Fin 2) := !₂[(t : ℂ), (t : ℂ)]
  have hx2 : ‖x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_two, x, Matrix.cons_val_zero,
      Matrix.cons_val_one, Complex.norm_of_nonneg ht]
    linarith
  refine ⟨x, ?_, ?_⟩
  · nlinarith [norm_nonneg x]
  · rw [sharpMatrix_pairing]
    change 2 * (t : ℂ) * star (t : ℂ) = 1
    rw [Complex.star_def, Complex.conj_ofReal]
    have hreal : 2 * t * t = 1 := by nlinarith
    exact_mod_cast hreal

lemma sharp_rangeMaximum : rangeMaximum sharpMatrix sharpPolynomial = 1 := by
  obtain ⟨z, hz, hm⟩ := rangeMaximum_attained (by norm_num : 0 < 2)
    sharpMatrix sharpPolynomial
  apply le_antisymm
  · rw [hm, sharpPolynomial_value_norm]
    exact sharpMatrix_numericalRange_le hz
  · have h := le_csSup
      (((numericalRange_compact sharpMatrix).image
        (continuous_polynomialValue sharpPolynomial).norm).bddAbove)
      (show ‖polynomialValue sharpPolynomial 1‖ ∈
        (fun z => ‖polynomialValue sharpPolynomial z‖) '' numericalRange sharpMatrix
        from ⟨1, one_mem_sharpMatrix_numericalRange, rfl⟩)
    simpa only [rangeMaximum, sharpPolynomial_value_norm, norm_one] using h

lemma sharpPolynomial_at : polynomialAt sharpMatrix sharpPolynomial =
    Matrix.kronecker sharpMatrix (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  simp [polynomialAt, sharpPolynomial, Fin.sum_univ_two]

lemma sharp_tensor_apply :
    Matrix.toEuclideanCLM (n := Fin 2 × Fin 1) (𝕜 := ℂ)
        (polynomialAt sharpMatrix sharpPolynomial)
        (EuclideanSpace.single (1, 0) 1) = EuclideanSpace.single (0, 0) 2 := by
  rw [sharpPolynomial_at]
  apply PiLp.ext
  rintro ⟨i,j⟩
  change ((Matrix.kronecker sharpMatrix (1 : Matrix (Fin 1) (Fin 1) ℂ)) *ᵥ
      (Pi.single (1, 0) 1)) (i,j) =
      (Pi.single (0, 0) (2 : ℂ) : (Fin 2 × Fin 1) → ℂ) (i,j)
  simp only [Matrix.mulVec_single]
  fin_cases i <;> fin_cases j <;> norm_num [sharpMatrix, Pi.single_apply]

lemma two_le_sharpPolynomial_norm : 2 ≤ ‖polynomialAt sharpMatrix sharpPolynomial‖ := by
  have h := (Matrix.toEuclideanCLM (n := Fin 2 × Fin 1) (𝕜 := ℂ)
    (polynomialAt sharpMatrix sharpPolynomial)).le_opNorm
      (EuclideanSpace.single (1,0) 1)
  rw [sharp_tensor_apply, Matrix.l2_opNorm_toEuclideanCLM] at h
  simpa using h

theorem optimal_constant {C : ℝ} (hC : UniversalBound C) : 2 ≤ C := by
  have h := hC 2 1 1 (by norm_num) (by norm_num) sharpMatrix sharpPolynomial
  rw [sharp_rangeMaximum, mul_one] at h
  exact two_le_sharpPolynomial_norm.trans h

end CompleteCrouzeix

end

end

end

end OAI
