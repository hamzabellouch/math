import OAI.Analysis.HilbertCrouzeix.Compression

namespace OAI

noncomputable section

open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate

namespace HilbertCrouzeix

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def sharpOperator : CoeffSpace 2 →L[ℂ] CoeffSpace 2 :=
  (EuclideanSpace.proj (1 : Fin 2)).smulRight
    ((2 : ℂ) • EuclideanSpace.single (0 : Fin 2) 1)

def sharpPolynomial : Fin (1 + 1) → Coeff 1 := ![0, 1]

theorem sharpPolynomial_apply (z : ℂ) : matrixPolynomial sharpPolynomial z = z • (1 : Coeff 1) := by
  simp [matrixPolynomial, sharpPolynomial, Fin.sum_univ_two]

theorem sharpPolynomial_norm (z : ℂ) : ‖matrixPolynomial sharpPolynomial z‖ = ‖z‖ := by
  rw [sharpPolynomial_apply, norm_smul, norm_one, mul_one]

theorem sharpOperator_apply (x : CoeffSpace 2) :
    sharpOperator x = x.ofLp 1 • ((2 : ℂ) • EuclideanSpace.single (0 : Fin 2) 1) := by
  simp only [sharpOperator, ContinuousLinearMap.smulRight_apply, EuclideanSpace.proj,
    PiLp.proj_apply]

theorem sharpOperator_numerical_le_one {z : ℂ} (hz : z ∈ numericalRange sharpOperator) :
    ‖z‖ ≤ 1 := by
  obtain ⟨x, hx, rfl⟩ := hz
  have hsq : ‖x.ofLp 0‖ ^ 2 + ‖x.ofLp 1‖ ^ 2 = 1 := by
    have h := EuclideanSpace.norm_sq_eq x
    simpa only [hx, one_pow, Fin.sum_univ_two] using h.symm
  rw [sharpOperator_apply]
  rw [inner_smul_right, inner_smul_right, EuclideanSpace.inner_single_right]
  simp only [norm_mul, norm_conj, one_mul]
  norm_num
  nlinarith [sq_nonneg (‖x.ofLp 0‖ - ‖x.ofLp 1‖)]

theorem sharpPolynomial_sup_le_one :
    normSup (numericalRange sharpOperator) (matrixPolynomial sharpPolynomial) ≤ 1 := by
  rw [normSup, ite_eq_left (numericalRange_nonempty sharpOperator)]
  apply csSup_le ((numericalRange_nonempty sharpOperator).image _)
  rintro _ ⟨z, hz, rfl⟩
  change ‖matrixPolynomial sharpPolynomial z‖ ≤ 1
  rw [sharpPolynomial_norm]
  exact sharpOperator_numerical_le_one hz

theorem sharpPolynomial_sup_nonneg :
    0 ≤ normSup (numericalRange sharpOperator) (matrixPolynomial sharpPolynomial) := by
  obtain ⟨z, hz⟩ := numericalRange_nonempty sharpOperator
  have hb : BddAbove ((fun z => ‖matrixPolynomial sharpPolynomial z‖) ''
      numericalRange sharpOperator) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    change ‖matrixPolynomial sharpPolynomial w‖ ≤ 1
    rw [sharpPolynomial_norm]
    exact sharpOperator_numerical_le_one hw
  rw [normSup, ite_eq_left (numericalRange_nonempty sharpOperator)]
  exact (norm_nonneg _).trans (le_csSup hb (mem_image_of_mem _ hz))

theorem sharpPolynomialEval_norm_ge_two :
    2 ≤ ‖polynomialEval sharpOperator sharpPolynomial‖ := by
  let e : CoeffSpace 2 := EuclideanSpace.single (1 : Fin 2) 1
  let v : CoeffSpace 1 := EuclideanSpace.single (0 : Fin 1) 1
  let ξ : Amplification (CoeffSpace 2) 1 := ↑(e ⊗ₜ[ℂ] v)
  have hξ : ‖ξ‖ = 1 := by
    simp only [ξ, UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul,
      e, v, EuclideanSpace.single, PiLp.norm_single, norm_one, mul_one]
  have heval : polynomialEval sharpOperator sharpPolynomial ξ =
      (↑(((2 : ℂ) • EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) ⊗ₜ[ℂ] v) :
        Amplification (CoeffSpace 2) 1) := by
    simp [polynomialEval, Fin.sum_univ_two, sharpPolynomial, ξ, tensorOp_tmul,
      sharpOperator_apply, e]
  have hvalue : ‖polynomialEval sharpOperator sharpPolynomial ξ‖ = 2 := by
    rw [heval]
    simp [UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul,
      norm_smul, v]
  simpa only [hvalue, hξ, mul_one] using
    (polynomialEval sharpOperator sharpPolynomial).le_opNorm ξ

theorem uniformlySharp : UniformlySharp := by
  intro c hc
  refine ⟨2, 1, 1, by norm_num, by norm_num, sharpOperator, sharpPolynomial, ?_⟩
  apply lt_of_lt_of_le _ sharpPolynomialEval_norm_ge_two
  by_cases h : 0 ≤ c
  · exact lt_of_le_of_lt
      (by simpa using mul_le_mul_of_nonneg_left sharpPolynomial_sup_le_one h) hc
  · exact lt_of_le_of_lt
      (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) sharpPolynomial_sup_nonneg)
      (by norm_num)


end HilbertCrouzeix

end

end OAI
