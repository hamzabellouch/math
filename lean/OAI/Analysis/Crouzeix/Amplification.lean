import Mathlib
import OAI.Analysis.Crouzeix.FiniteCompression

namespace OAI

/-! Amplification. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

def amplificationMap (e : H →ₗᵢ[ℂ] G) (m : ℕ) :
    Amplification H m →L[ℂ] Amplification G m :=
  (TensorProduct.mapL e.toContinuousLinearMap
    (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin m)))).completion

theorem norm_amplificationMap (e : H →ₗᵢ[ℂ] G) (m : ℕ)
    (x : Amplification H m) : ‖amplificationMap e m x‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (amplificationMap e m).continuous.norm continuous_norm) ?_
  intro a
  simp only [amplificationMap, ContinuousLinearMap.completion_apply_coe,
    UniformSpace.Completion.norm_coe, TensorProduct.mapL_apply]
  exact (TensorProduct.mapIsometry e (LinearIsometry.id :
    EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))).norm_map a

@[simp]
theorem amplificationMap_tmul (e : H →ₗᵢ[ℂ] G) {m : ℕ}
    (x : H) (y : EuclideanSpace ℂ (Fin m)) :
    amplificationMap e m (↑(x ⊗ₜ[ℂ] y)) =
      (↑(e x ⊗ₜ[ℂ] y) : Amplification G m) := by
  simp [amplificationMap]

def conjugateOperator (e : H ≃ₗᵢ[ℂ] G) : Operator H ≃A[ℂ] Operator G :=
  e.toContinuousLinearEquiv.conjContinuousAlgEquiv

@[simp]
theorem conjugateOperator_apply (e : H ≃ₗᵢ[ℂ] G) (A : Operator H) (x : G) :
    conjugateOperator e A x = e (A (e.symm x)) := rfl

@[simp]
theorem conjugateOperator_pow_apply (e : H ≃ₗᵢ[ℂ] G) (A : Operator H) (k : ℕ) (x : H) :
    (conjugateOperator e A ^ k) (e x) = e ((A ^ k) x) := by
  rw [← map_pow (conjugateOperator e) A k, conjugateOperator_apply, e.symm_apply_apply]

theorem numericalRange_conjugateOperator (e : H ≃ₗᵢ[ℂ] G) (A : Operator H) :
    numericalRange (conjugateOperator e A) = numericalRange A := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨e.symm x, by simpa using hx, ?_⟩
    simpa using (e.inner_map_map (e.symm x) (A (e.symm x))).symm
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e x, by simpa using hx, by simp [e.inner_map_map]⟩

theorem polynomialEval_conjugateOperator_apply (e : H ≃ₗᵢ[ℂ] G) (A : Operator H)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) (v : Amplification H m) :
    polynomialEval (conjugateOperator e A) B (amplificationMap e.toLinearIsometry m v) =
      amplificationMap e.toLinearIsometry m (polynomialEval A B v) := by
  refine UniformSpace.Completion.induction_on v
    (isClosed_eq ((polynomialEval (conjugateOperator e A) B).continuous.comp
      (amplificationMap e.toLinearIsometry m).continuous)
      ((amplificationMap e.toLinearIsometry m).continuous.comp
        (polynomialEval A B).continuous)) ?_
  intro a
  induction a using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [amplificationMap_tmul, polynomialEval_tmul, conjugateOperator_pow_apply,
      map_sum, LinearIsometryEquiv.coe_toLinearIsometry]
  | add a b ha hb =>
    simp only [UniformSpace.Completion.coe_add, map_add, ha, hb]

theorem norm_polynomialEval_le_conjugateOperator (e : H ≃ₗᵢ[ℂ] G) (A : Operator H)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    ‖polynomialEval A B‖ ≤ ‖polynomialEval (conjugateOperator e A) B‖ := by
  apply (polynomialEval A B).opNorm_le_bound (norm_nonneg _)
  intro v
  rw [← norm_amplificationMap e.toLinearIsometry m (polynomialEval A B v),
    ← polynomialEval_conjugateOperator_apply]
  simpa only [norm_amplificationMap] using
    (polynomialEval (conjugateOperator e A) B).le_opNorm (amplificationMap e.toLinearIsometry m v)

theorem norm_polynomialEval_conjugateOperator (e : H ≃ₗᵢ[ℂ] G) (A : Operator H)
    {m d : ℕ} (B : Fin (d + 1) → Coeff m) :
    ‖polynomialEval (conjugateOperator e A) B‖ = ‖polynomialEval A B‖ := by
  apply le_antisymm _ (norm_polynomialEval_le_conjugateOperator e A B)
  have he : conjugateOperator e.symm (conjugateOperator e A) = A := by ext x; simp
  simpa only [he] using
    norm_polynomialEval_le_conjugateOperator e.symm (conjugateOperator e A) B

open scoped Kronecker

def matrixAmplificationCoordinates (n m : ℕ) :
    Amplification (EuclideanSpace ℂ (Fin n)) m →L[ℂ]
      EuclideanSpace ℂ (Fin n × Fin m) :=
  (((EuclideanSpace.basisFun (Fin n) ℂ).tensorProduct
    (EuclideanSpace.basisFun (Fin m) ℂ)).repr.toContinuousLinearEquiv.toContinuousLinearMap).fromCompletion

theorem norm_matrixAmplificationCoordinates (n m : ℕ)
    (v : Amplification (EuclideanSpace ℂ (Fin n)) m) :
    ‖matrixAmplificationCoordinates n m v‖ = ‖v‖ := by
  refine UniformSpace.Completion.induction_on v
    (isClosed_eq (matrixAmplificationCoordinates n m).continuous.norm continuous_norm) ?_
  intro a
  simp only [matrixAmplificationCoordinates, ContinuousLinearMap.fromCompletion_apply_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.norm_map,
    UniformSpace.Completion.norm_coe]

@[simp]
theorem matrixAmplificationCoordinates_tmul {n m : ℕ}
    (x : EuclideanSpace ℂ (Fin n)) (y : EuclideanSpace ℂ (Fin m)) (i : Fin n) (j : Fin m) :
    matrixAmplificationCoordinates n m (↑(x ⊗ₜ[ℂ] y)) (i, j) = y j * x i := by
  simp only [matrixAmplificationCoordinates, ContinuousLinearMap.fromCompletion_apply_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    OrthonormalBasis.tensorProduct_repr_tmul_apply, EuclideanSpace.basisFun_repr]

theorem matrixAmplificationCoordinates_tensorOperator {n m : ℕ}
    (M : Coeff n) (B : Coeff m) (v : Amplification (EuclideanSpace ℂ (Fin n)) m) :
    matrixAmplificationCoordinates n m (tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) M) B v) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (M ⊗ₖ B) (matrixAmplificationCoordinates n m v) := by
  refine UniformSpace.Completion.induction_on v
    (isClosed_eq ((matrixAmplificationCoordinates n m).continuous.comp
      (tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) M) B).continuous)
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (M ⊗ₖ B)).continuous.comp
        (matrixAmplificationCoordinates n m).continuous)) ?_
  intro a
  induction a using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [tensorOperator, ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]
    apply PiLp.ext
    rintro ⟨i, j⟩
    simp only [matrixAmplificationCoordinates_tmul, Matrix.ofLp_toEuclideanCLM,
      Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker_apply,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  | add a b ha hb => simp only [UniformSpace.Completion.coe_add, map_add, ha, hb]

theorem matrixAmplificationCoordinates_polynomialEval {n m d : ℕ}
    (M : Coeff n) (B : Fin (d + 1) → Coeff m)
    (v : Amplification (EuclideanSpace ℂ (Fin n)) m) :
    matrixAmplificationCoordinates n m (polynomialEval (Matrix.toEuclideanCLM (𝕜 := ℂ) M) B v) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (∑ k : Fin (d + 1), (M ^ (k : ℕ)) ⊗ₖ B k)
        (matrixAmplificationCoordinates n m v) := by
  simp only [polynomialEval, sum_apply, map_sum, ← map_pow,
    matrixAmplificationCoordinates_tensorOperator]

theorem norm_polynomialEval_eq_kronecker {n m d : ℕ}
    (M : Coeff n) (B : Fin (d + 1) → Coeff m) :
    ‖polynomialEval (Matrix.toEuclideanCLM (𝕜 := ℂ) M) B‖ =
      ‖∑ k : Fin (d + 1), (M ^ (k : ℕ)) ⊗ₖ B k‖ := by
  let Q := ∑ k : Fin (d + 1), (M ^ (k : ℕ)) ⊗ₖ B k
  change _ = ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) Q)‖
  apply le_antisymm
  · apply (polynomialEval (Matrix.toEuclideanCLM (𝕜 := ℂ) M) B).opNorm_le_bound (norm_nonneg _)
    intro v
    rw [← norm_matrixAmplificationCoordinates n m (polynomialEval (Matrix.toEuclideanCLM (𝕜 := ℂ) M) B v),
      matrixAmplificationCoordinates_polynomialEval]
    simpa only [norm_matrixAmplificationCoordinates] using
      (Matrix.toEuclideanCLM (𝕜 := ℂ) Q).le_opNorm (matrixAmplificationCoordinates n m v)
  · apply (Matrix.toEuclideanCLM (𝕜 := ℂ) Q).opNorm_le_bound (norm_nonneg _)
    intro w
    let a := ((EuclideanSpace.basisFun (Fin n) ℂ).tensorProduct
      (EuclideanSpace.basisFun (Fin m) ℂ)).repr.symm w
    have he : matrixAmplificationCoordinates n m (↑a) = w := by
      simp only [matrixAmplificationCoordinates, ContinuousLinearMap.fromCompletion_apply_coe,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        ContinuousLinearEquiv.coe_coe, a, LinearIsometryEquiv.apply_symm_apply]
    rw [← he, ← matrixAmplificationCoordinates_polynomialEval,
      norm_matrixAmplificationCoordinates, norm_matrixAmplificationCoordinates]
    exact (polynomialEval (Matrix.toEuclideanCLM (𝕜 := ℂ) M) B).le_opNorm (↑a)

def FiniteMatrixPolynomialBound : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (M : Coeff n) (m : ℕ), 0 < m →
    ∀ (d : ℕ) (B : Fin (d + 1) → Coeff m),
    ‖polynomialEval (Matrix.toEuclideanCLM (𝕜 := ℂ) M) B‖ ≤
      2 * supNorm (numericalRange (Matrix.toEuclideanCLM (𝕜 := ℂ) M)) (matrixPolynomial B)

theorem finiteDimensional_polynomial_bound [FiniteDimensional ℂ H]
    (hfin : FiniteMatrixPolynomialBound) (A : Operator H)
    {m d : ℕ} (hm : 0 < m) (B : Fin (d + 1) → Coeff m) :
    ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B) := by
  cases subsingleton_or_nontrivial H with
  | inl h =>
    have := h
    exact ((zeroConclusion A).2.1 m d B).2.2
  | inr h =>
    have := h
    let e := (stdOrthonormalBasis ℂ H).repr
    let M : Coeff (Module.finrank ℂ H) :=
      (Matrix.toEuclideanCLM (𝕜 := ℂ)).symm (conjugateOperator e A)
    have he : Matrix.toEuclideanCLM (𝕜 := ℂ) M = conjugateOperator e A :=
      (Matrix.toEuclideanCLM (𝕜 := ℂ)).apply_symm_apply _
    have hb := hfin (Module.finrank ℂ H) Module.finrank_pos M m hm d B
    simpa only [he, norm_polynomialEval_conjugateOperator,
      numericalRange_conjugateOperator] using hb

theorem polynomial_bound_of_finite_matrix_bound (hfin : FiniteMatrixPolynomialBound)
    (A : Operator H) {m d : ℕ} (hm : 0 < m) (B : Fin (d + 1) → Coeff m) :
    ‖polynomialEval A B‖ ≤ 2 * supNorm (numericalRange A) (matrixPolynomial B) := by
  apply polynomial_inequality_of_finite_compressions
  intro E _
  exact finiteDimensional_polynomial_bound hfin (compression A E) hm B

end CrouzeixHilbert

end

end OAI
