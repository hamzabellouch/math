import Mathlib
import OAI.Analysis.Crouzeix.BoundaryFibers

namespace OAI

/-! Cauchy Projection. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

section Tensor

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def tensorBilinearCLM (m : ℕ) : Operator H →L[ℂ] Coeff m →L[ℂ] Operator (Amplification H m) := by
  let L : Operator H →ₗ[ℂ] Coeff m →L[ℂ] Operator (Amplification H m) := {
    toFun A := tensorCoefficientCLM A m
    map_add' A D := by
      ext B v
      exact congrArg (fun T : Operator (Amplification H m) => T v)
        ((tensorOperatorCLM B).map_add A D)
    map_smul' c A := by
      ext B v
      exact congrArg (fun T : Operator (Amplification H m) => T v)
        ((tensorOperatorCLM B).map_smul c A) }
  refine LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := Operator H) (F := Coeff m →L[ℂ] Operator (Amplification H m)) L 1 fun A => ?_
  rw [one_mul]
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    (fun B => norm_tensorOperator_le A B)

@[simp] theorem tensorBilinearCLM_apply (m : ℕ) (A : Operator H) (B : Coeff m) :
    tensorBilinearCLM m A B = tensorOperator A B := rfl

end Tensor

section OperatorIntegral

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem inner_integral_operator_apply (T : α → E →L[ℂ] E)
    (hT : Integrable T μ) (x y : E) :
    ⟪y, (∫ t, T t ∂μ) x⟫_ℂ = ∫ t, ⟪y, T t x⟫_ℂ ∂μ := by
  rw [ContinuousLinearMap.integral_apply hT]
  have hf : Integrable (fun t => T t x) μ :=
    (ContinuousLinearMap.apply ℂ _ x).integrable_comp hT
  exact (integral_inner (𝕜 := ℂ) hf y).symm

end OperatorIntegral

namespace Boundary

def boundaryField {n : ℕ} (U : C(CircleSpace, Coeff n)) : BoundaryL2 n :=
  ContinuousMap.toLp 2 circleMeasure ℂ
    ⟨fun t => toHS (U t), (toHSCLM n).continuous.comp U.continuous⟩

theorem boundaryField_apply_ae {n : ℕ} (U : C(CircleSpace, Coeff n)) :
    boundaryField U =ᵐ[circleMeasure] fun t => toHS (U t) :=
  ContinuousMap.coeFn_toLp _ _

theorem integrable_tensor_field {n : ℕ} (E U : C(CircleSpace, Coeff n)) :
    Integrable (fun t => tensorOperator (matrixOperatorMap n (E t)) (U t)) circleMeasure := by
  have hc : Continuous (fun t => tensorOperator (matrixOperatorMap n (E t)) (U t)) :=
    ((tensorBilinearCLM n).continuous.comp
      ((matrixOperatorMap n).continuous.comp E.continuous)).clm_apply U.continuous
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem densityLp_inner_boundaryField {n : ℕ} (E U : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).IsHermitian) (X Y : Coeff n) :
    ⟪densityLp E X Y, boundaryField U⟫_ℂ =
      ⟪vectorization Y, (∫ t, tensorOperator (matrixOperatorMap n (E t)) (U t)
         ∂circleMeasure) (vectorization X)⟫_ℂ := by
  rw [inner_integral_operator_apply _ (integrable_tensor_field E U), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [densityLp_apply_ae E X Y, boundaryField_apply_ae U] with t he hu
  rw [he, hu]
  exact weightedPartialTrace_testing (E t) (hE t) X Y (U t)

def matrixLaurentMonomial {n : ℕ} (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    C(CircleSpace, Coeff n) :=
  ⟨fun t => (c * fourier a.1 t) • Matrix.single a.2.1 a.2.2 (1 : ℂ),
    (continuous_const.mul (fourier a.1).continuous).smul continuous_const⟩

theorem toHS_single {n : ℕ} (i j : Fin n) :
    toHS (Matrix.single i j (1 : ℂ)) = EuclideanSpace.single (i,j) (1 : ℂ) := by
  ext ⟨a,b⟩
  change (Matrix.single i j (1 : ℂ)) a b = _
  simp only [Matrix.single_apply, PiLp.single_apply]
  by_cases hai : a = i <;> by_cases hbj : b = j <;> simp [hai, hbj, Prod.ext_iff, eq_comm]

@[simp] theorem boundaryField_matrixLaurentMonomial {n : ℕ}
    (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    boundaryField (matrixLaurentMonomial a c) = c • matrixFourier a := by
  apply Lp.ext
  filter_upwards [boundaryField_apply_ae (matrixLaurentMonomial a c),
    matrixFourier_apply_ae a, Lp.coeFn_smul c (matrixFourier a)] with t hu hf hs
  rw [hu, hs, Pi.smul_apply, hf]
  change toHS ((c * fourier a.1 t) • Matrix.single a.2.1 a.2.2 (1 : ℂ)) = _
  rw [← toHSCLM_apply, map_smul, toHSCLM_apply, toHS_single, mul_smul]

theorem boundary_real_inner_eq_re {n : ℕ} (u v : BoundaryL2 n) :
    ⟪u, v⟫_ℝ = (⟪u, v⟫_ℂ).re := boundary_real_inner u v

theorem eq_of_inner_matrixLaurentMonomial {n : ℕ} {u v : BoundaryL2 n}
    (h : ∀ (a : ℤ × (Fin n × Fin n)) (c : ℂ),
      ⟪u, boundaryField (matrixLaurentMonomial a c)⟫_ℝ =
      ⟪v, boundaryField (matrixLaurentMonomial a c)⟫_ℝ) : u = v := by
  apply (matrixFourierBasis n).repr.injective
  ext a
  simp only [HilbertBasis.repr_apply_apply, matrixFourierBasis_apply]
  rw [← inner_conj_symm (matrixFourier a) u, ← inner_conj_symm (matrixFourier a) v]
  congr 1
  apply Complex.ext
  · have hr := h a 1
    simpa only [boundaryField_matrixLaurentMonomial, one_smul,
      boundary_real_inner_eq_re] using hr
  · have hi := h a Complex.I
    simp only [boundaryField_matrixLaurentMonomial, boundary_real_inner_eq_re,
      inner_smul_right, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_sub] at hi
    exact neg_injective hi

end Boundary

end CrouzeixHilbert

end

end OAI
