import Mathlib
import OAI.Analysis.Crouzeix.BlockPolynomial

namespace OAI

/-! Endpoint Interpolation. -/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker TensorProduct ENNReal

namespace CrouzeixHilbert

open Realization Boundary

theorem aeval_transferDenominator_isUnit {n : ℕ} (D a : Coeff n)
    (hD : spectralRadius ℂ D < 1) (ha : ‖a‖ ≤ 1) :
    IsUnit (Polynomial.aeval D (transferDenominator a)) := by
  nontriviality (Coeff n)
  rw [← spectrum.zero_notMem_iff (R := ℂ), spectrum.map_polynomial_aeval]
  rintro ⟨z, hz, he⟩
  have hn : ‖z‖ < 1 := by
    rw [spectralRadius_eq_of_unital] at hD
    have hi : (‖z‖₊ : ℝ≥0∞) < 1 := (le_iSup₂ (α := ℝ≥0∞) z hz).trans_lt hD
    exact_mod_cast hi
  have hu : IsUnit (1 - z • a) := by
    apply isUnit_one_sub_of_norm_lt_one
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left ha (norm_nonneg z)).trans_lt (by simpa using hn)
  have hh := (Matrix.isUnit_iff_isUnit_det _).mp hu
  rw [← eval_transferDenominator] at hh
  exact isUnit_iff_ne_zero.mp hh he

@[simp] theorem transferDenominator_ne_zero {n : ℕ} (a : Coeff n) :
    transferDenominator a ≠ 0 := by
  intro h
  have he := eval_transferDenominator a 0
  rw [h, Polynomial.eval_zero, zero_smul, sub_zero, Matrix.det_one] at he
  exact zero_ne_one he

theorem leftTensor_isUnit {n m : ℕ} (A : Coeff n) (hA : IsUnit A) :
    IsUnit (A ⊗ₖ (1 : Coeff m)) := by
  refine ⟨⟨A ⊗ₖ (1 : Coeff m), Ring.inverse A ⊗ₖ 1, ?_, ?_⟩, rfl⟩
  · rw [← Matrix.mul_kronecker_mul, mul_one, Ring.mul_inverse_cancel _ hA]
    exact Matrix.one_kronecker_one
  · rw [← Matrix.mul_kronecker_mul, mul_one, Ring.inverse_mul_cancel _ hA]
    exact Matrix.one_kronecker_one

theorem blockPolynomialEval_pencil_transpose {n : ℕ} (D a : Coeff n) :
    blockPolynomialEval D (pencil a)ᵀ = 1 - D ⊗ₖ aᵀ := by
  rw [pencil, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
    ← Matrix.transpose_map, map_sub, map_one, blockPolynomialEval_smul_constant]
  simp only [Polynomial.aeval_X]

theorem blockPolynomialEval_adjugate_pencil {n : ℕ} (D a : Coeff n) :
    blockPolynomialEval D (pencil a).adjugateᵀ *
        blockPolynomialEval D (pencil a)ᵀ =
      Polynomial.aeval D (transferDenominator a) ⊗ₖ (1 : Coeff n) := by
  rw [← map_mul, ← Matrix.transpose_mul, Matrix.mul_adjugate,
    Matrix.transpose_smul, Matrix.transpose_one, blockPolynomialEval_scalar]
  rfl

theorem blockPolynomialEval_transferNumerator_transpose {n : ℕ} (D a b c d : Coeff n) :
    blockPolynomialEval D (transferNumerator a b c d)ᵀ =
      Polynomial.aeval D (transferDenominator a) ⊗ₖ dᵀ +
      (D ⊗ₖ bᵀ) * blockPolynomialEval D (pencil a).adjugateᵀ * (1 ⊗ₖ cᵀ) := by
  simp only [transferNumerator, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_mul, ← Matrix.transpose_map, map_add]
  rw [← mul_assoc, ← smul_mul_assoc, ← smul_mul_assoc, map_mul, map_mul,
    blockPolynomialEval_smul_constant, blockPolynomialEval_smul_constant,
    blockPolynomialEval_constant, Polynomial.aeval_X]

theorem rational_transfer_interpolates {n : ℕ} (D a b c d L X Y : Coeff n)
    (hD : spectralRadius ℂ D < 1) (ha : ‖a‖ ≤ 1)
    (hL : L = D * L * a + X * c) (hY : Y = D * L * b + X * d) :
    matrixRationalEval (Matrix.toEuclideanCLM (𝕜 := ℂ) D)
      (transferRational a b c d)ᵀ (vectorization X) = vectorization Y := by
  let e := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n × Fin n)
  let E := blockPolynomialEval D (pencil a)ᵀ
  let M := blockPolynomialEval D (pencil a).adjugateᵀ
  let Q := Polynomial.aeval D (transferDenominator a) ⊗ₖ (1 : Coeff n)
  have hME : M * E = Q := blockPolynomialEval_adjugate_pencil D a
  have hrec : e E (toHS L) = e (1 ⊗ₖ cᵀ) (toHS X) := by
    rw [show E = 1 - D ⊗ₖ aᵀ from blockPolynomialEval_pencil_transpose D a,
      map_sub, map_one, sub_apply, one_apply_eq_self,
      kronecker_toHS, kronecker_toHS, Matrix.transpose_transpose, Matrix.transpose_transpose, one_mul]
    change hsEquiv n L - hsEquiv n (D * L * a) = hsEquiv n (X * c)
    rw [← map_sub]
    exact congrArg (hsEquiv n) (sub_eq_iff_eq_add.mpr (hL.trans (add_comm _ _)))
  have hQc : Commute Q (D ⊗ₖ bᵀ) := by
    simpa only [blockPolynomialEval_smul_constant, Polynomial.aeval_X] using
      blockPolynomialEval_commute D (transferDenominator a)
        ((Polynomial.X : Polynomial ℂ) • bᵀ.map Polynomial.C)
  have hNX : e (blockPolynomialEval D (transferNumerator a b c d)ᵀ) (toHS X) =
      e Q (toHS Y) := by
    rw [blockPolynomialEval_transferNumerator_transpose, map_add, add_apply]
    have hd : Polynomial.aeval D (transferDenominator a) ⊗ₖ dᵀ = Q * (1 ⊗ₖ dᵀ) := by
      rw [← Matrix.mul_kronecker_mul, mul_one, one_mul]
    have hdX : e (1 ⊗ₖ dᵀ) (toHS X) = toHS (X * d) := by
      rw [kronecker_toHS, Matrix.transpose_transpose, one_mul]
    have hbL : e (D ⊗ₖ bᵀ) (toHS L) = toHS (D * L * b) := by
      rw [kronecker_toHS, Matrix.transpose_transpose]
    rw [hd, map_mul, mul_apply_eq_comp, hdX,
      map_mul, mul_apply_eq_comp, ← hrec, ← mul_apply_eq_comp, ← map_mul,
      mul_assoc, hME, ← hQc.eq, map_mul, mul_apply_eq_comp, hbL, ← map_add]
    congr 1
    change hsEquiv n (X * d) + hsEquiv n (D * L * b) = hsEquiv n Y
    rw [← map_add]
    exact congrArg (hsEquiv n) ((add_comm _ _).trans hY.symm)
  have hq := aeval_transferDenominator_isUnit D a hD ha
  have hQR : Q * blockRationalEval D (transferRational a b c d)ᵀ =
      blockPolynomialEval D (transferNumerator a b c d)ᵀ :=
    blockRationalEval_denom_cancel D (transferNumerator a b c d)ᵀ _
      (transferDenominator_ne_zero a) hq
  let coords : Amplification (EuclideanSpace ℂ (Fin n)) n →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin n × Fin n) :=
    ⟨(matrixAmplificationCoordinates n n).toLinearMap, norm_matrixAmplificationCoordinates n n⟩
  apply coords.injective
  change matrixAmplificationCoordinates n n _ = matrixAmplificationCoordinates n n _
  rw [matrixAmplificationCoordinates_rationalEval, vectorization_coordinates, vectorization_coordinates]
  have h0 : e Q (e (blockRationalEval D (transferRational a b c d)ᵀ) (toHS X)) =
      e Q (toHS Y) := by
    rw [← mul_apply_eq_comp, ← map_mul, hQR]
    exact hNX
  obtain ⟨u, hu⟩ := (leftTensor_isUnit (m := n) _ hq).map e
  rw [← hu] at h0
  have hi := congrArg (fun v => (↑(u⁻¹) : EuclideanSpace ℂ (Fin n × Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n × Fin n)) v) h0
  simpa only [← mul_apply_eq_comp, ← mul_assoc, Units.inv_mul, one_mul, one_apply_eq_self] using hi

end CrouzeixHilbert

end

end OAI
