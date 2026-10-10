import OAI.Probability.SignedSweeps.SupportInverse

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma symmetric_eq_basisDiagonal (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) :
    T = basisDiagonal (hT.eigenvectorBasis rfl) (hT.eigenvalues rfl) := by
  apply (hT.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis, basisDiagonal_apply_basis,
    hT.apply_eigenvectorBasis, RCLike.ofReal_eq_complex_ofReal]

lemma diagonal_function_commute {I : Type*} [Fintype I] (c : I → ℝ)
    (M : Matrix I I ℂ) (h : Matrix.diagonal (fun i => (c i : ℂ)) * M =
      M * Matrix.diagonal (fun i => (c i : ℂ))) (f : ℝ → ℝ) :
    Matrix.diagonal (fun i => (f (c i) : ℂ)) * M =
      M * Matrix.diagonal (fun i => (f (c i) : ℂ)) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hij := congrArg (fun N : Matrix I I ℂ => N i j) h
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij
  by_cases he : c i = c j
  · rw [he, mul_comm]
  · have hdiff : (c i : ℂ) - c j ≠ 0 := by
      exact sub_ne_zero.mpr (Complex.ofReal_injective.ne he)
    have hz : M i j = 0 := by
      apply (mul_eq_zero.mp (show ((c i : ℂ) - c j) * M i j = 0 by
        linear_combination hij)).resolve_left hdiff
    rw [hz, mul_zero, zero_mul]

lemma basisDiagonal_function_commute {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℂ E) (c : I → ℝ) (S : E →ₗ[ℂ] E)
    (h : basisDiagonal b c * S = S * basisDiagonal b c) (f : ℝ → ℝ) :
    basisDiagonal b (fun i => f (c i)) * S =
      S * basisDiagonal b (fun i => f (c i)) := by
  have hc := congrArg (LinearMap.toMatrix b.toBasis b.toBasis) h
  simp only [LinearMap.toMatrix_mul, basisDiagonal_toMatrix] at hc
  apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
  simp only [LinearMap.toMatrix_mul, basisDiagonal_toMatrix]
  exact diagonal_function_commute c _ hc f

lemma spectralFunction_commute (T S : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hTS : T * S = S * T) (f : ℝ → ℝ) :
    basisDiagonal (hT.eigenvectorBasis rfl) (fun i => f (hT.eigenvalues rfl i)) * S =
      S * basisDiagonal (hT.eigenvectorBasis rfl) (fun i => f (hT.eigenvalues rfl i)) := by
  apply basisDiagonal_function_commute _ (hT.eigenvalues rfl) S _ f
  simpa only [← symmetric_eq_basisDiagonal T hT] using hTS

lemma positiveRoot_commute (T S : E →ₗ[ℂ] E) (hT : T.IsPositive) (hTS : T * S = S * T) :
    positiveRoot T hT * S = S * positiveRoot T hT :=
  spectralFunction_commute T S hT.isSymmetric hTS Real.sqrt

lemma supportInverseRoot_commute (T S : E →ₗ[ℂ] E) (hT : T.IsPositive) (hTS : T * S = S * T) :
    supportInverseRoot T hT * S = S * supportInverseRoot T hT :=
  spectralFunction_commute T S hT.isSymmetric hTS (fun x => (Real.sqrt x)⁻¹)

lemma spectralSupport_commute (T S : E →ₗ[ℂ] E) (hT : T.IsPositive) (hTS : T * S = S * T) :
    spectralSupport T hT * S = S * spectralSupport T hT :=
  spectralFunction_commute T S hT.isSymmetric hTS (fun x => if x = 0 then 0 else 1)

lemma spectralSupport_root (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    spectralSupport T hT * positiveRoot T hT = positiveRoot T hT := by
  rw [spectralSupport, positiveRoot, basisDiagonal_mul]
  congr 1
  funext i
  split_ifs with h <;> simp [h]

lemma positiveRoot_right_support (T Q : E →ₗ[ℂ] E) (hT : T.IsPositive)
    (hQ : Q.IsSymmetric) (hTQ : T * Q = T) :
    positiveRoot T hT * Q = positiveRoot T hT := by
  have hQT : Q * T = T := by
    have hh := congrArg LinearMap.adjoint hTQ
    simp only [← LinearMap.star_eq_adjoint, star_mul] at hh
    simpa only [LinearMap.star_eq_adjoint, hT.isSymmetric.adjoint_eq, hQ.adjoint_eq] using hh
  apply (hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext
  intro i
  have hcomm := positiveRoot_commute T Q hT (hTQ.trans hQT.symm)
  rw [hcomm, Module.End.mul_apply]
  simp only [OrthonormalBasis.coe_toBasis, positiveRoot, basisDiagonal_apply_basis, map_smul]
  by_cases hi : hT.isSymmetric.eigenvalues rfl i = 0
  · simp [hi]
  · have hfix : Q (hT.isSymmetric.eigenvectorBasis rfl i) = hT.isSymmetric.eigenvectorBasis rfl i := by
      have hv := LinearMap.congr_fun hQT (hT.isSymmetric.eigenvectorBasis rfl i)
      rw [Module.End.mul_apply, hT.isSymmetric.apply_eigenvectorBasis,
        map_smul, RCLike.ofReal_eq_complex_ofReal] at hv
      exact (smul_right_injective _ (by exact_mod_cast hi)) hv
    rw [hfix]

theorem support_inverse_insertion {J : Type*} [Fintype J] [Nonempty J]
    (R : J → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive)
    (P K : E →ₗ[ℂ] E) (hTP : densityMean R * P = P * densityMean R)
    (hTK : densityMean R * K = K * densityMean R) (j : J) :
    positiveRoot (R j) (hR j) * K * P =
      positiveRoot (R j) (hR j) * supportInverseRoot (densityMean R) (densityMean_positive R hR) *
        K * P * positiveRoot (densityMean R) (densityMean_positive R hR) := by
  have hRK := positiveRoot_commute (densityMean R) K (densityMean_positive R hR) hTK
  have hRP := positiveRoot_commute (densityMean R) P (densityMean_positive R hR) hTP
  have hsup := positiveRoot_right_support (R j)
    (spectralSupport (densityMean R) (densityMean_positive R hR)) (hR j)
    (spectralSupport_positive _ _).isSymmetric (density_right_support R hR j)
  symm
  calc
    _ = positiveRoot (R j) (hR j) *
        (supportInverseRoot (densityMean R) (densityMean_positive R hR) *
          (K * (P * positiveRoot (densityMean R) (densityMean_positive R hR)))) := by
      simp only [mul_assoc]
    _ = positiveRoot (R j) (hR j) *
        (supportInverseRoot (densityMean R) (densityMean_positive R hR) *
          (positiveRoot (densityMean R) (densityMean_positive R hR) * (K * P))) := by
      rw [← hRP, ← mul_assoc K, ← hRK, mul_assoc]
    _ = (positiveRoot (R j) (hR j) *
        (supportInverseRoot (densityMean R) (densityMean_positive R hR) *
          positiveRoot (densityMean R) (densityMean_positive R hR))) * K * P := by
      simp only [mul_assoc]
    _ = _ := by rw [supportInverseRoot_mul_root, hsup]

end SignedSweeps
end

end OAI
