import OAI.Probability.SignedSweeps.SpectralCommute
import OAI.Probability.SignedSweeps.TensorDensity

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma root_inverse_root (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    positiveRoot T hT * supportInverseRoot T hT * positiveRoot T hT =
      positiveRoot T hT := by
  rw [root_mul_supportInverseRoot, spectralSupport_root]

lemma inverse_root_inverse (T : E →ₗ[ℂ] E) (hT : T.IsPositive) :
    supportInverseRoot T hT * positiveRoot T hT * supportInverseRoot T hT =
      supportInverseRoot T hT := by
  rw [supportInverseRoot_mul_root, spectralSupport, supportInverseRoot, basisDiagonal_mul]
  congr 1
  funext i
  split_ifs with h <;> simp [h]

lemma supportInverseRoot_unique (T D : E →ₗ[ℂ] E) (hT : T.IsPositive)
    (hTD : T * D = D * T)
    (hroot : positiveRoot T hT * D * positiveRoot T hT = positiveRoot T hT)
    (hD : D * positiveRoot T hT * D = D) :
    D = supportInverseRoot T hT := by
  have hRD := positiveRoot_commute T D hT hTD
  apply (hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext
  intro i
  by_cases hi : hT.isSymmetric.eigenvalues rfl i = 0
  · have hh := LinearMap.congr_fun hD ((hT.isSymmetric.eigenvectorBasis rfl) i)
    rw [mul_assoc D, hRD, ← mul_assoc D] at hh
    simp only [Module.End.mul_apply, positiveRoot, basisDiagonal_apply_basis,
      hi, Real.sqrt_zero, Complex.ofReal_zero, zero_smul, map_zero] at hh
    simpa only [OrthonormalBasis.coe_toBasis, supportInverseRoot,
      basisDiagonal_apply_basis, hi, Real.sqrt_zero, inv_zero,
      Complex.ofReal_zero, zero_smul] using hh.symm
  · have hs : (Real.sqrt (hT.isSymmetric.eigenvalues rfl i) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr
        (lt_of_le_of_ne (hT.nonneg_eigenvalues rfl i) (Ne.symm hi)))
    have hh := LinearMap.congr_fun hroot ((hT.isSymmetric.eigenvectorBasis rfl) i)
    rw [hRD] at hh
    simp only [Module.End.mul_apply, positiveRoot, basisDiagonal_apply_basis,
      map_smul] at hh
    have hc := (smul_right_injective _ hs) hh
    simp only [OrthonormalBasis.coe_toBasis, supportInverseRoot, basisDiagonal_apply_basis,
      Complex.ofReal_inv]
    calc
      _ = (Real.sqrt (hT.isSymmetric.eigenvalues rfl i) : ℂ)⁻¹ •
          ((Real.sqrt (hT.isSymmetric.eigenvalues rfl i) : ℂ) •
            D (hT.isSymmetric.eigenvectorBasis rfl i)) := by rw [inv_smul_smul₀ hs]
      _ = _ := by rw [hc]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical

lemma tensorOperator_supportInverseRoot (E : FiniteComplexHilbert) {p : ℕ}
    (A : Fin p → E →ₗ[ℂ] E) (hA : ∀ i, (A i).IsPositive) :
    supportInverseRoot (tensorOperator E A) (tensorOperator_positive E A hA) =
      tensorOperator E (fun i => supportInverseRoot (A i) (hA i)) := by
  symm
  apply supportInverseRoot_unique _ _ (tensorOperator_positive E A hA)
  · rw [← tensorOperator_mul, ← tensorOperator_mul]
    congr 1
    funext i
    exact (supportInverseRoot_commute (A i) (A i) (hA i) rfl).symm
  · rw [tensorOperator_positiveRoot E A hA, ← tensorOperator_mul, ← tensorOperator_mul]
    simp only [root_inverse_root]
  · rw [tensorOperator_positiveRoot E A hA, ← tensorOperator_mul, ← tensorOperator_mul]
    simp only [inverse_root_inverse]

lemma tensorOperator_spectralSupport (E : FiniteComplexHilbert) {p : ℕ}
    (A : Fin p → E →ₗ[ℂ] E) (hA : ∀ i, (A i).IsPositive) :
    spectralSupport (tensorOperator E A) (tensorOperator_positive E A hA) =
      tensorOperator E (fun i => spectralSupport (A i) (hA i)) := by
  rw [← supportInverseRoot_mul_root, tensorOperator_supportInverseRoot E A hA,
    tensorOperator_positiveRoot E A hA, ← tensorOperator_mul]
  simp only [supportInverseRoot_mul_root]

lemma tensor_density_right_support {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    (E : FiniteComplexHilbert) (W : Finset (A × B)) (e : Fin W.card ≃ {x // x ∈ W})
    (R : B → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive) :
    tensorOperator E (fun k => R (e k).1.2) *
      spectralSupport (tensorOperator E (fun _ : Fin W.card => densityMean R))
        (tensorOperator_positive E _ (fun _ => densityMean_positive R hR)) =
      tensorOperator E (fun k => R (e k).1.2) := by
  rw [tensorOperator_spectralSupport E _ (fun _ => densityMean_positive R hR), ← tensorOperator_mul]
  simp only [density_right_support R hR]

lemma tensor_density_cell_bound {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    (E : FiniteComplexHilbert) (W : Finset (A × B)) (e : Fin W.card ≃ {x // x ∈ W})
    (R : B → E →ₗ[ℂ] E) (hR : ∀ j, (R j).IsPositive)
    (S : A → E →ₗ[ℂ] E) (hS : ∀ i, (S i).IsPositive)
    (htrS : ∀ i, (LinearMap.trace ℂ E (S i)).re = 1) :
    ‖(positiveRoot (tensorOperator E (fun k => R (e k).1.2))
          (tensorOperator_positive E _ (fun k => hR (e k).1.2)) *
        supportInverseRoot (tensorOperator E (fun _ : Fin W.card => densityMean R))
          (tensorOperator_positive E _ (fun _ => densityMean_positive R hR)) *
        positiveRoot (tensorOperator E (fun k => S (e k).1.1))
          (tensorOperator_positive E _ (fun k => hS (e k).1.1))).toContinuousLinearMap‖ ^ 2 ≤
      missingCellFactor W := by
  rw [tensorOperator_positiveRoot, tensorOperator_supportInverseRoot,
    tensorOperator_positiveRoot, ← tensorOperator_mul, ← tensorOperator_mul]
  exact tensor_normalized_density_bound E W e R hR S hS htrS

end SignedSweeps
end

end OAI
