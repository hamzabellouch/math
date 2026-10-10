import OAI.Analysis.BoundedHochschild.StinespringKernel

namespace OAI

/-! The bounded left action on the positive-kernel construction. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype I]

/-- The quadratic form of a finite operator matrix, as a positive functional. -/
def operatorMatrixVectorFunctional (ξ : I → H) :
    CStarMatrix I I (H →L[ℂ] H) →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun A := ∑ i, ∑ j, inner ℂ (ξ i) (A i j (ξ j))
      map_add' A B := by
        simp only [CStarMatrix.add_apply, add_apply,
          inner_add_right, Finset.sum_add_distrib]
      map_smul' z A := by
        simp only [CStarMatrix.smul_apply, smul_apply,
          inner_smul_right, smul_eq_mul, Finset.mul_sum, RingHom.id_apply] }
    (fun A hA => operatorMatrix_quadratic_nonneg A hA ξ)

/-- Applying a completely positive map entrywise before a vector quadratic
form yields a positive functional on the original matrix algebra. -/
def cpMatrixVectorFunctional (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : I → H) :
    CStarMatrix I I M →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    ((operatorMatrixVectorFunctional ξ).toLinearMap.comp (CStarMatrix.mapₗ φ.toLinearMap))
    (fun A hA => operatorMatrix_quadratic_nonneg _ (φ.map_cstarMatrix_nonneg A hA) ξ)

lemma completelyPositive_kernel_left_bound
    (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : I → M) (ξ : I → H) (b : M) :
    (∑ i, ∑ j, inner ℂ (ξ i) (φ (star (b * a i) * (b * a j)) (ξ j))).re ≤
      ‖b‖ ^ 2 * (∑ i, ∑ j, inner ℂ (ξ i) (φ (star (a i) * a j) (ξ j))).re := by
  have h := (cpMatrixVectorFunctional φ ξ).monotone (algebraGram_left_le a b)
  change cpMatrixVectorFunctional φ ξ (algebraGram (fun i => b * a i)) ≤
    cpMatrixVectorFunctional φ ξ (‖b‖ ^ 2 • algebraGram a) at h
  rw [PositiveLinearMap.map_smul_of_tower] at h
  have hr := h.1
  rw [← Complex.coe_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hr
  exact hr

end BoundedHochschild.KadisonRingrose

end

end OAI
