import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealEndComplexification

namespace OAI

/-! # Descent and exponential compatibility for real matrices -/

noncomputable section
namespace PolycyclicRecognition

variable (n : ℕ)

def complexEndRealPart (B : Module.End ℂ (Fin n → ℂ)) : Module.End ℝ (Fin n → ℝ) :=
  Matrix.toLinAlgEquiv' ((LinearMap.toMatrixAlgEquiv' B).map Complex.re)

theorem realEndComplexification_injective : Function.Injective (realEndComplexification n) := by
  intro A B h
  apply (LinearMap.toMatrixAlgEquiv' : Module.End ℝ (Fin n → ℝ) ≃ₐ[ℝ] _).injective
  ext i j
  apply Complex.ofReal_injective
  have he := congrArg (fun T : Module.End ℂ (Fin n → ℂ) =>
    LinearMap.toMatrixAlgEquiv' T i j) h
  simpa only [realEndComplexification_matrix, Matrix.map_apply] using he

theorem complexEndRealPart_descent (B : Module.End ℂ (Fin n → ℂ))
    (hB : ∀ x, star (B x) = B (star x)) :
    realEndComplexification n (complexEndRealPart n B) = B := by
  apply (LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin n → ℂ) ≃ₐ[ℂ] _).injective
  ext i j
  rw [realEndComplexification_matrix]
  simp only [complexEndRealPart, LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv',
    Matrix.map_apply, LinearMap.toMatrixAlgEquiv'_apply]
  change ((B (Pi.single j 1) i).re : ℂ) = B (Pi.single j 1) i
  have hc := congrFun (hB (Pi.single j 1)) i
  have hi : (B (Pi.single j 1) i).im = 0 := by
    have hh := congrArg Complex.im hc
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_im] at hh
    have he : star (Pi.single j 1 : Fin n → ℂ) = Pi.single j 1 := by
      ext k
      simp [Pi.single_apply]
    rw [he] at hh
    linarith
  exact Complex.ext rfl (by simpa using hi.symm)

def complexContinuousExtension :
    ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) →ₐ[ℝ]
      ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :=
  ((Module.End.toContinuousLinearMap (𝕜 := ℂ) (Fin n → ℂ)).restrictScalars ℝ).toAlgHom.comp
    ((realEndComplexification n).comp
      (Module.End.toContinuousLinearMap (𝕜 := ℝ) (Fin n → ℝ)).symm.toAlgHom)

theorem realEndComplexification_exp (D : Module.End ℝ (Fin n → ℝ)) :
    realEndComplexification n
        ((NormedSpace.exp (LinearMap.toContinuousLinearMap D)).toLinearMap) =
      (NormedSpace.exp (LinearMap.toContinuousLinearMap
        (realEndComplexification n D))).toLinearMap := by
  let := NormedAlgebra.restrictScalars ℚ ℝ ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
  let := NormedAlgebra.restrictScalars ℚ ℂ ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
  have h := NormedSpace.map_exp (complexContinuousExtension n)
    (complexContinuousExtension n).toLinearMap.continuous_of_finiteDimensional
    (LinearMap.toContinuousLinearMap D)
  exact congrArg (fun T : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => T.toLinearMap) h

end PolycyclicRecognition

end

end OAI
