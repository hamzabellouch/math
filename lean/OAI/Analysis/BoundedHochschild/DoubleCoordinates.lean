import OAI.Analysis.BoundedHochschild.PaulsenExtension

namespace OAI

/-! Coordinate isometries in the doubled Hilbert space and extraction of
operator matrix entries. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def doubleCoordinate (i : Fin 2) : H →ₗᵢ[ℂ] HilbertDouble H where
  toFun ξ := PiLp.single 2 i ξ
  map_add' ξ η := PiLp.single_add 2 i
  map_smul' z ξ := by
    apply PiLp.ext
    intro j
    simp [PiLp.single_apply]
  norm_map' ξ := by simp

omit [CompleteSpace H] in
lemma doubleCoordinate_inner (i : Fin 2) (ξ : H) (η : HilbertDouble H) :
    inner ℂ (doubleCoordinate i ξ) η = inner ℂ ξ (η i) := by
  fin_cases i
  all_goals
    simp [doubleCoordinate, PiLp.inner_apply, PiLp.single_apply]

@[simp] lemma doubleCoordinate_adjoint (i : Fin 2) (η : HilbertDouble H) :
    (doubleCoordinate i).toContinuousLinearMap.adjoint η = η i := by
  apply ext_inner_left ℂ
  intro ξ
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact doubleCoordinate_inner i ξ η

lemma doubleCoordinate_extract (i j : Fin 2) (Q : Mat (H →L[ℂ] H)) :
    (doubleCoordinate i).toContinuousLinearMap.adjoint.comp
      ((doubleMatrixHom (H := H) Q).comp
        (doubleCoordinate j).toContinuousLinearMap) = Q i j := by
  apply ContinuousLinearMap.ext
  intro ξ
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    doubleCoordinate_adjoint]
  exact WeakPureInfiniteness.matrixOperator_single Q i j ξ

end BoundedHochschild.KadisonRingrose

end

end OAI
