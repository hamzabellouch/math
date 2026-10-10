import OAI.Analysis.BoundedHochschild.DoubleCoordinates
import OAI.Analysis.BoundedHochschild.MatrixFunctionalDilation

namespace OAI

/-! Recover the original linear map from the off-diagonal corner of its
positive two-by-two extension. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
lemma paulsen_single_mem (a : A) :
    singleCStarMatrix (0 : Fin 2) 1 a ∈ paulsenSystem A := by
  refine ⟨0, 0, ?_, ?_⟩ <;> simp [singleCStarMatrix, Matrix.single]

omit [PartialOrder A] [StarOrderedRing A] in
lemma paulsenLinear_single (f : A →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] (H →L[ℂ] H)) (a : A) :
    paulsenLinear f T (singleCStarMatrix (0 : Fin 2) 1 a) =
      singleCStarMatrix (0 : Fin 2) 1 (T a) := by
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [paulsenLinear, singleCStarMatrix, Matrix.single, starConjugateLinear]

lemma paulsenExtension_entry (f : A →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] (H →L[ℂ] H))
    (Φ : CompletelyPositiveMap (Mat A) (HilbertDouble H →L[ℂ] HilbertDouble H))
    (hΦ : ∀ X : paulsenSystem A, Φ (X : Mat A) = paulsenOperatorMap f T X) (a : A) :
    (doubleCoordinate (H := H) 0).toContinuousLinearMap.adjoint.comp
      ((Φ (singleCStarMatrix (0 : Fin 2) 1 a)).comp
        (doubleCoordinate 1).toContinuousLinearMap) = T a := by
  have he := hΦ ⟨singleCStarMatrix (0 : Fin 2) 1 a, paulsen_single_mem a⟩
  change Φ (singleCStarMatrix (0 : Fin 2) 1 a) =
    doubleMatrixHom (H := H) (paulsenLinear f T (singleCStarMatrix 0 1 a)) at he
  rw [he, paulsenLinear_single]
  rw [doubleCoordinate_extract]
  exact Matrix.single_apply_same _ _ _

omit [PartialOrder A] [StarOrderedRing A] in
lemma single_offDiagonal_factor (a : A) : singleCStarMatrix (0 : Fin 2) 1 a =
    matrixScalarHom 2 a * singleCStarMatrix (0 : Fin 2) 1 (1 : A) := by
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [singleCStarMatrix, Matrix.single, CStarMatrix.mul_apply]

lemma single_offDiagonal_norm_le_one [Nontrivial A] :
    ‖singleCStarMatrix (0 : Fin 2) 1 (1 : A)‖ ≤ 1 := by
  let E := singleCStarMatrix (0 : Fin 2) 1 (1 : A)
  have he : star E * E = diag (0 : A) 1 := by
    apply CStarMatrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [E, singleCStarMatrix, Matrix.single, diag, CStarMatrix.mul_apply,
        CStarMatrix.star_apply]
  have hn : ‖E‖ ^ 2 ≤ 1 := by
    rw [pow_two, ← CStarRing.norm_star_mul_self, he]
    simpa using norm_diag_le (0 : A) 1
  exact (sq_le_one_iff₀ (norm_nonneg E)).mp hn

end BoundedHochschild.KadisonRingrose

end

end OAI
