import OAI.Analysis.KadisonSimilarity.Tracial.MatrixSmallCorner
import OAI.Analysis.KadisonSimilarity.Tracial.TracialSmallCornerTransfer
import Mathlib.Data.Matrix.Basic

namespace OAI

/-! The matrix amplification of an included subfactor acts entrywise.
Commutation with the original subfactor therefore gives commutation with
the full matrix subfactor on the square array of standard copies. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  (φ : A →⋆ₐ[ℂ] B) {n : ℕ}

/-- The entrywise amplification of the actual subfactor embedding. -/
def matrixEntryHom : CStarMatrix (Fin n) (Fin n) A →⋆ₐ[ℂ]
    CStarMatrix (Fin n) (Fin n) B :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (({ φ.toAlgHom.mapMatrix with
      map_star' := fun X => by
        ext i j
        exact map_star φ (X j i) } :
      Matrix (Fin n) (Fin n) A →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) B).comp
      CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)

@[simp] theorem matrixEntryHom_apply (X : CStarMatrix (Fin n) (Fin n) A)
    (i j : Fin n) : matrixEntryHom φ X i j = φ (X i j) := rfl

theorem matrixEntryHom_injective (hφ : Function.Injective φ) :
    Function.Injective (matrixEntryHom (n := n) φ) := by
  intro X Y h
  ext i j
  apply hφ
  exact congrArg (fun Z : CStarMatrix (Fin n) (Fin n) B => Z i j) h

theorem normalizedMatrixTrace_entryHom
    [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] [NeZero n]
    (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
    (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    normalizedMatrixTrace τB n (matrixEntryHom φ X) = normalizedMatrixTrace τA n X := by
  simp only [normalizedMatrixTrace_apply, matrixEntryHom_apply, hφ]

/-- The common scalar matrix units belong to the included matrix subfactor. -/
theorem matrixEntryHom_cornerProjection (i : Fin n) :
    matrixEntryHom φ (matrixCornerProjection (A := A) i) =
      matrixCornerProjection (A := B) i := by
  ext j k
  simp only [matrixEntryHom_apply, matrixCornerProjection, CStarMatrix.ofMatrix_apply,
    Matrix.single_apply]
  split_ifs <;> simp only [map_one, map_zero]

variable [PartialOrder B] [StarOrderedRing B] [NeZero n]
  (τ : B →ₚ[ℂ] ℂ)

omit [NeZero n] in
/-- The array action can be read as a finite sum of operators on whole rows. -/
theorem matrixLeftArray_row (X : CStarMatrix (Fin n) (Fin n) B)
    (ξ : MatrixGNSArray τ n) (i : Fin n) :
    matrixLeftArray τ X ξ i = ∑ k, amplify (τ.gnsStarAlgHom (X i k)) n (ξ k) := by
  ext j
  simp only [matrixLeftArray_apply, WithLp.ofLp_sum, Finset.sum_apply, amplify_apply]

omit [NeZero n] in
/-- Entrywise commutation gives the full matrix-subfactor commutation. -/
theorem matrix_array_commutes_subfactor
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n)
    (hY : ∀ a : A, Y.comp (amplify (τ.gnsStarAlgHom (φ a)) n) =
      (amplify (τ.gnsStarAlgHom (φ a)) n).comp Y)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    (amplify Y n).comp (matrixLeftArray τ (matrixEntryHom φ X)) =
      (matrixLeftArray τ (matrixEntryHom φ X)).comp (amplify Y n) := by
  ext ξ i j
  change (Y (matrixLeftArray τ (matrixEntryHom φ X) ξ i)) j = _
  rw [matrixLeftArray_row, map_sum]
  change (∑ k, Y (amplify (τ.gnsStarAlgHom (φ (X i k))) n (ξ k))) j = _
  have he (k : Fin n) :
      Y (amplify (τ.gnsStarAlgHom (φ (X i k))) n (ξ k)) =
        amplify (τ.gnsStarAlgHom (φ (X i k))) n (Y (ξ k)) :=
    congrArg (fun T : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n => T (ξ k))
      (hY (X i k))
  simp_rw [he]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, amplify_apply, ContinuousLinearMap.comp_apply,
    matrixLeftArray_apply, matrixEntryHom_apply]

/-- The same commutation holds on the actual normalized matrix GNS space. -/
theorem matrix_gns_commutes_subfactor
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n)
    (hY : ∀ a : A, Y.comp (amplify (τ.gnsStarAlgHom (φ a)) n) =
      (amplify (τ.gnsStarAlgHom (φ a)) n).comp Y)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    (matrixGNSLiftOperator τ Y).comp
      ((normalizedMatrixTrace τ n).gnsStarAlgHom (matrixEntryHom φ X)) =
    ((normalizedMatrixTrace τ n).gnsStarAlgHom (matrixEntryHom φ X)).comp
      (matrixGNSLiftOperator τ Y) := by
  ext ξ
  apply (matrixGNSUnitary τ n).injective
  simp only [ContinuousLinearMap.comp_apply, matrixGNSLiftOperator_apply,
    matrixGNSUnitary_left]
  exact congrArg (fun T : MatrixGNSArray τ n →L[ℂ] MatrixGNSArray τ n =>
    T (matrixGNSUnitary τ n ξ)) (matrix_array_commutes_subfactor φ τ Y hY X)

/-- Projection comparison in the matrix subfactor extends the one-row
estimate to every projection of trace at most one over the matrix size. -/
theorem matrix_gns_all_small_corners
    [PartialOrder A] [StarOrderedRing A]
    (τA : A →ₚ[ℂ] ℂ) (hA : τA 1 = 1)
    (comparison : FiniteFactorProjectionComparison
      (fun X : CStarMatrix (Fin n) (Fin n) A => (normalizedMatrixTrace τA n X).re))
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n)
    (hY : ∀ a : A, Y.comp (amplify (τ.gnsStarAlgHom (φ a)) n) =
      (amplify (τ.gnsStarAlgHom (φ a)) n).comp Y)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ b : B, ‖commutator Y (amplify (τ.gnsStarAlgHom b) n)‖ ≤ ε * ‖b‖)
    (f : CStarMatrix (Fin n) (Fin n) A) (hf : IsStarProjection f)
    (ht : (normalizedMatrixTrace τA n f).re ≤ (n : ℝ)⁻¹) :
    ∀ z : CStarCorner (matrixEntryHom φ f) (hf.map (matrixEntryHom φ)),
      ‖commutator (matrixGNSLiftOperator τ Y)
        ((normalizedMatrixTrace τ n).gnsStarAlgHom (z : CStarMatrix (Fin n) (Fin n) B))‖ ≤
        ε * ‖z‖ := by
  let i : Fin n := 0
  have hetrace : (normalizedMatrixTrace τA n (matrixCornerProjection (A := A) i)).re =
      (n : ℝ)⁻¹ := by
    change (normalizedMatrixTrace τA n (CStarMatrix.ofMatrix (Matrix.single i i 1))).re = _
    rw [normalizedMatrixTrace_matrixUnit τA hA i]
    simp
  apply corner_commutator_bound_of_hom_comparison (matrixEntryHom φ)
    (normalizedMatrixTrace τ n).gnsStarAlgHom
    (fun X => (normalizedMatrixTrace τA n X).re) comparison
    (matrixCornerProjection i) f (matrixCornerProjection_isStarProjection i) hf
    (by rwa [hetrace]) (matrixGNSLiftOperator τ Y)
    (fun X => matrix_gns_commutes_subfactor φ τ Y hY X) hε
  intro z
  have he := matrixEntryHom_cornerProjection φ i
  let z' : CStarCorner (matrixCornerProjection (A := B) i)
      (matrixCornerProjection_isStarProjection i) :=
    ⟨z, ⟨by simpa only [← he] using z.property.1,
      by simpa only [← he] using z.property.2⟩⟩
  exact matrix_gns_small_corner_bound τ i Y hε hbound z'

end KadisonSimilarity

end

end OAI
