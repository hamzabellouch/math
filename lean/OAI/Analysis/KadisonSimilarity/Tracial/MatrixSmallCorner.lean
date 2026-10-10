import OAI.Analysis.KadisonSimilarity.Tracial.MatrixTracialGNS
import OAI.Analysis.KadisonSimilarity.Representation.CStarCorner

namespace OAI

/-! The distinguished scalar matrix corner has the original algebra's
commutator estimate on a finite standard multiplicity. The proof uses
actual coordinate insertion/projection and then transports the estimate
to the normalized matrix GNS space. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Place one operator in a diagonal coordinate of a Hilbert array. -/
def coordinateCornerOperator {n : ℕ} (i : Fin n) (T : H →L[ℂ] H) :
    HilbertCopies H n →L[ℂ] HilbertCopies H n :=
  (copyInsert i).comp (T.comp (PiLp.proj 2 (fun _ : Fin n => H) i))

@[simp] theorem coordinateCornerOperator_apply {n : ℕ} (i : Fin n) (T : H →L[ℂ] H)
    (ξ : HilbertCopies H n) :
    coordinateCornerOperator i T ξ = PiLp.single 2 i (T (ξ i)) := rfl

/-- A diagonal coordinate placement is contractive. -/
theorem norm_coordinateCornerOperator_le {n : ℕ} (i : Fin n) (T : H →L[ℂ] H) :
    ‖coordinateCornerOperator i T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro ξ
  rw [coordinateCornerOperator_apply, PiLp.norm_single]
  exact (T.le_opNorm (ξ i)).trans
    (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le ξ i) (norm_nonneg T))

/-- A diagonal amplification preserves each coordinate corner. -/
theorem commutator_coordinateCornerOperator {n : ℕ} (i : Fin n)
    (Y T : H →L[ℂ] H) :
    commutator (amplify Y n) (coordinateCornerOperator i T) =
      coordinateCornerOperator i (commutator Y T) := by
  ext ξ j
  by_cases h : j = i
  · subst j
    simp [commutator, coordinateCornerOperator_apply, amplify_apply]
  · simp [commutator, coordinateCornerOperator_apply, amplify_apply, h]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {n : ℕ} [NeZero n]

/-- A diagonal scalar matrix unit in the actual C-star matrix algebra. -/
def matrixCornerProjection (i : Fin n) : CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrix (Matrix.single i i 1)

omit [PartialOrder A] [StarOrderedRing A] [NeZero n] in
theorem matrixCornerProjection_isStarProjection (i : Fin n) :
    IsStarProjection (matrixCornerProjection (A := A) i) := by
  let E : Matrix (Fin n) (Fin n) A ≃⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A :=
    CStarMatrix.ofMatrixStarAlgEquiv
  constructor
  · change E (Matrix.single i i 1) * E (Matrix.single i i 1) = E (Matrix.single i i 1)
    rw [← map_mul]
    congr 1
    simp
  · change star (E (Matrix.single i i 1)) = E (Matrix.single i i 1)
    rw [← map_star]
    congr 1
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, star_one]

omit [PartialOrder A] [StarOrderedRing A] [NeZero n] in
theorem matrixCornerProjection_sandwich (i : Fin n)
    (X : CStarMatrix (Fin n) (Fin n) A) :
    matrixCornerProjection i * X * matrixCornerProjection i =
      CStarMatrix.ofMatrix (Matrix.single i i (X i i)) := by
  apply CStarMatrix.ofMatrix.symm.injective
  change Matrix.single i i (1 : A) * CStarMatrix.ofMatrix.symm X * Matrix.single i i 1 =
    Matrix.single i i (X i i)
  simpa only [one_mul, mul_one, CStarMatrix.ofMatrix_symm_apply] using
    (Matrix.single_mul_mul_single i i i i (1 : A) (CStarMatrix.ofMatrix.symm X) 1)

omit [NeZero n] in
/-- There is only one possibly nonzero entry in the distinguished corner. -/
theorem matrixCorner_eq_single (i : Fin n)
    (X : CStarCorner (matrixCornerProjection (A := A) i)
      (matrixCornerProjection_isStarProjection i)) :
    (X : CStarMatrix (Fin n) (Fin n) A) = CStarMatrix.ofMatrix (Matrix.single i i (X.val i i)) := by
  have hs := matrixCornerProjection_sandwich (A := A) i
    (X : CStarMatrix (Fin n) (Fin n) A)
  rw [X.property.1, X.property.2] at hs
  exact hs

omit [NeZero n] in
theorem matrixLeftArray_single (τ : A →ₚ[ℂ] ℂ) (i : Fin n) (a : A) :
    matrixLeftArray τ (CStarMatrix.ofMatrix (Matrix.single i i a)) =
      coordinateCornerOperator i (amplify (τ.gnsStarAlgHom a) n) := by
  ext ξ j k
  by_cases h : j = i
  · subst j
    simp [matrixLeftArray_apply, Matrix.single_apply, apply_ite, ite_apply, amplify_apply,
      coordinateCornerOperator_apply]
  · simp [matrixLeftArray_apply, coordinateCornerOperator_apply, h, Ne.symm h]

omit [NeZero n] in
/-- The concrete distinguished corner estimate on ordinary Hilbert arrays. -/
theorem matrix_array_small_corner_bound (τ : A →ₚ[ℂ] ℂ) (i : Fin n)
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ a : A, ‖commutator Y (amplify (τ.gnsStarAlgHom a) n)‖ ≤ ε * ‖a‖)
    (X : CStarCorner (matrixCornerProjection (A := A) i)
      (matrixCornerProjection_isStarProjection i)) :
    ‖commutator (amplify Y n) (matrixLeftArray τ (X : CStarMatrix (Fin n) (Fin n) A))‖ ≤
      ε * ‖X‖ := by
  rw [matrixCorner_eq_single i X, matrixLeftArray_single, commutator_coordinateCornerOperator]
  calc
    _ ≤ ‖commutator Y (amplify (τ.gnsStarAlgHom (X.val i i)) n)‖ :=
      norm_coordinateCornerOperator_le i _
    _ ≤ ε * ‖X.val i i‖ := hbound _
    _ ≤ ε * ‖X‖ := mul_le_mul_of_nonneg_left
      (CStarMatrix.norm_entry_le_norm (M := X.val)) hε

/-- The amplified standard-copy operator transported to matrix GNS. -/
def matrixGNSLiftOperator (τ : A →ₚ[ℂ] ℂ)
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n) :
    (normalizedMatrixTrace τ n).GNS →L[ℂ] (normalizedMatrixTrace τ n).GNS :=
  (matrixGNSUnitary τ n).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((amplify Y n).comp (matrixGNSUnitary τ n).toContinuousLinearEquiv.toContinuousLinearMap)

theorem matrixGNSLiftOperator_apply (τ : A →ₚ[ℂ] ℂ)
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n)
    (ξ : (normalizedMatrixTrace τ n).GNS) :
    matrixGNSUnitary τ n (matrixGNSLiftOperator τ Y ξ) =
      amplify Y n (matrixGNSUnitary τ n ξ) := by
  simp only [matrixGNSLiftOperator, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.apply_symm_apply]

/-- The transported commutator has precisely the array action. -/
theorem matrixGNSLiftOperator_commutator (τ : A →ₚ[ℂ] ℂ)
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n)
    (X : CStarMatrix (Fin n) (Fin n) A) (ξ : (normalizedMatrixTrace τ n).GNS) :
    matrixGNSUnitary τ n
      (commutator (matrixGNSLiftOperator τ Y) ((normalizedMatrixTrace τ n).gnsStarAlgHom X) ξ) =
    commutator (amplify Y n) (matrixLeftArray τ X) (matrixGNSUnitary τ n ξ) := by
  simp only [commutator, sub_apply, mul_apply_eq_comp,
    map_sub, matrixGNSLiftOperator_apply, matrixGNSUnitary_left]

/-- The distinguished-corner estimate on the actual normalized matrix GNS space. -/
theorem matrix_gns_small_corner_bound (τ : A →ₚ[ℂ] ℂ) (i : Fin n)
    (Y : HilbertCopies τ.GNS n →L[ℂ] HilbertCopies τ.GNS n)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ a : A, ‖commutator Y (amplify (τ.gnsStarAlgHom a) n)‖ ≤ ε * ‖a‖)
    (X : CStarCorner (matrixCornerProjection (A := A) i)
      (matrixCornerProjection_isStarProjection i)) :
    ‖commutator (matrixGNSLiftOperator τ Y)
      ((normalizedMatrixTrace τ n).gnsStarAlgHom (X : CStarMatrix (Fin n) (Fin n) A))‖ ≤
      ε * ‖X‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hε (norm_nonneg X))
  intro ξ
  calc
    _ = ‖matrixGNSUnitary τ n
        (commutator (matrixGNSLiftOperator τ Y)
          ((normalizedMatrixTrace τ n).gnsStarAlgHom (X : CStarMatrix (Fin n) (Fin n) A)) ξ)‖ :=
      ((matrixGNSUnitary τ n).norm_map _).symm
    _ = ‖commutator (amplify Y n) (matrixLeftArray τ X) (matrixGNSUnitary τ n ξ)‖ :=
      congrArg norm (matrixGNSLiftOperator_commutator τ Y X ξ)
    _ ≤ ‖commutator (amplify Y n) (matrixLeftArray τ X)‖ * ‖matrixGNSUnitary τ n ξ‖ :=
      (commutator (amplify Y n) (matrixLeftArray τ X)).le_opNorm _
    _ ≤ (ε * ‖X‖) * ‖ξ‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (matrix_array_small_corner_bound τ i Y hε hbound X)
        (norm_nonneg ξ)

end KadisonSimilarity

end

end OAI
