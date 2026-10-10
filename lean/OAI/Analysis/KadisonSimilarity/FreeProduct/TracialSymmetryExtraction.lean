import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialSymmetryDilation
import OAI.Analysis.KadisonSimilarity.Tracial.FullColumnTheorem
import OAI.Analysis.KadisonSimilarity.Similarity.CompletelyBounded

namespace OAI

/-! The centered symmetry dilation is tested on actual finite Hilbert
arrays. Its original entry is recovered by coordinate insertion and
projection, both contractive. Thus no matrix-size factor enters the
commutator estimate. -/

noncomputable section
namespace KadisonSimilarity

open HochschildMatrixDilation

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- An off-diagonal block of an operator on finite Hilbert arrays. -/
def matrixEntryCompression {n m : ℕ} (i : Fin m) (j : Fin n)
    (T : HilbertCopies H n →L[ℂ] HilbertCopies K m) : H →L[ℂ] K :=
  (PiLp.proj 2 (fun _ : Fin m => K) i).comp (T.comp (copyInsert j))

@[simp] theorem matrixEntryCompression_apply {n m : ℕ} (i : Fin m) (j : Fin n)
    (T : HilbertCopies H n →L[ℂ] HilbertCopies K m) (x : H) :
    matrixEntryCompression i j T x = T (PiLp.single 2 j x) i := rfl

/-- Coordinate compression is contractive, independently of the array sizes. -/
theorem norm_matrixEntryCompression_le {n m : ℕ} (i : Fin m) (j : Fin n)
    (T : HilbertCopies H n →L[ℂ] HilbertCopies K m) :
    ‖matrixEntryCompression i j T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  calc
    ‖matrixEntryCompression i j T x‖ = ‖T (PiLp.single 2 j x) i‖ := rfl
    _ ≤ ‖T (PiLp.single 2 j x)‖ := PiLp.norm_apply_le (T (PiLp.single 2 j x)) i
    _ ≤ ‖T‖ * ‖(PiLp.single 2 j x : HilbertCopies H n)‖ :=
      T.le_opNorm (PiLp.single 2 j x)
    _ = ‖T‖ * ‖x‖ := by rw [PiLp.norm_single]

@[simp] theorem matrixEntryCompression_matrixOperator {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) (i j : Fin n) :
    matrixEntryCompression i j (matrixOperator X) = X i j := by
  ext x
  simp [matrixEntryCompression_apply, matrixOperator_apply, PiLp.single_apply, apply_ite]

theorem matrixEntryCompression_commutator {n : ℕ}
    (Y : H →L[ℂ] H) (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) (i j : Fin n) :
    matrixEntryCompression i j (commutator (amplify Y n) (matrixOperator X)) =
      commutator Y (X i j) := by
  rw [commutator_amplify_matrixOperator]
  exact matrixEntryCompression_matrixOperator (fun p q => commutator Y (X p q)) i j

/-- Every matrix-entry commutator is a genuine corner of the amplified one. -/
theorem norm_entry_commutator_le {n : ℕ}
    (Y : H →L[ℂ] H) (X : Matrix (Fin n) (Fin n) (H →L[ℂ] H)) (i j : Fin n) :
    ‖commutator Y (X i j)‖ ≤ ‖commutator (amplify Y n) (matrixOperator X)‖ := by
  rw [← matrixEntryCompression_commutator Y X i j]
  exact norm_matrixEntryCompression_le i j _

variable [CompleteSpace H]
variable {A : Type*} [CStarAlgebra A]

/-- A C-star matrix acts entrywise on actual finite Hilbert sums. -/
def representedMatrix (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {n : ℕ}
    (X : CStarMatrix (Fin n) (Fin n) A) :
    HilbertCopies H n →L[ℂ] HilbertCopies H n :=
  matrixOperator (fun i j => σ (X i j))

/-- Entrywise application of the original representation to ordinary matrices. -/
def entryMatrixHom (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (n : ℕ) :
    Matrix (Fin n) (Fin n) A →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) (H →L[ℂ] H) where
  toAlgHom := σ.toAlgHom.mapMatrix
  map_star' X := by
    apply Matrix.ext
    intro i j
    change σ (star (X j i)) = star (σ (X j i))
    exact map_star σ (X j i)

/-- The concrete matrix action is a unital star representation. -/
def representedMatrixHom (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (n : ℕ) :
    CStarMatrix (Fin n) (Fin n) A →⋆ₐ[ℂ]
      (HilbertCopies H n →L[ℂ] HilbertCopies H n) :=
  ((operatorMatrixRepresentation n).comp (entryMatrixHom σ n)).comp
    CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom

@[simp] theorem representedMatrixHom_apply (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) {n : ℕ}
    (X : CStarMatrix (Fin n) (Fin n) A) :
    representedMatrixHom σ n X = representedMatrix σ X := rfl

/-- The four-by-four dilation acts on two successive two-coordinate sums. -/
def representedDoubleMatrix (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S : Mat (Mat A)) :
    HilbertCopies (HilbertCopies H 2) 2 →L[ℂ] HilbertCopies (HilbertCopies H 2) 2 :=
  matrixOperator (fun i j => representedMatrix σ (S i j))

@[simp] theorem representedDoubleMatrix_apply (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S : Mat (Mat A)) (x : HilbertCopies (HilbertCopies H 2) 2) (i k : Fin 2) :
    representedDoubleMatrix σ S x i k = ∑ j : Fin 2, ∑ l : Fin 2, σ (S i j k l) (x j l) := by
  simp [representedDoubleMatrix, representedMatrix, matrixOperator]

/-- Two successive coordinate corners recover each original algebra entry. -/
theorem double_matrix_commutator_corner (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Y : H →L[ℂ] H) (S : Mat (Mat A)) (i j k l : Fin 2) :
    matrixEntryCompression k l (matrixEntryCompression i j
      (commutator (amplify (amplify Y 2) 2) (representedDoubleMatrix σ S))) =
      commutator Y (σ (S i j k l)) := by
  have hout := matrixEntryCompression_commutator (amplify Y 2)
    (fun p q => representedMatrix σ (S p q)) i j
  have hin := matrixEntryCompression_commutator Y (fun p q => σ (S i j p q)) k l
  change matrixEntryCompression k l
    (matrixEntryCompression i j
      (commutator (amplify (amplify Y 2) 2)
        (matrixOperator (fun p q => representedMatrix σ (S p q))))) = _
  rw [hout]
  exact hin

/-- The double compression has norm at most one. -/
theorem norm_double_entry_commutator_le (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Y : H →L[ℂ] H) (S : Mat (Mat A)) (i j k l : Fin 2) :
    ‖commutator Y (σ (S i j k l))‖ ≤
      ‖commutator (amplify (amplify Y 2) 2) (representedDoubleMatrix σ S)‖ := by
  rw [← double_matrix_commutator_corner σ Y S i j k l]
  exact (norm_matrixEntryCompression_le k l _).trans
    (norm_matrixEntryCompression_le i j _)

variable [PartialOrder A] [StarOrderedRing A]

/-- The original commutator is exactly the designated double corner of the
centered symmetry's commutator. -/
theorem centered_symmetry_commutator_corner (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Y : H →L[ℂ] H) (a : A) (ha : ‖a‖ ≤ 1) :
    matrixEntryCompression 0 1 (matrixEntryCompression 0 1
      (commutator (amplify (amplify Y 2) 2)
        (representedDoubleMatrix σ (contractionSymmetryUnitary a ha)))) =
      commutator Y (σ a) := by
  rw [double_matrix_commutator_corner, contractionSymmetryUnitary_entry]

/-- Testing the actual four-by-four centered symmetry controls the original
contraction, with constant one. -/
theorem norm_commutator_le_centered_symmetry (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (Y : H →L[ℂ] H) (a : A) (ha : ‖a‖ ≤ 1) :
    ‖commutator Y (σ a)‖ ≤
      ‖commutator (amplify (amplify Y 2) 2)
        (representedDoubleMatrix σ (contractionSymmetryUnitary a ha))‖ := by
  simpa only [contractionSymmetryUnitary_entry] using
    norm_double_entry_commutator_le σ Y (contractionSymmetryUnitary a ha) 0 1 0 1

/-- In particular, a matrix commutator in the original amplification is
recovered from the centered symmetry over that matrix algebra. -/
theorem norm_amplified_commutator_le_centered_symmetry
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (Y : H →L[ℂ] H) {n : ℕ} [NeZero n]
    (X : CStarMatrix (Fin n) (Fin n) A) (hX : ‖X‖ ≤ 1) :
    ‖commutator (amplify Y n) (representedMatrix σ X)‖ ≤
      ‖commutator (amplify (amplify (amplify Y n) 2) 2)
        (representedDoubleMatrix (representedMatrixHom σ n)
          (contractionSymmetryUnitary X hX))‖ :=
  norm_commutator_le_centered_symmetry (representedMatrixHom σ n) (amplify Y n) X hX

end KadisonSimilarity

end

end OAI
