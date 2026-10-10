import OAI.Analysis.BoundedHochschild.PaulsenSystem
import OAI.Analysis.BoundedHochschild.FlipMatrixNesting

namespace OAI

/-! Identify amplified two-by-two operator systems with scalar-diagonal blocks. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma positiveBlock_zero_zero (p q x : A) : positiveBlock p q x 0 0 = p := by
  simp [positiveBlock, diag, offdiag]
lemma positiveBlock_zero_one (p q x : A) : positiveBlock p q x 0 1 = x := by
  simp [positiveBlock, diag, offdiag]
lemma positiveBlock_one_zero (p q x : A) : positiveBlock p q x 1 0 = star x := by
  simp [positiveBlock, diag, offdiag]
lemma positiveBlock_one_one (p q x : A) : positiveBlock p q x 1 1 = q := by
  simp [positiveBlock, diag, offdiag]

lemma paulsen_scalar_coefficient (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1) (z : ℂ) :
    f (algebraMap ℂ A z) = z := by
  simp [Algebra.algebraMap_eq_smul_one, hf]

lemma paulsen_diagonal_coefficient (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1)
    (X : paulsenSystem A) (i : Fin 2) :
    algebraMap ℂ A (f (X.val i i)) = X.val i i := by
  obtain ⟨z, w, hz, hw⟩ := X.property
  fin_cases i
  · exact (congrArg (fun a => algebraMap ℂ A (f a)) hz).trans
      ((congrArg (algebraMap ℂ A) (paulsen_scalar_coefficient f hf z)).trans hz.symm)
  · exact (congrArg (fun a => algebraMap ℂ A (f a)) hw).trans
      ((congrArg (algebraMap ℂ A) (paulsen_scalar_coefficient f hf w)).trans hw.symm)

variable [PartialOrder A] [StarOrderedRing A]

def paulsenMatrixDiagonal (f : A →ₗ[ℂ] ℂ) {n : ℕ} (i : Fin 2)
    (X : operatorSystemMatrices (paulsenSystem A) n) : CStarMatrix (Fin n) (Fin n) ℂ :=
  CStarMatrix.ofMatrix (fun p q => f (X.val p q i i))

def paulsenMatrixUpper {n : ℕ} (X : operatorSystemMatrices (paulsenSystem A) n) :
    CStarMatrix (Fin n) (Fin n) A := CStarMatrix.ofMatrix (fun p q => X.val p q 0 1)

lemma paulsenMatrix_lower {n : ℕ} (X : operatorSystemMatrices (paulsenSystem A) n)
    (hX : 0 ≤ X.val) (i j : Fin n) : X.val i j 1 0 = star (X.val j i 0 1) := by
  exact (congrArg (fun Y : CStarMatrix (Fin n) (Fin n) (Mat A) => Y i j 1 0)
    hX.isSelfAdjoint.star_eq).symm

lemma paulsenMatrix_source_block (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1) {n : ℕ}
    (X : operatorSystemMatrices (paulsenSystem A) n) (hX : 0 ≤ X.val) :
    flipMatrixNesting n 2 X.val = positiveBlock
      (scalarMatrixHom A n (paulsenMatrixDiagonal f 0 X))
      (scalarMatrixHom A n (paulsenMatrixDiagonal f 1 X)) (paulsenMatrixUpper X) := by
  let p := scalarMatrixHom A n (paulsenMatrixDiagonal f 0 X)
  let q := scalarMatrixHom A n (paulsenMatrixDiagonal f 1 X)
  let x := paulsenMatrixUpper X
  apply CStarMatrix.ext
  intro d e
  apply CStarMatrix.ext
  intro i j
  fin_cases d <;> fin_cases e
  · exact (paulsen_diagonal_coefficient f hf ⟨X.val i j, X.property i j⟩ 0).symm.trans
      (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) A => Z i j)
        (positiveBlock_zero_zero p q x)).symm
  · exact (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) A => Z i j)
      (positiveBlock_zero_one p q x)).symm
  · exact (paulsenMatrix_lower X hX i j).trans
      (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) A => Z i j)
        (positiveBlock_one_zero p q x)).symm
  · exact (paulsen_diagonal_coefficient f hf ⟨X.val i j, X.property i j⟩ 1).symm.trans
      (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) A => Z i j)
        (positiveBlock_one_one p q x)).symm

variable [PartialOrder B] [StarOrderedRing B]

lemma paulsenMatrix_target_block (f : A →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] B) {n : ℕ}
    (X : operatorSystemMatrices (paulsenSystem A) n) (hX : 0 ≤ X.val) :
    flipMatrixNesting n 2 (operatorSystemAmplification (paulsenSystem A)
      (paulsenSystemMap f T) n X) = positiveBlock
      (scalarMatrixHom B n (paulsenMatrixDiagonal f 0 X))
      (scalarMatrixHom B n (paulsenMatrixDiagonal f 1 X)) ((paulsenMatrixUpper X).map T) := by
  let p := scalarMatrixHom B n (paulsenMatrixDiagonal f 0 X)
  let q := scalarMatrixHom B n (paulsenMatrixDiagonal f 1 X)
  let x := (paulsenMatrixUpper X).map T
  apply CStarMatrix.ext
  intro d e
  apply CStarMatrix.ext
  intro i j
  fin_cases d <;> fin_cases e
  · exact (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) B => Z i j)
      (positiveBlock_zero_zero p q x)).symm
  · exact (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) B => Z i j)
      (positiveBlock_zero_one p q x)).symm
  · have hh : star (T (star (X.val i j 1 0))) = star (T (X.val j i 0 1)) := by
      have h := congrArg (fun a => star (T (star a))) (paulsenMatrix_lower X hX i j)
      simpa only [star_star] using h
    exact hh.trans (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) B => Z i j)
      (positiveBlock_one_zero p q x)).symm
  · exact (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) B => Z i j)
      (positiveBlock_one_one p q x)).symm

end BoundedHochschild.KadisonRingrose

end

end OAI
