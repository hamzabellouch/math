import OAI.Analysis.KadisonKastler.CompletelyBounded
import OAI.Analysis.KadisonKastler.RectangularCorner
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Data.Matrix.Composition
import Mathlib.Tactic.FinCases

namespace OAI

/-!
# Contractivity of unital completely positive maps

The proofs use Mathlib's completely positive maps and the spectral order
on C⋆-matrices. The Schwarz inequality is obtained from positivity of a
two-by-two Gram matrix.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Every diagonal entry of a positive C⋆-matrix is positive. -/
theorem cstarMatrix_diagonal_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (M : CStarMatrix n n A) (hM : 0 ≤ M) (i : n) : 0 ≤ M i i := by
  rw [StarOrderedRing.nonneg_iff] at hM
  refine AddSubmonoid.closure_induction (fun X hX => ?_) (by simp)
    (fun X Y _ _ hX hY => ?_) hM
  · obtain ⟨X, rfl⟩ := hX
    simp only [CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply]
    exact Finset.sum_nonneg fun j _ => star_mul_self_nonneg _
  · exact add_nonneg hX hY

/-- The positive Gram matrix used for the Schwarz inequality. -/
def schwarzGram (a : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix !![star a * a, star a; a, 1]

theorem schwarzGram_nonneg (a : A) : 0 ≤ schwarzGram a := by
  let V : CStarMatrix (Fin 2) (Fin 2) A := CStarMatrix.ofMatrix !![a, 1; 0, 0]
  have hfactor : schwarzGram a = star V * V := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [schwarzGram, V, CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
        CStarMatrix.conjTranspose_apply, Fin.sum_univ_two]
  rw [hfactor]
  exact star_mul_self_nonneg _

/-- Complete positivity already forces preservation of the involution. -/
theorem completelyPositive_map_star (φ : A →CP B) (a : A) :
    φ (star a) = star (φ a) := by
  let P := (schwarzGram a).map φ
  have hP : 0 ≤ P := φ.map_cstarMatrix_nonneg _ (schwarzGram_nonneg a)
  have h := congrArg (fun N : CStarMatrix (Fin 2) (Fin 2) B => N 0 1) hP.star_eq
  simpa [P, schwarzGram, CStarMatrix.star_eq_conjTranspose,
    CStarMatrix.conjTranspose_apply] using h.symm

/-- Kadison–Schwarz for a unital completely positive map. -/
theorem unital_completelyPositive_schwarz (φ : A →CP B) (hφ : φ 1 = 1) (a : A) :
    star (φ a) * φ a ≤ φ (star a * a) := by
  let P := (schwarzGram a).map φ
  have hP : 0 ≤ P := φ.map_cstarMatrix_nonneg _ (schwarzGram_nonneg a)
  have hstar := completelyPositive_map_star φ a
  let D : CStarMatrix (Fin 2) (Fin 2) B :=
    CStarMatrix.ofMatrix !![1, 0; -(φ a), 0]
  have hnonneg := cstarMatrix_diagonal_nonneg (star D * P * D)
    (star_left_conjugate_nonneg hP D) 0
  have hentry : (star D * P * D) 0 0 = φ (star a * a) - star (φ a) * φ a := by
    simp [D, P, schwarzGram, CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
      CStarMatrix.conjTranspose_apply, Fin.sum_univ_two, hφ, hstar, sub_eq_add_neg]
  rw [hentry] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- A unital completely positive map is contractive. -/
theorem unital_completelyPositive_norm_le (φ : A →CP B) (hφ : φ 1 = 1) (a : A) :
    ‖φ a‖ ≤ ‖a‖ := by
  nontriviality B
  have horder := unital_completelyPositive_schwarz φ hφ a
  have hmono := CStarAlgebra.norm_le_norm_of_le_of_nonneg horder
    (star_mul_self_nonneg (φ a))
  have hpositive := PositiveLinearMap.norm_apply_le_of_nonneg
    (PositiveLinearMap.ofClass φ) (star a * a) (star_mul_self_nonneg a)
  change ‖φ (star a * a)‖ ≤ ‖φ 1‖ * ‖star a * a‖ at hpositive
  rw [hφ, norm_one, one_mul, CStarRing.norm_star_mul_self] at hpositive
  rw [CStarRing.norm_star_mul_self] at hmono
  nlinarith [norm_nonneg (φ a), norm_nonneg a]

/-- A unital completely positive map, bundled for the closed-range argument. -/
def unitalCompletelyPositiveToContinuousLinearMap (φ : A →CP B) (hφ : φ 1 = 1) :
    A →L[ℂ] B :=
  φ.toLinearMap.mkContinuous 1 (fun a => by
    change ‖φ a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using unital_completelyPositive_norm_le φ hφ a)

@[simp]
theorem unitalCompletelyPositiveToContinuousLinearMap_apply
    (φ : A →CP B) (hφ : φ 1 = 1) (a : A) :
    unitalCompletelyPositiveToContinuousLinearMap φ hφ a = φ a := rfl

/-- Flattening blocks of C⋆-matrices is a star-algebra equivalence. -/
def cstarMatrixComp (I J : Type*) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] :
    CStarMatrix I I (CStarMatrix J J A) ≃⋆ₐ[ℂ] CStarMatrix (I × J) (I × J) A :=
  { Matrix.compAlgEquiv I J A ℂ with
    map_smul' _ _ := rfl
    map_star' M := by
      ext i j
      rfl }

/-- A matrix amplification of a completely positive map is completely positive. -/
def completelyPositiveAmplification (φ : A →CP B) (n : Type*) [Fintype n] [DecidableEq n] :
    CStarMatrix n n A →CP CStarMatrix n n B where
  toLinearMap := CStarMatrix.mapₗ φ.toLinearMap
  map_cstarMatrix_nonneg' k M hM := by
    let eA := cstarMatrixComp (A := A) (Fin k) n
    let eB := cstarMatrixComp (A := B) (Fin k) n
    have hflat := φ.map_cstarMatrix_nonneg (eA M) (map_nonneg eA hM)
    have hback := map_nonneg eB.symm hflat
    have heq : eB.symm ((eA M).map φ) = M.map (CStarMatrix.mapₗ φ.toLinearMap) := by
      ext i j v w
      rfl
    rw [heq] at hback
    exact hback

/-- Every square amplification of a unital completely positive map is contractive. -/
theorem unital_completelyPositive_matrix_norm_le (φ : A →CP B) (hφ : φ 1 = 1)
    {n : Type*} [Fintype n] [DecidableEq n] (X : CStarMatrix n n A) :
    ‖CStarMatrix.mapₗ φ.toLinearMap X‖ ≤ ‖X‖ := by
  have hone : completelyPositiveAmplification φ n 1 = 1 := by
    ext i j
    change φ ((1 : CStarMatrix n n A) i j) =
      (1 : CStarMatrix n n B) i j
    by_cases hij : i = j
    · subst j
      simp [hφ]
    · simp [hij]
  exact unital_completelyPositive_norm_le (completelyPositiveAmplification φ n) hone X

theorem unital_completelyPositive_square_norm_le (φ : A →CP B) (hφ : φ 1 = 1)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) A) :
    ‖CStarMatrix.mapₗ φ.toLinearMap X‖ ≤ ‖X‖ :=
  unital_completelyPositive_matrix_norm_le φ hφ X

/-- Unital complete positivity implies complete contractivity with the
rectangular convention used in the multiplication-correction argument. -/
theorem unital_completelyPositive_completelyBoundedBy (φ : A →CP B) (hφ : φ 1 = 1) :
    CompletelyBoundedBy φ.toLinearMap 1 := by
  intro p q X
  have h := unital_completelyPositive_matrix_norm_le φ hφ (rectangularCorner X)
  rw [← rectangularCorner_map, norm_rectangularCorner, norm_rectangularCorner] at h
  simpa only [one_mul] using h

end

end KadisonKastler

end OAI
