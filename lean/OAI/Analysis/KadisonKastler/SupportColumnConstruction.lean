import OAI.Analysis.KadisonKastler.ScalarAmplification
import OAI.Analysis.KadisonKastler.RectangularOperator
import Mathlib.Data.Matrix.Basis

namespace OAI

/-! # A one-column partial isometry for a small diagonal support -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A l m n k : Type*} [Ring A] [StarRing A]
variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

/-- A single entry in a rectangular C⋆-matrix. -/
def matrixEntry (i : m) (j : n) (a : A) : CStarMatrix m n A :=
  CStarMatrix.ofMatrix (Matrix.single i j a)

omit [StarRing A] in
@[simp]
theorem matrixEntry_zero (i : m) (j : n) : matrixEntry i j (0 : A) = 0 := by
  apply CStarMatrix.ext
  intro u v
  simp [matrixEntry, Matrix.single]

@[simp]
theorem matrixEntry_conjTranspose (i : m) (j : n) (a : A) :
    (matrixEntry i j a).conjTranspose = matrixEntry j i (star a) := by
  exact Matrix.conjTranspose_single i j a

omit [StarRing A] in
theorem matrixEntry_mul [Fintype m] (i : l) (j j' : m) (v : n) (a b : A) :
    matrixEntry i j a * matrixEntry j' v b =
      if j = j' then matrixEntry i v (a * b) else 0 := by
  by_cases h : j = j'
  · subst j'
    exact (Matrix.single_mul_single_same a i j v b).trans (ite_eq_left rfl).symm
  · exact (Matrix.single_mul_single_of_ne a i j j' h b).trans (ite_eq_right h).symm

/-- A finite orthogonal family of projections has a projection as its sum. -/
theorem isStarProjection_fintype_sum {B τ : Type*} [Ring B] [StarRing B] [Fintype τ]
    (P : τ → B) (hP : ∀ t, IsStarProjection (P t))
    (horth : ∀ s t, s ≠ t → P s * P t = 0) : IsStarProjection (∑ t, P t) := by
  classical
  constructor
  · change (∑ t, P t) * (∑ t, P t) = ∑ t, P t
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum, Finset.sum_eq_single s]
    · exact (hP s).isIdempotentElem.eq
    · intro t _ hts
      exact horth s t (Ne.symm hts)
    · simp
  · change star (∑ t, P t) = ∑ t, P t
    simp only [star_sum, (hP _).isSelfAdjoint.star_eq]

variable [Fintype m] [Fintype k] [DecidableEq k] [Algebra ℂ A] [StarModule ℂ A]

/-- The diagonal atom labelled by a row and a matrix-unit index. -/
def supportAtom (E : Generator.MatrixUnitSystem k A) (s : m × k) : CStarMatrix m m A :=
  matrixEntry s.1 s.1 (E.entry s.2 s.2)

omit [StarModule ℂ A] in
theorem supportAtom_projection (E : Generator.MatrixUnitSystem k A) (s : m × k) :
    IsStarProjection (supportAtom E s) := by
  constructor
  · change supportAtom E s * supportAtom E s = supportAtom E s
    simp [supportAtom, matrixEntry_mul, E.mul_entry]
  · change star (supportAtom E s) = supportAtom E s
    simp [supportAtom, CStarMatrix.star_eq_conjTranspose, E.star_entry]

omit [StarModule ℂ A] in
theorem supportAtom_orthogonal (E : Generator.MatrixUnitSystem k A)
    (s t : m × k) (hst : s ≠ t) : supportAtom E s * supportAtom E t = 0 := by
  by_cases hi : s.1 = t.1
  · have ha : s.2 ≠ t.2 := fun h => hst (Prod.ext hi h)
    simp [supportAtom, matrixEntry_mul, hi, E.mul_entry, ha]
  · simp [supportAtom, matrixEntry_mul, hi]

omit [StarModule ℂ A] in
/-- All diagonal row-label atoms form a partition of the identity. -/
theorem supportAtom_total (E : Generator.MatrixUnitSystem k A) :
    (∑ s : m × k, supportAtom E s) = 1 := by
  apply CStarMatrix.ext
  intro i j
  change (∑ s : m × k, Matrix.single s.1 s.1 (E.entry s.2 s.2)) i j = _
  simp only [Matrix.sum_apply, Fintype.sum_prod_type]
  by_cases hij : i = j
  · subst j
    simpa [Matrix.single] using E.total
  · have hx (x : m) : ¬ (x = i ∧ x = j) := fun h => hij (h.1.symm.trans h.2)
    simp [Matrix.single, hx, hij]

/-- The projection onto a set of diagonal row-label atoms. -/
def supportProjection (E : Generator.MatrixUnitSystem k A) (S : Finset (m × k)) :
    CStarMatrix m m A := ∑ s : S, supportAtom E s.val

omit [Fintype m] [StarModule ℂ A] in
theorem supportProjection_eq_sum (E : Generator.MatrixUnitSystem k A)
    (S : Finset (m × k)) : supportProjection E S = ∑ s ∈ S, supportAtom E s :=
  Finset.sum_coe_sort S (supportAtom E)

omit [StarModule ℂ A] in
theorem supportProjection_isStarProjection (E : Generator.MatrixUnitSystem k A)
    (S : Finset (m × k)) : IsStarProjection (supportProjection E S) :=
  isStarProjection_fintype_sum _ (fun s => supportAtom_projection E s.val)
    (fun s t hst => supportAtom_orthogonal E s.val t.val (Subtype.coe_injective.ne hst))

/-- The column sends distinct support atoms to distinct diagonal matrix-unit labels. -/
def supportColumn (E : Generator.MatrixUnitSystem k A) (S : Finset (m × k))
    (f : S ↪ k) : CStarMatrix m (Fin 1) A :=
  ∑ s : S, matrixEntry s.val.1 0 (E.entry s.val.2 (f s))

omit [Fintype m] [StarModule ℂ A] in
theorem supportColumn_atom_mul (E : Generator.MatrixUnitSystem k A) (S : Finset (m × k))
    (f : S ↪ k) (s t : S) :
    matrixEntry s.val.1 (0 : Fin 1) (E.entry s.val.2 (f s)) *
        (matrixEntry t.val.1 (0 : Fin 1) (E.entry t.val.2 (f t))).conjTranspose =
      if s = t then supportAtom E s.val else 0 := by
  rw [matrixEntry_conjTranspose, E.star_entry, matrixEntry_mul]
  simp only [↓reduceIte]
  by_cases h : s = t
  · subst t
    simp [supportAtom, E.mul_entry]
  · have hf : f s ≠ f t := fun he => h (f.injective he)
    simp [E.mul_entry, hf, h]

omit [Fintype m] [Fintype k] [DecidableEq k] [Algebra ℂ A] [StarModule ℂ A]
  [DecidableEq m] [DecidableEq n] in
theorem matrix_conjTranspose_sum {τ : Type*} [Fintype τ]
    (F : τ → CStarMatrix m n A) :
    (∑ t, F t).conjTranspose = ∑ t, (F t).conjTranspose :=
  Matrix.conjTranspose_sum Finset.univ F

omit [Fintype k] [DecidableEq k] [Algebra ℂ A] [StarModule ℂ A]
  [DecidableEq l] [DecidableEq m] [DecidableEq n] [StarRing A] in
theorem matrix_sum_mul {τ : Type*} [Fintype τ]
    (F : τ → CStarMatrix l m A) (N : CStarMatrix m n A) :
    (∑ t, F t) * N = ∑ t, F t * N :=
  Matrix.sum_mul Finset.univ F N

omit [Fintype k] [DecidableEq k] [Algebra ℂ A] [StarModule ℂ A]
  [DecidableEq l] [DecidableEq m] [DecidableEq n] [StarRing A] in
theorem matrix_mul_sum {τ : Type*} [Fintype τ]
    (M : CStarMatrix l m A) (F : τ → CStarMatrix m n A) :
    M * (∑ t, F t) = ∑ t, M * F t :=
  Matrix.mul_sum Finset.univ F M

omit [Fintype m] [StarModule ℂ A] in
/-- The range projection of the constructed column is exactly the given support. -/
theorem supportColumn_mul_conjTranspose (E : Generator.MatrixUnitSystem k A)
    (S : Finset (m × k)) (f : S ↪ k) :
    supportColumn E S f * (supportColumn E S f).conjTranspose = supportProjection E S := by
  classical
  simp only [supportColumn, matrix_conjTranspose_sum, matrix_sum_mul, matrix_mul_sum,
    supportColumn_atom_mul]
  simp [supportProjection]

end

end KadisonKastler

end OAI
