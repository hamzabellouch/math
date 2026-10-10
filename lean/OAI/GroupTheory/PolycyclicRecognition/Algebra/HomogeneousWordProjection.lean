import OAI.GroupTheory.PolycyclicRecognition.Algebra.PrimitiveWordProjection
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinWords

namespace OAI

/-! # Homogeneous primitive words and their right-nested Lie expressions -/

noncomputable section
namespace PolycyclicRecognition

variable {n : ℕ}

def IsHomogeneousRationalWord (p : RationalWords n) (d : ℕ) : Prop :=
  ∀ w, p.coeff w ≠ 0 → w.length = d

theorem rationalWordDegree_coeff (p : RationalWords n) (w : FreeMonoid (Fin n)) :
    (rationalWordDegree p).coeff w = (w.length : ℚ) * p.coeff w := by
  induction p using MonoidAlgebra.induction_on with
  | of v =>
    change (rationalWordDegree (MonoidAlgebra.single v 1)).coeff w =
      (w.length : ℚ) * (MonoidAlgebra.single v (1 : ℚ)).coeff w
    rw [rationalWordDegree_single]
    by_cases h : v = w
    · subst v; simp
    · simp [MonoidAlgebra.coeff_single, h]
  | add p q hp hq =>
    simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, mul_add]
  | smul r p hp =>
    simp only [map_smul, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, hp, smul_eq_mul]
    ring

theorem IsHomogeneousRationalWord.degree_eq {p : RationalWords n} {d : ℕ}
    (hp : IsHomogeneousRationalWord p d) : rationalWordDegree p = (d : ℚ) • p := by
  ext w
  rw [rationalWordDegree_coeff]
  by_cases h : p.coeff w = 0
  · simp [h]
  · simp [hp w h]

variable {A : Type*} [Ring A] [Algebra ℚ A] (X : Fin n → A)

theorem rationalWordEvaluation_letter (i : Fin n) :
    rationalWordEvaluation X (rationalWordLetter i) = X i := by
  simp [rationalWordLetter, rationalWordEvaluation_single]

theorem rationalWordEvaluation_wordRightLie (l : List (Fin n)) :
    rationalWordEvaluation X (wordRightLie rationalWordLetter l) = wordRightLie X l := by
  induction l with
  | nil => simp [wordRightLie]
  | cons i l ih =>
    cases l with
    | nil => simpa [wordRightLie] using rationalWordEvaluation_letter X i
    | cons j l =>
      simp only [wordRightLie, map_sub, map_mul, rationalWordEvaluation_letter] at ih ⊢
      rw [ih]

theorem rationalWordEvaluation_projection (p : RationalWords n) :
    rationalWordEvaluation X (wordLieProjection rationalWordLetter p) =
      wordLieProjection X p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change rationalWordEvaluation X (wordLieProjection rationalWordLetter
      (MonoidAlgebra.single w 1)) = wordLieProjection X (MonoidAlgebra.single w 1)
    simp only [wordLieProjection_single, one_smul, rationalWordEvaluation_wordRightLie]
  | add p q hp hq => simp only [map_add, hp, hq]
  | smul r p hp => simp only [map_smul, hp]

/-- The degree identity holds after substitution in any rational associative algebra. -/
theorem primitive_homogeneous_word_projection {p : RationalWords n} {d : ℕ}
    (hp : IsPrimitiveRationalWord p) (hd : IsHomogeneousRationalWord p d) :
    wordLieProjection X p = (d : ℚ) • rationalWordEvaluation X p := by
  rw [← rationalWordEvaluation_projection, hp.projection_eq_degree, hd.degree_eq, map_smul]

end PolycyclicRecognition

end

end OAI
