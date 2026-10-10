import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteBracketWords

namespace OAI

/-! # All bases from a finite word list

The indexing type is finite and includes every ordered word basis selected
from the list. Nilpotence proves this family is nonempty for a generating
alphabet, including the zero-dimensional case.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- All ordered bases selected from `S`, retaining the actual word labels. -/
def WordBasisSelections (X : I → L) (S : Finset (FreeMagma I)) :=
  {w : Fin (finrank ℝ L) → S //
    ∃ b : Basis (Fin (finrank ℝ L)) ℝ L, ∀ j, evalBracketWord X (w j) = b j}

namespace WordBasisSelections

variable (X : I → L) (S : Finset (FreeMagma I))

instance : Fintype (WordBasisSelections X S) := by
  classical
  unfold WordBasisSelections
  infer_instance

/-- The word labels of this selected basis. -/
def words (β : WordBasisSelections X S) (j : Fin (finrank ℝ L)) : FreeMagma I := β.val j

/-- The corresponding actual basis of the Lie algebra. -/
def basis (β : WordBasisSelections X S) : Basis (Fin (finrank ℝ L)) ℝ L :=
  Classical.choose β.property

theorem eval_words (β : WordBasisSelections X S) (j : Fin (finrank ℝ L)) :
    evalBracketWord X (words X S β j) = basis X S β j :=
  Classical.choose_spec β.property j

theorem words_mem (β : WordBasisSelections X S) (j : Fin (finrank ℝ L)) :
    words X S β j ∈ S := (β.val j).property

end WordBasisSelections

variable [Fintype I] [DecidableEq I] [FiniteDimensional ℝ L]

/-- A basis chosen from all words automatically belongs to the finite list:
any omitted word is zero and therefore cannot be a basis vector. -/
theorem nonempty_wordBasisSelections (X : I → L) {k : ℕ}
    (hk : lowerCentralSeries ℝ L L k = ⊥)
    (hgen : LieSubalgebra.lieSpan ℝ L (Set.range X) = ⊤) :
    Nonempty (WordBasisSelections X (boundedBracketWords k)) := by
  obtain ⟨b, hb⟩ := exists_bracketWord_basis X hgen
  choose words hwords using hb
  have hm (j : Fin (finrank ℝ L)) : words j ∈ boundedBracketWords k := by
    apply (mem_boundedBracketWords _ _).mpr
    by_contra h
    have hz := evalBracketWord_eq_zero_of_depth X hk (words j) (Nat.le_of_not_lt h)
    exact b.ne_zero j ((hwords j).symm.trans hz)
  exact ⟨⟨fun j => ⟨words j, hm j⟩, b, hwords⟩⟩

end PolycyclicRecognition

end

end OAI
