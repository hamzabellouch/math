import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSupportData
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteWordBases

namespace OAI

/-! # The finite Cartan word model

The support datum uses all ordered bases selected from a finite list that
contains every nonzero evaluated word. It is therefore attached to the Lie
algebra generators, rather than to an extra family of assumed bases.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule LieAlgebra

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- Finite homogeneous generators, their abelianization basis, and an actual
lower-central-series bound for the Cartan ideal. -/
structure CartanWordModel where
  letterCount : ℕ
  letter : Fin letterCount → cartanRootIdeal H
  weight : Fin letterCount → Weight ℝ H L
  weight_nonzero : ∀ i, (weight i).IsNonZero
  letter_root : ∀ i, (letter i : L) ∈ rootSpace H (weight i)
  abelianBasis : Basis (Fin letterCount) ℝ (cartanRootAbelianization H)
  letter_quotient : ∀ i, (lowerCentralSeries ℝ (cartanRootIdeal H)
    (cartanRootIdeal H) 1).toSubmodule.mkQ (letter i) = abelianBasis i
  generates : LieSubalgebra.lieSpan ℝ (cartanRootIdeal H) (Set.range letter) = ⊤
  bound : ℕ
  bound_zero : lowerCentralSeries ℝ (cartanRootIdeal H) (cartanRootIdeal H) bound = ⊥

/-- Construction uses the triangular adjoint action and the actual Cartan
root ideal; no word-generation or nilpotence premise is left to the caller. -/
theorem nonempty_cartanWordModel {n : ℕ} (T : TriangularAdjoint L n) :
    Nonempty (CartanWordModel H) := by
  obtain ⟨m, X, χ, bq, hroot, hq, hgen⟩ := exists_cartan_abelianization_generators H T
  let := cartanRootIdeal_nilpotent H T
  obtain ⟨k, hk⟩ := LieModule.IsNilpotent.nilpotent ℝ (cartanRootIdeal H) (cartanRootIdeal H)
  exact ⟨⟨m, X, χ, fun i => (hroot i).1, fun i => (hroot i).2, bq, hq, hgen, k, hk⟩⟩

namespace CartanWordModel

variable {H} (M : CartanWordModel H)

abbrev wordList : Finset (FreeMagma (Fin M.letterCount)) := boundedBracketWords M.bound

abbrev Bases := WordBasisSelections M.letter M.wordList

instance : Nonempty M.Bases := nonempty_wordBasisSelections M.letter M.bound_zero M.generates

omit [FiniteDimensional ℝ L] in
/-- No nonzero direction has been omitted by the finite cutoff. -/
theorem mem_wordList_of_eval_ne_zero (w : FreeMagma (Fin M.letterCount))
    (hw : evalBracketWord M.letter w ≠ 0) : w ∈ M.wordList := by
  apply (mem_boundedBracketWords _ _).mpr
  by_contra hn
  exact hw (evalBracketWord_eq_zero_of_depth M.letter M.bound_zero w (Nat.le_of_not_lt hn))

omit [FiniteDimensional ℝ L] in
/-- Brackets of list entries are again list entries unless their value is zero. -/
theorem bracket_mem_wordList (u v : FreeMagma (Fin M.letterCount))
    (h : ⁅evalBracketWord M.letter u, evalBracketWord M.letter v⁆ ≠ 0) :
    u * v ∈ M.wordList := M.mem_wordList_of_eval_ne_zero (u * v) h

/-- The finite support data derived from all word bases. -/
def supportDatum {n : ℕ} (T : TriangularAdjoint L n)
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0) :
    SupportDatum (HeightSpace T.character) (Fin M.letterCount) M.Bases :=
  cartanSupportDatum H T M.letter M.weight M.letter_root M.abelianBasis
    M.letter_quotient M.generates hunimod
    (WordBasisSelections.basis M.letter M.wordList)
    (WordBasisSelections.words M.letter M.wordList)
    (WordBasisSelections.eval_words M.letter M.wordList)

@[simp] theorem supportDatum_weight {n : ℕ} (T : TriangularAdjoint L n)
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0) (i : Fin M.letterCount) :
    (M.supportDatum T hunimod).weight i = cartanHeightWeight T H (M.weight i) := rfl

/-- The segment support from the actual finite word model vanishes precisely
at zero height. Its other norm properties follow from `SupportDatum.normCore`. -/
theorem segmentSupport_eq_zero_iff {n : ℕ} (T : TriangularAdjoint L n)
    (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
    (w : HeightSpace T.character) :
    (M.supportDatum T hunimod).segmentSupport w = 0 ↔ w = 0 :=
  (M.supportDatum T hunimod).segmentSupport_eq_zero_iff w

end CartanWordModel
end PolycyclicRecognition

end

end OAI
