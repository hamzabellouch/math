import OAI.GroupTheory.PolycyclicRecognition.Algebra.MixedWordBasis
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BoxWordExpansion
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentBoxes

namespace OAI

/-! # The concrete nilpotent box model of a cone ideal

The finite mixed words generate the ideal even as a vector space. Using
them as an alphabet allows the existing box calculus to apply directly.
Flattening this alphabet retains the original word and its exact width.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule LieAlgebra
open scoped BigOperators

def substituteBracketWord {I J : Type*} (f : I → FreeMagma J) :
    FreeMagma I → FreeMagma J
  | .of i => f i
  | .mul u v => substituteBracketWord f u * substituteBracketWord f v

theorem eval_substituteBracketWord {I J V : Type*} [LieRing V] [LieAlgebra ℝ V]
    (X : J → V) (f : I → FreeMagma J) (w : FreeMagma I) :
    evalBracketWord X (substituteBracketWord f w) =
      evalBracketWord (fun i => evalBracketWord X (f i)) w := by
  induction w using FreeMagma.rec with
  | of i => rfl
  | mul u v hu hv =>
    change ⁅evalBracketWord X (substituteBracketWord f u),
      evalBracketWord X (substituteBracketWord f v)⁆ =
      ⁅evalBracketWord (fun i => evalBracketWord X (f i)) u,
        evalBracketWord (fun i => evalBracketWord X (f i)) v⁆
    rw [hu, hv]

theorem exponent_substituteBracketWord {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (s : J → ℝ) (f : I → FreeMagma J) (w : FreeMagma I) :
    bracketWordExponent s (substituteBracketWord f w) =
      bracketWordExponent (fun i => bracketWordExponent s (f i)) w := by
  induction w using FreeMagma.rec with
  | of i => simp only [substituteBracketWord, bracketWordExponent_of]
  | mul u v hu hv =>
    change bracketWordExponent s (substituteBracketWord f u * substituteBracketWord f v) =
      bracketWordExponent (fun i => bracketWordExponent s (f i)) (u * v)
    simp only [bracketWordExponent_mul, hu, hv]

theorem bracketWordExponent_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → ℝ) (hs : ∀ i, 0 ≤ s i) (w : FreeMagma I) :
    0 ≤ bracketWordExponent s w := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hs i)

theorem bracketWordExponent_pos_of_mixed {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → ℝ) (outside : I → Prop) (hs : ∀ i, 0 ≤ s i)
    (hpos : ∀ i, outside i → 0 < s i) (w : FreeMagma I)
    (hw : IsMixedWord outside w) : 0 < bracketWordExponent s w := by
  induction w using FreeMagma.rec with
  | of i => simpa only [bracketWordExponent_of] using hpos i hw
  | mul u v hu hv =>
    change 0 < bracketWordExponent s (u * v)
    rw [bracketWordExponent_mul]
    rcases hw with hw | hw
    · exact add_pos_of_pos_of_nonneg (hu hw) (bracketWordExponent_nonneg s hs v)
    · exact add_pos_of_nonneg_of_pos (bracketWordExponent_nonneg s hs u) (hv hw)

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

theorem coneMixedVector_generates (C : Set (H →ₗ[ℝ] ℝ)) :
    LieSubalgebra.lieSpan ℝ (M.coneWordIdeal C) (Set.range (M.coneMixedVector C)) = ⊤ := by
  apply top_unique
  have hle : Submodule.span ℝ (Set.range (M.coneMixedVector C)) ≤
      (LieSubalgebra.lieSpan ℝ (M.coneWordIdeal C)
        (Set.range (M.coneMixedVector C))).toSubmodule :=
    Submodule.span_le.mpr LieSubalgebra.subset_lieSpan
  rw [M.coneMixedVector_span C] at hle
  exact hle

def coneIdealWordBound (C : Set (H →ₗ[ℝ] ℝ)) : ℕ := by
  let := M.coneIdeal_nilpotent C
  exact (LieModule.IsNilpotent.nilpotent ℝ (M.coneWordIdeal C)
    (M.coneWordIdeal C)).choose

theorem coneIdealWordBound_zero (C : Set (H →ₗ[ℝ] ℝ)) :
    lowerCentralSeries ℝ (M.coneWordIdeal C) (M.coneWordIdeal C)
      (M.coneIdealWordBound C) = ⊥ := by
  let := M.coneIdeal_nilpotent C
  exact (LieModule.IsNilpotent.nilpotent ℝ (M.coneWordIdeal C)
    (M.coneWordIdeal C)).choose_spec

abbrev coneIdealWordList (C : Set (H →ₗ[ℝ] ℝ)) :=
  boundedBracketWords (I := M.coneMixedWords C) (M.coneIdealWordBound C)

abbrev ConeIdealBases (C : Set (H →ₗ[ℝ] ℝ)) :=
  WordBasisSelections (M.coneMixedVector C) (M.coneIdealWordList C)

instance (C : Set (H →ₗ[ℝ] ℝ)) : Nonempty (M.ConeIdealBases C) :=
  nonempty_wordBasisSelections (M.coneMixedVector C)
    (M.coneIdealWordBound_zero C) (M.coneMixedVector_generates C)

def coneOriginalWord (C : Set (H →ₗ[ℝ] ℝ))
    (w : FreeMagma (M.coneMixedWords C)) : FreeMagma (Fin M.letterCount) :=
  substituteBracketWord (fun i => i.val.val) w

theorem coneOriginalWord_mixed (C : Set (H →ₗ[ℝ] ℝ))
    (w : FreeMagma (M.coneMixedWords C)) :
    IsMixedWord (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) (M.coneOriginalWord C w) := by
  induction w using FreeMagma.rec with
  | of i => exact i.property
  | mul u v hu _ => exact Or.inl hu

theorem coneOriginalWord_eval (C : Set (H →ₗ[ℝ] ℝ))
    (w : FreeMagma (M.coneMixedWords C)) :
    evalBracketWord M.letter (M.coneOriginalWord C w) =
      ((evalBracketWord (M.coneMixedVector C) w : M.coneWordIdeal C) :
        cartanRootIdeal H) := by
  rw [coneOriginalWord, eval_substituteBracketWord]
  exact (evalBracketWord_map (M.coneWordIdeal C).incl (M.coneMixedVector C) w).symm

theorem coneOriginalWord_mem_of_eval_ne_zero (C : Set (H →ₗ[ℝ] ℝ))
    (w : FreeMagma (M.coneMixedWords C))
    (hw : evalBracketWord (M.coneMixedVector C) w ≠ 0) :
    M.coneOriginalWord C w ∈ M.wordList := by
  apply M.mem_wordList_of_eval_ne_zero
  rw [M.coneOriginalWord_eval]
  exact fun h => hw (Subtype.ext h)

def coneIdealWordCost (C : Set (H →ₗ[ℝ] ℝ)) (s : Fin M.letterCount → ℝ)
    (w : FreeMagma (M.coneMixedWords C)) : ℝ :=
  bracketWordExponent (fun i : M.coneMixedWords C => bracketWordExponent s i.val.val) w

theorem coneIdealWordCost_eq_original (C : Set (H →ₗ[ℝ] ℝ))
    (s : Fin M.letterCount → ℝ) (w : FreeMagma (M.coneMixedWords C)) :
    M.coneIdealWordCost C s w = bracketWordExponent s (M.coneOriginalWord C w) :=
  (exponent_substituteBracketWord s _ w).symm

theorem coneIdealWordCost_pos (C : Set (H →ₗ[ℝ] ℝ))
    (s : Fin M.letterCount → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hpos : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∉ C → 0 < s i)
    (w : FreeMagma (M.coneMixedWords C)) : 0 < M.coneIdealWordCost C s w := by
  rw [M.coneIdealWordCost_eq_original]
  exact bracketWordExponent_pos_of_mixed s _ hs hpos _ (M.coneOriginalWord_mixed C w)

end CartanWordModel
end PolycyclicRecognition

end

end OAI
