import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexConditionalPrefixWords
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexWitness

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

noncomputable section

namespace MatrixMultiplication.CW75ReorderedWords

open MatrixMultiplication.Foundation
open CW75LabelHierarchy ConditionalPrefixWords ComplexWitness
open scoped BigOperators Classical

universe u v

abbrev BlockPosition (counts : Scalar → ℕ) (t : ℕ) := Fin (t * ∑ a, counts a)

variable {Position : Type u} [Fintype Position]

abbrev LongWord (Position : Type u) := Position → Word

def longX (word : Position → Scalar) : LongWord Position := fun i => x (word i)
def longY (word : Position → Scalar) : LongWord Position := fun i => y (word i)
def longZ (word : Position → Scalar) : LongWord Position := fun i => z (word i)

def longCoordinate (side : Side) (word : Position → Scalar) : LongWord Position :=
  fun i => originalCoordinate side (word i)

def coordinateOf : Side → LongWord Position → LongWord Position → LongWord Position →
    LongWord Position
  | .x, u, _, _ => u
  | .y, _, v, _ => v
  | .z, _, _, w => w

omit [Fintype Position] in
theorem coordinateOf_original (side : Side) (word : Position → Scalar) :
    coordinateOf side (longX word) (longY word) (longZ word) =
      longCoordinate side word := by
  cases side <;> rfl

omit [Fintype Position] in
theorem longCoordinates_injective : Function.Injective
    (fun word : Position → Scalar => (longX word, longY word, longZ word)) := by
  intro word other h
  funext i
  apply coordinates_injective
  exact Prod.ext (congrFun (congrArg Prod.fst h) i)
    (Prod.ext (congrFun (congrArg (fun q => q.2.1) h) i)
      (congrFun (congrArg (fun q => q.2.2) h) i))

variable {Prefix : Type v} {counts : Scalar → ℕ} {n t : ℕ}

def Represents (priorWord : Prefix → ExactPrefix counts curveLabels n t Position)
    (prior : Prefix) (u v w : LongWord Position) (word : Position → Scalar) : Prop :=
  u = longX word ∧ v = longY word ∧ w = longZ word ∧
    ∀ i, (priorWord prior).val i = labelRecordOf curveLabels n (word i)

def eligible (priorWord : Prefix → ExactPrefix counts curveLabels n t Position)
    (prior : Prefix) (u v w : LongWord Position) : Prop :=
  ∃ word : Position → Scalar, Represents priorWord prior u v w word

def firstRead (priorWord : Prefix → ExactPrefix counts curveLabels n t Position)
    (prior : Prefix) (own : LongWord Position) : Position → Label n :=
  fun i => curveFirstReader n ((priorWord prior).val i) (own i)

def secondRead (priorWord : Prefix → ExactPrefix counts curveLabels n t Position)
    (prior : Prefix) (own : LongWord Position) : Position → Label n :=
  fun i => curveSecondReader n ((priorWord prior).val i) (own i)

theorem firstRead_on_original_word
    (priorWord : Prefix → ExactPrefix counts curveLabels n t Position) (prior : Prefix)
    (word : Position → Scalar) (hn : n < 5)
    (hprior : ∀ i, (priorWord prior).val i = labelRecordOf curveLabels n (word i)) :
    firstRead priorWord prior (longCoordinate (curveFirstSide n) word) =
      fun i => curveLabels n (word i) := by
  funext i
  change curveFirstReader n ((priorWord prior).val i)
    (originalCoordinate (curveFirstSide n) (word i)) = curveLabels n (word i)
  rw [hprior i]
  exact curveFirstReader_readable n hn (word i)

theorem secondRead_on_original_word
    (priorWord : Prefix → ExactPrefix counts curveLabels n t Position) (prior : Prefix)
    (word : Position → Scalar) (hn : n < 5)
    (hprior : ∀ i, (priorWord prior).val i = labelRecordOf curveLabels n (word i)) :
    secondRead priorWord prior (longCoordinate (curveSecondSide n) word) =
      fun i => curveLabels n (word i) := by
  funext i
  change curveSecondReader n ((priorWord prior).val i)
    (originalCoordinate (curveSecondSide n) (word i)) = curveLabels n (word i)
  rw [hprior i]
  exact curveSecondReader_readable n hn (word i)

theorem readers_recover_original_fine
    (priorWord : Prefix → ExactPrefix counts curveLabels n t Position) (prior : Prefix)
    (u v w : LongWord Position) (hn : n < 5) (h : eligible priorWord prior u v w) :
    ∃ word : Position → Scalar, Represents priorWord prior u v w word ∧
      firstRead priorWord prior (coordinateOf (curveFirstSide n) u v w) =
        (fun i => curveLabels n (word i)) ∧
      secondRead priorWord prior (coordinateOf (curveSecondSide n) u v w) =
        (fun i => curveLabels n (word i)) := by
  obtain ⟨word, hw⟩ := h
  refine ⟨word, hw, ?_, ?_⟩
  · rw [hw.1, hw.2.1, hw.2.2.1, coordinateOf_original]
    exact firstRead_on_original_word priorWord prior word hn hw.2.2.2
  · rw [hw.1, hw.2.1, hw.2.2.1, coordinateOf_original]
    exact secondRead_on_original_word priorWord prior word hn hw.2.2.2

theorem readable_of_eligible
    (priorWord : Prefix → ExactPrefix counts curveLabels n t Position) (prior : Prefix)
    (u v w : LongWord Position) (hn : n < 5) (h : eligible priorWord prior u v w) :
    firstRead priorWord prior (coordinateOf (curveFirstSide n) u v w) =
      secondRead priorWord prior (coordinateOf (curveSecondSide n) u v w) := by
  obtain ⟨word, _, hfirst, hsecond⟩ :=
    readers_recover_original_fine priorWord prior u v w hn h
  exact hfirst.trans hsecond.symm

theorem represented_word_unique
    (priorWord : Prefix → ExactPrefix counts curveLabels n t Position) (prior : Prefix)
    (u v w : LongWord Position) {word other : Position → Scalar}
    (hword : Represents priorWord prior u v w word)
    (hother : Represents priorWord prior u v w other) : word = other := by
  apply longCoordinates_injective
  exact Prod.ext (hword.1.symm.trans hother.1)
    (Prod.ext (hword.2.1.symm.trans hother.2.1)
      (hword.2.2.1.symm.trans hother.2.2.1))

theorem eligible_coefficient_one
    (priorWord : Prefix → ExactPrefix counts curveLabels n t Position) (prior : Prefix)
    (u v w : LongWord Position) (h : eligible priorWord prior u v w) (i : Position) :
    CW75Primitive.tensor (u i) (v i) (w i) = 1 := by
  obtain ⟨word, hw⟩ := h
  rw [hw.1, hw.2.1, hw.2.2.1]
  exact coefficient_one (word i)

theorem eligible_original_grade
    (priorWord : Prefix → ExactPrefix counts curveLabels n t Position) (prior : Prefix)
    (u v w : LongWord Position) {word : Position → Scalar}
    (h : Represents priorWord prior u v w word) (i : Position) :
    CWOriginalWords.decodeWord (u i) (v i) (w i) = grade (word i) := by
  rw [h.1, h.2.1, h.2.2.1]
  exact decode_original_grade (word i)

theorem eligible_appendCode_iff
    (old : ExactPrefix counts curveLabels n t Position)
    (code : Fin (StageHierarchyResources.stageRefinementCount counts curveLabels n t))
    (u v w : LongWord Position) :
    eligible id (appendCode old code) u v w ↔
      ∃ word : Position → Scalar, Represents id old u v w word ∧
        ((conditionalPoolEquivFin old).symm code).val =
          (fun i => curveLabels n (word i)) := by
  constructor
  · rintro ⟨word, hu, hv, hw, hprior⟩
    refine ⟨word, ⟨hu, hv, hw, ?_⟩, ?_⟩
    · intro i
      have hi := hprior i
      change (old.val i, ((conditionalPoolEquivFin old).symm code).val i) =
        (labelRecordOf curveLabels n (word i), curveLabels n (word i)) at hi
      exact congrArg Prod.fst hi
    · funext i
      have hi := hprior i
      change (old.val i, ((conditionalPoolEquivFin old).symm code).val i) =
        (labelRecordOf curveLabels n (word i), curveLabels n (word i)) at hi
      exact congrArg Prod.snd hi
  · rintro ⟨word, ⟨hu, hv, hw, hprior⟩, hfine⟩
    refine ⟨word, hu, hv, hw, ?_⟩
    intro i
    change (old.val i, ((conditionalPoolEquivFin old).symm code).val i) =
      (labelRecordOf curveLabels n (word i), curveLabels n (word i))
    exact Prod.ext (hprior i) (congrFun hfine i)

theorem represented_fine_eq
    (priorWord : Prefix → ExactPrefix counts curveLabels n t Position) (prior : Prefix)
    (u v w : LongWord Position) {word other : Position → Scalar}
    (hword : Represents priorWord prior u v w word)
    (hother : Represents priorWord prior u v w other) :
    (fun i => curveLabels n (word i)) = (fun i => curveLabels n (other i)) := by
  rw [represented_word_unique priorWord prior u v w hword hother]

theorem eligible_appendCode_iff_of_represents
    (old : ExactPrefix counts curveLabels n t Position)
    (code : Fin (StageHierarchyResources.stageRefinementCount counts curveLabels n t))
    (u v w : LongWord Position) (word : Position → Scalar)
    (hword : Represents id old u v w word) :
    eligible id (appendCode old code) u v w ↔
      ((conditionalPoolEquivFin old).symm code).val = (fun i => curveLabels n (word i)) := by
  rw [eligible_appendCode_iff]
  constructor
  · rintro ⟨other, hother, hfine⟩
    exact hfine.trans (represented_fine_eq id old u v w hother hword)
  · intro hfine
    exact ⟨word, hword, hfine⟩

theorem root_eligible_iff
    (old : ExactPrefix counts curveLabels 0 t Position) (u v w : LongWord Position) :
    eligible id old u v w ↔ ∀ i, CW75Primitive.tensor (u i) (v i) (w i) ≠ 0 := by
  constructor
  · intro h i
    rw [eligible_coefficient_one id old u v w h i]
    exact one_ne_zero
  · intro h
    have hchoice : ∀ i : Position, ∃ a : Scalar, (x a, y a, z a) = (u i, v i, w i) :=
      fun i => CW75LabelHierarchy.support_exhausted (u i) (v i) (w i) (h i)
    choose word hword using hchoice
    refine ⟨word, ?_, ?_, ?_, ?_⟩
    · funext i
      exact (congrArg Prod.fst (hword i)).symm
    · funext i
      exact (congrArg (fun q => q.2.1) (hword i)).symm
    · funext i
      exact (congrArg (fun q => q.2.2) (hword i)).symm
    · intro i
      change (old.val i : PUnit) = PUnit.unit
      exact Subsingleton.elim _ _

def terminalWord (last : ExactPrefix counts curveLabels 5 t Position) :
    PopulationWords Position (fun a => t * counts a) := by
  let source := sourcePrefixEquiv counts curveLabels 5 t Position curve_completeRecord_injective last
  refine ⟨source.val, ?_⟩
  intro a
  refine Eq.trans ?_ (source.property a)
  unfold wordPopulation
  exact congrArg
    (fun inst : Fintype {i : Position // source.val i = a} => @Fintype.card _ inst)
    (Subsingleton.elim _ _)

theorem terminalWord_record (last : ExactPrefix counts curveLabels 5 t Position) (i : Position) :
    labelRecordOf curveLabels 5 ((terminalWord last).val i) = last.val i :=
  sourceSymbol_record last i

theorem terminalWord_of_represents
    (last : ExactPrefix counts curveLabels 5 t Position) (u v w : LongWord Position)
    (word : Position → Scalar) (hword : Represents id last u v w word) :
    (terminalWord last).val = word := by
  funext i
  exact (sourceSymbol_eq_iff curve_completeRecord_injective last i (word i)).2 (hword.2.2.2 i)

theorem terminal_eligible_iff
    (last : ExactPrefix counts curveLabels 5 t Position) (u v w : LongWord Position) :
    eligible id last u v w ↔
      u = longX (terminalWord last).val ∧ v = longY (terminalWord last).val ∧
        w = longZ (terminalWord last).val := by
  constructor
  · rintro ⟨word, hword⟩
    rw [terminalWord_of_represents last u v w word hword]
    exact ⟨hword.1, hword.2.1, hword.2.2.1⟩
  · rintro ⟨hu, hv, hw⟩
    refine ⟨(terminalWord last).val, hu, hv, hw, ?_⟩
    intro i
    exact (terminalWord_record last i).symm

theorem terminal_original_grade
    (last : ExactPrefix counts curveLabels 5 t Position) (u v w : LongWord Position)
    (h : eligible id last u v w) (i : Position) :
    CWOriginalWords.decodeWord (u i) (v i) (w i) = grade ((terminalWord last).val i) := by
  obtain ⟨hu, hv, hw⟩ := (terminal_eligible_iff last u v w).mp h
  rw [hu, hv, hw]
  exact decode_original_grade ((terminalWord last).val i)

theorem stage0_XY_readable
    (priorWord : Prefix → ExactPrefix counts curveLabels 0 t Position) (prior : Prefix)
    (u v w : LongWord Position) (h : eligible priorWord prior u v w) :
    firstRead priorWord prior u = secondRead priorWord prior v := by
  simpa [curveFirstSide, curveSecondSide, coordinateOf] using
    readable_of_eligible priorWord prior u v w (by decide : 0 < 5) h

theorem stage1_XZ_readable
    (priorWord : Prefix → ExactPrefix counts curveLabels 1 t Position) (prior : Prefix)
    (u v w : LongWord Position) (h : eligible priorWord prior u v w) :
    firstRead priorWord prior u = secondRead priorWord prior w := by
  simpa [curveFirstSide, curveSecondSide, coordinateOf] using
    readable_of_eligible priorWord prior u v w (by decide : 1 < 5) h

theorem stage2_XY_readable
    (priorWord : Prefix → ExactPrefix counts curveLabels 2 t Position) (prior : Prefix)
    (u v w : LongWord Position) (h : eligible priorWord prior u v w) :
    firstRead priorWord prior u = secondRead priorWord prior v := by
  simpa [curveFirstSide, curveSecondSide, coordinateOf] using
    readable_of_eligible priorWord prior u v w (by decide : 2 < 5) h

theorem stage3_YZ_readable
    (priorWord : Prefix → ExactPrefix counts curveLabels 3 t Position) (prior : Prefix)
    (u v w : LongWord Position) (h : eligible priorWord prior u v w) :
    firstRead priorWord prior v = secondRead priorWord prior w := by
  simpa [curveFirstSide, curveSecondSide, coordinateOf] using
    readable_of_eligible priorWord prior u v w (by decide : 3 < 5) h

theorem stage4_YZ_readable
    (priorWord : Prefix → ExactPrefix counts curveLabels 4 t Position) (prior : Prefix)
    (u v w : LongWord Position) (h : eligible priorWord prior u v w) :
    firstRead priorWord prior v = secondRead priorWord prior w := by
  simpa [curveFirstSide, curveSecondSide, coordinateOf] using
    readable_of_eligible priorWord prior u v w (by decide : 4 < 5) h

end MatrixMultiplication.CW75ReorderedWords

end

end OAI
