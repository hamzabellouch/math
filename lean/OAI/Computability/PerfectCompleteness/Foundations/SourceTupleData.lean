import Mathlib.Tactic.DeriveFintype
import OAI.Computability.PerfectCompleteness.Machines.SourceCoordinateMachine

namespace OAI


namespace PerfectCompleteness.SourceTupleData


open UniqueGamesTheorem.Foundations Target

inductive Tape (width : Nat) where
  | table
  | digit (position : Fin width)
  | work (slot : Fin 5)
  | variableName (position : Fin width) (slot : Fin 3)
  deriving DecidableEq, Fintype

variable {width : Nat}

def localTape (position : Fin width) : Fin 10 → Tape width
  | 0 => .table
  | 1 => .digit position
  | 2 => .work 0
  | 3 => .work 1
  | 4 => .work 2
  | 5 => .work 3
  | 6 => .work 4
  | 7 => .variableName position 0
  | 8 => .variableName position 1
  | 9 => .variableName position 2

theorem localTape_injective (position : Fin width) : Function.Injective (localTape position) := by
  intro i j same
  fin_cases i <;> fin_cases j <;> simp [localTape] at same ⊢

def placedTape {K : Type} (place : Tape width → K) (position : Fin width) : Fin 10 → K :=
  fun slot => place (localTape position slot)

theorem placedTape_injective {K : Type} (place : Tape width → K)
    (distinct : Function.Injective place) (position : Fin width) :
    Function.Injective (placedTape place position) :=
  distinct.comp (localTape_injective position)

def selectedClause (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (position : Fin width) :
    Clause formula.variables := formula.clauses[(indices position).val]

def «stacks» (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (prepared : Fin width → Bool) : Tape width → List Bool
  | .table => SourceOccurrenceEncoding.bits formula
  | .digit position => List.replicate (indices position).val true
  | .work _ => []
  | .variableName position slot =>
      if prepared position then
        NormalizationReadMachine.clauseCounters (selectedClause formula indices position) slot
      else []

@[simp] theorem table_at (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (prepared : Fin width → Bool) :
    «stacks» formula indices prepared .table = SourceOccurrenceEncoding.bits formula := rfl

@[simp] theorem digits_at (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (prepared : Fin width → Bool)
    (position : Fin width) :
    «stacks» formula indices prepared (.digit position) =
      List.replicate (indices position).val true := rfl

@[simp] theorem work_at (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (prepared : Fin width → Bool)
    (slot : Fin 5) : «stacks» formula indices prepared (.work slot) = [] := rfl

@[simp] theorem variables_at (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (prepared : Fin width → Bool)
    (position : Fin width) (slot : Fin 3) :
    «stacks» formula indices prepared (.variableName position slot) =
      if prepared position then
        List.replicate (selectedClause formula indices position)[slot].variableIndex.val true
      else [] := rfl

theorem coordinate_table (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (prepared : Fin width → Bool)
    (position : Fin width) :
    «stacks» formula indices prepared (localTape position 0) =
      SourceOccurrenceEncoding.bits formula := rfl

theorem coordinate_digit (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (prepared : Fin width → Bool)
    (position : Fin width) :
    «stacks» formula indices prepared (localTape position 1) =
      List.replicate (indices position).val true := rfl

theorem coordinate_initial_empty (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (prepared : Fin width → Bool)
    (position : Fin width) (fresh : prepared position = false)
    (slot : Fin 10) (work : 2 ≤ slot.val) :
    «stacks» formula indices prepared (localTape position slot) = [] := by
  fin_cases slot <;> simp [localTape, «stacks», fresh] at work ⊢

theorem resultTapes_eq (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (prepared : Fin width → Bool)
    (position : Fin width) (_fresh : prepared position = false) :
    SourceCoordinateMachine.resultTapes (localTape position) («stacks» formula indices prepared)
        (selectedClause formula indices position) =
      «stacks» formula indices (Function.update prepared position true) := by
  funext key
  cases key with
  | table =>
      simp [SourceCoordinateMachine.resultTapes, NormalizationReadMachine.tapes,
        SourceCoordinateMachine.readerTapes, SourceCoordinateMachine.readerMap, localTape, «stacks»]
  | digit other =>
      simp [SourceCoordinateMachine.resultTapes, NormalizationReadMachine.tapes,
        SourceCoordinateMachine.readerTapes, SourceCoordinateMachine.readerMap, localTape, «stacks»]
  | work slot =>
      fin_cases slot <;>
        simp [SourceCoordinateMachine.resultTapes, NormalizationReadMachine.tapes,
          SourceCoordinateMachine.readerTapes, SourceCoordinateMachine.readerMap, localTape, «stacks»]
  | variableName other slot =>
      by_cases same : other = position
      · subst other
        fin_cases slot <;>
          simp [SourceCoordinateMachine.resultTapes, NormalizationReadMachine.tapes,
            SourceCoordinateMachine.readerTapes, SourceCoordinateMachine.readerMap,
            localTape, «stacks»]
      · simp [SourceCoordinateMachine.resultTapes, NormalizationReadMachine.tapes,
          SourceCoordinateMachine.readerTapes, SourceCoordinateMachine.readerMap,
          localTape, «stacks», same]

def shapes (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (initialShapes : Fin width → CanonicalKeyShape.Shape) (prepared : Fin width → Bool) :
    Fin width → CanonicalKeyShape.Shape :=
  fun position => if prepared position then
    SourceClauseReaderMachine.clauseShape (selectedClause formula indices position)
  else initialShapes position

theorem shapes_update (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length)
    (initialShapes : Fin width → CanonicalKeyShape.Shape) (prepared : Fin width → Bool)
    (position : Fin width) :
    Function.update (shapes formula indices initialShapes prepared) position
        (SourceClauseReaderMachine.clauseShape (selectedClause formula indices position)) =
      shapes formula indices initialShapes (Function.update prepared position true) := by
  funext other
  by_cases same : other = position
  · subst other
    simp [shapes]
  · simp [shapes, same]

end PerfectCompleteness.SourceTupleData

end OAI
