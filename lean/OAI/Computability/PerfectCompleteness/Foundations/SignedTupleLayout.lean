import OAI.Computability.PerfectCompleteness.Foundations.SourceTupleResetPlacementLemmas
import OAI.Computability.PerfectCompleteness.Machines.CompletedEdgeMachine

namespace OAI

section

namespace PerfectCompleteness.SignedTupleLayout

open UniqueGamesTheorem.Foundations Complexity Target
open scoped Classical

noncomputable section

inductive Tape (width : Nat) (Extra : Type) where
  | source (tape : SourceTupleData.Tape width)
  | current (position : Fin width)
  | remaining (position : Fin width)
  | encodedVariable (position : Fin width) (slot : Fin 3)
  | adapterScratch
  | edgeWork (slot : Fin 10)
  | edgeCount
  | extra (value : Extra)
  deriving DecidableEq, Fintype

variable {width : Nat} {Extra U Desc : Type}

abbrev State (width : Nat) (U Desc : Type) := SourceTupleBodyPlacement.State width U Desc

def frame (Desc : Type) : SourceTupleBodyPlacement.Frame Desc := ((none, (false, none)), none)

def initialSource (ambient : U) : SourceTupleMachine.State width U :=
  SourceTupleMachine.state ambient
    (SourceTupleMachine.initial (fun _ => CanonicalKeyShape.Shape.bit) (fun _ => false))

def clean (ambient : U) : State width U Desc :=
  SourceTupleBodyPlacement.registers (initialSource ambient, frame Desc)

def preparedSource (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (ambient : U) : SourceTupleMachine.State width U :=
  SourceClauseReaderMachine.clean
    (ambient, fun position => SourceClauseReaderMachine.clauseShape
      (SourceTupleData.selectedClause formula indices position))
    (SourceTupleMachine.result formula indices (List.finRange width)
      (SourceTupleMachine.initial (fun _ => CanonicalKeyShape.Shape.bit) (fun _ => false))).signs

def preparedState (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (ambient : U) : State width U Desc :=
  SourceTupleBodyPlacement.registers (preparedSource formula indices ambient, frame Desc)

def sourceView : Tape width Extra → Option (SourceTupleData.Tape width)
  | .source tape => some tape
  | _ => none

@[simp] theorem sourceView_left (tape : SourceTupleData.Tape width) :
    sourceView (Tape.source (Extra := Extra) tape) = some tape := rfl

theorem sourceView_right (tape : Tape width Extra) (source : SourceTupleData.Tape width)
    (h : sourceView tape = some source) : Tape.source source = tape := by
  cases tape <;> simp_all [sourceView]

def metadata (position : Fin width) : Fin 6 → Tape width Extra
  | 0 => .current position
  | 1 => .encodedVariable position 0
  | 2 => .encodedVariable position 1
  | 3 => .encodedVariable position 2
  | 4 => .edgeWork 5
  | 5 => .edgeWork 9

theorem metadata_injective (position : Fin width) :
    Function.Injective (metadata (Extra := Extra) position) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [metadata] at h ⊢

def ids (formula : Formula) (indices : Fin width → Fin formula.clauses.length) : Fin width → Nat :=
  fun position => (indices position).val

def vars (formula : Formula) (indices : Fin width → Fin formula.clauses.length) :
    Fin width → Fin 3 → Nat :=
  fun position slot => (SourceTupleData.selectedClause formula indices position)[slot].variableIndex.val

structure Clear (base : Tape width Extra → List Bool) : Prop where
  rawDigits : ∀ i, base (.source (.digit i)) = []
  rawVariables : ∀ i j, base (.source (.variableName i j)) = []
  sourceWork : ∀ j, base (.source (.work j)) = []
  encodedVariables : ∀ i j, base (.encodedVariable i j) = []
  scratch : base .adapterScratch = []

structure Input (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) : Prop extends Clear base where
  table : base (.source .table) = SourceOccurrenceEncoding.bits formula
  current : ∀ i, base (.current i) = encodeWord (indices i).val

def digitTapes (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) : Tape width Extra → List Bool
  | .source (.digit i) => List.replicate (indices i).val true
  | tape => base tape

def rawTapes (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) : Tape width Extra → List Bool
  | .source (.digit i) => List.replicate (indices i).val true
  | .source (.variableName i j) => List.replicate (vars formula indices i j) true
  | tape => base tape

def preparedTapes (formula : Formula) (indices : Fin width → Fin formula.clauses.length)
    (base : Tape width Extra → List Bool) : Tape width Extra → List Bool
  | .source (.digit i) => List.replicate (indices i).val true
  | .source (.variableName i j) => List.replicate (vars formula indices i j) true
  | .encodedVariable i j => encodeWord (vars formula indices i j)
  | tape => base tape

theorem prepared_metadata (formula : Formula)
    (indices : Fin width → Fin formula.clauses.length) (base : Tape width Extra → List Bool)
    (input : Input formula indices base) (i : Fin width) (field : Fin 4) :
    preparedTapes formula indices base (KeyMetadataMachine.idTape (metadata i) field) =
      encodeWord (KeyMetadataMachine.fieldValue (ids formula indices i) (vars formula indices i) field) := by
  fin_cases field <;>
    simp [KeyMetadataMachine.idTape, KeyMetadataMachine.idIndex, metadata, preparedTapes,
      KeyMetadataMachine.fieldValue, ids, input.current] <;> rfl

end
end PerfectCompleteness.SignedTupleLayout

end

end OAI
