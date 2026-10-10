import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.Semantics
import OAI.Combinatorics.IndependentSets.PCP.ClauseVerifier
import OAI.Combinatorics.IndependentSets.Machines.MachineFieldProfile

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.CompareLoop

open Turing
open IndependentSetsGames.Foundations.Complexity
open RuntimeModel

inductive Label
  | leftFirst | leftSecond | rightFirst | rightSecond | compare
  | equalStore | differentStore
  deriving DecidableEq

instance : Fintype Label where
  elems := {.leftFirst, .leftSecond, .rightFirst, .rightSecond, .compare,
    .equalStore, .differentStore}
  complete label := by cases label <;> simp

variable {q : Nat} {Λ : Type}

def statement (labels : Label → Λ) (next : Λ) :
    Label → TM2.Stmt Alphabet Λ (State q)
  | .leftFirst => compareStatement (MachineFieldProfile.copyStatement
      (Reduction.MachineTransfer.loopAt .tail .scratch id false
        (labels .leftFirst) (some (labels .leftSecond))))
  | .leftSecond => compareStatement (MachineFieldProfile.copyStatement
      (MachineCopy.forkLoop .scratch .tail .compareLeft false
        (labels .leftSecond) (some (labels .rightFirst))))
  | .rightFirst => compareStatement (MachineFieldProfile.copyStatement
      (Reduction.MachineTransfer.loopAt .head .scratch id false
        (labels .rightFirst) (some (labels .rightSecond))))
  | .rightSecond => compareStatement (MachineFieldProfile.copyStatement
      (MachineCopy.forkLoop .scratch .head .compareRight false
        (labels .rightSecond) (some (labels .compare))))
  | .compare => compareStatement (MachineCompare.loop .compareLeft .compareRight
      (labels .compare) (some (labels .equalStore)) (some (labels .differentStore)))
  | .equalStore => storeLoop true next
  | .differentStore => storeLoop false next

private theorem compareProgram_at
    (program : Λ → TM2.Stmt Alphabet Λ (State q)) (label : Λ)
    (stmt : TM2.Stmt Alphabet Λ
      (MachineCompare.State (GenericGraphTables.RelationTable q × Bool)))
    (atLabel : program label = compareStatement stmt) :
    (MachineControl.program (Equiv.refl Λ) (compareEquiv q) program) label = stmt := by
  change MachineControl.statement id (compareEquiv q) (program label) = stmt
  rw [atLabel]
  exact MachineFieldProfile.statement_roundtrip (compareEquiv q) stmt

def compareWordsInTime (labels : Label → Λ) (next : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State q))
    (atLabel : ∀ label, program (labels label) = statement labels next label)
    (base : Tape → List Bool)
    (hLeft : base .compareLeft = []) (hRight : base .compareRight = [])
    (hScratch : base .scratch = [])
    (relation : GenericGraphTables.RelationTable q) (oldLoop : Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .leftFirst), normal relation oldLoop, base⟩
      (some ⟨some next, normal relation (decide (base .tail = base .head)), base⟩)
      (2 * ((base .tail).length + 1) + 2 * ((base .head).length + 1) +
        max (base .tail).length (base .head).length + 2) := by
  let view := MachineControl.program (Equiv.refl Λ) (compareEquiv q) program
  have compared := MachineFieldProfile.nonDestructiveCompareInTime
    Tape.tail Tape.head Tape.compareLeft Tape.compareRight Tape.scratch
    (by decide) (by decide) (by decide)
    (labels .leftFirst) (labels .leftSecond) (labels .rightFirst)
    (labels .rightSecond) (labels .compare)
    (some (labels .equalStore)) (some (labels .differentStore)) view
    (compareProgram_at program _ _ (atLabel .leftFirst))
    (compareProgram_at program _ _ (atLabel .leftSecond))
    (compareProgram_at program _ _ (atLabel .rightFirst))
    (compareProgram_at program _ _ (atLabel .rightSecond))
    (compareProgram_at program _ _ (atLabel .compare))
    base hLeft hRight hScratch (relation, oldLoop)
  have restoredProgram :
      MachineControl.program (Equiv.refl Λ) (compareEquiv q).symm view = program := by
    funext label
    exact MachineFieldProfile.statement_roundtrip (compareEquiv q).symm (program label)
  have transported := transportInTime (compareEquiv q).symm view compared
  rw [restoredProgram] at transported
  have copied : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .leftFirst), normal relation oldLoop, base⟩
      (some ⟨if base .tail = base .head then some (labels .equalStore)
        else some (labels .differentStore), normal relation oldLoop, base⟩)
      (2 * ((base .tail).length + 1) + 2 * ((base .head).length + 1) +
        max (base .tail).length (base .head).length + 1) := by
    simpa [MachineControl.configuration, compareEquiv, MachineFieldProfile.normalState,
      normal] using transported
  have stored : StateTransition.EvalsToInTime (TM2.step program)
      ⟨if base .tail = base .head then some (labels .equalStore)
        else some (labels .differentStore), normal relation oldLoop, base⟩
      (some ⟨some next, normal relation (decide (base .tail = base .head)), base⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change TM2.step program
        ⟨if base .tail = base .head then some (labels .equalStore)
          else some (labels .differentStore), normal relation oldLoop, base⟩ = _
      by_cases heq : base .tail = base .head
      · simp [heq, TM2.step, atLabel, statement, stepAux_storeLoop, normal]
      · simp [heq, TM2.step, atLabel, statement, stepAux_storeLoop, normal]
    steps_le_m := Nat.le_refl _
  }
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ copied stored
  exact { toEvalsTo := run.toEvalsTo, steps_le_m := by have h := run.steps_le_m; omega }

def comparisonTime (tailName headName : Nat) : Nat :=
  2 * (tailName + 2) + 2 * (headName + 2) + max (tailName + 1) (headName + 1) + 2

theorem encodeWord_eq_iff (left right : Nat) :
    encodeWord left = encodeWord right ↔ left = right := by
  constructor
  · intro h
    have hh := congrArg List.length h
    simpa only [encodeWord_length, Nat.add_right_cancel_iff] using hh
  · rintro rfl
    rfl

def compareInTime (labels : Label → Λ) (next : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State q))
    (atLabel : ∀ label, program (labels label) = statement labels next label)
    (base : Tape → List Bool) (tailName headName : Nat)
    (hTail : base .tail = encodeWord tailName) (hHead : base .head = encodeWord headName)
    (hLeft : base .compareLeft = []) (hRight : base .compareRight = [])
    (hScratch : base .scratch = [])
    (relation : GenericGraphTables.RelationTable q) (oldLoop : Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .leftFirst), normal relation oldLoop, base⟩
      (some ⟨some next, normal relation (decide (tailName = headName)), base⟩)
      (comparisonTime tailName headName) := by
  have run := compareWordsInTime labels next program atLabel base hLeft hRight hScratch
    relation oldLoop
  simpa only [hTail, hHead, encodeWord_eq_iff, encodeWord_length, comparisonTime,
    Nat.add_assoc] using run

theorem comparisonTime_le (tailName headName N : Nat)
    (hTail : tailName ≤ N) (hHead : headName ≤ N) :
    comparisonTime tailName headName ≤ 5 * N + 11 := by
  have hm : max (tailName + 1) (headName + 1) ≤ N + 1 := max_le (by omega) (by omega)
  unfold comparisonTime
  omega

theorem comparisonTime_le_of_lt (tailName headName N : Nat)
    (hTail : tailName < N) (hHead : headName < N) :
    comparisonTime tailName headName ≤ 5 * N + 6 := by
  have hm : max (tailName + 1) (headName + 1) ≤ N := max_le (by omega) (by omega)
  unfold comparisonTime
  omega

def compareWordsInTime_bounded (labels : Label → Λ) (next : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State q))
    (atLabel : ∀ label, program (labels label) = statement labels next label)
    (base : Tape → List Bool)
    (hLeft : base .compareLeft = []) (hRight : base .compareRight = [])
    (hScratch : base .scratch = [])
    (relation : GenericGraphTables.RelationTable q) (oldLoop : Bool)
    (N : Nat) (hTail : (base .tail).length ≤ N) (hHead : (base .head).length ≤ N) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .leftFirst), normal relation oldLoop, base⟩
      (some ⟨some next, normal relation (decide (base .tail = base .head)), base⟩)
      (5 * N + 6) := by
  let run := compareWordsInTime labels next program atLabel base hLeft hRight hScratch
    relation oldLoop
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have hm := max_le hTail hHead
  have h := run.steps_le_m
  omega

def rowLoop (table : GenericGraphTables.Table q) (e : Fin table.darts) : Bool :=
  decide (table.rows[e].tail.val = table.rows[table.rows[e].reverseIndex].tail.val)

def rowState (table : GenericGraphTables.Table q) (e : Fin table.darts) : State q :=
  normal table.rows[e].relation (rowLoop table e)

theorem rowLoop_eq_graph (table : GenericGraphTables.Table q) (e : Fin table.darts) :
    rowLoop table e = decide ((GenericGraphTables.semantics table).tail e =
      (GenericGraphTables.semantics table).head e) := by
  unfold rowLoop
  exact Bool.decide_congr Fin.val_inj

theorem rowContext_eq (table : GenericGraphTables.Table q) (e : Fin table.darts) :
    context (rowState table e).1 =
      (table.rows[e].relation, decide ((GenericGraphTables.semantics table).tail e =
        (GenericGraphTables.semantics table).head e)) := by
  change (table.rows[e].relation, rowLoop table e) = _
  rw [rowLoop_eq_graph]

def compareRowInTime (labels : Label → Λ) (next : Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State q))
    (atLabel : ∀ label, program (labels label) = statement labels next label)
    (table : GenericGraphTables.Table q) (e : Fin table.darts)
    (base : Tape → List Bool)
    (hTail : base .tail = encodeWord table.rows[e].tail.val)
    (hHead : base .head = encodeWord table.rows[table.rows[e].reverseIndex].tail.val)
    (hLeft : base .compareLeft = []) (hRight : base .compareRight = [])
    (hScratch : base .scratch = []) (oldLoop : Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .leftFirst), normal table.rows[e].relation oldLoop, base⟩
      (some ⟨some next, rowState table e, base⟩) (5 * table.vertices + 6) := by
  let run := compareInTime labels next program atLabel base _ _ hTail hHead
    hLeft hRight hScratch table.rows[e].relation oldLoop
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  exact run.steps_le_m.trans (comparisonTime_le_of_lt _ _ _
    table.rows[e].tail.isLt table.rows[table.rows[e].reverseIndex].tail.isLt)

theorem relationFromRowState (table : GenericGraphTables.Table q) (e : Fin table.darts)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (a b : GraphTables.Label) :
    GraphTables.relationAt
      (Relations.relationFromTable (context (rowState table e).1).1
        (context (rowState table e).1).2 event slot orientation) a b =
      (AlphabetGraph.graph (GenericGraphTables.semantics table)).accepts
        (((e, event), slot), orientation)
        (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b) := by
  rw [rowContext_eq]
  exact Relations.relationAt_relation_graph (GenericGraphTables.semantics table)
    e event slot orientation a b

end IndependentSetsGames.Foundations.PCP.AlphabetTable.CompareLoop

end OAI
