import Mathlib
import OAI.Computability.MinUncut.Machines.Relations

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.RuntimeModel

open Turing
open MinUncutGames.Foundations.Complexity

inductive Tape
  | original | cursor | scan | vertices | darts | counter | edge
  | tail | reverseIndex | head | scratch | indexScan
  | compareLeft | compareRight | reversed | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.original, .cursor, .scan, .vertices, .darts,
  .counter, .edge, .tail, .reverseIndex, .head, .scratch, .indexScan, .compareLeft, .compareRight,
  .reversed, .output]

protected theorem Tape.enumList_getElem?_ctorIdx_eq (x : Tape) :
    Tape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Tape) := Bool

abbrev Flags := Bool × Bool × Option Bool
abbrev Ambient (q : Nat) := Flags × GenericGraphTables.RelationTable q
abbrev State (q : Nat) := Ambient q × Option Bool

def normal {q : Nat} (relation : GenericGraphTables.RelationTable q) (selfLoop : Bool) : State q :=
  (((selfLoop, false, none), relation), none)

def initial (q : Nat) : State q := normal (Vector.replicate (q * q) false) false

def context {q : Nat} (ambient : Ambient q) : GenericGraphTables.RelationTable q × Bool :=
  (ambient.2, ambient.1.1)

def compareEquiv (q : Nat) : State q ≃
    MachineCompare.State (GenericGraphTables.RelationTable q × Bool) where
  toFun s := ((s.1.2, s.1.1.1), s.1.1.2.1, s.1.1.2.2, s.2)
  invFun s := (((s.1.2, s.2.1, s.2.2.1), s.1.1), s.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem compareEquiv_normal {q : Nat}
    (relation : GenericGraphTables.RelationTable q) (selfLoop : Bool) :
    compareEquiv q (normal relation selfLoop) =
      ((relation, selfLoop), false, none, none) := rfl

def emitterEquiv (q : Nat) : ((Ambient q × Unit) × Option Bool) ≃ State q where
  toFun s := (s.1.1, s.2)
  invFun s := ((s.1, ()), s.2)
  left_inv s := by rcases s with ⟨⟨s, u⟩, r⟩; cases u; rfl
  right_inv _ := rfl

def setupPorts : Fin 7 → Tape :=
  ![.original, .cursor, .vertices, .darts, .counter, .scratch, .edge]

theorem setupPorts_injective : Function.Injective setupPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [setupPorts]

def headPorts : Fin 6 → Tape :=
  ![.original, .reverseIndex, .scan, .indexScan, .head, .scratch]

theorem headPorts_injective : Function.Injective headPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [headPorts]

def rowSources : Fin 5 → Tape := ![.vertices, .darts, .edge, .tail, .head]
def headerSources : Fin 2 → Tape := ![.vertices, .darts]
def fieldPorts : Fin 3 → Tape := ![.tail, .reverseIndex, .head]

def cleanupPorts : Fin 15 → Tape :=
  ![.original, .cursor, .scan, .vertices, .darts, .counter, .edge,
    .tail, .reverseIndex, .head, .scratch, .indexScan, .compareLeft, .compareRight, .reversed]

theorem cleanupPorts_ne_output (i : Fin 15) : cleanupPorts i ≠ .output := by
  fin_cases i <;> simp [cleanupPorts]

theorem cleanupPorts_cover (tape : Tape) (h : tape ≠ .output) :
    ∃ i, cleanupPorts i = tape := by
  cases tape
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨8, rfl⟩
  · exact ⟨9, rfl⟩
  · exact ⟨10, rfl⟩
  · exact ⟨11, rfl⟩
  · exact ⟨12, rfl⟩
  · exact ⟨13, rfl⟩
  · exact ⟨14, rfl⟩
  · exact (h rfl).elim

variable {Λ : Type} {q : Nat}

def compareStatement (stmt : TM2.Stmt Alphabet Λ
    (MachineCompare.State (GenericGraphTables.RelationTable q × Bool))) :
    TM2.Stmt Alphabet Λ (State q) :=
  MachineControl.statement id (compareEquiv q).symm stmt

def emitterStatement (stmt : TM2.Stmt Alphabet Λ ((Ambient q × Unit) × Option Bool)) :
    TM2.Stmt Alphabet Λ (State q) :=
  MachineControl.statement id (emitterEquiv q) stmt

def storeLoop (value : Bool) (next : Λ) : TM2.Stmt Alphabet Λ (State q) :=
  .load (fun state => (((value, false, none), state.1.2), none)) (.goto fun _ => next)

theorem stepAux_storeLoop (value : Bool) (next : Λ) (state : State q)
    (base : Tape → List Bool) :
    TM2.stepAux (storeLoop value next) state base =
      ⟨some next, normal state.1.2 value, base⟩ := rfl

def nextRow (next : Λ) : TM2.Stmt Alphabet Λ (State q) :=
  .push .edge (fun _ => true)
    (.load (fun state => (state.1, none)) (.goto fun _ => next))

theorem stepAux_nextRow (next : Λ) (state : State q)
    (base : Tape → List Bool) (edge : Nat) (suffix : List Bool)
    (he : base .edge = encodeWord edge ++ suffix) :
    TM2.stepAux (nextRow next) state base =
      ⟨some next, (state.1, none),
        Function.update base .edge (encodeWord (edge + 1) ++ suffix)⟩ := by
  simp [nextRow, TM2.stepAux, he, encodeWord, List.replicate_succ]

def transportInTime {K τ υ : Type} [DecidableEq K] {Γ : K → Type}
    (e : τ ≃ υ) (p : Λ → TM2.Stmt Γ Λ τ)
    {start finish : TM2.Cfg Γ Λ τ} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step p) start (some finish) budget) :
    StateTransition.EvalsToInTime (TM2.step (MachineControl.program (Equiv.refl Λ) e p))
      (MachineControl.configuration id e start)
      (some (MachineControl.configuration id e finish)) budget := by
  apply MachineComposition.liftExecutionInTime _ _ (MachineControl.configuration id e) _ run
  intro a b hab
  have h := MachineControl.step_simulation (Equiv.refl Λ) e p a
  rw [hab] at h
  exact h

end MinUncutGames.Foundations.PCP.AlphabetTable.RuntimeModel

end
section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.CompareLoop

open Turing
open MinUncutGames.Foundations.Complexity
open RuntimeModel

inductive Label
  | leftFirst | leftSecond | rightFirst | rightSecond | compare
  | equalStore | differentStore
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.leftFirst, .leftSecond, .rightFirst,
  .rightSecond, .compare, .equalStore, .differentStore]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

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
  simp only [rowLoop, ConstraintGraph.head, GenericGraphTables.semantics_tail,
    GenericGraphTables.semantics_reverse, Fin.val_inj]
  rfl

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

end MinUncutGames.Foundations.PCP.AlphabetTable.CompareLoop

end
section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.Emitter

open Turing
open MinUncutGames.Foundations.Complexity
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

inductive Command (h : Nat) (σ : Type) (bound : Nat)
  | literal (word : List Bool)
  | bit (value : σ → Bool)
  | bounded (value : σ → Fin bound)
  | scaled (source : Fin h) (coefficient : Nat)
  | scaledIf (source : Fin h) (coefficient : Nat) (active : σ → Bool)

inductive Phase (bound : Nat)
  | entry | emit (symbol : Bool) | restore | offset (value : Fin bound)
  | scanIf (active : Bool) | emitIf (active symbol : Bool)
  deriving DecidableEq, Fintype

variable {K : Type}

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := (σ × Unit) × Option Bool

def transition (_ : Unit) (_ : Bool) : Unit := ()
def payload (coefficient : Nat) (_ : Unit) (symbol : Bool) : List Bool :=
  if symbol then List.replicate coefficient true else []

def commandBits {h bound : Nat} {σ : Type} (values : Fin h → Nat) (ambient : σ) :
    Command h σ bound → List Bool
  | .literal word => word
  | .bit value => encodeWord (if value ambient then 1 else 0)
  | .bounded value => List.replicate (value ambient).val true
  | .scaled source coefficient => List.replicate (coefficient * values source) true
  | .scaledIf source coefficient active =>
      List.replicate ((if active ambient then coefficient else 0) * values source) true

def commandSteps {h bound : Nat} {σ : Type} (values : Fin h → Nat) :
    Command h σ bound → Nat
  | .literal _ | .bit _ => 1
  | .bounded _ => 2
  | .scaled source _ => 3 * (values source + 1) + 2
  | .scaledIf source _ _ => 3 * (values source + 1) + 3

variable {Λ σ : Type} {h bound : Nat} [DecidableEq K]

def commandStatement (sources : Fin h → K) (scratch output : K)
    (labels : Phase bound → Λ) (next : Λ) (command : Command h σ bound) :
    Phase bound → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .entry => match command with
    | .literal word => pushWord output word
        (.load (fun state => (state.1, none)) (.goto fun _ => next))
    | .bit value => .branch (fun state => value state.1.1)
        (pushWord output [true, false]
          (.load (fun state => (state.1, none)) (.goto fun _ => next)))
        (pushWord output [false]
          (.load (fun state => (state.1, none)) (.goto fun _ => next)))
    | .bounded value => .goto fun state => labels (.offset (value state.1.1))
    | .scaled source _ => MachineTransducerCopy.scanLoop (sources source) scratch ()
        (fun _ symbol => labels (.emit symbol)) (labels .restore)
    | .scaledIf _ _ active => .goto fun state => labels (.scanIf (active state.1.1))
  | .emit symbol => match command with
    | .scaled _ coefficient => MachineTransducerCopy.emitter output transition
        (payload coefficient) (labels .entry) () symbol
    | _ => .goto fun _ => next
  | .restore => match command with
    | .scaled source _ | .scaledIf source _ _ => Reduction.MachineTransfer.loopAt scratch (sources source)
        id false (labels .restore) (some next)
    | _ => .goto fun _ => next
  | .offset value => pushWord output (List.replicate value.val true)
      (.load (fun state => (state.1, none)) (.goto fun _ => next))
  | .scanIf active => match command with
    | .scaledIf source _ _ => MachineTransducerCopy.scanLoop (sources source) scratch ()
        (fun _ symbol => labels (.emitIf active symbol)) (labels .restore)
    | _ => .goto fun _ => next
  | .emitIf active symbol => match command with
    | .scaledIf _ coefficient _ => MachineTransducerCopy.emitter output transition
        (payload (if active then coefficient else 0)) (labels (.scanIf active)) () symbol
    | _ => .goto fun _ => next

private theorem output_encodeWord (coefficient n : Nat) :
    Reduction.MachineTransducer.output transition (payload coefficient) () (encodeWord n) =
      List.replicate (coefficient * n) true := by
  induction n with
  | zero => simp [encodeWord, Reduction.MachineTransducer.output, payload]
  | succ n ih =>
    simp only [encodeWord, List.replicate_succ, List.cons_append,
      Reduction.MachineTransducer.output, payload, ite_true, transition]
    change List.replicate coefficient true ++
      Reduction.MachineTransducer.output transition (payload coefficient) () (encodeWord n) = _
    rw [ih, ← List.replicate_add]
    congr 1
    simp [Nat.mul_succ, Nat.add_comm]

theorem commandTrace (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Phase bound → Λ) (next : Λ) (command : Command h σ bound)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ phase,
      program (labels phase) = commandStatement sources scratch output labels next command phase)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ) :
    (MachineComposition.advance (TM2.step program))^[commandSteps values command]
      (some ⟨some (labels .entry), ((ambient, ()), none), base⟩) =
      some ⟨some next, ((ambient, ()), none),
        Function.update base output ((commandBits values ambient command).reverse ++ base output)⟩ := by
  cases command with
  | literal word =>
    change some (TM2.stepAux (program (labels .entry)) ((ambient, ()), none) base) = _
    rw [atLabels]
    simp only [commandStatement, stepAux_pushWord, TM2.stepAux, commandBits]
  | bit value =>
    change some (TM2.stepAux (program (labels .entry)) ((ambient, ()), none) base) = _
    rw [atLabels]
    cases hb : value ambient <;>
      simp [commandStatement, TM2.stepAux, pushWord, commandBits, hb, encodeWord]
  | bounded value =>
    change (TM2.step program ⟨some (labels .entry), ((ambient, ()), none), base⟩).bind
      (TM2.step program) = _
    have first : TM2.step program ⟨some (labels .entry), ((ambient, ()), none), base⟩ =
        some ⟨some (labels (.offset (value ambient))), ((ambient, ()), none), base⟩ := by
      change some (TM2.stepAux (program (labels .entry)) _ _) = _
      rw [atLabels]
      rfl
    rw [first]
    change some (TM2.stepAux (program (labels (.offset (value ambient)))) _ _) = _
    rw [atLabels]
    simp only [commandStatement, stepAux_pushWord, TM2.stepAux, commandBits]
  | scaled source coefficient =>
    have emitAt : ∀ control symbol, program (labels (.emit symbol)) =
        MachineTransducerCopy.emitter output transition (payload coefficient)
          (labels .entry) control symbol := by
      intro control symbol
      cases control
      exact atLabels (.emit symbol)
    have run := MachineTransducerCopy.transduceCopyTrace (sources source) scratch output
      (sourceScratch source) (sourceOutput source) scratchOutput () transition (payload coefficient)
      (labels .entry) (labels .restore) (fun _ symbol => labels (.emit symbol)) (some next)
      program (atLabels .entry) emitAt (atLabels .restore) base scratchEmpty ambient () none
    rw [operands source, encodeWord_length, output_encodeWord] at run
    exact run
  | scaledIf source coefficient active =>
    have first : TM2.step program ⟨some (labels .entry), ((ambient, ()), none), base⟩ =
        some ⟨some (labels (.scanIf (active ambient))), ((ambient, ()), none), base⟩ := by
      change some (TM2.stepAux (program (labels .entry)) _ _) = _
      rw [atLabels]
      rfl
    have emitAt : ∀ control symbol, program (labels (.emitIf (active ambient) symbol)) =
        MachineTransducerCopy.emitter output transition
          (payload (if active ambient then coefficient else 0))
          (labels (.scanIf (active ambient))) control symbol := by
      intro control symbol
      cases control
      exact atLabels (.emitIf (active ambient) symbol)
    have run := MachineTransducerCopy.transduceCopyTrace (sources source) scratch output
      (sourceScratch source) (sourceOutput source) scratchOutput () transition
      (payload (if active ambient then coefficient else 0))
      (labels (.scanIf (active ambient))) (labels .restore)
      (fun _ symbol => labels (.emitIf (active ambient) symbol)) (some next)
      program (atLabels (.scanIf (active ambient))) emitAt (atLabels .restore)
      base scratchEmpty ambient () none
    rw [operands source, encodeWord_length, output_encodeWord] at run
    change (MachineComposition.advance (TM2.step program))^[
      (3 * (values source + 1) + 2) + 1] _ = _
    rw [Function.iterate_succ_apply]
    simp only [MachineComposition.advance_some]
    rw [first]
    exact run

abbrev Label (count bound : Nat) := Fin (count + 1) × Phase bound

def labelAt (count bound r : Nat) (phase : Phase bound) : Label count bound :=
  (⟨min r count, by omega⟩, phase)

def commandAt {count : Nat} (commands : Fin count → Command h σ bound) (r : Nat) :
    Command h σ bound :=
  if hr : r < count then commands ⟨r, hr⟩ else .literal []

def statement {count : Nat} (commands : Fin count → Command h σ bound)
    (sources : Fin h → K) (scratch output : K)
    (labels : Label count bound → Λ) (exit : Option Λ) (label : Label count bound) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  if label.1.val < count then
    commandStatement sources scratch output (fun phase => labels (labelAt count bound label.1.val phase))
      (labels (labelAt count bound (label.1.val + 1) .entry))
      (commandAt commands label.1.val) label.2
  else Reduction.MachineTransfer.exitAt output exit

def program {count : Nat} (commands : Fin count → Command h σ bound)
    (sources : Fin h → K) (scratch output : K) :
    Label count bound → TM2.Stmt (Alphabet (K := K)) (Label count bound) (State σ) :=
  statement commands sources scratch output id none

def machine [Fintype K] [Fintype σ] {count : Nat}
    (commands : Fin count → Command h σ bound) (sources : Fin h → K)
    (scratch output input : K) (ambient : σ) : FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ _ := Bool
  Λ := Label count bound
  main := labelAt count bound 0 .entry
  σ := State σ
  initialState := ((ambient, ()), none)
  m := program commands sources scratch output

def prefixBits {count : Nat} (commands : Fin count → Command h σ bound)
    (values : Fin h → Nat) (ambient : σ) : Nat → List Bool
  | 0 => []
  | r + 1 => prefixBits commands values ambient r ++
      commandBits values ambient (commandAt commands r)

def prefixSteps {count : Nat} (commands : Fin count → Command h σ bound)
    (values : Fin h → Nat) : Nat → Nat
  | 0 => 0
  | r + 1 => prefixSteps commands values r + commandSteps values (commandAt commands r)

def resultTapes (output : K) (base : K → List Bool) (bits : List Bool) : K → List Bool :=
  Function.update base output (bits.reverse ++ base output)

@[simp] theorem resultTapes_output (output : K) (base : K → List Bool) (bits : List Bool) :
    resultTapes output base bits output = bits.reverse ++ base output := by
  simp [resultTapes]

theorem resultTapes_other (output : K) (base : K → List Bool) (bits : List Bool)
    (k : K) (hk : k ≠ output) : resultTapes output base bits k = base k := by
  simp [resultTapes, hk]

theorem prefixTrace {count : Nat} (commands : Fin count → Command h σ bound)
    (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label count bound → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement commands sources scratch output labels exit label)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ) (r : Nat) (hr : r ≤ count) :
    (MachineComposition.advance (TM2.step p))^[prefixSteps commands values r]
      (some ⟨some (labels (labelAt count bound 0 .entry)), ((ambient, ()), none), base⟩) =
      some ⟨some (labels (labelAt count bound r .entry)), ((ambient, ()), none),
        resultTapes output base (prefixBits commands values ambient r)⟩ := by
  induction r with
  | zero => simp [prefixSteps, prefixBits, resultTapes]
  | succ r ih =>
    have hrc : r < count := by omega
    let prior := resultTapes output base (prefixBits commands values ambient r)
    have priorOperands : ∀ i, prior (sources i) = encodeWord (values i) := by
      intro i
      simpa [prior, resultTapes, sourceOutput i] using operands i
    have priorScratch : prior scratch = [] := by
      simpa [prior, resultTapes, scratchOutput] using scratchEmpty
    have commandAtLabels : ∀ phase, p (labels (labelAt count bound r phase)) =
        commandStatement sources scratch output (fun phase => labels (labelAt count bound r phase))
          (labels (labelAt count bound (r + 1) .entry)) (commandAt commands r) phase := by
      intro phase
      rw [atLabels]
      simp only [statement, labelAt, Nat.min_eq_left (Nat.le_of_lt hrc), hrc, ite_true]
    have one := commandTrace sources scratch output sourceScratch sourceOutput scratchOutput
      (fun phase => labels (labelAt count bound r phase))
      (labels (labelAt count bound (r + 1) .entry)) (commandAt commands r)
      p commandAtLabels values prior priorOperands priorScratch ambient
    rw [prefixSteps, Nat.add_comm, Function.iterate_add_apply, ih (by omega)]
    rw [one]
    congr 2
    simp [prior, prefixBits, resultTapes, List.reverse_append, List.append_assoc]

theorem planTrace {count : Nat} (commands : Fin count → Command h σ bound)
    (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label count bound → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement commands sources scratch output labels exit label)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ) :
    (MachineComposition.advance (TM2.step p))^[prefixSteps commands values count + 1]
      (some ⟨some (labels (labelAt count bound 0 .entry)), ((ambient, ()), none), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        resultTapes output base (prefixBits commands values ambient count)⟩ := by
  rw [Function.iterate_succ_apply', prefixTrace commands sources scratch output sourceScratch
    sourceOutput scratchOutput labels exit p atLabels values base operands scratchEmpty ambient count
    (Nat.le_refl _)]
  change some (TM2.stepAux (p (labels (labelAt count bound count .entry))) _ _) = _
  rw [atLabels]
  cases exit <;> simp [statement, labelAt, Reduction.MachineTransfer.exitAt, TM2.stepAux]

theorem prefixSteps_le {count : Nat} (commands : Fin count → Command h σ bound)
    (values : Fin h → Nat) (N : Nat) (bounded : ∀ i, values i ≤ N)
    (r : Nat) : prefixSteps commands values r ≤ r * (3 * (N + 1) + 3) := by
  induction r with
  | zero => simp [prefixSteps]
  | succ r ih =>
    have one : commandSteps values (commandAt commands r) ≤ 3 * (N + 1) + 3 := by
      cases commandAt commands r with
      | literal _ => simp only [commandSteps]; omega
      | bit _ => simp only [commandSteps]; omega
      | bounded _ => simp only [commandSteps]; omega
      | scaled source _ => have hs := bounded source; simp only [commandSteps]; omega
      | scaledIf source _ _ => have hs := bounded source; simp only [commandSteps]; omega
    calc
      prefixSteps commands values (r + 1) =
          prefixSteps commands values r + commandSteps values (commandAt commands r) := rfl
      _ ≤ r * (3 * (N + 1) + 3) + (3 * (N + 1) + 3) := Nat.add_le_add ih one
      _ = (r + 1) * (3 * (N + 1) + 3) := (Nat.succ_mul r _).symm

def planInTime {count : Nat} (commands : Fin count → Command h σ bound)
    (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label count bound → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement commands sources scratch output labels exit label)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ)
    (N : Nat) (bounded : ∀ i, values i ≤ N) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (labelAt count bound 0 .entry)), ((ambient, ()), none), base⟩
      (some ⟨exit, ((ambient, ()), none),
        resultTapes output base (prefixBits commands values ambient count)⟩)
      (count * (3 * (N + 1) + 3) + 1) where
  steps := prefixSteps commands values count + 1
  evals_in_steps := planTrace commands sources scratch output sourceScratch sourceOutput
    scratchOutput labels exit p atLabels values base operands scratchEmpty ambient
  steps_le_m := Nat.add_le_add_right (prefixSteps_le commands values N bounded count) 1

def listCommands (commands : List (Command h σ bound)) :
    Fin commands.length → Command h σ bound := fun i => commands[i]

theorem prefixBits_listCommands (commands : List (Command h σ bound))
    (values : Fin h → Nat) (ambient : σ) (r : Nat) (hr : r ≤ commands.length) :
    prefixBits (listCommands commands) values ambient r =
      (commands.take r).flatMap (commandBits values ambient) := by
  induction r with
  | zero => simp [prefixBits]
  | succ r ih =>
    have hrc : r < commands.length := by omega
    rw [prefixBits, ih (by omega), List.take_succ_eq_append_getElem hrc,
      List.flatMap_append]
    simp [commandAt, hrc, listCommands]

theorem bits_listCommands (commands : List (Command h σ bound))
    (values : Fin h → Nat) (ambient : σ) :
    prefixBits (listCommands commands) values ambient commands.length =
      commands.flatMap (commandBits values ambient) := by
  simpa using prefixBits_listCommands commands values ambient commands.length (Nat.le_refl _)

def affineCommands (terms : List (Fin h × Nat)) (offset : σ → Fin bound) :
    List (Command h σ bound) :=
  terms.map (fun term => .scaled term.1 term.2) ++ [.bounded offset, .literal [false]]

def affineValue (terms : List (Fin h × Nat)) (values : Fin h → Nat) (offset : Nat) : Nat :=
  (terms.map (fun term => term.2 * values term.1)).sum + offset

private theorem scaleBits (terms : List (Fin h × Nat)) (values : Fin h → Nat) (ambient : σ) :
    (terms.map (fun term => (Command.scaled term.1 term.2 : Command h σ bound))).flatMap
      (commandBits values ambient) =
    List.replicate ((terms.map (fun term => term.2 * values term.1)).sum) true := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
    simp only [List.map_cons, List.flatMap_cons, commandBits, List.sum_cons]
    rw [ih, List.replicate_add]

theorem affineCommands_bits (terms : List (Fin h × Nat)) (offset : σ → Fin bound)
    (values : Fin h → Nat) (ambient : σ) :
    (affineCommands terms offset).flatMap (commandBits values ambient) =
      encodeWord (affineValue terms values (offset ambient).val) := by
  simp only [affineCommands, List.flatMap_append, scaleBits, List.flatMap_cons,
    List.flatMap_nil, commandBits, List.append_nil, affineValue, encodeWord,
    List.replicate_add, List.append_assoc]

@[simp] theorem affineCommands_length (terms : List (Fin h × Nat)) (offset : σ → Fin bound) :
    (affineCommands terms offset).length = terms.length + 2 := by
  simp [affineCommands]

def bitCommands (bits : List (σ → Bool)) : List (Command h σ bound) := bits.map .bit

theorem bitCommands_bits (bits : List (σ → Bool)) (values : Fin h → Nat) (ambient : σ) :
    (bitCommands (h := h) (bound := bound) bits).flatMap (commandBits values ambient) =
      encodeWords (bits.map (fun bit => if bit ambient then 1 else 0)) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simpa only [bitCommands, List.map_cons, List.flatMap_cons, commandBits, encodeWords]
      using congrArg (encodeWord (if bit ambient then 1 else 0) ++ ·) ih

def affineInTime (terms : List (Fin h × Nat)) (offset : σ → Fin bound)
    (sources : Fin h → K) (scratch output : K)
    (sourceScratch : ∀ i, sources i ≠ scratch)
    (sourceOutput : ∀ i, sources i ≠ output) (scratchOutput : scratch ≠ output)
    (labels : Label (affineCommands terms offset).length bound → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) =
      statement (listCommands (affineCommands terms offset)) sources scratch output labels exit label)
    (values : Fin h → Nat) (base : K → List Bool)
    (operands : ∀ i, base (sources i) = encodeWord (values i))
    (scratchEmpty : base scratch = []) (ambient : σ)
    (N : Nat) (bounded : ∀ i, values i ≤ N) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels (labelAt (affineCommands terms offset).length bound 0 .entry)),
        ((ambient, ()), none), base⟩
      (some ⟨exit, ((ambient, ()), none),
        resultTapes output base (encodeWord (affineValue terms values (offset ambient).val))⟩)
      ((terms.length + 2) * (3 * (N + 1) + 3) + 1) := by
  have run := planInTime (listCommands (affineCommands terms offset)) sources scratch output
    sourceScratch sourceOutput scratchOutput labels exit p atLabels values base operands
    scratchEmpty ambient N bounded
  rw [bits_listCommands, affineCommands_bits] at run
  simpa only [affineCommands_length] using run

def Command.mapAmbient {τ : Type} (view : σ → τ) :
    Command h τ bound → Command h σ bound
  | .literal word => .literal word
  | .bit value => .bit (value ∘ view)
  | .bounded value => .bounded (value ∘ view)
  | .scaled source coefficient => .scaled source coefficient
  | .scaledIf source coefficient active => .scaledIf source coefficient (active ∘ view)

@[simp] theorem commandBits_mapAmbient {τ : Type} (view : σ → τ)
    (command : Command h τ bound) (values : Fin h → Nat) (ambient : σ) :
    commandBits values ambient (command.mapAmbient view) =
      commandBits values (view ambient) command := by
  cases command <;> rfl

@[simp] theorem commandSteps_mapAmbient {τ : Type} (view : σ → τ)
    (command : Command h τ bound) (values : Fin h → Nat) :
    commandSteps values (command.mapAmbient view) = commandSteps values command := by
  cases command <;> rfl

end MinUncutGames.Foundations.PCP.AlphabetTable.Emitter

end

end OAI
