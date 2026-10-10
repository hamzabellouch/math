import Mathlib
import OAI.Computability.DirectedFeedback.Encoding.Lookup

namespace OAI

namespace DFVSGames.Foundations.PCP.AlphabetTable.CompareLoop

open Turing
open DFVSGames.Foundations.Complexity
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

private theorem compareProgram_at_inline_CompareLoop
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
    (compareProgram_at_inline_CompareLoop program _ _ (atLabel .leftFirst))
    (compareProgram_at_inline_CompareLoop program _ _ (atLabel .leftSecond))
    (compareProgram_at_inline_CompareLoop program _ _ (atLabel .rightFirst))
    (compareProgram_at_inline_CompareLoop program _ _ (atLabel .rightSecond))
    (compareProgram_at_inline_CompareLoop program _ _ (atLabel .compare))
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
  change decide (table.rows[e].tail.val = table.rows[table.rows[e].reverseIndex].tail.val) =
    decide (table.rows[e].tail = table.rows[table.rows[e].reverseIndex].tail)
  simp only [Fin.val_inj]

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

end DFVSGames.Foundations.PCP.AlphabetTable.CompareLoop

namespace DFVSGames.Foundations.PCP.AlphabetTable.Emitter

open Turing
open DFVSGames.Foundations.Complexity
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

abbrev Alphabet {K : Type} (_ : K) := Bool
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

variable {K Λ σ : Type} {h bound : Nat} [DecidableEq K]

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

private theorem output_encodeWord_inline_Emitter (coefficient n : Nat) :
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
    rw [operands source, encodeWord_length, output_encodeWord_inline_Emitter] at run
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
    rw [operands source, encodeWord_length, output_encodeWord_inline_Emitter] at run
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

private theorem scaleBits_inline_Emitter (terms : List (Fin h × Nat)) (values : Fin h → Nat) (ambient : σ) :
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
  simp only [affineCommands, List.flatMap_append, scaleBits_inline_Emitter, List.flatMap_cons,
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

end DFVSGames.Foundations.PCP.AlphabetTable.Emitter

namespace DFVSGames.Foundations.PCP.AlphabetTable.Addresses

open DFVSGames.Foundations.Hastad
open Enumeration

abbrev Terms := List (Fin 5 × Nat)

structure Field (bound : Nat) where
  terms : Terms
  offset : Fin bound

def values (n m edge tail head : Nat) : Fin 5 → Nat := ![n, m, edge, tail, head]

def eval {bound : Nat} (field : Field bound) (inputs : Fin 5 → Nat) : Nat :=
  Emitter.affineValue field.terms inputs field.offset.val

def fieldBound (q : Nat) : Nat :=
  12 * localCount q + tapeCount q + pairTapeCount q + 1

theorem fieldBound_pos (q : Nat) : 0 < fieldBound q := by
  unfold fieldBound
  omega

theorem tapeCount_lt_bound (q : Nat) : tapeCount q < fieldBound q := by
  unfold fieldBound
  omega

theorem pairTapeCount_lt_bound (q : Nat) : pairTapeCount q < fieldBound q := by
  unfold fieldBound
  omega

theorem localCount_lt_bound (q : Nat) : localCount q < fieldBound q := by
  unfold fieldBound
  omega

theorem local_add_pair_lt_bound (q : Nat) : localCount q + pairTapeCount q < fieldBound q := by
  unfold fieldBound
  omega

theorem twelve_local_lt_bound (q : Nat) : 12 * localCount q < fieldBound q := by
  unfold fieldBound
  omega

def zeroOffset (q : Nat) : Fin (fieldBound q) := ⟨0, fieldBound_pos q⟩

def eventOffset (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q)) : Fin (fieldBound q) :=
  ⟨(localEventEquiv q event).val,
    (localEventEquiv q event).isLt.trans (localCount_lt_bound q)⟩

def rawQueryOffset (q : Nat) : Queries.RawQuery q → Fin (fieldBound q)
  | .inl (_, tape) =>
    ⟨(cubeEquiv q tape).val, (cubeEquiv q tape).isLt.trans (tapeCount_lt_bound q)⟩
  | .inr tape =>
    ⟨(pairCubeEquiv q tape).val, (pairCubeEquiv q tape).isLt.trans (pairTapeCount_lt_bound q)⟩

def reverseOffset (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : Fin (fieldBound q) :=
  ⟨(localEventEquiv q event).val * 12 + slot.val * 2 + bitValue (!orientation), by
    have he := (localEventEquiv q event).isLt
    have hs := slot.isLt
    have hb : bitValue (!orientation) < 2 := by
      simpa only [boolEquiv_val] using (boolEquiv (!orientation)).isLt
    have hbound := twelve_local_lt_bound q
    omega⟩

def headerVertices (q : Nat) : Field (fieldBound q) :=
  ⟨[(0, tapeCount q), (1, localCount q + pairTapeCount q)], zeroOffset q⟩

def headerDarts (q : Nat) : Field (fieldBound q) :=
  ⟨[(1, 12 * localCount q)], zeroOffset q⟩

def eventVertexField (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q)) :
    Field (fieldBound q) :=
  ⟨[(2, localCount q)], eventOffset q event⟩

def vertexQueryTerms (q : Nat) (side : Bool) : Terms :=
  [(1, localCount q), (if side then 4 else 3, tapeCount q)]

def edgeQueryTerms (q : Nat) : Terms :=
  [(1, localCount q), (0, tapeCount q), (2, pairTapeCount q)]

def rawQueryTerms (q : Nat) : Queries.RawQuery q → Terms
  | .inl (side, _) => vertexQueryTerms q side
  | .inr _ => edgeQueryTerms q

def rawQueryField (q : Nat) (query : Queries.RawQuery q) : Field (fieldBound q) :=
  ⟨rawQueryTerms q query, rawQueryOffset q query⟩

def reverseDartField (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : Field (fieldBound q) :=
  ⟨[(2, 12 * localCount q)], reverseOffset q event slot orientation⟩

theorem headerVertices_eval (q n m edge tail head : Nat) :
    eval (headerVertices q) (values n m edge tail head) = vertexCount n m q := by
  simp [eval, headerVertices, values, zeroOffset, Emitter.affineValue,
    vertexCount, eventCount, addressCount, Nat.mul_add,
    Nat.mul_comm, Nat.add_comm, Nat.add_assoc]

theorem headerDarts_eval (q n m edge tail head : Nat) :
    eval (headerDarts q) (values n m edge tail head) = dartCount m q := by
  simp [eval, headerDarts, values, zeroOffset, Emitter.affineValue,
    dartCount, eventCount, Nat.mul_comm, Nat.mul_assoc]

theorem eventVertexField_eval (n m q : Nat) (edge : Fin m)
    (event : AlphabetGraph.LocalEvent (Fin q)) (tail head : Nat) :
    eval (eventVertexField q event) (values n m edge.val tail head) =
      (vertexEquiv n m q (.inl (edge, event))).val := by
  rw [vertexEquiv_event_val, eventEquiv_val]
  simp [eval, eventVertexField, eventOffset, values, Emitter.affineValue, Nat.mul_comm]

theorem rawQueryField_eval (n m q : Nat) (edge : Fin m) (tail head : Fin n)
    (query : Queries.RawQuery q) :
    eval (rawQueryField q query) (values n m edge.val tail.val head.val) =
      (vertexEquiv n m q (.inr (Queries.globalize tail head edge query))).val := by
  cases query with
  | inl query =>
    rcases query with ⟨side, tape⟩
    cases side <;>
      simp [eval, rawQueryField, rawQueryTerms, vertexQueryTerms, rawQueryOffset,
        values, Emitter.affineValue, Queries.globalize, eventCount,
        Nat.mul_comm, Nat.add_assoc]
  | inr tape =>
    simp [eval, rawQueryField, rawQueryTerms, edgeQueryTerms, rawQueryOffset,
      values, Emitter.affineValue, Queries.globalize, eventCount,
      Nat.mul_comm, Nat.add_assoc]

theorem reverseDartField_eval (n m q : Nat) (edge : Fin m)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (tail head : Nat) :
    eval (reverseDartField q event slot orientation) (values n m edge.val tail head) =
      (dartEquiv m q (QueryIncidence.reverse (((edge, event), slot), orientation))).val := by
  rw [dartEquiv_reverse_val, eventEquiv_val]
  simp [eval, reverseDartField, reverseOffset, values, Emitter.affineValue,
    Nat.mul_add, Nat.mul_comm, Nat.mul_assoc,
    Nat.add_assoc]

def queryEventTerms (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) : Terms :=
  rawQueryTerms q (Queries.query (fun _ _ => false) event slot)

theorem rawQueryTerms_query (q : Nat) (P : Fin q → Fin q → Bool)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) :
    rawQueryTerms q (Queries.query P event slot) = queryEventTerms q event slot := by
  rcases event with ⟨kind, ⟨side, tape⟩, f, g, r₀, r₁, r₂⟩
  by_cases hk₀ : kind = 0 <;> by_cases hk₁ : kind = 1 <;> by_cases hk₂ : kind = 2 <;>
    simp only [queryEventTerms, Queries.query, hk₀, hk₁, hk₂, ite_true, ite_false]
  all_goals split_ifs <;> rfl

def queryEventOffset (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (P : Fin q → Fin q → Bool) : Fin (fieldBound q) :=
  rawQueryOffset q (Queries.query P event slot)

def fieldForQueryEvent (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (P : Fin q → Fin q → Bool) : Field (fieldBound q) :=
  ⟨queryEventTerms q event slot, queryEventOffset q event slot P⟩

theorem fieldForQueryEvent_eq_rawQueryField (q : Nat)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6)
    (P : Fin q → Fin q → Bool) :
    fieldForQueryEvent q event slot P = rawQueryField q (Queries.query P event slot) := by
  unfold fieldForQueryEvent queryEventOffset rawQueryField
  rw [rawQueryTerms_query]

theorem fieldForQueryEvent_eval (n m q : Nat) (edge : Fin m) (tail head : Fin n)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6)
    (P : Fin q → Fin q → Bool) :
    eval (fieldForQueryEvent q event slot P) (values n m edge.val tail.val head.val) =
      (vertexEquiv n m q
        (.inr (Queries.globalize tail head edge (Queries.query P event slot)))).val := by
  rw [fieldForQueryEvent_eq_rawQueryField]
  exact rawQueryField_eval n m q edge tail head _

theorem fieldForQueryEvent_eval_verifier (n m q : Nat)
    (G : ConstraintGraph (Fin n) (Fin m) (Fin q)) (edge : Fin m)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) :
    eval (fieldForQueryEvent q event slot (G.accepts edge))
      (values n m edge.val (G.tail edge).val (G.head edge).val) =
      (vertexEquiv n m q (.inr ((AlphabetGraph.verifier G).query (edge, event) slot))).val := by
  rw [← Queries.globalize_query G edge event slot]
  exact fieldForQueryEvent_eval n m q edge (G.tail edge) (G.head edge) event slot _

def dartTailTerms (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) : Terms :=
  if orientation then queryEventTerms q event slot else [(2, localCount q)]

def dartTailOffset (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) (P : Fin q → Fin q → Bool) : Fin (fieldBound q) :=
  if orientation then queryEventOffset q event slot P else eventOffset q event

def fieldForDartTail (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) (P : Fin q → Fin q → Bool) : Field (fieldBound q) :=
  ⟨dartTailTerms q event slot orientation, dartTailOffset q event slot orientation P⟩

theorem fieldForDartTail_eval (n m q : Nat) (edge : Fin m) (tail head : Fin n)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (P : Fin q → Fin q → Bool) :
    eval (fieldForDartTail q event slot orientation P)
      (values n m edge.val tail.val head.val) =
      (vertexEquiv n m q (if orientation then
        .inr (Queries.globalize tail head edge (Queries.query P event slot))
        else .inl (edge, event))).val := by
  cases orientation with
  | false => exact eventVertexField_eval n m q edge event tail.val head.val
  | true => exact fieldForQueryEvent_eval n m q edge tail head event slot P

def CoefficientsBounded (q : Nat) (terms : Terms) : Prop :=
  ∀ term ∈ terms, term.2 < fieldBound q

theorem headerVertices_coefficients (q : Nat) : CoefficientsBounded q (headerVertices q).terms := by
  simp only [CoefficientsBounded, headerVertices, List.mem_cons, List.not_mem_nil, or_false]
  intro term h
  rcases h with rfl | rfl
  · exact tapeCount_lt_bound q
  · exact local_add_pair_lt_bound q

theorem headerDarts_coefficients (q : Nat) : CoefficientsBounded q (headerDarts q).terms := by
  intro term h
  have heq : term = (1, 12 * localCount q) := by simpa [headerDarts] using h
  subst term
  exact twelve_local_lt_bound q

theorem eventVertexField_coefficients (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q)) :
    CoefficientsBounded q (eventVertexField q event).terms := by
  intro term h
  have heq : term = (2, localCount q) := by simpa [eventVertexField] using h
  subst term
  exact localCount_lt_bound q

theorem rawQueryTerms_coefficients (q : Nat) (query : Queries.RawQuery q) :
    CoefficientsBounded q (rawQueryTerms q query) := by
  cases query with
  | inl query =>
    rcases query with ⟨side, tape⟩
    intro term h
    simp only [rawQueryTerms, vertexQueryTerms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact localCount_lt_bound q
    · exact tapeCount_lt_bound q
  | inr tape =>
    intro term h
    simp only [rawQueryTerms, edgeQueryTerms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact localCount_lt_bound q
    · exact tapeCount_lt_bound q
    · exact pairTapeCount_lt_bound q

theorem queryEventTerms_coefficients (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) : CoefficientsBounded q (queryEventTerms q event slot) :=
  rawQueryTerms_coefficients q _

theorem reverseDartField_coefficients (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) :
    CoefficientsBounded q (reverseDartField q event slot orientation).terms := by
  intro term h
  have heq : term = (2, 12 * localCount q) := by simpa [reverseDartField] using h
  subst term
  exact twelve_local_lt_bound q

theorem rawQueryTerms_length_le (q : Nat) (query : Queries.RawQuery q) :
    (rawQueryTerms q query).length ≤ 3 := by
  cases query with
  | inl query => rcases query with ⟨side, tape⟩; simp [rawQueryTerms, vertexQueryTerms]
  | inr tape => simp [rawQueryTerms, edgeQueryTerms]

theorem queryEventTerms_length_le (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) : (queryEventTerms q event slot).length ≤ 3 :=
  rawQueryTerms_length_le q _

theorem dartTailTerms_coefficients (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) :
    CoefficientsBounded q (dartTailTerms q event slot orientation) := by
  cases orientation with
  | false => exact eventVertexField_coefficients q event
  | true => exact queryEventTerms_coefficients q event slot

theorem dartTailTerms_length_le (q : Nat) (event : AlphabetGraph.LocalEvent (Fin q))
    (slot : Fin 6) (orientation : Bool) :
    (dartTailTerms q event slot orientation).length ≤ 3 := by
  cases orientation with
  | false => simp [dartTailTerms]
  | true => exact queryEventTerms_length_le q event slot

theorem offset_lt {bound : Nat} (field : Field bound) : field.offset.val < bound :=
  field.offset.isLt

end DFVSGames.Foundations.PCP.AlphabetTable.Addresses

end OAI
