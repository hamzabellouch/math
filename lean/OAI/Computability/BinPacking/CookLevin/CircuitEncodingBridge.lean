import Mathlib.Data.List.FinRange
import Mathlib.Tactic.DeriveFintype
import OAI.Computability.BinPacking.Computation.MachineHorner
import OAI.Computability.BinPacking.CookLevin.ConfigIndex

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel

open Turing
open BinPackingGames.Foundations.Hastad
open BinPackingGames.Reduction

def gateTemplate (tag : Fin 5) (position : Fin 9) : Fin 3 × Bool :=
  match tag.val with
  | 0 => (0, false)
  | 1 => (0, true)
  | 2 => [(0, true), (1, true), (1, true),
      (0, false), (1, false), (1, false),
      (0, true), (1, true), (1, true)].get position
  | 3 => [(0, false), (1, true), (1, true),
      (0, false), (2, true), (2, true),
      (0, true), (1, false), (2, false)].get position
  | _ => [(0, true), (1, false), (1, false),
      (0, true), (2, false), (2, false),
      (0, false), (1, true), (2, true)].get position

structure Record where
  tag : Fin 5
  output : Nat
  first : Nat
  second : Nat
  deriving DecidableEq

def Record.slot (r : Record) (j : Fin 3) : Nat :=
  match j.val with
  | 0 => r.output
  | 1 => r.first
  | _ => r.second

def Record.words (r : Record) : List Nat :=
  [r.tag.val, r.output, r.first, r.second]

def Record.bits (r : Record) : List Bool := encodeWords r.words

def Record.fieldValue (r : Record) (j : Fin 4) : Nat :=
  match j.val with
  | 0 => r.tag.val
  | 1 => r.output
  | 2 => r.first
  | _ => r.second

def templateWords (tag : Fin 5) (values : Fin 3 → Nat) : List Nat :=
  (List.finRange 9).flatMap fun j =>
    [values (gateTemplate tag j).1, if (gateTemplate tag j).2 then 1 else 0]

def Record.outputWords (r : Record) : List Nat := templateWords r.tag r.slot
def Record.outputBits (r : Record) : List Bool := encodeWords r.outputWords

def outputWords (selected : Nat) : List Nat :=
  [selected, 1, selected, 1, selected, 1]

inductive Tape where
  | input | header | counter | selected | field (slot : Fin 4)
  | scratch | reversed | output
  deriving DecidableEq, Fintype

inductive Context where
  | header (slot : Fin 2)
  | gate (tag : Fin 5) (position : Fin 9)
  | output (position : Fin 3)
  deriving DecidableEq, Fintype

abbrev State := (Unit × Context) × Option Bool
abbrev Alphabet (_ : Tape) := Bool

inductive Label where
  | headerStart (slot : Fin 3)
  | headerLoop (slot : Fin 3)
  | setup (context : Context)
  | scan (context : Context)
  | emit (context control : Context) (symbol : Bool)
  | restore (context : Context)
  | clearHeader | guard
  | fieldStart (slot : Fin 4)
  | fieldLoop (slot : Fin 4)
  | decodeTag
  | cleanup (slot : Fin 4)
  | finalCounter | clearSelected | finalReverse
  deriving DecidableEq, Fintype

def defaultControl : Context := .header 0
def initialState : State := (((), defaultControl), none)

def headerTape (slot : Fin 3) : Tape :=
  match slot.val with
  | 0 => .header
  | 1 => .counter
  | _ => .selected

def headerNext (slot : Fin 3) : Option Label :=
  if h : slot.val + 1 < 3 then some (.headerStart ⟨slot.val + 1, h⟩)
  else some (.setup (.header 0))

def contextSource : Context → Tape
  | .header j => if j.val = 0 then .header else .counter
  | .gate tag j => .field ⟨(gateTemplate tag j).1.val + 1, by
      have := (gateTemplate tag j).1.isLt
      omega⟩
  | .output _ => .selected

def affineEmit (scale offset : Nat) : Bool → List Bool
  | true => List.replicate scale true
  | false => encodeWord offset

def literalEmit (positive : Bool) : Bool → List Bool
  | true => [true]
  | false => [false] ++ encodeWord (if positive then 1 else 0)

def emission : Context → Bool → List Bool
  | .header j => if j.val = 0 then affineEmit 1 0 else affineEmit 3 1
  | .gate tag j => literalEmit (gateTemplate tag j).2
  | .output _ => literalEmit true

def contextNext : Context → Option Label
  | .header j => if j.val = 0 then some (.setup (.header 1)) else some .clearHeader
  | .gate tag j => if h : j.val + 1 < 9 then
      some (.setup (.gate tag ⟨j.val + 1, h⟩)) else some (.cleanup 0)
  | .output j => if h : j.val + 1 < 3 then
      some (.setup (.output ⟨j.val + 1, h⟩)) else some .finalCounter

def cleanupNext (j : Fin 4) : Label :=
  if h : j.val + 1 < 4 then .cleanup ⟨j.val + 1, h⟩ else .guard

def drain (tape : Tape) (again next : Label) : TM2.Stmt Alphabet Label State :=
  .pop tape (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun _ => again)
      (.load (fun state => (state.1, none)) (.goto fun _ => next)))

def resetGoto (next : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => initialState) (.goto fun _ => next)

def tagDecoder : Nat → Fin 5 → TM2.Stmt Alphabet Label State
  | 0, tag => .pop (.field 0) (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false) .halt
        (resetGoto (.setup (.gate tag 0))))
  | fuel + 1, tag => .pop (.field 0) (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (tagDecoder fuel ⟨min (tag.val + 1) 4, by omega⟩)
        (resetGoto (.setup (.gate tag 0))))

def program : Label → TM2.Stmt Alphabet Label State
  | .headerStart j => SourceMachine.fieldStart (headerTape j) (.headerLoop j)
  | .headerLoop j => SourceMachine.fieldLoop .input (headerTape j) (.headerLoop j)
      (headerNext j)
  | .setup c => .load (fun _ => (((), c), none)) (.goto fun _ => .scan c)
  | .scan c => MachineTransducerCopy.scanLoop (contextSource c) .scratch
      defaultControl (fun q b => .emit c q b) (.restore c)
  | .emit c q b => MachineTransducerCopy.emitter .reversed (fun q _ => q)
      emission (.scan c) q b
  | .restore c => MachineTransfer.loopAt .scratch (contextSource c) id false
      (.restore c) (contextNext c)
  | .clearHeader => drain .header .clearHeader .guard
  | .guard => MachineUnaryCounter.guard .counter (.fieldStart 0) (.setup (.output 0))
  | .fieldStart j => SourceMachine.fieldStart (.field j) (.fieldLoop j)
  | .fieldLoop j => SourceMachine.fieldLoop .input (.field j) (.fieldLoop j)
      (SourceMachine.fieldNext Label.fieldStart (some .decodeTag) j)
  | .decodeTag => tagDecoder 4 0
  | .cleanup j => drain (.field j) (.cleanup j) (cleanupNext j)
  | .finalCounter => .pop .counter (fun state _ => (state.1, none))
      (.goto fun _ => .clearSelected)
  | .clearSelected => drain .selected .clearSelected .finalReverse
  | .finalReverse => MachineTransfer.loopAt .reversed .output id false .finalReverse none

def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel

namespace BinPackingGames.Foundations.Complexity.CookLevin

open CircuitProducerModel

def gateRecord (output : Nat) : Gate → Record
  | .const false => ⟨0, output, 0, 0⟩
  | .const true => ⟨1, output, 0, 0⟩
  | .not a => ⟨2, output, a, 0⟩
  | .and a b => ⟨3, output, a, b⟩
  | .or a b => ⟨4, output, a, b⟩

def gateRecords (start : Nat) : List Gate → List Record
  | [] => []
  | g :: gs => gateRecord start g :: gateRecords (start + 1) gs

def Circuit.records (C : Circuit) : List Record := gateRecords C.inputs C.gates

def recordsWords (rs : List Record) : List Nat := rs.flatMap Record.words
def recordsBits (rs : List Record) : List Bool := encodeWords (recordsWords rs)

def circuitWords (C : Circuit) : List Nat :=
  [C.wires, C.gates.length, C.output.val] ++ recordsWords C.records

def circuitBits (C : Circuit) : List Bool := encodeWords (circuitWords C)

@[simp] theorem gateRecords_length (start : Nat) (gs : List Gate) :
    (gateRecords start gs).length = gs.length := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih => simp [gateRecords, ih]

@[simp] theorem Circuit.records_length (C : Circuit) : C.records.length = C.gates.length :=
  gateRecords_length C.inputs C.gates

@[simp] theorem recordsWords_cons (r : Record) (rs : List Record) :
    recordsWords (r :: rs) = r.words ++ recordsWords rs := rfl

@[simp] theorem recordsBits_cons (r : Record) (rs : List Record) :
    recordsBits (r :: rs) = r.bits ++ recordsBits rs := by
  simp [recordsBits, Record.bits]

@[simp] theorem recordsWords_length (rs : List Record) :
    (recordsWords rs).length = 4 * rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      rw [recordsWords_cons, List.length_append, ih]
      simp only [Record.words, List.length_cons, List.length_nil]
      omega

@[simp] theorem circuitWords_length (C : Circuit) :
    (circuitWords C).length = 3 + 4 * C.gates.length := by
  simp [circuitWords]
  omega

def gateFromFields (tag first second : Nat) : Gate :=
  match tag with
  | 0 => .const false
  | 1 => .const true
  | 2 => .not first
  | 3 => .and first second
  | _ => .or first second

def decodeGateWords : List Nat → List Gate
  | tag :: _ :: first :: second :: rest =>
      gateFromFields tag first second :: decodeGateWords rest
  | _ => []

theorem decodeGateWords_gateRecord (output : Nat) (g : Gate) (rest : List Nat) :
    decodeGateWords ((gateRecord output g).words ++ rest) =
      g :: decodeGateWords rest := by
  cases g with
  | const b => cases b <;> rfl
  | not a => rfl
  | and a b => rfl
  | or a b => rfl

@[simp] theorem decodeGateWords_gateRecords (start : Nat) (gs : List Gate) :
    decodeGateWords (recordsWords (gateRecords start gs)) = gs := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih =>
      rw [gateRecords, recordsWords_cons, decodeGateWords_gateRecord, ih]

theorem circuitWords_injective : Function.Injective circuitWords := by
  intro C D h
  have hh : C.wires = D.wires ∧ C.gates.length = D.gates.length ∧
      C.output.val = D.output.val ∧ recordsWords C.records = recordsWords D.records := by
    simpa only [circuitWords, List.cons_append, List.nil_append, List.cons.injEq] using h
  have hg : C.gates = D.gates := by
    have hd := congrArg decodeGateWords hh.2.2.2
    simpa only [Circuit.records, decodeGateWords_gateRecords] using hd
  have hi : C.inputs = D.inputs := by
    have hw := hh.1
    simp only [Circuit.wires] at hw
    rw [hg] at hw
    omega
  cases C with
  | mk ci cg co cx =>
    cases D with
    | mk di dg dord dx =>
      dsimp at hi hg hh
      subst di
      subst dg
      have hx : cx = dx := Fin.ext hh.2.2.1
      subst dx
      rfl

theorem circuitBits_injective : Function.Injective circuitBits := by
  intro C D h
  exact circuitWords_injective (encodeWords_injective h)

theorem gateRecord_fields_le (start bound : Nat) (g : Gate)
    (hs : start ≤ bound) (hg : g.Bounded bound) :
    ∀ n ∈ (gateRecord start g).words, n ≤ bound + 4 := by
  cases g with
  | const b => cases b <;> simp [gateRecord, Record.words] <;> omega
  | not a => simp [gateRecord, Record.words, Gate.Bounded] at *; omega
  | and a b => simp [gateRecord, Record.words, Gate.Bounded] at *; omega
  | or a b => simp [gateRecord, Record.words, Gate.Bounded] at *; omega

theorem gateRecords_fields_le (start : Nat) (gs : List Gate) (ho : Ordered start gs) :
    ∀ n ∈ recordsWords (gateRecords start gs), n ≤ start + gs.length + 4 := by
  induction gs generalizing start with
  | nil => simp [gateRecords, recordsWords]
  | cons g gs ih =>
      rcases (ordered_cons start g gs).mp ho with ⟨hg, hgs⟩
      intro n hn
      rw [gateRecords, recordsWords_cons, List.mem_append] at hn
      rcases hn with hn | hn
      · have h := gateRecord_fields_le start start g (Nat.le_refl _) hg n hn
        simp only [List.length_cons]
        omega
      · have h := ih (start + 1) hgs n hn
        simp only [List.length_cons]
        omega

theorem circuitWords_bounded (C : Circuit) :
    ∀ n ∈ circuitWords C, n ≤ C.wires + 4 := by
  intro n hn
  simp only [circuitWords, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with (rfl | rfl | rfl) | hn
  · omega
  · simp only [Circuit.wires]; omega
  · have := C.output.isLt
    change C.output.val ≤ C.inputs + C.gates.length + 4
    omega
  · exact gateRecords_fields_le C.inputs C.gates C.ordered n hn

theorem circuitBits_length_le (C : Circuit) :
    (circuitBits C).length ≤ (3 + 4 * C.gates.length) * (C.wires + 5) := by
  have h := encodeWords_length_le (circuitWords C) (C.wires + 4)
    (circuitWords_bounded C)
  simpa only [circuitBits, circuitWords_length, Nat.add_assoc] using h

theorem circuit_header_le_length (C : Circuit) :
    C.wires + C.gates.length + C.output.val + 3 ≤ (circuitBits C).length := by
  simp only [circuitBits, circuitWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end BinPackingGames.Foundations.Complexity.CookLevin

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission

open Turing
open BinPackingGames.Reduction
open CircuitProducerModel

theorem contextSource_ne_scratch (context : Context) :
    contextSource context ≠ Tape.scratch := by
  cases context with
  | header slot => simp only [contextSource]; split <;> simp
  | gate tag position => simp [contextSource]
  | output position => simp [contextSource]

theorem contextSource_ne_reversed (context : Context) :
    contextSource context ≠ Tape.reversed := by
  cases context with
  | header slot => simp only [contextSource]; split <;> simp
  | gate tag position => simp [contextSource]
  | output position => simp [contextSource]

def contextOutput (context : Context) (base : Tape → List Bool) : List Bool :=
  MachineTransducer.output (fun control _ => control) emission
    context (base (contextSource context))

def contextSteps (context : Context) (base : Tape → List Bool) : Nat :=
  3 * (base (contextSource context)).length + 3

def contextTapes (context : Context) (base : Tape → List Bool) : Tape → List Bool :=
  Function.update base .reversed ((contextOutput context base).reverse ++ base .reversed)

@[simp] theorem contextTapes_other (context : Context) (base : Tape → List Bool)
    (tape : Tape) (different : tape ≠ .reversed) :
    contextTapes context base tape = base tape := by
  simp [contextTapes, different]

@[simp] theorem contextTapes_source (context other : Context) (base : Tape → List Bool) :
    contextTapes context base (contextSource other) = base (contextSource other) :=
  contextTapes_other context base _ (contextSource_ne_reversed other)

@[simp] theorem contextTapes_scratch (context : Context) (base : Tape → List Bool) :
    contextTapes context base .scratch = base .scratch :=
  contextTapes_other context base _ (by decide)

@[simp] theorem contextOutput_update (context : Context) (base : Tape → List Bool)
    (out : List Bool) :
    contextOutput context (Function.update base .reversed out) = contextOutput context base := by
  simp [contextOutput, contextSource_ne_reversed]

@[simp] theorem contextSteps_update (context : Context) (base : Tape → List Bool)
    (out : List Bool) :
    contextSteps context (Function.update base .reversed out) = contextSteps context base := by
  simp [contextSteps, contextSource_ne_reversed]

theorem setupStep (context : Context) (base : Tape → List Bool) (state : State) :
    TM2.step program ⟨some (.setup context), state, base⟩ =
      some ⟨some (.scan context), (((), context), none), base⟩ := rfl

theorem contextTrace (context : Context) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State) :
    (MachineComposition.advance (TM2.step program))^[contextSteps context base]
      (some ⟨some (.setup context), state, base⟩) =
      some ⟨contextNext context, initialState, contextTapes context base⟩ := by
  have copied := MachineTransducerCopy.transduceCopyTrace
    (contextSource context) Tape.scratch Tape.reversed
    (contextSource_ne_scratch context) (contextSource_ne_reversed context) (by decide)
    defaultControl (fun control _ => control) emission
    (.scan context) (.restore context) (fun control symbol => .emit context control symbol)
    (contextNext context) program rfl (by intros; rfl) rfl base scratchEmpty () context none
  rw [contextSteps, show 3 * (base (contextSource context)).length + 3 =
      (3 * (base (contextSource context)).length + 2) + 1 by omega,
    Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step program))^[
    3 * (base (contextSource context)).length + 2]
    (TM2.step program ⟨some (.setup context), state, base⟩) = _
  rw [setupStep]
  exact copied

def contextInTime (context : Context) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.setup context), state, base⟩
      (some ⟨contextNext context, initialState, contextTapes context base⟩)
      (contextSteps context base) where
  steps := contextSteps context base
  evals_in_steps := contextTrace context base scratchEmpty state
  steps_le_m := Nat.le_refl _

theorem output_eq_flatMap (context : Context) (input : List Bool) :
    MachineTransducer.output (fun control _ => control) emission context input =
      input.flatMap (emission context) := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
    simp only [MachineTransducer.output, List.flatMap_cons, ih]

theorem literalEmit_word (positive : Bool) (value : Nat) :
    (encodeWord value).flatMap (literalEmit positive) =
      encodeWords [value, if positive then 1 else 0] := by
  induction value with
  | zero => simp [encodeWord, encodeWords, literalEmit]
  | succ value ih =>
    simpa [encodeWord, encodeWords, List.replicate_succ, literalEmit] using
      congrArg (List.cons true) ih

theorem affineEmit_word (scale offset value : Nat) :
    (encodeWord value).flatMap (affineEmit scale offset) =
      encodeWord (offset + scale * value) := by
  have hrep : (List.replicate value true).flatMap (affineEmit scale offset) =
      List.replicate (scale * value) true := by
    rw [List.flatMap_replicate]
    change (List.replicate value (List.replicate scale true)).flatten = _
    rw [List.flatten_replicate_replicate, Nat.mul_comm value scale]
  simp only [encodeWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, hrep, affineEmit]
  rw [← List.append_assoc, List.replicate_append_replicate, Nat.add_comm (scale * value) offset]

def contextWords (context : Context) (value : Nat) : List Nat :=
  match context with
  | .header j => if j.val = 0 then [value] else [3 * value + 1]
  | .gate tag j => [value, if (gateTemplate tag j).2 then 1 else 0]
  | .output _ => [value, 1]

theorem output_word (context : Context) (value : Nat) :
    MachineTransducer.output (fun control _ => control) emission context (encodeWord value) =
      encodeWords (contextWords context value) := by
  rw [output_eq_flatMap]
  cases context with
  | header j =>
    by_cases hj : j.val = 0 <;>
      simp [emission, contextWords, hj, affineEmit_word, encodeWords, Nat.add_comm]
  | gate tag j => exact literalEmit_word (gateTemplate tag j).2 value
  | output j => simpa [emission, contextWords] using literalEmit_word true value

theorem contextTrace_word (context : Context) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State) (value : Nat)
    (cached : base (contextSource context) = encodeWord value) :
    (MachineComposition.advance (TM2.step program))^[3 * (value + 1) + 3]
      (some ⟨some (.setup context), state, base⟩) =
      some ⟨contextNext context, initialState,
        Function.update base .reversed
          ((encodeWords (contextWords context value)).reverse ++ base .reversed)⟩ := by
  simpa only [contextSteps, contextTapes, contextOutput, cached, encodeWord_length, output_word]
    using contextTrace context base scratchEmpty state

def contextListOutput (contexts : List Context) (base : Tape → List Bool) : List Bool :=
  contexts.flatMap (fun context => contextOutput context base)

def contextListSteps (contexts : List Context) (base : Tape → List Bool) : Nat :=
  (contexts.map (fun context => contextSteps context base)).sum

def contextListStart (contexts : List Context) (exit : Option Label) : Option Label :=
  match contexts with
  | [] => exit
  | context :: _ => some (.setup context)

def ContextListLinked : List Context → Option Label → Prop
  | [], _ => True
  | context :: rest, exit =>
    contextNext context = contextListStart rest exit ∧ ContextListLinked rest exit

@[simp] theorem contextListOutput_update (contexts : List Context) (base : Tape → List Bool)
    (out : List Bool) :
    contextListOutput contexts (Function.update base .reversed out) = contextListOutput contexts base := by
  simp [contextListOutput]

@[simp] theorem contextListSteps_update (contexts : List Context) (base : Tape → List Bool)
    (out : List Bool) :
    contextListSteps contexts (Function.update base .reversed out) = contextListSteps contexts base := by
  simp [contextListSteps]

private theorem chain {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (first : f^[m] x = y) (second : f^[n] y = z) : f^[n + m] x = z := by
  rw [Function.iterate_add_apply, first, second]

theorem contextListTrace (contexts : List Context) (exit : Option Label)
    (linked : ContextListLinked contexts exit) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State)
    (emptyInitial : contexts = [] → state = initialState) :
    (MachineComposition.advance (TM2.step program))^[contextListSteps contexts base]
      (some ⟨contextListStart contexts exit, state, base⟩) =
      some ⟨exit, initialState, Function.update base .reversed
        ((contextListOutput contexts base).reverse ++ base .reversed)⟩ := by
  induction contexts generalizing base state with
  | nil =>
    rw [emptyInitial rfl]
    simp [contextListSteps, contextListOutput, contextListStart]
  | cons context rest ih =>
    let after := contextTapes context base
    have first := contextTrace context base scratchEmpty state
    have second := ih linked.2 after (by simpa [after] using scratchEmpty)
      initialState (by intro _; rfl)
    rw [linked.1] at first
    have combined := chain first second
    simp only [after, contextTapes, contextListSteps_update, contextListOutput_update,
      Function.update_self, Function.update_idem] at combined
    rw [show contextListSteps (context :: rest) base =
        contextListSteps rest base + contextSteps context base by
      simp [contextListSteps, Nat.add_comm]]
    simpa only [contextListStart, contextListOutput, List.flatMap_cons,
      List.reverse_append, List.append_assoc] using combined

def gateContexts (tag : Fin 5) : List Context :=
  (List.finRange 9).map (Context.gate tag)

def outputContexts : List Context := [.output 0, .output 1, .output 2]

theorem gateContexts_linked (tag : Fin 5) :
    ContextListLinked (gateContexts tag) (some (.cleanup 0)) := by
  simp [gateContexts, List.finRange, List.ofFn_succ, ContextListLinked,
    contextListStart, contextNext]

theorem outputContexts_linked :
    ContextListLinked outputContexts (some .finalCounter) := by
  simp [outputContexts, ContextListLinked, contextListStart, contextNext]

theorem contextOutput_gate_word (record : Record) (position : Fin 9)
    (base : Tape → List Bool)
    (h1 : base (.field 1) = encodeWord record.output)
    (h2 : base (.field 2) = encodeWord record.first)
    (h3 : base (.field 3) = encodeWord record.second) :
    contextOutput (.gate record.tag position) base = encodeWords
      [record.slot (gateTemplate record.tag position).1,
        if (gateTemplate record.tag position).2 then 1 else 0] := by
  have fields (slot : Fin 3) :
      base (.field ⟨slot.val + 1, by omega⟩) = encodeWord (record.slot slot) := by
    have slotCases : slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 2 := by omega
    rcases slotCases with h | h | h
    · simpa [Record.slot, h] using h1
    · simpa [Record.slot, h] using h2
    · simpa [Record.slot, h] using h3
  unfold contextOutput
  rw [show base (contextSource (.gate record.tag position)) =
      encodeWord (record.slot (gateTemplate record.tag position).1) from fields _]
  exact output_word (.gate record.tag position) _

theorem encodeWords_flatMap {A : Type*} (items : List A) (words : A → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun item => encodeWords (words item)) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem gateOutput_words (record : Record) (base : Tape → List Bool)
    (h1 : base (.field 1) = encodeWord record.output)
    (h2 : base (.field 2) = encodeWord record.first)
    (h3 : base (.field 3) = encodeWord record.second) :
    contextListOutput (gateContexts record.tag) base = record.outputBits := by
  simp only [contextListOutput, gateContexts, List.flatMap_map,
    Record.outputBits, Record.outputWords, templateWords, encodeWords_flatMap]
  congr 1
  funext position
  exact contextOutput_gate_word record position base h1 h2 h3

def gateSteps (record : Record) : Nat :=
  ((List.finRange 9).map fun position =>
    3 * (record.slot (gateTemplate record.tag position).1 + 1) + 3).sum

theorem gateSteps_eq (record : Record) (base : Tape → List Bool)
    (h1 : base (.field 1) = encodeWord record.output)
    (h2 : base (.field 2) = encodeWord record.first)
    (h3 : base (.field 3) = encodeWord record.second) :
    contextListSteps (gateContexts record.tag) base = gateSteps record := by
  have fields (slot : Fin 3) :
      base (.field ⟨slot.val + 1, by omega⟩) = encodeWord (record.slot slot) := by
    have slotCases : slot.val = 0 ∨ slot.val = 1 ∨ slot.val = 2 := by omega
    rcases slotCases with h | h | h
    · simpa [Record.slot, h] using h1
    · simpa [Record.slot, h] using h2
    · simpa [Record.slot, h] using h3
  simp only [contextListSteps, gateContexts, List.map_map, gateSteps]
  congr 2
  funext position
  simp only [Function.comp_apply, contextSteps, contextSource, fields, encodeWord_length]

theorem slot_le_sum (record : Record) (slot : Fin 3) :
    record.slot slot ≤ record.output + record.first + record.second := by
  unfold Record.slot
  split <;> omega

private theorem sum_map_le_length_mul {A : Type*} (items : List A)
    (value : A → Nat) (bound : Nat) (bounded : ∀ item ∈ items, value item ≤ bound) :
    (items.map value).sum ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons item rest ih =>
    have head := bounded item (by simp)
    have tail := ih (fun a ha => bounded a (by simp [ha]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem gateSteps_le (record : Record) :
    gateSteps record ≤ 27 * (record.output + record.first + record.second) + 54 := by
  have bound := sum_map_le_length_mul (List.finRange 9)
    (fun position => 3 * (record.slot (gateTemplate record.tag position).1 + 1) + 3)
    (3 * (record.output + record.first + record.second) + 6) (by
      intro position _
      have := slot_le_sum record (gateTemplate record.tag position).1
      omega)
  simp only [List.length_finRange] at bound
  unfold gateSteps
  omega

private theorem length_flatMap_le_length_mul {A : Type*} (items : List A)
    (word : A → List Bool) (bound : Nat) (bounded : ∀ item ∈ items, (word item).length ≤ bound) :
    (items.flatMap word).length ≤ items.length * bound := by
  induction items with
  | nil => simp
  | cons item rest ih =>
    have head := bounded item (by simp)
    have tail := ih (fun a ha => bounded a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      Nat.add_mul, Nat.one_mul]
    omega

theorem outputBits_length_le (record : Record) :
    record.outputBits.length ≤ 9 * (record.output + record.first + record.second) + 27 := by
  have bound := length_flatMap_le_length_mul (List.finRange 9)
    (fun position => encodeWords
      [record.slot (gateTemplate record.tag position).1,
        if (gateTemplate record.tag position).2 then 1 else 0])
    (record.output + record.first + record.second + 3) (by
      intro position _
      have index := slot_le_sum record (gateTemplate record.tag position).1
      have sign : (if (gateTemplate record.tag position).2 then 1 else 0 : Nat) ≤ 1 := by
        split <;> omega
      simp only [encodeWords, List.length_append, encodeWord_length, List.length_nil]
      omega)
  simp only [List.length_finRange] at bound
  unfold Record.outputBits Record.outputWords templateWords
  rw [encodeWords_flatMap]
  omega

theorem recordBits_length (record : Record) :
    record.bits.length = record.tag.val + record.output + record.first + record.second + 4 := by
  simp [Record.bits, Record.words, encodeWords_length]
  omega

theorem gateSteps_le_inputSize (record : Record) :
    gateSteps record ≤ 27 * record.bits.length := by
  have bound := gateSteps_le record
  rw [recordBits_length]
  omega

theorem outputBits_length_le_inputSize (record : Record) :
    record.outputBits.length ≤ 9 * record.bits.length := by
  have bound := outputBits_length_le record
  rw [recordBits_length]
  omega

theorem gateTrace (record : Record) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State)
    (h1 : base (.field 1) = encodeWord record.output)
    (h2 : base (.field 2) = encodeWord record.first)
    (h3 : base (.field 3) = encodeWord record.second) :
    (MachineComposition.advance (TM2.step program))^[gateSteps record]
      (some ⟨some (.setup (.gate record.tag 0)), state, base⟩) =
      some ⟨some (.cleanup 0), initialState, Function.update base .reversed
        (record.outputBits.reverse ++ base .reversed)⟩ := by
  have trace := contextListTrace (gateContexts record.tag) (some (.cleanup 0))
    (gateContexts_linked record.tag) base scratchEmpty state
    (by intro h; have := congrArg List.length h; simp [gateContexts] at this)
  rw [gateSteps_eq record base h1 h2 h3, gateOutput_words record base h1 h2 h3] at trace
  simpa [contextListStart, gateContexts, List.finRange] using trace

def gateInTime (record : Record) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State)
    (h1 : base (.field 1) = encodeWord record.output)
    (h2 : base (.field 2) = encodeWord record.first)
    (h3 : base (.field 3) = encodeWord record.second) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.setup (.gate record.tag 0)), state, base⟩
      (some ⟨some (.cleanup 0), initialState, Function.update base .reversed
        (record.outputBits.reverse ++ base .reversed)⟩)
      (gateSteps record) where
  steps := gateSteps record
  evals_in_steps := gateTrace record base scratchEmpty state h1 h2 h3
  steps_le_m := Nat.le_refl _

theorem outputTrace (selected : Nat) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State)
    (cached : base .selected = encodeWord selected) :
    (MachineComposition.advance (TM2.step program))^[9 * (selected + 1) + 9]
      (some ⟨some (.setup (.output 0)), state, base⟩) =
      some ⟨some .finalCounter, initialState, Function.update base .reversed
        ((encodeWords (outputWords selected)).reverse ++ base .reversed)⟩ := by
  have trace := contextListTrace outputContexts (some .finalCounter)
    outputContexts_linked base scratchEmpty state (by simp [outputContexts])
  have steps : contextListSteps outputContexts base = 9 * (selected + 1) + 9 := by
    simp [contextListSteps, outputContexts, contextSteps, contextSource, cached]
    omega
  have out : contextListOutput outputContexts base = encodeWords (outputWords selected) := by
    simp [contextListOutput, outputContexts, contextOutput, contextSource, cached,
      output_word, contextWords, outputWords, encodeWords, List.append_assoc]
  rw [steps, out] at trace
  exact trace

def outputInTime (selected : Nat) (base : Tape → List Bool)
    (scratchEmpty : base .scratch = []) (state : State)
    (cached : base .selected = encodeWord selected) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.setup (.output 0)), state, base⟩
      (some ⟨some .finalCounter, initialState, Function.update base .reversed
        ((encodeWords (outputWords selected)).reverse ++ base .reversed)⟩)
      (9 * (selected + 1) + 9) where
  steps := 9 * (selected + 1) + 9
  evals_in_steps := outputTrace selected base scratchEmpty state cached
  steps_le_m := Nat.le_refl _

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitEmission

namespace BinPackingGames.Foundations.Complexity.CookLevin.PostfixModel

inductive Token where
  | const (value : Bool)
  | not | and | or
  | input (wire : Nat)
  deriving DecidableEq

namespace Token

def tag : Token → Fin 6
  | .const false => 0
  | .const true => 1
  | .not => 2
  | .and => 3
  | .or => 4
  | .input _ => 5

def words : Token → List Nat
  | .const false => [0]
  | .const true => [1]
  | .not => [2]
  | .and => [3]
  | .or => [4]
  | .input wire => [5, wire]

def bits (token : Token) : List Bool := encodeWords token.words

def takeGate : Token → List Nat → Option (Gate × List Nat)
  | .const value, roots => some (.const value, roots)
  | .input wire, roots => some (.or wire wire, roots)
  | .not, arg :: roots => some (.not arg, roots)
  | .and, right :: left :: roots => some (.and left right, roots)
  | .or, right :: left :: roots => some (.or left right, roots)
  | _, _ => none

end Token

def tokenWords (tokens : List Token) : List Nat := tokens.flatMap Token.words
def tokenBits (tokens : List Token) : List Bool := encodeWords (tokenWords tokens)

def compileTokens (start : Nat) (roots : List Nat) :
    List Token → Option (Nat × List Nat × List Gate)
  | [] => some (start, roots, [])
  | token :: tokens => do
      let (gate, remaining) ← token.takeGate roots
      let (next, finalRoots, gates) ← compileTokens (start + 1) (start :: remaining) tokens
      pure (next, finalRoots, gate :: gates)

def inputBits (start : Nat) (tokens : List Token) : List Bool :=
  encodeWords [start, tokens.length] ++ tokenBits tokens

end BinPackingGames.Foundations.Complexity.CookLevin.PostfixModel

namespace BinPackingGames.Foundations.Complexity.CookLevin

open Target CircuitProducerModel

theorem gateClauses_words {n : Nat} (output : Fin n) (g : Gate) (h : g.Bounded n) :
    (gateClauses output g h).flatMap clauseWords = (gateRecord output.val g).outputWords := by
  cases g with
  | const b => cases b <;> rfl
  | not x => rfl
  | and x y => rfl
  | or x y => rfl

@[simp] theorem unitClause_words {n : Nat} (output : Fin n) :
    clauseWords (unitClause output true) = outputWords output.val := rfl

theorem gateRecords_outputWords (start : Nat) (gs : List Gate) :
    (List.finRange gs.length).flatMap
        (fun i => (gateRecord (start + i.val) gs[i.val]).outputWords) =
      (gateRecords start gs).flatMap Record.outputWords := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih =>
    change (List.finRange (gs.length + 1)).flatMap
      (fun i => (gateRecord (start + i.val) (g :: gs)[i.val]).outputWords) = _
    rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
    change (gateRecord start g).outputWords ++
        (List.finRange gs.length).flatMap
          (fun i => (gateRecord (start + (i.val + 1)) gs[i.val]).outputWords) =
      (gateRecord start g).outputWords ++
        (gateRecords (start + 1) gs).flatMap Record.outputWords
    apply congrArg ((gateRecord start g).outputWords ++ ·)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (start + 1)

theorem Circuit.gateBlocks_words (C : Circuit) :
    ((List.finRange C.gates.length).flatMap C.gateBlock).flatMap clauseWords =
      C.records.flatMap Record.outputWords := by
  rw [List.flatMap_assoc]
  calc
    _ = (List.finRange C.gates.length).flatMap
        (fun i => (gateRecord (C.inputs + i.val) C.gates[i.val]).outputWords) := by
      apply List.flatMap_congr
      intro i _
      exact gateClauses_words (C.gateOutput i) (C.gateAt i) (C.gateBounded i)
    _ = C.records.flatMap Record.outputWords := gateRecords_outputWords C.inputs C.gates

theorem Circuit.formulaWords_eq_records (C : Circuit) :
    formulaWords C.toFormula =
      [C.wires, 3 * C.gates.length + 1] ++
        C.records.flatMap Record.outputWords ++ outputWords C.output.val := by
  unfold formulaWords
  change [C.wires, C.toFormula.clauses.length] ++ C.toFormula.clauses.flatMap clauseWords = _
  rw [C.toFormula_clause_count]
  change [C.wires, 3 * C.gates.length + 1] ++
      (((List.finRange C.gates.length).flatMap C.gateBlock ++
        [unitClause C.output true]).flatMap clauseWords) = _
  rw [List.flatMap_append, C.gateBlocks_words]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, unitClause_words,
    List.append_assoc]

theorem Circuit.formulaBits_eq_records (C : Circuit) :
    formulaBits C.toFormula =
      encodeWords ([C.wires, 3 * C.gates.length + 1] ++
        C.records.flatMap Record.outputWords ++ outputWords C.output.val) :=
  congrArg encodeWords C.formulaWords_eq_records

end BinPackingGames.Foundations.Complexity.CookLevin

end OAI
