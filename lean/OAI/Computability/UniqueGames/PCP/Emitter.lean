import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Machines.MachineTransducerCopy

namespace OAI

/-!
Actual finite TM2 templates for affine unary fields and finite relation bits.
Commands write in forward bit order onto a stack, so their concatenated result
appears reversed in the accumulator. Every unbounded operand is read from an
isolated unary tape and restored by the checked preserving transducer.
-/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Emitter

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

/-- All varying literals are finite: one Boolean or one bounded offset. -/
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

/-- A literal Boolean is emitted by a real finite branch. A bounded offset is
dispatched to a finite label, whose push chain has a fixed length. -/
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

/-- Exact execution of one command of the supplied actual program. The only
program hypotheses are equations for its concrete finite statements. -/
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

/-- Bundling makes the fixed finite tape, control-label, and register sets
explicit. Neither the label type nor the state type contains a natural input. -/
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

/-- Composition of the actual finite command traces, with preserved operand
stacks available again at every command boundary. -/
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

/-- The complete callable program, including its actual final jump or halt. -/
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

/-- A linear bound in the largest unary input field; plan size is fixed. -/
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

/-- The finite relation table is encoded one actual Boolean branch at a time. -/
def bitCommands (bits : List (σ → Bool)) : List (Command h σ bound) := bits.map .bit

theorem bitCommands_bits (bits : List (σ → Bool)) (values : Fin h → Nat) (ambient : σ) :
    (bitCommands (h := h) (bound := bound) bits).flatMap (commandBits values ambient) =
      encodeWords (bits.map (fun bit => if bit ambient then 1 else 0)) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simpa only [bitCommands, List.map_cons, List.flatMap_cons, commandBits, encodeWords]
      using congrArg (encodeWord (if bit ambient then 1 else 0) ++ ·) ih

/-- The affine template itself has an actual composable machine certificate. -/
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

/-- Enlarge the finite ambient registers by reading a projection of them. -/
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

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Emitter

end OAI
