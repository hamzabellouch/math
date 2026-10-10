import OAI.Computability.PerfectCompleteness.Machines.CellsMachine
import OAI.Computability.PerfectCompleteness.Machines.CircuitLemmas
import OAI.Computability.PerfectCompleteness.Machines.InitializationControl
import OAI.Computability.PerfectCompleteness.Machines.InputCellsMachineLemmas
import OAI.Computability.PerfectCompleteness.Machines.PaddingCellsMachine
import OAI.Computability.PerfectCompleteness.Machines.PayloadCellsAlignment
import OAI.Computability.PerfectCompleteness.Machines.PayloadRowsLoop
import OAI.Computability.PerfectCompleteness.Machines.ValidityComposition

namespace OAI


noncomputable section
namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.CellsTokensAlignment


open WitnessEncoding InitializationTemplate PaddingCellsMachine

local instance (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

theorem cellsInterval_append (V : NPVerifier) (input : List Bool) (S start m n : Nat)
    (within : start + (m + n) ≤ S) :
    cellsInterval V input S start (m + n) within =
      cellsInterval V input S start m (by omega) ++
        cellsInterval V input S (start + m) n (by omega) := by
  simp only [cellsInterval, List.flatMap_def, ← List.ofFn_eq_map]
  rw [List.ofFn_add, List.flatten_append]
  simp only [Fin.val_castLE, Fin.val_natAdd, Nat.add_assoc]

theorem cellsInterval_full (V : NPVerifier) (input : List Bool) (S : Nat) :
    cellsInterval V input S 0 S (by omega) = InitializationControl.cells V input S := by
  simp only [cellsInterval, InitializationControl.cells, Nat.zero_add]

theorem prefix_eq_interval (V : NPVerifier) (input : List Bool) (S : Nat)
    (within : (inputPrefix input).length ≤ S) :
    InputCellsMachine.streamTokens (InputCellsMachine.prefixTruth V) (inputPrefix input) =
      cellsInterval V input S 0 (inputPrefix input).length (by omega) := by
  simpa only [cellsInterval, List.flatMap_def, ← List.ofFn_eq_map, Nat.zero_add] using
    InputCellsMachine.prefixStream_eq_initialCells V input S within

theorem payload_eq_interval (V : NPVerifier) (input : List Bool) (S : Nat)
    (within : (inputPrefix input).length + V.witnessBound.eval input.length ≤ S) :
    PayloadRowsLoop.tokens (PayloadCellsMachine.symbolTable V)
      (V.witnessBound.eval input.length) 0 (V.witnessBound.eval input.length) =
      cellsInterval V input S (inputPrefix input).length (V.witnessBound.eval input.length) within := by
  rw [PayloadRowsLoop.tokens_eq_forTokens, forTokens_eq_ofFn]
  simp only [cellsInterval, List.flatMap_def, ← List.ofFn_eq_map, Nat.zero_add]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact PayloadCellsMachine.payloadRowTokens_eq V input S i.val i.isLt (by omega)

theorem cells_eq_streams (V : NPVerifier) (input : List Bool) (S : Nat)
    (within : (inputPrefix input).length + V.witnessBound.eval input.length ≤ S) :
    InputCellsMachine.streamTokens (InputCellsMachine.prefixTruth V) (inputPrefix input) ++
      PayloadRowsLoop.tokens (PayloadCellsMachine.symbolTable V)
        (V.witnessBound.eval input.length) 0 (V.witnessBound.eval input.length) ++
      repeatedRows (blankRow V)
        (S - (inputPrefix input).length - V.witnessBound.eval input.length) =
      InitializationControl.cells V input S := by
  let P := (inputPrefix input).length
  let q := V.witnessBound.eval input.length
  let r := S - P - q
  have hpq : P + q ≤ S := within
  have total : (P + q) + r = S := by dsimp only [r]; omega
  have hpre := prefix_eq_interval V input S (by omega)
  have hpay := payload_eq_interval V input S within
  have hpad := cellsInterval_padding V input S (P + q) r (by omega) (by exact le_rfl)
  rw [hpre, hpay, ← hpad]
  have first := cellsInterval_append V input S 0 P q (by omega)
  have second := cellsInterval_append V input S 0 (P + q) r (by omega)
  simp only [Nat.zero_add] at first second
  rw [← first, ← second]
  simpa only [total] using cellsInterval_full V input S

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.CellsTokensAlignment


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationAssemblyBounds

open Polynomial


local instance (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def cellsPolynomial (V : NPVerifier) : Polynomial Nat :=
  let A := (VerifierCircuit.indexing V).symbolCount
  let q := V.witnessBound
  let s := Bounds.capacityPolynomial V.computation.time q
    (Runtime.programPushBound V.computation.tm)
  (2 * (s + 2) + (C (A + 4) * (2 * X + 1) + 3)) + (2 * (q + 2) + 1) +
    (q * (C A * (120 * (q + 2)^2 + 1) + 3) + 1) + (s + 1) + (q + 3)

def timePolynomial (V : NPVerifier) : Polynomial Nat :=
  1 + cellsPolynomial V + ValidityMachine.Full.timePolynomial.comp V.witnessBound

theorem capacityPolynomial_eval (V : NPVerifier) (n : Nat) :
    (Bounds.capacityPolynomial V.computation.time V.witnessBound
      (Runtime.programPushBound V.computation.tm)).eval n = VerifierCircuit.capacity V n := by
  simp [VerifierCircuit.capacity, NPVerifier.horizon, Nat.mul_comm]

theorem cellsPolynomial_eval (V : NPVerifier) (input : List Bool) :
    (cellsPolynomial V).eval input.length =
      (2 * (VerifierCircuit.capacity V input.length + 2) +
        (((VerifierCircuit.indexing V).symbolCount + 4) * (WitnessEncoding.inputPrefix input).length + 3)) +
      (2 * (V.witnessBound.eval input.length + 2) + 1) +
      (V.witnessBound.eval input.length * ((VerifierCircuit.indexing V).symbolCount *
        (120 * (V.witnessBound.eval input.length + 2)^2 + 1) + 3) + 1) +
      (VerifierCircuit.capacity V input.length + 1) + (V.witnessBound.eval input.length + 3) := by
  simp only [cellsPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_one, capacityPolynomial_eval, WitnessEncoding.inputPrefix_length]

theorem cells_steps_le (V : NPVerifier) (input : List Bool) :
    CellsMachine.steps (PayloadCellsMachine.symbolTable V) (WitnessEncoding.inputPrefix input).length
      (V.witnessBound.eval input.length) (VerifierCircuit.capacity V input.length) ≤
      (cellsPolynomial V).eval input.length := by
  rw [cellsPolynomial_eval]
  exact CellsMachine.steps_le (PayloadCellsMachine.symbolTable V)
    (WitnessEncoding.inputPrefix input).length (V.witnessBound.eval input.length)
    (VerifierCircuit.capacity V input.length)

theorem steps_le (V : NPVerifier) (input : List Bool) :
    1 + CellsMachine.steps (PayloadCellsMachine.symbolTable V) (WitnessEncoding.inputPrefix input).length
      (V.witnessBound.eval input.length) (VerifierCircuit.capacity V input.length) +
      ValidityMachine.Full.steps (V.witnessBound.eval input.length) ≤
      (timePolynomial V).eval input.length := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_comp]
  exact Nat.add_le_add (Nat.add_le_add_left (cells_steps_le V input) 1)
    (ValidityMachine.Full.steps_le_time (V.witnessBound.eval input.length))

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationAssemblyBounds

end


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationAssembly

open Turing PostfixModel


inductive Tape (cellWork : Nat) where
  | rawInput | framedInput | witnessBound | capacity | reversed | count
  | validityWork (index : Fin 7)
  | cellWork (index : Fin cellWork)
  deriving DecidableEq, Fintype

def validitySlots (n : Nat) : Fin 10 ↪ Tape n :=
  ⟨![.witnessBound, .validityWork 0, .validityWork 1, .validityWork 2,
      .validityWork 3, .validityWork 4, .validityWork 5, .reversed, .count,
      .validityWork 6], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

def controlPorts (n : Nat) : InitializationControl.Ports (Tape n) where
  reversed := .reversed
  count := .count
  distinct := by intro h; cases h

theorem validityReady {n : Nat} (base : Tape n → List Bool) (q : Nat)
    (hbound : base .witnessBound = encodeWord q)
    (hwork : ∀ j, base (.validityWork j) = []) :
    ClashMachine.Full.Ready (validitySlots n) base q where
  source := hbound
  empty := by
    intro j hj ho hc
    fin_cases j <;> try contradiction
    · exact hwork 0
    · exact hwork 1
    · exact hwork 2
    · exact hwork 3
    · exact hwork 4
    · exact hwork 5
    · exact hwork 6

theorem control_emitted_eq {n : Nat} (base : Tape n → List Bool) (ts : List Token) :
    InitializationControl.emitted (controlPorts n) base ts =
      ClashMachine.emitted ((validitySlots n) 7) ((validitySlots n) 8) base ts := rfl

theorem validityReady_control {n : Nat} {base : Tape n → List Bool} {q : Nat}
    (ready : ClashMachine.Full.Ready (validitySlots n) base q) (V : NPVerifier) :
    ClashMachine.Full.Ready (validitySlots n)
      (InitializationControl.emitted (controlPorts n) base (InitializationControl.tokens V)) q := by
  rw [control_emitted_eq]
  exact ready.emitted (InitializationControl.tokens V)

theorem validitySlots_not_cellWork (n : Nat) (i : Fin 10) (j : Fin n) :
    validitySlots n i ≠ Tape.cellWork j := by
  rw [validitySlots.eq_1]
  change (![Tape.witnessBound, Tape.validityWork 0, Tape.validityWork 1,
    Tape.validityWork 2, Tape.validityWork 3, Tape.validityWork 4, Tape.validityWork 5,
    Tape.reversed, Tape.count, Tape.validityWork 6] i : Tape n) ≠ Tape.cellWork j
  fin_cases i <;> simp

theorem controlTrace {n : Nat} {Λ σ : Type}
    (V : NPVerifier) (entry : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : Tape n => Bool) Λ σ)
    (code : program entry = InitializationControl.statement V (controlPorts n) exit)
    (base : Tape n → List Bool) (state : σ) (q : Nat)
    (ready : ClashMachine.Full.Ready (validitySlots n) base q) :
    ((MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some entry, state, base⟩) =
        some ⟨exit, state, InitializationControl.emitted (controlPorts n) base
          (InitializationControl.tokens V)⟩) ∧
      ClashMachine.Full.Ready (validitySlots n)
        (InitializationControl.emitted (controlPorts n) base (InitializationControl.tokens V)) q :=
  ⟨InitializationControl.trace V (controlPorts n) entry exit program code base state,
    validityReady_control ready V⟩

noncomputable section

open MachineComposition
open ClashMachine (State clean emitted)

def cellsSlots : Fin 14 ↪ Tape 9 :=
  ⟨![.framedInput, .witnessBound, .capacity, .reversed, .count,
      .cellWork 0, .cellWork 1, .cellWork 2, .cellWork 3, .cellWork 4,
      .cellWork 5, .cellWork 6, .cellWork 7, .cellWork 8], by decide⟩

inductive CodeLabel (A : Nat) where
  | control
  | cells (label : CellsMachine.Label A)
  | validity (label : ValidityMachine.Full.Label)
  deriving DecidableEq, Fintype

abbrev Label (V : NPVerifier) := CodeLabel (VerifierCircuit.indexing V).symbolCount

variable {K Λ σ : Type} [DecidableEq K]

def placedControl (slots : Tape 9 ↪ K) : InitializationControl.Ports K where
  reversed := slots .reversed
  count := slots .count
  distinct := slots.injective.ne (by decide)

def cellsLabels {V : NPVerifier} (labels : Label V ↪ Λ) :
    CellsMachine.Label (VerifierCircuit.indexing V).symbolCount ↪ Λ :=
  ⟨fun l => labels (.cells l), fun _ _ h => CodeLabel.cells.inj (labels.injective h)⟩

structure Ready (V : NPVerifier) (slots : Tape 9 ↪ K) (base : K → List Bool)
    (input : List Bool) : Prop where
  rawWord : base (slots .rawInput) = input
  framedWord : base (slots .framedInput) = WitnessEncoding.inputPrefix input
  boundWord : base (slots .witnessBound) = encodeWord (V.witnessBound.eval input.length)
  capacityWord : base (slots .capacity) = encodeWord (VerifierCircuit.capacity V input.length)
  cellEmpty : ∀ j, base (slots (.cellWork j)) = []
  validityEmpty : ∀ j, base (slots (.validityWork j)) = []

theorem Ready.afterEmitted {V : NPVerifier} {slots : Tape 9 ↪ K}
    {base : K → List Bool} {input : List Bool} (ready : Ready V slots base input)
    (ts : List Token) :
    Ready V slots (emitted (slots .reversed) (slots .count) base ts) input := by
  constructor
  · simpa [emitted, slots.injective.eq_iff] using ready.rawWord
  · simpa [emitted, slots.injective.eq_iff] using ready.framedWord
  · simpa [emitted, slots.injective.eq_iff] using ready.boundWord
  · simpa [emitted, slots.injective.eq_iff] using ready.capacityWord
  · intro j
    simpa [emitted, slots.injective.eq_iff] using ready.cellEmpty j
  · intro j
    simpa [emitted, slots.injective.eq_iff] using ready.validityEmpty j

omit [DecidableEq K] in
theorem Ready.cellsReady {V : NPVerifier} {slots : Tape 9 ↪ K}
    {base : K → List Bool} {input : List Bool} (ready : Ready V slots base input) :
    CellsMachine.Ready (cellsSlots.trans slots) base (WitnessEncoding.inputPrefix input)
      (V.witnessBound.eval input.length) (VerifierCircuit.capacity V input.length) := by
  constructor
  · exact ready.framedWord
  · exact ready.boundWord
  · exact ready.capacityWord
  · intro j hj
    fin_cases j <;> simp_all [cellsSlots, ready.cellEmpty]

omit [DecidableEq K] in
theorem Ready.validityReady {V : NPVerifier} {slots : Tape 9 ↪ K}
    {base : K → List Bool} {input : List Bool} (ready : Ready V slots base input) :
    ClashMachine.Full.Ready ((validitySlots 9).trans slots) base
      (V.witnessBound.eval input.length) := by
  have localReady := InitializationAssembly.validityReady (fun t => base (slots t))
    (V.witnessBound.eval input.length) ready.boundWord ready.validityEmpty
  constructor
  · exact localReady.source
  · intro j hj ho hc
    exact localReady.empty j hj ho hc

theorem capacity_within (V : NPVerifier) (input : List Bool) :
    (WitnessEncoding.inputPrefix input).length + V.witnessBound.eval input.length ≤
      VerifierCircuit.capacity V input.length := by
  simp only [WitnessEncoding.inputPrefix_length, VerifierCircuit.capacity]
  omega

def statement (V : NPVerifier) (slots : Tape 9 ↪ K) (labels : Label V ↪ Λ)
    (exit : Option Λ) : Label V → TM2.Stmt (fun _ : K => Bool) Λ (State σ)
  | .control => InitializationControl.statement V (placedControl slots)
      (some (labels (.cells (.prefix .capacityFirst))))
  | .cells l => CellsMachine.statement (cellsSlots.trans slots) (cellsLabels labels)
      (some (labels (.validity (.nonempty .initialize))))
      (InputCellsMachine.prefixTruth V) (PayloadCellsMachine.symbolTable V)
      (PaddingCellsMachine.blankRow V) l
  | .validity l => ValidityMachine.Full.statement ((validitySlots 9).trans slots)
      (fun l => labels (.validity l)) exit l

def Agrees (V : NPVerifier) (slots : Tape 9 ↪ K) (labels : Label V ↪ Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ)) : Prop :=
  ∀ l, program (labels l) = statement V slots labels exit l

def steps (V : NPVerifier) (input : List Bool) : Nat :=
  1 + CellsMachine.steps (PayloadCellsMachine.symbolTable V)
    (WitnessEncoding.inputPrefix input).length (V.witnessBound.eval input.length)
    (VerifierCircuit.capacity V input.length) +
    ValidityMachine.Full.steps (V.witnessBound.eval input.length)

theorem cellsTokens_eq (V : NPVerifier) (input : List Bool) :
    CellsMachine.tokens (InputCellsMachine.prefixTruth V) (PayloadCellsMachine.symbolTable V)
      (PaddingCellsMachine.blankRow V) (WitnessEncoding.inputPrefix input)
      (V.witnessBound.eval input.length) (VerifierCircuit.capacity V input.length) =
      InitializationControl.cells V input (VerifierCircuit.capacity V input.length) :=
  CellsTokensAlignment.cells_eq_streams V input (VerifierCircuit.capacity V input.length)
    (capacity_within V input)

theorem trace (V : NPVerifier) (slots : Tape 9 ↪ K) (labels : Label V ↪ Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (ha : Agrees V slots labels exit program) (base : K → List Bool) (input : List Bool)
    (ready : Ready V slots base input) (ambient : σ) :
    (advance (TM2.step program))^[steps V input]
      (some ⟨some (labels .control), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots .reversed) (slots .count) base
        (InitializationTemplate.initializationTokens V input)⟩ := by
  let first := InitializationControl.tokens V
  let middle := InitializationControl.cells V input (VerifierCircuit.capacity V input.length)
  let b₁ := emitted (slots .reversed) (slots .count) base first
  let b₂ := emitted (slots .reversed) (slots .count) b₁ middle
  have h₁ := InitializationControl.trace V (placedControl slots) (labels .control)
    (some (labels (.cells (.prefix .capacityFirst)))) program (ha .control) base (clean ambient)
  change (advance (TM2.step program))^[1]
    (some ⟨some (labels .control), clean ambient, base⟩) =
    some ⟨some (labels (.cells (.prefix .capacityFirst))), clean ambient, b₁⟩ at h₁
  have h₂ := CellsMachine.trace (cellsSlots.trans slots) (cellsLabels labels)
    (some (labels (.validity (.nonempty .initialize))))
    (InputCellsMachine.prefixTruth V) (PayloadCellsMachine.symbolTable V)
    (PaddingCellsMachine.blankRow V) program (fun l => ha (.cells l)) b₁
    (WitnessEncoding.inputPrefix input) (V.witnessBound.eval input.length)
    (VerifierCircuit.capacity V input.length) (capacity_within V input)
    (ready.afterEmitted first).cellsReady ambient
  rw [cellsTokens_eq] at h₂
  change (advance (TM2.step program))^[CellsMachine.steps (PayloadCellsMachine.symbolTable V)
    (WitnessEncoding.inputPrefix input).length (V.witnessBound.eval input.length)
    (VerifierCircuit.capacity V input.length)]
    (some ⟨some (labels (.cells (.prefix .capacityFirst))), clean ambient, b₁⟩) =
    some ⟨some (labels (.validity (.nonempty .initialize))), clean ambient, b₂⟩ at h₂
  have h₃ := ValidityMachine.Full.trace ((validitySlots 9).trans slots)
    (fun l => labels (.validity l)) exit program (fun l => ha (.validity l)) b₂
    (V.witnessBound.eval input.length)
    ((ready.afterEmitted first).afterEmitted middle).validityReady ambient
  have h := ClashMachine.chain (ClashMachine.chain h₁ h₂) h₃
  simpa only [steps, b₂, b₁, first, middle,
    show ((validitySlots 9).trans slots) 7 = slots .reversed from rfl,
    show ((validitySlots 9).trans slots) 8 = slots .count from rfl,
    ClashMachine.emitted_append (slots .reversed) (slots .count)
      (slots.injective.ne (by decide : (Tape.reversed : Tape 9) ≠ .count)),
    InitializationControl.initializationTokens_eq_blocks] using h

def program (V : NPVerifier) :
    Label V → TM2.Stmt (fun _ : Tape 9 => Bool) (Label V) (State Unit) :=
  statement V (Function.Embedding.refl _) (Function.Embedding.refl _) none

def machine (V : NPVerifier) : FinTM2 where
  K := Tape 9
  k₀ := .rawInput
  k₁ := .reversed
  Γ := fun _ => Bool
  Λ := Label V
  main := .control
  σ := State Unit
  initialState := clean ()
  Γk₀Fin := inferInstance
  m := program V

theorem machineTrace (V : NPVerifier) (base : Tape 9 → List Bool) (input : List Bool)
    (ready : Ready V (Function.Embedding.refl _) base input) :
    (advance (machine V).step)^[steps V input]
      (some ⟨some .control, clean (), base⟩) =
      some ⟨none, clean (), emitted .reversed .count base
        (InitializationTemplate.initializationTokens V input)⟩ :=
  trace V (Function.Embedding.refl _) (Function.Embedding.refl _) none
    (program V) (fun _ => rfl) base input ready ()

def timePolynomial (V : NPVerifier) : Polynomial Nat :=
  InitializationAssemblyBounds.timePolynomial V

theorem steps_le_timePolynomial (V : NPVerifier) (input : List Bool) :
    steps V input ≤ (timePolynomial V).eval input.length :=
  InitializationAssemblyBounds.steps_le V input

def inPolynomialTime (V : NPVerifier) (slots : Tape 9 ↪ K) (labels : Label V ↪ Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (ha : Agrees V slots labels exit program) (base : K → List Bool) (input : List Bool)
    (ready : Ready V slots base input) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .control), clean ambient, base⟩
      (some ⟨exit, clean ambient, emitted (slots .reversed) (slots .count) base
        (InitializationTemplate.initializationTokens V input)⟩)
      ((timePolynomial V).eval input.length) where
  steps := steps V input
  evals_in_steps := by
    change (advance (TM2.step program))^[steps V input] _ = _
    exact trace V slots labels exit program ha base input ready ambient
  steps_le_m := steps_le_timePolynomial V input

def machineInPolynomialTime (V : NPVerifier) (base : Tape 9 → List Bool) (input : List Bool)
    (ready : Ready V (Function.Embedding.refl _) base input) :
    StateTransition.EvalsToInTime (machine V).step
      ⟨some .control, clean (), base⟩
      (some ⟨none, clean (), emitted .reversed .count base
        (InitializationTemplate.initializationTokens V input)⟩)
      ((timePolynomial V).eval input.length) :=
  inPolynomialTime V (Function.Embedding.refl _) (Function.Embedding.refl _) none
    (program V) (fun _ => rfl) base input ready ()

end
end UniqueGamesTheorem.Foundations.Complexity.CookLevin.InitializationAssembly

end OAI
