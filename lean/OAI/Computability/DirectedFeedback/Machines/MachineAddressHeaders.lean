import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineTuple

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.CloneMachineAffine

open DFVSGames.Foundations.Complexity
open CloneMachineModel

theorem output_eq_flatMap {Q : Type} [Fintype Q]
    (emit : Q → Bool → List Bool) (q : Q) (input : List Bool) :
    MachineTransducer.output (fun state _ => state) emit q input =
      input.flatMap (emit q) := by
  induction input with
  | nil => rfl
  | cons b input ih =>
    simp only [MachineTransducer.output, List.flatMap_cons, ih]

theorem output_append {Q : Type} [Fintype Q]
    (emit : Q → Bool → List Bool) (q : Q) (first rest : List Bool) :
    MachineTransducer.output (fun state _ => state) emit q (first ++ rest) =
      MachineTransducer.output (fun state _ => state) emit q first ++
        MachineTransducer.output (fun state _ => state) emit q rest := by
  simp only [output_eq_flatMap, List.flatMap_append]

theorem affineEmit_replicate_true (scale offset v : Nat) :
    (List.replicate v true).flatMap (affineEmit scale offset) =
      List.replicate (scale * v) true := by
  rw [List.flatMap_replicate]
  change (List.replicate v (List.replicate scale true)).flatten = _
  rw [List.flatten_replicate_replicate, Nat.mul_comm v scale]

theorem affineEmit_word (scale offset v : Nat) :
    (encodeWord v).flatMap (affineEmit scale offset) =
      encodeWord (offset + scale * v) := by
  simp only [encodeWord, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, affineEmit_replicate_true, affineEmit]
  rw [← List.append_assoc, List.replicate_append_replicate, Nat.add_comm (scale * v) offset]

theorem affineEmit_word_append (scale offset v : Nat) (rest : List Bool) :
    (encodeWord v ++ rest).flatMap (affineEmit scale offset) =
      encodeWord (offset + scale * v) ++ rest.flatMap (affineEmit scale offset) := by
  rw [List.flatMap_append, affineEmit_word]

theorem affineEmit_words (scale offset : Nat) (vs : List Nat) :
    (encodeWords vs).flatMap (affineEmit scale offset) =
      encodeWords (vs.map (fun v => offset + scale * v)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [encodeWords, List.flatMap_append, List.map_cons, affineEmit_word, ih]

theorem output_word (triples : List (Nat × Nat × Nat))
    (c : Context triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) c (encodeWord v) =
      encodeWord (contextOffset triples c + contextScale c * v) := by
  rw [output_eq_flatMap]
  exact affineEmit_word (contextScale c) (contextOffset triples c) v

theorem output_word_append (triples : List (Nat × Nat × Nat))
    (c : Context triples.length) (v : Nat) (rest : List Bool) :
    MachineTransducer.output (fun q _ => q) (emission triples) c (encodeWord v ++ rest) =
      encodeWord (contextOffset triples c + contextScale c * v) ++
        MachineTransducer.output (fun q _ => q) (emission triples) c rest := by
  rw [output_append, output_word]

theorem output_words (triples : List (Nat × Nat × Nat))
    (c : Context triples.length) (vs : List Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) c (encodeWords vs) =
      encodeWords (vs.map (fun v => contextOffset triples c + contextScale c * v)) := by
  rw [output_eq_flatMap]
  exact affineEmit_words (contextScale c) (contextOffset triples c) vs

theorem output_header_variables (triples : List (Nat × Nat × Nat)) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inl 0) (encodeWord v) =
      encodeWord (48 * v) := by
  simpa [contextOffset, contextScale] using output_word triples (.inl 0) v

theorem output_header_count (triples : List (Nat × Nat × Nat)) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inl 1) (encodeWord v) =
      encodeWord (triples.length * v) := by
  simpa [contextOffset, contextScale] using output_word triples (.inl 1) v

theorem output_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (j : Fin 4) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, j)) (encodeWord v) =
      encodeWord (tripleField (triples.get i) j + (if j.val < 3 then 48 else 1) * v) := by
  exact output_word triples (.inr (i, j)) v

theorem output_first_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, 0)) (encodeWord v) =
      encodeWord ((triples.get i).1 + 48 * v) := by
  simpa [tripleField] using output_field triples i 0 v

theorem output_second_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, 1)) (encodeWord v) =
      encodeWord ((triples.get i).2.1 + 48 * v) := by
  simpa [tripleField] using output_field triples i 1 v

theorem output_third_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, 2)) (encodeWord v) =
      encodeWord ((triples.get i).2.2 + 48 * v) := by
  simpa [tripleField] using output_field triples i 2 v

theorem output_rhs_field (triples : List (Nat × Nat × Nat))
    (i : Fin triples.length) (v : Nat) :
    MachineTransducer.output (fun q _ => q) (emission triples) (.inr (i, 3)) (encodeWord v) =
      encodeWord v := by
  simpa [tripleField] using output_field triples i 3 v

end DFVSGames.Reduction.CloneMachineAffine
end

section

namespace DFVSGames.Reduction.MachineAddressHeaders

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineComposition

namespace Prefix

inductive Label
  | copyOut | copyBack | read (slot : Fin 3 × Bool) | clear
  deriving DecidableEq, Fintype

def readStart (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 2 r, false)
def readLoop (r : Nat) : Label := .read (SourceFieldArray.boundedIndex 2 r, true)

variable {K Λ σ : Type} [DecidableEq K]

def destination (slots : Fin 5 ↪ K) (r : Nat) : K := if r = 0 then slots 2 else slots 3

def statement (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .copyOut => MachineTransfer.loopAt (slots 0) (slots 4) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (slots 4) (slots 0) (slots 1) false
      (labels .copyBack) (some (labels (readStart 0)))
  | .read slot => if slot.1.val < 2 then
      if slot.2 then SourceMachine.fieldLoop (slots 1) (destination slots slot.1.val)
        (labels (.read (slot.1, true))) (some (labels (readStart (slot.1.val + 1))))
      else SourceMachine.fieldStart (destination slots slot.1.val) (labels (.read (slot.1, true)))
    else SourceFieldArray.finish (slots 1) (some (labels .clear))
  | .clear => MachineDrain.drain (slots 1) (labels .clear) exit

omit [DecidableEq K] in
theorem atReadStart (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (r : Nat) (hr : r < 2) :
    statement (σ := σ) slots labels exit (readStart r) =
      SourceMachine.fieldStart (destination slots r) (labels (readLoop r)) := by
  simp [statement, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

omit [DecidableEq K] in
theorem atReadLoop (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (r : Nat) (hr : r < 2) :
    statement (σ := σ) slots labels exit (readLoop r) =
      SourceMachine.fieldLoop (slots 1) (destination slots r) (labels (readLoop r))
        (some (labels (readStart (r + 1)))) := by
  simp [statement, readStart, readLoop, SourceFieldArray.boundedIndex_val hr.le, hr]

omit [DecidableEq K] in
theorem atReadDone (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    statement (σ := σ) slots labels exit (readStart 2) =
      SourceFieldArray.finish (slots 1) (some (labels .clear)) := by
  simp [statement, readStart]

def copied (slots : Fin 5 ↪ K) (base : K → List Bool) : K → List Bool :=
  Function.update base (slots 1) (base (slots 0))

def readTapes (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat)
    (suffix : List Bool) : K → List Bool :=
  SourceFieldArray.sequenceTapes (slots 1) (destination slots) (copied slots base)
    0 [n, m] suffix

def resultTapes (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat) : K → List Bool :=
  Function.update (Function.update (Function.update base (slots 1) [])
    (slots 2) (encodeWord n ++ base (slots 2))) (slots 3) (encodeWord m ++ base (slots 3))

theorem clear_readTapes (slots : Fin 5 ↪ K) (base : K → List Bool)
    (n m : Nat) (suffix : List Bool) :
    Function.update (readTapes slots base n m suffix) (slots 1) [] =
      resultTapes slots base n m := by
  funext tape
  by_cases hw : tape = slots 1
  · subst tape
    simp [readTapes, resultTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
      SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff]
  · by_cases hn : tape = slots 2
    · subst tape
      simp [readTapes, resultTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
        SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff]
    · by_cases hm : tape = slots 3
      · subst tape
        simp [readTapes, resultTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
          SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff]
      · simp [readTapes, resultTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
          SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff, hw, hn, hm]

theorem readTapes_work (slots : Fin 5 ↪ K) (base : K → List Bool)
    (n m : Nat) (suffix : List Bool) : readTapes slots base n m suffix (slots 1) = suffix := by
  simp [readTapes, SourceFieldArray.sequenceTapes, SourceMachine.afterField,
    SourceMachine.fieldTapes, copied, destination, slots.injective.eq_iff, encodeWords]

theorem resultTapes_other (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat)
    (tape : K) (hw : tape ≠ slots 1) (hn : tape ≠ slots 2) (hm : tape ≠ slots 3) :
    resultTapes slots base n m tape = base tape := by simp [resultTapes, hw, hn, hm]

@[simp] theorem resultTapes_source (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (slots 0) = base (slots 0) := by
  simp [resultTapes, slots.injective.eq_iff]

@[simp] theorem resultTapes_work (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (slots 1) = [] := by simp [resultTapes]

@[simp] theorem resultTapes_n (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (slots 2) = encodeWord n ++ base (slots 2) := by
  simp [resultTapes, slots.injective.eq_iff]

@[simp] theorem resultTapes_m (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (slots 3) = encodeWord m ++ base (slots 3) := by
  simp [resultTapes]

def inTime (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (n m : Nat) (suffix : List Bool)
    (hinput : base (slots 0) = encodeWords [n, m] ++ suffix)
    (hwork : base (slots 1) = []) (hscratch : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copyOut), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩)
      (3 * (base (slots 0)).length + 6) := by
  have copying := MachineCopy.copyInTime (slots 0) (slots 1) (slots 4)
    (by simp [slots.injective.eq_iff]) (by simp [slots.injective.eq_iff])
    (by simp [slots.injective.eq_iff]) false (labels .copyOut) (labels .copyBack)
    (some (labels (readStart 0))) program (atLabels .copyOut) (atLabels .copyBack)
    base hscratch (ambient, ()) register
  have hc : Function.update base (slots 1) (base (slots 0) ++ base (slots 1)) =
      copied slots base := by simp [copied, hwork]
  rw [hc] at copying
  have reading := SourceFieldArray.sequenceInTime (slots 1) (destination slots)
    (fun r => labels (readStart r)) (fun r => labels (readLoop r)) (some (labels .clear))
    program (copied slots base) 0 [n, m] suffix
    (by
      intro r hr
      simp only [destination]
      split <;> simp [slots.injective.eq_iff])
    (by
      intro r hr
      simpa only [Nat.zero_add] using
        (atLabels (readStart r)).trans (atReadStart slots labels exit r (by simpa using hr)))
    (by
      intro r hr
      simpa only [Nat.zero_add] using
        (atLabels (readLoop r)).trans (atReadLoop slots labels exit r (by simpa using hr)))
    (by simpa using (atLabels (readStart 2)).trans (atReadDone slots labels exit))
    (by simp [copied, hinput]) (ambient, ()) none
  have draining := MachineDrain.drainInTime (slots 1) (labels .clear) exit program
    (atLabels .clear) (readTapes slots base n m suffix) (ambient, ()) none
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _
    (StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ copying reading) draining
  refine { steps := joined.steps, evals_in_steps := ?_, steps_le_m := ?_ }
  · simpa only [clear_readTapes] using joined.evals_in_steps
  · apply Nat.le_trans joined.steps_le_m
    rw [readTapes_work, hinput]
    simp only [List.length_append, encodeWords_length, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil]
    omega

end Prefix

def baseConstant (s d : Nat) : Nat := 2 ^ s + 2 ^ d + 4
def radix (s d n m : Nat) : Nat := n + m + baseConstant s d
def capacity (k s d n m : Nat) : Nat := (radix s d n m) ^ (1 + 9 * k)
def edgeFactor (k s d noiseCount : Nat) : Nat :=
  2 ^ ((2 * k + 1) * (s + d + 1)) * noiseCount
def edgeCount (k s d noiseCount m : Nat) : Nat := edgeFactor k s d noiseCount * m ^ k

noncomputable section

inductive Kind | capacity | edges
  deriving DecidableEq

instance : Fintype Kind where
  elems := {.capacity, .edges}
  complete := by intro kind; cases kind <;> simp

def polynomial (k s d noiseCount : Nat) : Kind → Polynomial Nat
  | .capacity => Polynomial.X ^ (1 + 9 * k)
  | .edges => Polynomial.C (edgeFactor k s d noiseCount) * Polynomial.X ^ k

@[simp] theorem polynomial_capacity_eval (k s d noiseCount B : Nat) :
    (polynomial k s d noiseCount .capacity).eval B = B ^ (1 + 9 * k) := by
  simp [polynomial]

@[simp] theorem polynomial_edges_eval (k s d noiseCount m : Nat) :
    (polynomial k s d noiseCount .edges).eval m = edgeCount k s d noiseCount m := by
  simp [polynomial, edgeCount]

namespace Arithmetic

inductive Control
  | variableCount | occurrenceCount | baseValue | capacity | temporary | reversed
  | accA | accB | counter | scratch
  deriving DecidableEq

instance : Fintype Control where
  elems := {.variableCount, .occurrenceCount, .baseValue, .capacity, .temporary,
    .reversed, .accA, .accB, .counter, .scratch}
  complete := by intro control; cases control <;> simp

abbrev Coefficients (k s d noiseCount : Nat) :=
  Fin (CookLevin.PolynomialMachine.width (polynomial k s d noiseCount .capacity)) ⊕
    Fin (CookLevin.PolynomialMachine.width (polynomial k s d noiseCount .edges))

abbrev Layout (k s d noiseCount : Nat) := Control ⊕ Coefficients k s d noiseCount

def inputControl : Kind → Control
  | .capacity => .baseValue | .edges => .occurrenceCount

def outputControl : Kind → Control
  | .capacity => .capacity | .edges => .temporary

def controlSlots (kind : Kind) : Fin 6 ↪ Control where
  toFun i := match i.val with
    | 0 => inputControl kind | 1 => .accA | 2 => .accB
    | 3 => outputControl kind | 4 => .counter | _ => .scratch
  inj' := by
    intro i j h
    cases kind <;> fin_cases i <;> fin_cases j <;> cases h <;> rfl

def coefficientBlock (k s d noiseCount : Nat) (kind : Kind) :
    Fin (CookLevin.PolynomialMachine.width (polynomial k s d noiseCount kind)) ↪
      Coefficients k s d noiseCount :=
  match kind with
  | .capacity => ⟨Sum.inl, Sum.inl_injective⟩
  | .edges => ⟨Sum.inr, Sum.inr_injective⟩

def localSlots (k s d noiseCount : Nat) (kind : Kind) :
    MachineHorner.Layout (CookLevin.PolynomialMachine.width (polynomial k s d noiseCount kind)) ↪
      Layout k s d noiseCount where
  toFun
    | .inl i => .inl (controlSlots kind i)
    | .inr i => .inr (coefficientBlock k s d noiseCount kind i)
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl ((controlSlots kind).injective (Sum.inl.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b =>
        exact congrArg Sum.inr ((coefficientBlock k s d noiseCount kind).injective (Sum.inr.inj h))

variable {k s d noiseCount : Nat} {K Λ σ : Type}

def control (slots : Layout k s d noiseCount ↪ K) (c : Control) : K := slots (.inl c)

def evalSlots (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    MachineHorner.Layout (CookLevin.PolynomialMachine.width (polynomial k s d noiseCount kind)) ↪ K :=
  (localSlots k s d noiseCount kind).trans slots

@[simp] theorem control_eq_iff (slots : Layout k s d noiseCount ↪ K) (a b : Control) :
    control slots a = control slots b ↔ a = b := by simp [control, slots.injective.eq_iff]

@[simp] theorem evalSlots_radix (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 0) = control slots (inputControl kind) := rfl
@[simp] theorem evalSlots_accA (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 1) = control slots .accA := rfl
@[simp] theorem evalSlots_accB (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 2) = control slots .accB := rfl
@[simp] theorem evalSlots_destination (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 3) = control slots (outputControl kind) := rfl
@[simp] theorem evalSlots_counter (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 4) = control slots .counter := rfl
@[simp] theorem evalSlots_scratch (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 5) = control slots .scratch := rfl
@[simp] theorem evalSlots_digit (slots : Layout k s d noiseCount ↪ K) (kind : Kind)
    (i : Fin (CookLevin.PolynomialMachine.width (polynomial k s d noiseCount kind))) :
    evalSlots slots kind (.inr i) = slots (.inr (coefficientBlock k s d noiseCount kind i)) := rfl

inductive Label (k s d noiseCount : Nat)
  | copyNOut | copyNBack | copyMOut | copyMBack | addM | seedBase
  | evaluate (kind : Kind) (localLabel : SourceHeaderCounts.Eval.Label (polynomial k s d noiseCount kind))
  | doubleScan | doubleEmit (symbol : Bool) | doubleRestore | alphabet | edgeTransfer
  deriving DecidableEq, Fintype

def evalStart (kind : Kind) : Label k s d noiseCount :=
  .evaluate kind (SourceHeaderCounts.Eval.start (polynomial k s d noiseCount kind))

def afterEval : Kind → Label k s d noiseCount
  | .capacity => .doubleScan | .edges => .edgeTransfer

variable [DecidableEq K]

def statement (slots : Layout k s d noiseCount ↪ K) (labels : Label k s d noiseCount → Λ)
    (exit : Option Λ) :
    Label k s d noiseCount → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .copyNOut => MachineTransfer.loopAt (control slots .variableCount) (control slots .scratch)
      id false (labels .copyNOut) (some (labels .copyNBack))
  | .copyNBack => MachineCopy.forkLoop (control slots .scratch) (control slots .variableCount)
      (control slots .baseValue) false (labels .copyNBack) (some (labels .copyMOut))
  | .copyMOut => MachineTransfer.loopAt (control slots .occurrenceCount) (control slots .scratch)
      id false (labels .copyMOut) (some (labels .copyMBack))
  | .copyMBack => MachineCopy.forkLoop (control slots .scratch) (control slots .occurrenceCount)
      (control slots .temporary) false (labels .copyMBack) (some (labels .addM))
  | .addM => MachineUnaryAddAt.loop (control slots .temporary) (control slots .baseValue)
      (labels .addM) (some (labels .seedBase))
  | .seedBase => .pop (control slots .temporary) (fun state _ => state)
      (MachineSubstitution.pushWord (control slots .baseValue) (List.replicate (baseConstant s d) true)
        (.goto fun _ => labels (evalStart .capacity)))
  | .evaluate kind localLabel => SourceHeaderCounts.Eval.statement
      (polynomial k s d noiseCount kind) (evalSlots slots kind)
      (fun label => labels (.evaluate kind label)) (some (labels (afterEval kind))) localLabel
  | .doubleScan => MachineTransducerCopy.scanLoop (control slots .capacity) (control slots .scratch)
      () (fun _ symbol => labels (.doubleEmit symbol)) (labels .doubleRestore)
  | .doubleEmit symbol => MachineTransducerCopy.emitter (control slots .reversed)
      (fun q _ => q) (fun _ : Unit => CloneMachineModel.affineEmit 2 0)
      (labels .doubleScan) () symbol
  | .doubleRestore => MachineTransfer.loopAt (control slots .scratch) (control slots .capacity)
      id false (labels .doubleRestore) (some (labels .alphabet))
  | .alphabet => MachineSubstitution.pushWord (control slots .reversed) (encodeWord (2 ^ s))
      (.goto fun _ => labels (evalStart .edges))
  | .edgeTransfer => MachineTransfer.loopAt (control slots .temporary) (control slots .reversed)
      id false (labels .edgeTransfer) exit

structure WorkClean (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool) : Prop where
  accA : base (control slots .accA) = []
  accB : base (control slots .accB) = []
  counter : base (control slots .counter) = []
  scratch : base (control slots .scratch) = []
  coefficients : ∀ i : Coefficients k s d noiseCount, base (slots (.inr i)) = []

structure Clean (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool) : Prop
    extends WorkClean slots base where
  baseValue : base (control slots .baseValue) = []
  capacity : base (control slots .capacity) = []
  temporary : base (control slots .temporary) = []

theorem WorkClean.update_control {slots : Layout k s d noiseCount ↪ K} {base : K → List Bool}
    (clean : WorkClean slots base) (c : Control)
    (other : c ≠ .accA ∧ c ≠ .accB ∧ c ≠ .counter ∧ c ≠ .scratch) (word : List Bool) :
    WorkClean slots (Function.update base (control slots c) word) := by
  constructor
  · simpa [other.1.symm] using clean.accA
  · simpa [other.2.1.symm] using clean.accB
  · simpa [other.2.2.1.symm] using clean.counter
  · simpa [other.2.2.2.symm] using clean.scratch
  · intro i
    simpa [control, slots.injective.eq_iff] using clean.coefficients i

theorem evalPhaseTrace (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (kind : Kind) (base : K → List Bool) (value : Nat)
    (hinput : base (control slots (inputControl kind)) = encodeWord value)
    (hdest : base (control slots (outputControl kind)) = [])
    (clean : WorkClean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount kind) value]
      (some ⟨some (labels (evalStart kind)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (afterEval kind)), ((ambient, ()), none),
        Function.update base (control slots (outputControl kind))
          (encodeWord ((polynomial k s d noiseCount kind).eval value))⟩ := by
  have evaluated := SourceHeaderCounts.Eval.trace (polynomial k s d noiseCount kind)
    (evalSlots slots kind) (fun label => labels (.evaluate kind label))
    (some (labels (afterEval kind))) program (fun label => atLabels (.evaluate kind label))
    base value (by simpa using hinput)
    (fun i => by simpa using clean.coefficients (coefficientBlock k s d noiseCount kind i))
    ⟨by simpa using clean.accA, by simpa using clean.accB,
      by simpa using clean.counter, by simpa using clean.scratch⟩ ambient register
  simpa only [evalStart, MachineHorner.resultTapes, evalSlots_destination, hdest, List.append_nil]
    using evaluated

def headerBits (k s d noiseCount n m : Nat) : List Bool :=
  encodeWords [2 * capacity k s d n m, 2 ^ s, edgeCount k s d noiseCount m]

def resultTapes (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool)
    (n m : Nat) : K → List Bool :=
  Function.update (Function.update (Function.update base
    (control slots .baseValue) (encodeWord (radix s d n m)))
    (control slots .capacity) (encodeWord (capacity k s d n m)))
    (control slots .reversed) ((headerBits k s d noiseCount n m).reverse ++ base (control slots .reversed))

def steps (k s d noiseCount n m : Nat) : Nat :=
  2 * n + 3 * m + 10 +
    SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount .capacity) (radix s d n m) +
    SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount .edges) m +
    3 * capacity k s d n m + edgeCount k s d noiseCount m + 8

private theorem trace_trans_inline_MachineAddressHeaders {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def preparedBase (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool)
    (n m : Nat) : K → List Bool :=
  Function.update base (control slots .baseValue) (encodeWord (radix s d n m))

theorem prepareBaseTrace (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .occurrenceCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * n + 3 * m + 10]
      (some ⟨some (labels .copyNOut), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (evalStart .capacity)), ((ambient, ()), none),
        preparedBase slots base n m⟩ := by
  let t1 := Function.update base (control slots .baseValue) (encodeWord n)
  let t2 := Function.update t1 (control slots .temporary) (encodeWord m)
  let t3 := Function.update (Function.update t2 (control slots .temporary) [false])
    (control slots .baseValue) (encodeWord (m + n))
  let t4 := Function.update (Function.update t3 (control slots .temporary) [])
    (control slots .baseValue) (encodeWord (radix s d n m))
  have copyingN := MachineCopy.copyTrace (control slots .variableCount)
    (control slots .baseValue) (control slots .scratch) (by simp) (by simp) (by simp)
    false (labels .copyNOut) (labels .copyNBack) (some (labels .copyMOut)) program
    (atLabels .copyNOut) (atLabels .copyNBack) base clean.scratch (ambient, ()) register
  rw [hn, clean.baseValue, List.append_nil, encodeWord_length] at copyingN
  have copyingM := MachineCopy.copyTrace (control slots .occurrenceCount)
    (control slots .temporary) (control slots .scratch) (by simp) (by simp) (by simp)
    false (labels .copyMOut) (labels .copyMBack) (some (labels .addM)) program
    (atLabels .copyMOut) (atLabels .copyMBack) t1
    (by simpa [t1] using clean.scratch) (ambient, ()) none
  have hm1 : t1 (control slots .occurrenceCount) = encodeWord m := by simpa [t1] using hm
  have ht1 : t1 (control slots .temporary) = [] := by simpa [t1] using clean.temporary
  rw [hm1, ht1, List.append_nil, encodeWord_length] at copyingM
  have adding := MachineUnaryAddAt.addFromTapes (control slots .temporary)
    (control slots .baseValue) (by simp) (labels .addM) (some (labels .seedBase)) program
    (atLabels .addM) t2 m n [] [] (by simp [t2]) (by simp [t2, t1]) (ambient, ()) none
  have added : MachineUnaryAddAt.unaryTapes (control slots .temporary)
      (control slots .baseValue) t2 0 (m + n) [] [] = t3 := by
    simp [MachineUnaryAddAt.unaryTapes, MachineTransfer.tapesAt, t3, encodeWord]
  rw [added] at adding
  have seeding : (advance (TM2.step program))^[1]
      (some ⟨some (labels .seedBase), ((ambient, ()), none), t3⟩) =
      some ⟨some (labels (evalStart .capacity)), ((ambient, ()), none), t4⟩ := by
    change some (TM2.stepAux (program (labels .seedBase)) _ _) = _
    rw [atLabels]
    simp only [statement, TM2.stepAux]
    have htemp : t3 (control slots .temporary) = [false] := by simp [t3]
    rw [htemp]
    simp only [List.tail_cons]
    rw [MachineSubstitution.stepAux_pushWord]
    simp only [TM2.stepAux]
    have different : control slots .baseValue ≠ control slots .temporary := by simp
    rw [Function.update_of_ne different]
    have hbase : t3 (control slots .baseValue) = encodeWord (m + n) := by simp [t3]
    rw [hbase]
    have wordEq : (List.replicate (baseConstant s d) true).reverse ++ encodeWord (m + n) =
        encodeWord (radix s d n m) := by
      simp [encodeWord, List.reverse_replicate, ← List.append_assoc,
        List.replicate_append_replicate, radix, Nat.add_comm, Nat.add_assoc]
    rw [wordEq]
  have combined := trace_trans_inline_MachineAddressHeaders _ (trace_trans_inline_MachineAddressHeaders _ (trace_trans_inline_MachineAddressHeaders _ copyingN copyingM) adding) seeding
  have timeEq : 2 * (n + 1 + 1) + 2 * (m + 1 + 1) + (m + 1) + 1 =
      2 * n + 3 * m + 10 := by omega
  rw [timeEq] at combined
  have frame : t4 = preparedBase slots base n m := by
    funext tape
    by_cases ht : tape = control slots .temporary
    · subst tape
      simp [t4, t3, t2, t1, preparedBase, clean.temporary]
    · simp [t4, t3, t2, t1, preparedBase, Function.update_apply, ht]
      split_ifs <;> rfl
  rw [frame] at combined
  exact combined

theorem doubleTrace (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (value : Nat)
    (hcap : base (control slots .capacity) = encodeWord value)
    (hscratch : base (control slots .scratch) = []) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[3 * value + 5]
      (some ⟨some (labels .doubleScan), ((ambient, ()), register), base⟩) =
      some ⟨some (labels .alphabet), ((ambient, ()), none),
        Function.update base (control slots .reversed)
          ((encodeWord (2 * value)).reverse ++ base (control slots .reversed))⟩ := by
  have copied := MachineTransducerCopy.transduceCopyTrace (control slots .capacity)
    (control slots .scratch) (control slots .reversed) (by simp) (by simp) (by simp)
    () (fun q _ => q) (fun _ : Unit => CloneMachineModel.affineEmit 2 0)
    (labels .doubleScan) (labels .doubleRestore) (fun _ symbol => labels (.doubleEmit symbol))
    (some (labels .alphabet)) program (atLabels .doubleScan)
    (by intro q symbol; cases q; exact atLabels (.doubleEmit symbol))
    (atLabels .doubleRestore) base hscratch ambient () register
  rw [hcap, CloneMachineAffine.output_eq_flatMap, CloneMachineAffine.affineEmit_word,
    Nat.zero_add, encodeWord_length] at copied
  have timeEq : 3 * (value + 1) + 2 = 3 * value + 5 := by omega
  rw [timeEq] at copied
  exact copied

theorem trace (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .occurrenceCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps k s d noiseCount n m]
      (some ⟨some (labels .copyNOut), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩ := by
  let t1 := preparedBase slots base n m
  let t2 := Function.update t1 (control slots .capacity) (encodeWord (capacity k s d n m))
  let t3 := Function.update t2 (control slots .reversed)
    ((encodeWord (2 * capacity k s d n m)).reverse ++ t2 (control slots .reversed))
  let t4 := Function.update t3 (control slots .reversed)
    ((encodeWord (2 ^ s)).reverse ++ t3 (control slots .reversed))
  let t5 := Function.update t4 (control slots .temporary) (encodeWord (edgeCount k s d noiseCount m))
  have prepared := prepareBaseTrace slots labels exit program atLabels base n m hn hm clean ambient register
  have cw1 : WorkClean slots t1 := clean.toWorkClean.update_control .baseValue (by decide) _
  have evaluatedCap := evalPhaseTrace slots labels exit program atLabels .capacity t1 (radix s d n m)
    (by simp [t1, preparedBase, inputControl])
    (by simpa [t1, preparedBase, outputControl] using clean.capacity) cw1 ambient none
  simp only [polynomial_capacity_eval] at evaluatedCap
  change (advance (TM2.step program))^[SourceHeaderCounts.Eval.steps
      (polynomial k s d noiseCount .capacity) (radix s d n m)]
    (some ⟨some (labels (evalStart .capacity)), ((ambient, ()), none), t1⟩) =
    some ⟨some (labels .doubleScan), ((ambient, ()), none), t2⟩ at evaluatedCap
  have cw2 : WorkClean slots t2 := cw1.update_control .capacity (by decide) _
  have doubled := doubleTrace slots labels exit program atLabels t2 (capacity k s d n m)
    (by simp [t2]) cw2.scratch ambient none
  have alphabetStep : (advance (TM2.step program))^[1]
      (some ⟨some (labels .alphabet), ((ambient, ()), none), t3⟩) =
      some ⟨some (labels (evalStart .edges)), ((ambient, ()), none), t4⟩ := by
    change some (TM2.stepAux (program (labels .alphabet)) _ _) = _
    rw [atLabels]
    change some (TM2.stepAux (MachineSubstitution.pushWord _ _ _) _ _) = _
    rw [MachineSubstitution.stepAux_pushWord]
    rfl
  have cw3 : WorkClean slots t3 := cw2.update_control .reversed (by decide) _
  have cw4 : WorkClean slots t4 := cw3.update_control .reversed (by decide) _
  have evaluatedEdges := evalPhaseTrace slots labels exit program atLabels .edges t4 m
    (by simpa [t4, t3, t2, t1, preparedBase, inputControl] using hm)
    (by simpa [t4, t3, t2, t1, preparedBase, outputControl] using clean.temporary)
    cw4 ambient none
  simp only [polynomial_edges_eval] at evaluatedEdges
  change (advance (TM2.step program))^[SourceHeaderCounts.Eval.steps
      (polynomial k s d noiseCount .edges) m]
    (some ⟨some (labels (evalStart .edges)), ((ambient, ()), none), t4⟩) =
    some ⟨some (labels .edgeTransfer), ((ambient, ()), none), t5⟩ at evaluatedEdges
  have transferred := MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool)
    (σ := σ × Unit) (control slots .temporary)
    (control slots .reversed) (by simp) id false (labels .edgeTransfer) exit program
    (atLabels .edgeTransfer) t5 (ambient, ()) none
  change (advance (TM2.step program))^[(t5 (control slots .temporary)).length + 1]
    (some ⟨some (labels .edgeTransfer), ((ambient, ()), none), t5⟩) = _ at transferred
  have ht5 : t5 (control slots .temporary) = encodeWord (edgeCount k s d noiseCount m) := by simp [t5]
  rw [ht5, encodeWord_length] at transferred
  simp only [List.map_id] at transferred
  have combined := trace_trans_inline_MachineAddressHeaders _ (trace_trans_inline_MachineAddressHeaders _ (trace_trans_inline_MachineAddressHeaders _
    (trace_trans_inline_MachineAddressHeaders _ (trace_trans_inline_MachineAddressHeaders _ prepared evaluatedCap) doubled) alphabetStep) evaluatedEdges) transferred
  have timeEq : 2 * n + 3 * m + 10 +
      SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount .capacity) (radix s d n m) +
      (3 * capacity k s d n m + 5) + 1 +
      SourceHeaderCounts.Eval.steps (polynomial k s d noiseCount .edges) m +
      (edgeCount k s d noiseCount m + 1 + 1) = steps k s d noiseCount n m := by
    unfold steps
    omega
  rw [timeEq] at combined
  have frame : MachineTransfer.tapesAt (control slots .temporary) (control slots .reversed)
      t5 [] ((encodeWord (edgeCount k s d noiseCount m)).reverse ++ t5 (control slots .reversed)) =
      resultTapes slots base n m := by
    funext tape
    by_cases ht : tape = control slots .temporary
    · subst tape
      simp [MachineTransfer.tapesAt, resultTapes, clean.temporary]
    · simp [MachineTransfer.tapesAt, t5, t4, t3, t2, t1, preparedBase, resultTapes,
        headerBits, encodeWords, List.reverse_append, List.append_assoc, Function.update_apply, ht]
      split_ifs <;> rfl
  rw [frame] at combined
  exact combined

def inTime (slots : Layout k s d noiseCount ↪ K)
    (labels : Label k s d noiseCount → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .occurrenceCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copyNOut), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩)
      (steps k s d noiseCount n m) where
  steps := steps k s d noiseCount n m
  evals_in_steps := trace slots labels exit program atLabels base n m hn hm clean ambient register
  steps_le_m := Nat.le_refl _

def timePolynomial (k s d noiseCount : Nat) : Polynomial Nat :=
  let B : Polynomial Nat := Polynomial.C 2 * Polynomial.X + Polynomial.C (baseConstant s d)
  (CookLevin.PolynomialMachine.timePolynomial (polynomial k s d noiseCount .capacity)).comp B +
    CookLevin.PolynomialMachine.timePolynomial (polynomial k s d noiseCount .edges) +
    Polynomial.C 3 * (polynomial k s d noiseCount .capacity).comp B +
    polynomial k s d noiseCount .edges + Polynomial.C 5 * Polynomial.X + Polynomial.C 18

theorem steps_le_timePolynomial (k s d noiseCount n m L : Nat) (hn : n ≤ L) (hm : m ≤ L) :
    steps k s d noiseCount n m ≤ (timePolynomial k s d noiseCount).eval L := by
  have hB : radix s d n m ≤ 2 * L + baseConstant s d := by unfold radix; omega
  have hEval (p : Polynomial Nat) (a b : Nat) (hab : a ≤ b) :
      SourceHeaderCounts.Eval.steps p a ≤ (CookLevin.PolynomialMachine.timePolynomial p).eval b := by
    apply Nat.le_trans (m := (CookLevin.PolynomialMachine.timePolynomial p).eval a)
    · rw [CookLevin.PolynomialMachine.timePolynomial_eval]
      unfold SourceHeaderCounts.Eval.steps
      omega
    · exact natPolynomial_eval_mono _ hab
  have h1 := hEval (polynomial k s d noiseCount .capacity) _ _ hB
  have h2 := hEval (polynomial k s d noiseCount .edges) _ _ hm
  have hc : capacity k s d n m ≤ (2 * L + baseConstant s d) ^ (1 + 9 * k) :=
    Nat.pow_le_pow_left hB _
  have he : edgeCount k s d noiseCount m ≤ edgeCount k s d noiseCount L :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm _)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_comp, polynomial_capacity_eval, polynomial_edges_eval]
  unfold steps
  omega

end Arithmetic

abbrev Layout (k s d noiseCount : Nat) := Fin 2 ⊕ Arithmetic.Layout k s d noiseCount

variable {k s d noiseCount : Nat} {K Λ σ : Type} [DecidableEq K]

def arithmeticSlots (slots : Layout k s d noiseCount ↪ K) :
    Arithmetic.Layout k s d noiseCount ↪ K :=
  (⟨Sum.inr, Sum.inr_injective⟩ : Arithmetic.Layout k s d noiseCount ↪
    Layout k s d noiseCount).trans slots

def prefixLocal (k s d noiseCount : Nat) : Fin 5 ↪ Layout k s d noiseCount where
  toFun i := match i.val with
    | 0 => .inl 0 | 1 => .inl 1
    | 2 => .inr (.inl .variableCount)
    | 3 => .inr (.inl .occurrenceCount)
    | _ => .inr (.inl .scratch)
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> cases h <;> rfl

def prefixSlots (slots : Layout k s d noiseCount ↪ K) : Fin 5 ↪ K :=
  (prefixLocal k s d noiseCount).trans slots

omit [DecidableEq K] in
theorem prefixSlots_apply (slots : Layout k s d noiseCount ↪ K) (index : Fin 5) :
    prefixSlots slots index = slots (match index.val with
      | 0 => .inl 0 | 1 => .inl 1
      | 2 => .inr (.inl .variableCount)
      | 3 => .inr (.inl .occurrenceCount)
      | _ => .inr (.inl .scratch)) := rfl

abbrev Label (k s d noiseCount : Nat) := Prefix.Label ⊕ Arithmetic.Label k s d noiseCount

def statement (slots : Layout k s d noiseCount ↪ K) (labels : Label k s d noiseCount → Λ)
    (exit : Option Λ) : Label k s d noiseCount →
      TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .inl label => Prefix.statement (prefixSlots slots) (fun l => labels (.inl l))
      (some (labels (.inr .copyNOut))) label
  | .inr label => Arithmetic.statement (arithmeticSlots slots) (fun l => labels (.inr l)) exit label

structure Clean (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool) : Prop
    extends Arithmetic.Clean (arithmeticSlots slots) base where
  readCopy : base (slots (.inl 1)) = []
  variableCount : base (Arithmetic.control (arithmeticSlots slots) .variableCount) = []
  occurrenceCount : base (Arithmetic.control (arithmeticSlots slots) .occurrenceCount) = []

theorem prefixResult_control (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool)
    (n m : Nat) (c : Arithmetic.Control)
    (hn : c ≠ .variableCount) (hm : c ≠ .occurrenceCount) :
    Prefix.resultTapes (prefixSlots slots) base n m
      (Arithmetic.control (arithmeticSlots slots) c) =
    base (Arithmetic.control (arithmeticSlots slots) c) := by
  apply Prefix.resultTapes_other <;>
    simp [prefixSlots_apply, Arithmetic.control, arithmeticSlots,
      slots.injective.eq_iff, hn, hm]

theorem prefixResult_coefficient (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) (i : Arithmetic.Coefficients k s d noiseCount) :
    Prefix.resultTapes (prefixSlots slots) base n m (arithmeticSlots slots (.inr i)) =
      base (arithmeticSlots slots (.inr i)) := by
  apply Prefix.resultTapes_other <;>
    simp [prefixSlots_apply, arithmeticSlots, slots.injective.eq_iff]

theorem Clean.afterPrefix {slots : Layout k s d noiseCount ↪ K} {base : K → List Bool}
    (clean : Clean slots base) (n m : Nat) :
    Arithmetic.Clean (arithmeticSlots slots) (Prefix.resultTapes (prefixSlots slots) base n m) := by
  constructor
  · constructor
    · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.accA
    · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.accB
    · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.counter
    · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.scratch
    · intro i; rw [prefixResult_coefficient]; exact clean.coefficients i
  · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.baseValue
  · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.capacity
  · rw [prefixResult_control _ _ _ _ _ (by decide) (by decide)]; exact clean.temporary

def resultTapes (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool)
    (n m : Nat) : K → List Bool :=
  Arithmetic.resultTapes (arithmeticSlots slots)
    (Prefix.resultTapes (prefixSlots slots) base n m) n m

def inTime (slots : Layout k s d noiseCount ↪ K) (labels : Label k s d noiseCount → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (input : SourceEncoding.Input)
    (hinput : base (slots (.inl 0)) = SourceEncoding.inputBits input)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inl .copyOut)), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none),
        resultTapes slots base input.«variables» input.equations.length⟩)
      (Arithmetic.steps k s d noiseCount input.«variables» input.equations.length +
        (3 * (SourceEncoding.inputBits input).length + 6)) := by
  have parsed := Prefix.inTime (prefixSlots slots) (fun l => labels (.inl l))
    (some (labels (.inr .copyNOut))) program (fun l => atLabels (.inl l))
    base input.«variables» input.equations.length
    (encodeWords (input.equations.flatMap SourceEncoding.equationWords))
    (by simpa [prefixSlots_apply, SourceEncoding.inputBits,
      SourceEncoding.inputWords, encodeWords, List.append_assoc] using hinput)
    clean.readCopy clean.scratch ambient register
  have hn : Prefix.resultTapes (prefixSlots slots) base input.«variables» input.equations.length
      (Arithmetic.control (arithmeticSlots slots) .variableCount) = encodeWord input.«variables» := by
    change Prefix.resultTapes (prefixSlots slots) base input.«variables» input.equations.length
      (prefixSlots slots 2) = _
    rw [Prefix.resultTapes_n]
    change encodeWord input.«variables» ++
      base (Arithmetic.control (arithmeticSlots slots) .variableCount) = _
    rw [clean.variableCount, List.append_nil]
  have hm : Prefix.resultTapes (prefixSlots slots) base input.«variables» input.equations.length
      (Arithmetic.control (arithmeticSlots slots) .occurrenceCount) =
        encodeWord input.equations.length := by
    change Prefix.resultTapes (prefixSlots slots) base input.«variables» input.equations.length
      (prefixSlots slots 3) = _
    rw [Prefix.resultTapes_m]
    change encodeWord input.equations.length ++
      base (Arithmetic.control (arithmeticSlots slots) .occurrenceCount) = _
    rw [clean.occurrenceCount, List.append_nil]
  have arithmetic := Arithmetic.inTime (arithmeticSlots slots) (fun l => labels (.inr l))
    exit program (fun l => atLabels (.inr l))
    (Prefix.resultTapes (prefixSlots slots) base input.«variables» input.equations.length)
    input.«variables» input.equations.length hn hm
    (clean.afterPrefix input.«variables» input.equations.length) ambient none
  have joined := StateTransition.EvalsToInTime.trans (TM2.step program) _ _ _ _ _ parsed arithmetic
  have sourceEq : base (prefixSlots slots 0) = SourceEncoding.inputBits input := hinput
  simpa only [resultTapes, sourceEq] using joined

def timePolynomial (k s d noiseCount : Nat) : Polynomial Nat :=
  Arithmetic.timePolynomial k s d noiseCount + Polynomial.C 3 * Polynomial.X + Polynomial.C 6

def inPolynomialTime (slots : Layout k s d noiseCount ↪ K) (labels : Label k s d noiseCount → Λ)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ label, program (labels label) = statement slots labels exit label)
    (base : K → List Bool) (input : SourceEncoding.Input)
    (hinput : base (slots (.inl 0)) = SourceEncoding.inputBits input)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inl .copyOut)), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none),
        resultTapes slots base input.«variables» input.equations.length⟩)
      ((timePolynomial k s d noiseCount).eval (SourceEncoding.inputBits input).length) := by
  have run := inTime slots labels exit program atLabels base input hinput clean ambient register
  refine { steps := run.steps, evals_in_steps := run.evals_in_steps, steps_le_m := ?_ }
  apply Nat.le_trans run.steps_le_m
  have bound := Arithmetic.steps_le_timePolynomial k s d noiseCount
    input.«variables» input.equations.length (SourceEncoding.inputBits input).length
    (SourceEncoding.inputBits_length_ge_variables input) (SourceEncoding.inputBits_length_ge_equations input)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

@[simp] theorem resultTapes_source (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (slots (.inl 0)) = base (slots (.inl 0)) := by
  simp [resultTapes, Arithmetic.resultTapes, Prefix.resultTapes,
    prefixSlots_apply, arithmeticSlots, Arithmetic.control, slots.injective.eq_iff]

@[simp] theorem resultTapes_n (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (Arithmetic.control (arithmeticSlots slots) .variableCount) =
      encodeWord n ++ base (Arithmetic.control (arithmeticSlots slots) .variableCount) := by
  simp [resultTapes, Arithmetic.resultTapes, Prefix.resultTapes,
    prefixSlots_apply, arithmeticSlots, Arithmetic.control, slots.injective.eq_iff]

@[simp] theorem resultTapes_m (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (Arithmetic.control (arithmeticSlots slots) .occurrenceCount) =
      encodeWord m ++ base (Arithmetic.control (arithmeticSlots slots) .occurrenceCount) := by
  simp [resultTapes, Arithmetic.resultTapes, Prefix.resultTapes,
    prefixSlots_apply, arithmeticSlots, Arithmetic.control, slots.injective.eq_iff]

@[simp] theorem resultTapes_base (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (Arithmetic.control (arithmeticSlots slots) .baseValue) =
      encodeWord (radix s d n m) := by simp [resultTapes, Arithmetic.resultTapes]

@[simp] theorem resultTapes_capacity (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (Arithmetic.control (arithmeticSlots slots) .capacity) =
      encodeWord (capacity k s d n m) := by simp [resultTapes, Arithmetic.resultTapes]

@[simp] theorem resultTapes_reversed (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (Arithmetic.control (arithmeticSlots slots) .reversed) =
      (Arithmetic.headerBits k s d noiseCount n m).reverse ++
        base (Arithmetic.control (arithmeticSlots slots) .reversed) := by
  simp [resultTapes, Arithmetic.resultTapes,
    prefixResult_control slots base n m .reversed (by decide) (by decide)]

theorem resultTapes_other (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) (tape : K)
    (hread : tape ≠ slots (.inl 1))
    (hn : tape ≠ Arithmetic.control (arithmeticSlots slots) .variableCount)
    (hm : tape ≠ Arithmetic.control (arithmeticSlots slots) .occurrenceCount)
    (hB : tape ≠ Arithmetic.control (arithmeticSlots slots) .baseValue)
    (hcap : tape ≠ Arithmetic.control (arithmeticSlots slots) .capacity)
    (hout : tape ≠ Arithmetic.control (arithmeticSlots slots) .reversed) :
    resultTapes slots base n m tape = base tape := by
  simp only [resultTapes, Arithmetic.resultTapes, Function.update_of_ne hout,
    Function.update_of_ne hcap, Function.update_of_ne hB]
  apply Prefix.resultTapes_other <;> assumption

@[simp] theorem resultTapes_readCopy (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) : resultTapes slots base n m (slots (.inl 1)) = [] := by
  simp [resultTapes, Arithmetic.resultTapes, Prefix.resultTapes,
    prefixSlots_apply, arithmeticSlots, Arithmetic.control, slots.injective.eq_iff]

end

end DFVSGames.Reduction.MachineAddressHeaders
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
