import Mathlib
import OAI.Computability.MaxCut.Machines.MachineRegularLift

namespace OAI

/-!
Actual finite control for the dummy self-loop rows of one padded vertex.
The port count is a fixed program parameter. Vertex and reverse-dart indices
remain on unary tapes, and each row advances the reverse index by one actual
push. The all-true relation is a fixed literal field, initialized once.
-/

namespace MaxCutGames.Foundations.Complexity.MachineDummyRows

open Turing
open PCP.GraphTables
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

/-- The actual 64-by-64 always-accepting relation. -/
def trueRelation : RelationTable := Vector.replicate 4096 true

def trueBits : List Bool := encodeWords (relationWords trueRelation)

theorem trueBits_length : trueBits.length = 8192 := by
  simp only [trueBits, encodeWords_length, relationWords, trueRelation,
    Vector.toList_replicate, List.map_replicate, List.sum_replicate_nat,
    List.length_replicate] ; rfl

def rowBits (v e : Nat) : List Bool := encodeWord v ++ encodeWord e ++ trueBits

theorem rowBits_length (v e : Nat) : (rowBits v e).length = v + e + 8194 := by
  simp [rowBits, trueBits_length, encodeWord_length]
  omega

theorem rowBits_eq_graph_row {n m : Nat} (v : Fin n) (e : Fin m) :
    rowBits v.val e.val = encodeWords (rowWords (⟨v, e, trueRelation⟩ : DartRow n m)) := by
  rw [MachineTableRows.rowBits_eq]
  rfl

/-- Ordered serialized rows with successive physically stored reverse indices. -/
def rowsBits (v e : Nat) : Nat → List Bool
  | 0 => []
  | count + 1 => rowBits v e ++ rowsBits v (e + 1) count

/-- One initialization label and ten labels per fixed port. -/
abbrev Label (d : Nat) := Unit ⊕ (Fin d × (MachineTableRows.Label ⊕ Unit))

def start (d : Nat) : Label d := .inl ()
def rowLabel {d : Nat} (p : Fin d) (stage : MachineTableRows.Label) : Label d :=
  .inr (p, .inl stage)
def bumpLabel {d : Nat} (p : Fin d) : Label d := .inr (p, .inr ())

def fields : Fin 3 → Fin 6 := fun i => i.castLE (by decide)

/-- The only data-changing index operation is a tape push, below. This
function chooses a finite continuation among the fixed port-control labels. -/
def afterPort {d : Nat} (p : Fin d) : Option (Label d) :=
  if h : p.val + 1 < d then some (rowLabel ⟨p.val + 1, h⟩ .relationRead) else none

def entry (d : Nat) : Option (Label d) :=
  if h : 0 < d then some (rowLabel ⟨0, h⟩ .relationRead) else none

variable {σ : Type}

abbrev Alphabet (_ : Fin 6) := Bool

def continueAt {d : Nat} (exit : Option (Label d)) :
    TM2.Stmt Alphabet (Label d) (σ × Option Bool) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

theorem stepAux_continueAt {d : Nat} (exit : Option (Label d))
    (state : σ × Option Bool) (tapes : Fin 6 → List Bool) :
    TM2.stepAux (continueAt exit) state tapes = ⟨exit, state, tapes⟩ := by
  cases exit <;> rfl

/-- No input-dependent natural number occurs in the finite program. -/
def program (d : Nat) : Label d → TM2.Stmt Alphabet (Label d) (σ × Option Bool)
  | .inl () => pushWord 2 trueBits.reverse
      (.load (fun state => (state.1, none)) (continueAt (entry d)))
  | .inr (p, .inl stage) => MachineTableRows.routine fields 3 4 5
      (rowLabel p) (some (bumpLabel p)) stage
  | .inr (p, .inr ()) => .push 1 (fun _ => true) (continueAt (afterPort p))

/-- The three unary row fields, two empty work tapes, and accumulated output. -/
def fieldTapes (v e : Nat) (output : List Bool) : Fin 6 → List Bool :=
  ![encodeWord v, encodeWord e, trueBits, [], output, []]

/-- Before initialization, the fixed-relation tape is empty. -/
def initialTapes (v e : Nat) (output : List Bool) : Fin 6 → List Bool :=
  Function.update (fieldTapes v e output) 2 []

/-- The fixed literal relation is actually emitted by a finite push chain. -/
theorem initializeStep (d v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program d) ⟨some (start d), (ambient, register), initialTapes v e output⟩ =
      some ⟨entry d, (ambient, none), fieldTapes v e output⟩ := by
  change some (TM2.stepAux (program d (start d)) (ambient, register)
    (initialTapes v e output)) = _
  simp only [start, program, stepAux_pushWord, List.reverse_reverse, TM2.stepAux,
    initialTapes, Function.update_self, List.append_nil, Function.update_idem]
  have ht : Function.update (fieldTapes v e output) 2 trueBits = fieldTapes v e output := by
    funext i
    fin_cases i <;> simp [fieldTapes]
  rw [ht, stepAux_continueAt]

theorem rowTrace {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[
        4 * (v + e + 8194) + 2 * output.length + 9]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨some (bumpLabel p), (ambient, none), fieldTapes v e (output ++ rowBits v e)⟩ := by
  have hfields (i : Fin 3) : fields i ≠ (3 : Fin 6) ∧ fields i ≠ (5 : Fin 6) := by
    fin_cases i <;> decide
  have h := MachineTableRows.appendTrace fields (3 : Fin 6) 4 5 hfields
    (by decide) (by decide) (by decide) (rowLabel p) (some (bumpLabel p))
    (program d) (fun _ => rfl) (fieldTapes v e output) rfl rfl ambient register
  have hbits : MachineTableRows.fieldBits fields (fieldTapes v e output) = rowBits v e := by
    rfl
  have hsize : MachineTableRows.fieldSize fields (fieldTapes v e output) = v + e + 8194 := by
    rw [← MachineTableRows.fieldBits_length, hbits, rowBits_length]
  have ht : Function.update (fieldTapes v e output) 4 (output ++ rowBits v e) =
      fieldTapes v e (output ++ rowBits v e) := by
    funext i
    fin_cases i <;> simp [fieldTapes]
  simpa only [hsize, hbits, show fieldTapes v e output 4 = output from rfl, ht] using h

/-- The reverse index advances by pushing a real unary bit. The delimiter,
all input fields, output, and work tapes have their exact stated contents. -/
theorem bumpStep {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool) (ambient : σ) :
    TM2.step (program d) ⟨some (bumpLabel p), (ambient, none), fieldTapes v e output⟩ =
      some ⟨afterPort p, (ambient, none), fieldTapes v (e + 1) output⟩ := by
  change some (TM2.stepAux (program d (bumpLabel p)) (ambient, none)
    (fieldTapes v e output)) = _
  simp only [bumpLabel, program, TM2.stepAux]
  rw [stepAux_continueAt]
  congr 2
  funext i
  fin_cases i <;> simp [fieldTapes, encodeWord, List.replicate_succ]

/-- The concrete row body and its actual index increment are consecutive
phases of one fixed program; no whole-body trace is supplied as a premise. -/
theorem rowAndBumpTrace {d : Nat} (p : Fin d) (v e : Nat) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[
        4 * (v + e + 8194) + 2 * output.length + 10]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨afterPort p, (ambient, none), fieldTapes v (e + 1) (output ++ rowBits v e)⟩ := by
  rw [show 4 * (v + e + 8194) + 2 * output.length + 10 =
      (4 * (v + e + 8194) + 2 * output.length + 9) + 1 by omega,
    Function.iterate_succ_apply', rowTrace, MachineComposition.advance_some]
  exact bumpStep p v e (output ++ rowBits v e) ambient

/-- Exact sum of actual row-and-increment costs. This recurrence is matched
to the program by `suffixTrace`, rather than postulated as a runtime. -/
def steps (v e : Nat) (output : List Bool) : Nat → Nat
  | 0 => 0
  | count + 1 => (4 * (v + e + 8194) + 2 * output.length + 10) +
      steps v (e + 1) (output ++ rowBits v e) count

/-- Actual execution from any port boundary to the final halt. The finite
control index fixes the remaining number of rows; all unbounded values are
physically stored in `fieldTapes`. -/
theorem suffixTrace {d : Nat} (count : Nat) (p : Fin d) (hp : p.val + count = d)
    (v e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[steps v e output count]
      (some ⟨some (rowLabel p .relationRead), (ambient, register), fieldTapes v e output⟩) =
      some ⟨none, (ambient, none), fieldTapes v (e + count) (output ++ rowsBits v e count)⟩ := by
  induction count generalizing p v e output register with
  | zero =>
    have hlt := p.isLt
    omega
  | succ count ih =>
    rw [steps, Nat.add_comm (4 * (v + e + 8194) + 2 * output.length + 10),
      Function.iterate_add_apply, rowAndBumpTrace]
    by_cases hc : count = 0
    · subst count
      have hlast : ¬ p.val + 1 < d := by omega
      simp [afterPort, hlast, steps, rowsBits]
    · have hnext : p.val + 1 < d := by omega
      rw [afterPort, dite_eq_left hnext]
      have hh := ih ⟨p.val + 1, hnext⟩ (by change (p.val + 1) + count = d; omega)
        v (e + 1) (output ++ rowBits v e) none
      have he : (e + 1) + count = e + (count + 1) := by omega
      simpa only [rowsBits, List.append_assoc, he] using hh

/-- One fixed-relation initialization transition followed by all actual rows.
At zero ports initialization itself halts; no row is spuriously produced. -/
theorem allTrace (d v e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[steps v e output d + 1]
      (some ⟨some (start d), (ambient, register), initialTapes v e output⟩) =
      some ⟨none, (ambient, none), fieldTapes v (e + d) (output ++ rowsBits v e d)⟩ := by
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (program d)))^[steps v e output d]
    (TM2.step (program d) ⟨some (start d), (ambient, register), initialTapes v e output⟩) = _
  rw [initializeStep]
  by_cases hd : 0 < d
  · rw [entry, dite_eq_left hd]
    exact suffixTrace d ⟨0, hd⟩ (by simp) v e output ambient none
  · have hz : d = 0 := by omega
    subst d
    simp [entry, steps, rowsBits]

/-- Actual finite graph rows in increasing reverse-index order. -/
def graphRows {n m : Nat} (v : Fin n) (e : Nat) :
    (count : Nat) → e + count ≤ m → List (DartRow n m)
  | 0, _ => []
  | count + 1, h =>
      ⟨v, ⟨e, by omega⟩, trueRelation⟩ ::
        graphRows v (e + 1) count (by omega)

theorem graphRows_length {n m : Nat} (v : Fin n) (e count : Nat) (h : e + count ≤ m) :
    (graphRows v e count h).length = count := by
  induction count generalizing e with
  | zero => rfl
  | succ count ih => simp [graphRows, ih]

/-- The machine's bit stream is exactly the existing codec on the actual
ordered row list, including both index fields and every predicate entry. -/
theorem rowsBits_eq_graphRows {n m : Nat} (v : Fin n) (e count : Nat)
    (h : e + count ≤ m) :
    rowsBits v.val e count = encodeWords ((graphRows v e count h).flatMap rowWords) := by
  induction count generalizing e with
  | zero => rfl
  | succ count ih =>
    simp [rowsBits, graphRows, encodeWords_append, MachineTableRows.rowBits_eq,
      rowBits, trueBits]
    exact ih (e + 1) (by omega)

/-- For one vertex of an `n`-vertex degree-`d` graph, every dummy dart is its
own reverse. The caller's initial index is the actual unary value `d * v`. -/
def dummyRows {n : Nat} (d : Nat) (v : Fin n) : List (DartRow n (n * d)) :=
  graphRows v (d * v.val) d (by
    have h := Nat.mul_le_mul_right d (Nat.succ_le_of_lt v.isLt)
    simpa only [Nat.succ_mul, Nat.mul_comm] using h)

theorem dummyRows_length {n : Nat} (d : Nat) (v : Fin n) :
    (dummyRows d v).length = d := graphRows_length _ _ _ _

theorem dummyRowsTrace {n : Nat} (d : Nat) (v : Fin n) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program d)))^[steps v.val (d * v.val) output d + 1]
      (some ⟨some (start d), (ambient, register), initialTapes v.val (d * v.val) output⟩) =
      some ⟨none, (ambient, none), fieldTapes v.val (d * v.val + d)
        (output ++ encodeWords ((dummyRows d v).flatMap rowWords))⟩ := by
  have h := allTrace d v.val (d * v.val) output ambient register
  rw [rowsBits_eq_graphRows v (d * v.val) d (by
    have h := Nat.mul_le_mul_right d (Nat.succ_le_of_lt v.isLt)
    simpa only [Nat.succ_mul, Nat.mul_comm] using h)] at h
  exact h

/-- Every actual row cost is bounded by the largest row and accumulated
output encountered during this finite loop. -/
theorem steps_le_bound (v e : Nat) (output : List Bool) (count : Nat) :
    steps v e output count ≤ count *
      (4 * (v + e + count + 8194) +
        2 * (output.length + count * (v + e + count + 8194)) + 10) := by
  induction count generalizing e output with
  | zero => simp [steps]
  | succ count ih =>
    let B := v + e + (count + 1) + 8194
    let C := 4 * B + 2 * (output.length + (count + 1) * B) + 10
    have hb : v + (e + 1) + count + 8194 = B := by dsimp [B]; omega
    have hi := ih (e + 1) (output ++ rowBits v e)
    rw [List.length_append, rowBits_length, hb] at hi
    have hrow : v + e + 8194 ≤ B := by dsimp [B]; omega
    have hout : output.length + (v + e + 8194) + count * B ≤
        output.length + (count + 1) * B := by
      calc
        _ ≤ output.length + B + count * B :=
          Nat.add_le_add_right (Nat.add_le_add_left hrow output.length) _
        _ = _ := by simp only [Nat.add_mul, Nat.one_mul]; omega
    have hconstant : 4 * B + 2 * (output.length + (v + e + 8194) + count * B) + 10 ≤ C := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hout) (4 * B)) 10
    have hremaining := hi.trans (Nat.mul_le_mul_left count hconstant)
    have hbody : 4 * (v + e + 8194) + 2 * output.length + 10 ≤ C := by
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 4 hrow)
        (Nat.mul_le_mul_left 2 (Nat.le_add_right output.length ((count + 1) * B)))) 10
    change (4 * (v + e + 8194) + 2 * output.length + 10) +
      steps v (e + 1) (output ++ rowBits v e) count ≤ (count + 1) * C
    calc
      _ ≤ C + count * C := Nat.add_le_add hbody hremaining
      _ = (count + 1) * C := by rw [Nat.add_mul, Nat.one_mul]; omega

/-- The variable-size input is exactly the two physical unary fields and
existing output. The relation field is a fixed program constant. -/
def inputSize (v e : Nat) (output : List Bool) : Nat :=
  (encodeWord v).length + (encodeWord e).length + output.length

/-- A linear polynomial for each fixed port count `d`. -/
noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C d *
    (Polynomial.C 4 * (Polynomial.X + Polynomial.C (d + 8192)) +
      Polynomial.C 2 * (Polynomial.X + Polynomial.C d *
        (Polynomial.X + Polynomial.C (d + 8192))) + Polynomial.C 10) + 1

theorem timePolynomial_bounds (d v e : Nat) (output : List Bool) :
    steps v e output d + 1 ≤ (timePolynomial d).eval (inputSize v e output) := by
  have h := steps_le_bound v e output d
  have hB : v + e + d + 8194 ≤ inputSize v e output + d + 8192 := by
    simp only [inputSize, encodeWord_length]
    omega
  have hO : output.length ≤ inputSize v e output := by
    simp only [inputSize, encodeWord_length]
    omega
  have hm := Nat.mul_le_mul_left d hB
  have hinner :
      4 * (v + e + d + 8194) + 2 * (output.length + d * (v + e + d + 8194)) + 10 ≤
      4 * (inputSize v e output + d + 8192) +
        2 * (inputSize v e output + d * (inputSize v e output + d + 8192)) + 10 := by
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 4 hB)
      (Nat.mul_le_mul_left 2 (Nat.add_le_add hO hm))) 10
  have htotal := h.trans (Nat.mul_le_mul_left d hinner)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  simpa only [Nat.add_assoc] using Nat.add_le_add_right htotal 1

/-- A fixed finite machine. Its control stores only the fixed port position;
vertex and reverse-index values reside on the tapes. -/
def machine (d : Nat) : FinTM2 where
  K := Fin 6
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := Label d
  main := start d
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program d

/-- The full actual finite-machine execution, including initialization and
all rows. No body trace or runtime hypothesis is an input to this certificate. -/
def machineInTime (d v e : Nat) (output : List Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine d).step
      ⟨some (start d), ((), register), initialTapes v e output⟩
      (some ⟨none, ((), none), fieldTapes v (e + d) (output ++ rowsBits v e d)⟩)
      ((timePolynomial d).eval (inputSize v e output)) where
  steps := steps v e output d + 1
  evals_in_steps := by
    convert allTrace d v e output () register using 1 ; rfl
  steps_le_m := timePolynomial_bounds d v e output

/-- The same actual machine on the padding invariant `e = d * v`, with
its exact existing-codec graph-row output. -/
def machineDummyInTime {n : Nat} (d : Nat) (v : Fin n)
    (output : List Bool) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine d).step
      ⟨some (start d), ((), register), initialTapes v.val (d * v.val) output⟩
      (some ⟨none, ((), none), fieldTapes v.val (d * v.val + d)
        (output ++ encodeWords ((dummyRows d v).flatMap rowWords))⟩)
      ((timePolynomial d).eval (inputSize v.val (d * v.val) output)) where
  steps := steps v.val (d * v.val) output d + 1
  evals_in_steps := by
    convert dummyRowsTrace d v output () register using 1 ; rfl
  steps_le_m := timePolynomial_bounds d v.val (d * v.val) output

/-- Input tail and both work tapes retain their required contents. The
relation tape keeps the one initialized fixed field for subsequent use. -/
theorem finalFrame (v e : Nat) (output : List Bool) :
    fieldTapes v e output 0 = encodeWord v ∧
    fieldTapes v e output 2 = trueBits ∧
    fieldTapes v e output 3 = [] ∧ fieldTapes v e output 5 = [] :=
  ⟨rfl, rfl, rfl, rfl⟩

end MaxCutGames.Foundations.Complexity.MachineDummyRows

/-!
# Actual inherited-row emission for a dummy vertex

The fixed program preserves the physical unary vertex index on tape zero,
computes its inherited reverse index on tape one, invokes the actual one-port
dummy-row emitter, and drains the computed index and fixed true relation.
Tape four accumulates output. Tapes one, two, three, and five are empty at both
boundaries. The degree is fixed program data, not an input-dependent control
parameter.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularDummyRow

open Turing MachineComposition PCP.GraphTables

abbrev Tape := Fin 6
abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := σ × Option Bool

inductive Label
  | affine (stage : MachineUnaryAffineAt.Label)
  | row (stage : MachineDummyRows.Label 1)
  | reverse | relation
  deriving DecidableEq, Fintype

def reverseIndex (q x : Nat) : Nat := (q + 1) * x + q

def emittedBits (q x : Nat) : List Bool :=
  MachineDummyRows.rowBits x (reverseIndex q x)

/-- The row subprogram is a static label placement of the checked emitter. -/
def instruction {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt Alphabet Λ (State σ)
  | .affine .seed => MachineUnaryAffineAt.seed 1 q (labels (.affine .scan))
  | .affine .scan => MachineUnaryAffineAt.scan 0 3 1 (q + 1)
      (labels (.affine .scan)) (labels (.affine .restore))
  | .affine .restore => Reduction.MachineTransfer.loopAt 3 0 id false
      (labels (.affine .restore)) (some (labels (.row (MachineDummyRows.start 1))))
  | .row stage => MachineCloudPadding.Placement.statement (id : Tape → Tape)
      (fun l => labels (.row l)) (some (labels .reverse))
      (MachineDummyRows.program 1 stage)
  | .reverse => MachineDrain.drain 1 (labels .reverse) (some (labels .relation))
  | .relation => MachineDrain.drain 2 (labels .relation) exit

structure Input (x : Nat) (base : Tape → List Bool) : Prop where
  source : base 0 = encodeWord x
  reverseEmpty : base 1 = []
  relationEmpty : base 2 = []
  scratchEmpty : base 3 = []
  rowEmpty : base 5 = []

def memory (x : Nat) (output : List Bool) : Tape → List Bool :=
  ![encodeWord x, [], [], [], output, []]

theorem memory_input (x : Nat) (output : List Bool) : Input x (memory x output) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem join_trace_inline_MachineRegularDummyRow {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

theorem affine_frame (x e : Nat) (base : Tape → List Bool) (input : Input x base) :
    Function.update base 1 (encodeWord e) =
      MachineDummyRows.initialTapes x e (base 4) := by
  funext k
  fin_cases k <;>
    simp [MachineDummyRows.initialTapes, MachineDummyRows.fieldTapes,
      input.source, input.relationEmpty, input.scratchEmpty, input.rowEmpty]

theorem cleanup_frame (x e : Nat) (output : List Bool)
    (base : Tape → List Bool) (input : Input x base) :
    Function.update (Function.update (MachineDummyRows.fieldTapes x e output) 1 []) 2 [] =
      Function.update base 4 output := by
  funext k
  fin_cases k <;>
    simp [MachineDummyRows.fieldTapes, input.source, input.reverseEmpty,
      input.relationEmpty, input.scratchEmpty, input.rowEmpty]

/-- The existing one-port emitter executes under the caller's actual labels. -/
theorem rowTraceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (x e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineDummyRows.steps x e output 1 + 1]
      (some ⟨some (labels (.row (MachineDummyRows.start 1))), (ambient, register),
        MachineDummyRows.initialTapes x e output⟩) =
      some ⟨some (labels .reverse), (ambient, none),
        MachineDummyRows.fieldTapes x (e + 1) (output ++ MachineDummyRows.rowBits x e)⟩ := by
  have run := MachineDummyRows.allTrace 1 x e output ambient register
  have placed := MachineCloudPadding.Placement.trace (id : Tape → Tape) (fun k => some k)
    (fun _ => rfl) (fun _ _ h => (Option.some.inj h).symm)
    (fun l => labels (.row l)) (some (labels .reverse)) (fun _ => [])
    (MachineDummyRows.program 1) program
    (fun l => code (.row l)) _ _ _ run
  have identityTapes (source : Tape → List Bool) :
      MachineCloudPadding.Placement.tapes (fun k : Tape => some k) source
        (fun _ : Tape => []) = source := rfl
  simpa only [MachineCloudPadding.Placement.configuration,
    MachineCloudPadding.Placement.label, identityTapes,
    MachineDummyRows.rowsBits, List.append_nil] using placed

/-- Both cleanup loops pop their entire physical fields. -/
theorem cleanupTraceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (x e : Nat) (output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[
        ((encodeWord e).length + 1) + (MachineDummyRows.trueBits.length + 1)]
      (some ⟨some (labels .reverse), (ambient, register),
        MachineDummyRows.fieldTapes x e output⟩) =
      some ⟨exit, (ambient, none),
        Function.update (Function.update (MachineDummyRows.fieldTapes x e output) 1 []) 2 []⟩ := by
  let base := MachineDummyRows.fieldTapes x e output
  let mid := Function.update base (1 : Tape) []
  have first := MachineDrain.drainTrace (1 : Tape) (labels .reverse)
    (some (labels .relation)) program (code .reverse) base (base 1) ambient register
  have second := MachineDrain.drainTrace (2 : Tape) (labels .relation)
    exit program (code .relation) mid (mid 2) ambient none
  simp only [Function.update_eq_self] at first second
  have hreverse : base 1 = encodeWord e := rfl
  have hrelation : mid 2 = MachineDummyRows.trueBits := by
    simp only [mid, Function.update_of_ne (by decide : (2 : Tape) ≠ 1)]
    rfl
  rw [hreverse] at first
  rw [hrelation] at second
  exact join_trace_inline_MachineRegularDummyRow first second

/-- Sum of the actual arithmetic, row-emission, and cleanup transition counts. -/
def steps (q x : Nat) (output : List Bool) : Nat :=
  ((2 * (x + 1) + 1) + (MachineDummyRows.steps x (reverseIndex q x) output 1 + 1)) +
    (((encodeWord (reverseIndex q x + 1)).length + 1) +
      (MachineDummyRows.trueBits.length + 1))

/-- For each fixed degree, the exact cost is linear in index and prior output. -/
def timeBound (q x outputLength : Nat) : Nat :=
  (5 * q + 11) * x + 2 * outputLength + 5 * q + 40986

theorem steps_eq (q x : Nat) (output : List Bool) :
    steps q x output = timeBound q x output.length := by
  simp only [steps, MachineDummyRows.steps, encodeWord_length, MachineDummyRows.trueBits_length,
    reverseIndex, timeBound]
  ring

/-- Exact physical execution; only the accumulated output changes at the boundary. -/
theorem traceAt {σ Λ : Type} (q : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Alphabet Λ (State σ))
    (code : ∀ l, program (labels l) = instruction q labels exit l)
    (x : Nat) (base : Tape → List Bool) (input : Input x base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps q x (base 4)]
      (some ⟨some (labels (.affine .seed)), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Function.update base 4 (base 4 ++ emittedBits q x)⟩ := by
  have affine := MachineUnaryAffineAt.seededAffineTrace (0 : Tape) 3 1
    (by decide) (by decide) (by decide) (q + 1) q
    (labels (.affine .seed)) (labels (.affine .scan)) (labels (.affine .restore))
    (some (labels (.row (MachineDummyRows.start 1)))) program
    (code (.affine .seed)) (code (.affine .scan)) (code (.affine .restore))
    base x [] (by simpa only [List.append_nil] using input.source)
    input.scratchEmpty ambient register
  simp only [input.reverseEmpty, List.append_nil] at affine
  change (advance (TM2.step program))^[2 * (x + 1) + 1]
    (some ⟨some (labels (.affine .seed)), (ambient, register), base⟩) =
      some ⟨some (labels (.row (MachineDummyRows.start 1))), (ambient, none),
        Function.update base 1 (encodeWord (reverseIndex q x))⟩ at affine
  rw [affine_frame x (reverseIndex q x) base input] at affine
  have row := rowTraceAt q labels exit program code x (reverseIndex q x) (base 4) ambient none
  have clean := cleanupTraceAt q labels exit program code x (reverseIndex q x + 1)
    (base 4 ++ MachineDummyRows.rowBits x (reverseIndex q x)) ambient none
  rw [cleanup_frame x (reverseIndex q x + 1) _ base input] at clean
  exact join_trace_inline_MachineRegularDummyRow (join_trace_inline_MachineRegularDummyRow affine row) clean

/-- A canonical finite machine over six Boolean stacks. -/
def machine (q : Nat) : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 4
  Γ := Alphabet
  Λ := Label
  main := .affine .seed
  σ := State Unit
  initialState := ((), none)
  m := instruction q id none

def machineInTime (q x : Nat) (base : Tape → List Bool) (input : Input x base)
    (register : Option Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some (.affine .seed), ((), register), base⟩
      (some ⟨none, ((), none), Function.update base (4 : Tape)
        (base 4 ++ emittedBits q x)⟩)
      (timeBound q x (base 4).length) where
  steps := steps q x (base 4)
  evals_in_steps := traceAt q id none (instruction q id none)
    (fun _ => rfl) x base input () register
  steps_le_m := (steps_eq q x (base 4)).le

end MaxCutGames.Foundations.Complexity.MachineRegularDummyRow

namespace MaxCutGames.Foundations.Complexity.MachinePaddingRows

open Turing MachineComposition

inductive Control | initialize | guard | bump
  deriving DecidableEq

protected abbrev Control.enumList : List Control := [.initialize, .guard, .bump]

protected theorem Control.enumList_getElem?_ctorIdx_eq (x : Control) :
    Control.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Control.enumList_nodup : Control.enumList.Nodup := by decide

instance : Fintype Control where
  elems := ⟨Control.enumList, Control.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := Fin 6 ⊕ Unit
abbrev Label (d : Nat) := MachineDummyRows.Label d ⊕ Control
abbrev Alphabet : Tape → Type := MachineEmbedding.Alphabet
  (fun _ : Fin 6 => Bool) (fun _ : Unit => Bool)
abbrev State := (Unit × Option Bool) × Unit

def bodyEntry (d : Nat) (hd : 0 < d) : Label d :=
  .inl (MachineDummyRows.rowLabel ⟨0, hd⟩ .relationRead)

def extra (d : Nat) (hd : 0 < d) : Control → TM2.Stmt Alphabet (Label d) State
  | .initialize => Reduction.MachineSubstitution.pushWord (.inl 2)
      MachineDummyRows.trueBits.reverse
      (.load (fun _ => (((), none), ())) (.goto (fun _ => .inr .guard)))
  | .guard => .pop (.inr ()) (fun _ bit => (((), bit), ()))
      (.branch (fun s => s.1.2.getD false)
        (.load (fun _ => (((), none), ())) (.goto (fun _ => bodyEntry d hd)))
        (.push (.inr ()) (fun _ => false)
          (.load (fun _ => (((), none), ())) .halt)))
  | .bump => .push (.inl 0) (fun _ => true) (.goto (fun _ => .inr .guard))

def program (d : Nat) (hd : 0 < d) : Label d → TM2.Stmt Alphabet (Label d) State :=
  MachineEmbedding.program (some (.inr .bump)) (MachineDummyRows.program d) (extra d hd)

def tapes (v e fuel : Nat) (output : List Bool) : ∀ k, List (Alphabet k) :=
  MachineEmbedding.tapes (MachineDummyRows.fieldTapes v e output)
    (fun _ : Unit => encodeWord fuel)

def cfg (d : Nat) (label : Option (Label d)) (v e fuel : Nat)
    (output : List Bool) : TM2.Cfg Alphabet (Label d) State :=
  ⟨label, (((), none), ()), tapes v e fuel output⟩

theorem bodyTrace (d : Nat) (hd : 0 < d) (v e fuel : Nat) (output : List Bool) :
    (advance (TM2.step (program d hd)))^[MachineDummyRows.steps v e output d]
      (some (cfg d (some (bodyEntry d hd)) v e fuel output)) =
      some (cfg d (some (.inr .bump)) v (e + d) fuel
        (output ++ MachineDummyRows.rowsBits v e d)) := by
  have run := MachineDummyRows.suffixTrace d ⟨0, hd⟩ (by simp)
    v e output () none
  have lifted := liftSuccessfulTrace
    (TM2.step (MachineDummyRows.program d)) (TM2.step (program d hd))
    (MachineEmbedding.configuration (some (.inr .bump)) ()
      (fun _ : Unit => encodeWord fuel))
    (by
      intro a b h
      exact MachineEmbedding.step_simulation (some (.inr Control.bump)) ()
        (fun _ : Unit => encodeWord fuel) (MachineDummyRows.program d) (extra d hd) a b h)
    (MachineDummyRows.steps v e output d) _ _ run
  exact lifted

theorem guard_succ (d : Nat) (hd : 0 < d) (v e fuel : Nat) (output : List Bool) :
    TM2.step (program d hd) (cfg d (some (.inr .guard)) v e (fuel + 1) output) =
      some (cfg d (some (bodyEntry d hd)) v e fuel output) := by
  change some (TM2.stepAux (extra d hd .guard) _ _) = _
  simp only [extra, TM2.stepAux, tapes, MachineEmbedding.tapes_inr,
    encodeWord, List.replicate_succ, List.cons_append, List.head?_cons,
    List.tail_cons, Option.getD_some, Bool.cond_true]
  congr 2
  funext k
  cases k <;> simp [tapes, MachineEmbedding.tapes, Function.update, encodeWord]

theorem guard_zero (d : Nat) (hd : 0 < d) (v e : Nat) (output : List Bool) :
    TM2.step (program d hd) (cfg d (some (.inr .guard)) v e 0 output) =
      some (cfg d none v e 0 output) := by
  change some (TM2.stepAux (extra d hd .guard) _ _) = _
  simp only [extra, TM2.stepAux, tapes, MachineEmbedding.tapes_inr,
    encodeWord, List.replicate_zero, List.nil_append, List.head?_cons,
    List.tail_cons, Option.getD_some, Bool.cond_false]
  congr 2
  funext k
  cases k <;> simp [tapes, MachineEmbedding.tapes, Function.update, encodeWord]

theorem bump_step (d : Nat) (hd : 0 < d) (v e fuel : Nat) (output : List Bool) :
    TM2.step (program d hd) (cfg d (some (.inr .bump)) v e fuel output) =
      some (cfg d (some (.inr .guard)) (v + 1) e fuel output) := by
  change some (TM2.stepAux (extra d hd .bump) _ _) = _
  simp only [extra, TM2.stepAux]
  congr 2
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [tapes, MachineEmbedding.tapes,
      MachineDummyRows.fieldTapes, encodeWord, List.replicate_succ]
  | inr k => simp [tapes, MachineEmbedding.tapes]

def paddingBits (d v e : Nat) : Nat → List Bool
  | 0 => []
  | count + 1 => MachineDummyRows.rowsBits v e d ++ paddingBits d (v + 1) (e + d) count

def steps (d v e : Nat) (output : List Bool) : Nat → Nat
  | 0 => 1
  | count + 1 => (MachineDummyRows.steps v e output d + 2) +
      steps d (v + 1) (e + d) (output ++ MachineDummyRows.rowsBits v e d) count

/-- The entire varying-length padding loop is proved from its actual guards,
actual row bodies and actual vertex increments. -/
theorem loopTrace (d : Nat) (hd : 0 < d) (count v e : Nat) (output : List Bool) :
    (advance (TM2.step (program d hd)))^[steps d v e output count]
      (some (cfg d (some (.inr .guard)) v e count output)) =
      some (cfg d none (v + count) (e + count * d) 0
        (output ++ paddingBits d v e count)) := by
  induction count generalizing v e output with
  | zero => simpa [steps, paddingBits] using guard_zero d hd v e output
  | succ count ih =>
      rw [steps, Nat.add_comm (MachineDummyRows.steps v e output d + 2),
        Function.iterate_add_apply]
      have hb : (advance (TM2.step (program d hd)))^[MachineDummyRows.steps v e output d + 2]
          (some (cfg d (some (.inr .guard)) v e (count + 1) output)) =
          some (cfg d (some (.inr .guard)) (v + 1) (e + d) count
            (output ++ MachineDummyRows.rowsBits v e d)) := by
        rw [show MachineDummyRows.steps v e output d + 2 =
          (MachineDummyRows.steps v e output d + 1) + 1 by omega,
          Function.iterate_succ_apply, advance_some, guard_succ,
          Function.iterate_succ_apply', bodyTrace, advance_some, bump_step]
      rw [hb, ih]
      simp only [paddingBits, List.append_assoc, Nat.succ_mul]
      congr 2 <;> omega

def initialTapes (v e fuel : Nat) (output : List Bool) : ∀ k, List (Alphabet k) :=
  Function.update (tapes v e fuel output) (.inl 2) []

theorem initialize_step (d : Nat) (hd : 0 < d) (v e fuel : Nat) (output : List Bool) :
    TM2.step (program d hd)
      ⟨some (.inr .initialize), (((), none), ()), initialTapes v e fuel output⟩ =
      some (cfg d (some (.inr .guard)) v e fuel output) := by
  change some (TM2.stepAux (extra d hd .initialize) _ _) = _
  simp only [extra, Reduction.MachineSubstitution.stepAux_pushWord,
    List.reverse_reverse, initialTapes, Function.update_self, List.append_nil,
    Function.update_idem, TM2.stepAux]
  congr 2
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [tapes, MachineEmbedding.tapes,
      MachineDummyRows.fieldTapes]
  | inr k => simp [tapes, MachineEmbedding.tapes]

theorem paddingTrace (d : Nat) (hd : 0 < d) (count v e : Nat) (output : List Bool) :
    (advance (TM2.step (program d hd)))^[steps d v e output count + 1]
      (some ⟨some (.inr .initialize), (((), none), ()), initialTapes v e count output⟩) =
      some (cfg d none (v + count) (e + count * d) 0
        (output ++ paddingBits d v e count)) := by
  rw [Function.iterate_succ_apply, advance_some, initialize_step, loopTrace]

def machine (d : Nat) (hd : 0 < d) : FinTM2 where
  K := Tape
  k₀ := .inl 0
  k₁ := .inl 4
  Γ := Alphabet
  Λ := Label d
  main := .inr .initialize
  σ := State
  initialState := (((), none), ())
  m := program d hd

/-- The exact time count is the sum of the physically executed row loops.
Its polynomial bound is derived separately from this recurrence. -/
def execution (d : Nat) (hd : 0 < d) (count v e : Nat) (output : List Bool) :
    StateTransition.EvalsToInTime (machine d hd).step
      ⟨some (.inr .initialize), (((), none), ()), initialTapes v e count output⟩
      (some (cfg d none (v + count) (e + count * d) 0
        (output ++ paddingBits d v e count)))
      (steps d v e output count + 1) where
  steps := steps d v e output count + 1
  evals_in_steps := by convert paddingTrace d hd count v e output using 1 ; rfl
  steps_le_m := le_rfl

end MaxCutGames.Foundations.Complexity.MachinePaddingRows

end OAI
