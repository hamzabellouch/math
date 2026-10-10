import Mathlib
import OAI.Computability.MinUncut.Machines.RuntimeModel

namespace OAI

section

namespace MinUncutGames.Foundations.Hastad.SourceHeaderCounts

open Turing Complexity
open MachineComposition

noncomputable section

namespace Eval

open CookLevin.PolynomialMachine

variable {K Λ σ : Type} [DecidableEq K]

abbrev Label (p : Polynomial Nat) := Unit ⊕ (MachineHorner.Label (width p) ⊕ Unit)

def start (p : Polynomial Nat) : Label p := .inl ()
def inner (p : Polynomial Nat) (l : MachineHorner.Label (width p)) : Label p := .inr (.inl l)
def finish (p : Polynomial Nat) : Label p := .inr (.inr ())

def word (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K) : K → List Bool :=
  Function.extend slots (fieldWord p) (fun _ => [])

def indices (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K) : List K :=
  (fieldIndices p).map slots

omit [DecidableEq K] in
theorem indices_nodup (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K) :
    (indices p slots).Nodup := (fieldIndices_nodup p).map slots.injective

omit [DecidableEq K] in
@[simp] theorem word_slot (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (i : MachineHorner.Layout (width p)) : word p slots (slots i) = fieldWord p i :=
  slots.injective.extend_apply _ _ i

omit [DecidableEq K] in
@[simp] theorem control_not_mem (p : Polynomial Nat)
    (slots : MachineHorner.Layout (width p) ↪ K) (i : Fin 6) :
    slots (.inl i) ∉ indices p slots := by
  simp [indices, slots.injective.eq_iff]

omit [DecidableEq K] in
@[simp] theorem digit_mem (p : Polynomial Nat)
    (slots : MachineHorner.Layout (width p) ↪ K) (i : Fin (width p)) :
    slots (.inr i) ∈ indices p slots := by
  simp [indices, slots.injective.eq_iff]

def prepared (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (base : K → List Bool) : K → List Bool :=
  prependFieldsTapes (word p slots) (indices p slots) base

@[simp] theorem prepared_control (p : Polynomial Nat)
    (slots : MachineHorner.Layout (width p) ↪ K) (base : K → List Bool) (i : Fin 6) :
    prepared p slots base (slots (.inl i)) = base (slots (.inl i)) := by
  rw [prepared, prependFieldsTapes_apply _ _ (indices_nodup p slots)]
  simp

@[simp] theorem prepared_digit (p : Polynomial Nat)
    (slots : MachineHorner.Layout (width p) ↪ K) (base : K → List Bool)
    (i : Fin (width p)) (hi : base (slots (.inr i)) = []) :
    prepared p slots base (slots (.inr i)) = encodeWord (digit p i.val) := by
  rw [prepared, prependFieldsTapes_apply _ _ (indices_nodup p slots)]
  simp [fieldWord, hi]

theorem clear_result (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (base : K → List Bool) (result : Nat)
    (hcoeff : ∀ i : Fin (width p), base (slots (.inr i)) = []) :
    clearFieldsTapes (fun k => (word p slots k).length) (indices p slots)
      (MachineHorner.resultTapes slots (prepared p slots base) result) =
      MachineHorner.resultTapes slots base result := by
  funext k
  rw [clearFieldsTapes_apply _ _ (indices_nodup p slots)]
  by_cases h : k ∈ indices p slots
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
    simp [MachineHorner.resultTapes, slots.injective.eq_iff, prepared_digit,
      fieldWord, hcoeff]
  · by_cases hd : k = slots (.inl 3)
    · subst k
      simp [MachineHorner.resultTapes]
    · simp [h, MachineHorner.resultTapes, hd, prepared,
        prependFieldsTapes_apply _ _ (indices_nodup p slots)]

def statement (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (labels : Label p → Λ) (exit : Option Λ) :
    Label p → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .inl _ => prependFields (word p slots) (indices p slots)
      (.goto fun _ => labels (inner p .start))
  | .inr (.inl l) => MachineHorner.statement slots (fun l => labels (inner p l))
      (some (labels (finish p))) l
  | .inr (.inr _) => clearFields (fun k => (word p slots k).length) (indices p slots)
      (Reduction.MachineTransfer.exitAt (slots (.inl 3)) exit)

def steps (p : Polynomial Nat) (n : Nat) : Nat :=
  MachineHorner.steps n (digit p) (width p) + 2

theorem trace (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (labels : Label p → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement p slots labels exit l)
    (base : K → List Bool) (n : Nat)
    (hinput : base (slots (.inl 0)) = encodeWord n)
    (hcoeff : ∀ i : Fin (width p), base (slots (.inr i)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps p n]
      (some ⟨some (labels (start p)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (p.eval n)⟩ := by
  have hp : (advance (TM2.step program))^[1]
      (some ⟨some (labels (start p)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (inner p .start)), ((ambient, ()), register), prepared p slots base⟩ := by
    change some (TM2.stepAux (program (labels (start p))) _ _) = _
    rw [atLabels]
    change some (TM2.stepAux (prependFields _ _ _) _ _) = _
    rw [stepAux_prependFields]
    rfl
  have hh := MachineHorner.hornerTrace slots (fun l => labels (inner p l))
    (some (labels (finish p))) program (fun l => atLabels (inner p l))
    (prepared p slots base) n (digit p) (by simpa using hinput)
    (fun i => prepared_digit p slots base i (hcoeff i))
    (by
      constructor
      · simpa using clean.accA
      · simpa using clean.accB
      · simpa using clean.counter
      · simpa using clean.scratch) ambient register
  rw [hornerValue_eq_eval] at hh
  have hc : (advance (TM2.step program))^[1]
      (some ⟨some (labels (finish p)), ((ambient, ()), none),
        MachineHorner.resultTapes slots (prepared p slots base) (p.eval n)⟩) =
      some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (p.eval n)⟩ := by
    change some (TM2.stepAux (program (labels (finish p))) _ _) = _
    rw [atLabels]
    change some (TM2.stepAux (clearFields _ _ _) _ _) = _
    rw [stepAux_clearFields, clear_result p slots base _ hcoeff]
    cases exit <;> rfl
  rw [show steps p n = 1 + (MachineHorner.steps n (digit p) (width p) + 1) by
    unfold steps; omega, Function.iterate_add_apply, Function.iterate_add_apply, hp, hh, hc]

def inTime (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (labels : Label p → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement p slots labels exit l)
    (base : K → List Bool) (n : Nat)
    (hinput : base (slots (.inl 0)) = encodeWord n)
    (hcoeff : ∀ i : Fin (width p), base (slots (.inr i)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (start p)), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (p.eval n)⟩)
      ((timePolynomial p).eval n) where
  steps := steps p n
  evals_in_steps := trace p slots labels exit program atLabels base n hinput hcoeff clean ambient register
  steps_le_m := by rw [timePolynomial_eval]; unfold steps; omega

end Eval

def leftValue (u n : Nat) : Nat := 2 ^ (2 ^ u) * n ^ u
def rightValue (u m : Nat) : Nat := 2 ^ (8 ^ u) * m ^ u
def dummyValue (u n m : Nat) : Nat := leftValue u n + rightValue u m
def bitValue (u n m : Nat) : Nat := dummyValue u n m + 1
def occurrenceValue (u D m : Nat) : Nat :=
  3 ^ u * (SourceOccurrences.testTapeEncoding u D).size * m ^ u

inductive Kind
  | left | right | occurrences
  deriving DecidableEq

protected abbrev Kind.enumList : List Kind := [.left, .right, .occurrences]

protected theorem Kind.enumList_getElem?_ctorIdx_eq (x : Kind) :
    Kind.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Kind.enumList_nodup : Kind.enumList.Nodup := by decide

instance : Fintype Kind where
  elems := ⟨Kind.enumList, Kind.enumList_nodup⟩
  complete x := by cases x <;> decide

def polynomial (u D : Nat) : Kind → Polynomial Nat
  | .left => Polynomial.C (2 ^ (2 ^ u)) * Polynomial.X ^ u
  | .right => Polynomial.C (2 ^ (8 ^ u)) * Polynomial.X ^ u
  | .occurrences => Polynomial.C (3 ^ u * (SourceOccurrences.testTapeEncoding u D).size) *
      Polynomial.X ^ u

@[simp] theorem polynomial_left_eval (u D n : Nat) :
    (polynomial u D .left).eval n = leftValue u n := by simp [polynomial, leftValue]
@[simp] theorem polynomial_right_eval (u D m : Nat) :
    (polynomial u D .right).eval m = rightValue u m := by simp [polynomial, rightValue]
@[simp] theorem polynomial_occurrences_eval (u D m : Nat) :
    (polynomial u D .occurrences).eval m = occurrenceValue u D m := by
  simp [polynomial, occurrenceValue]

theorem bitValue_eq_nBits (F : Target.Formula) (u : Nat) :
    bitValue u F.«variables» F.clauses.length = SourceOccurrences.nBits F u := by
  rw [SourceOccurrences.nBits_eq]
  simp [bitValue, dummyValue, leftValue, rightValue, Nat.mul_comm, Nat.add_assoc]

theorem occurrenceValue_eq_length (F : Target.Formula) (u D : Nat)
    (hm : 0 < F.clauses.length) :
    occurrenceValue u D F.clauses.length = (SourceOccurrences.sourceList F u D).length := by
  have hne : F.clauses ≠ [] := by intro h; simp [h] at hm
  have hfalse : ¬ F.clauses.isEmpty = true := by simpa using hne
  simp only [SourceOccurrences.sourceList, ite_eq_right hfalse]
  rw [SourceOccurrences.rawSourceList_length]
  unfold occurrenceValue
  rw [SourceBounds.testTapeEncoding_size]
  ac_rfl

inductive Control
  | variableCount | clauseCount | leftBlockSize | rightTemporary | dummyIndex
  | bitCount | occurrenceCount | accA | accB | counter | scratch
  deriving DecidableEq

protected abbrev Control.enumList : List Control := [.variableCount, .clauseCount, .leftBlockSize,
  .rightTemporary, .dummyIndex, .bitCount, .occurrenceCount, .accA, .accB, .counter, .scratch]

protected theorem Control.enumList_getElem?_ctorIdx_eq (x : Control) :
    Control.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Control.enumList_nodup : Control.enumList.Nodup := by decide

instance : Fintype Control where
  elems := ⟨Control.enumList, Control.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Coefficients (u D : Nat) :=
  Fin (CookLevin.PolynomialMachine.width (polynomial u D .left)) ⊕
    (Fin (CookLevin.PolynomialMachine.width (polynomial u D .right)) ⊕
      Fin (CookLevin.PolynomialMachine.width (polynomial u D .occurrences)))

abbrev Layout (u D : Nat) := Control ⊕ Coefficients u D

def coefficientBlock (u D : Nat) (kind : Kind) :
    Fin (CookLevin.PolynomialMachine.width (polynomial u D kind)) ↪ Coefficients u D :=
  match kind with
  | .left => ⟨Sum.inl, Sum.inl_injective⟩
  | .right => ⟨fun i => .inr (.inl i), Sum.inr_injective.comp Sum.inl_injective⟩
  | .occurrences => ⟨fun i => .inr (.inr i), Sum.inr_injective.comp Sum.inr_injective⟩

def inputControl : Kind → Control
  | .left => .variableCount | _ => .clauseCount

def outputControl : Kind → Control
  | .left => .leftBlockSize | .right => .rightTemporary | .occurrences => .occurrenceCount

def controlSlots (kind : Kind) : Fin 6 ↪ Control where
  toFun i := match i.val with
    | 0 => inputControl kind | 1 => .accA | 2 => .accB
    | 3 => outputControl kind | 4 => .counter | _ => .scratch
  inj' := by
    intro i j h
    cases kind <;> fin_cases i <;> fin_cases j <;> cases h <;> rfl

def localSlots (u D : Nat) (kind : Kind) :
    MachineHorner.Layout (CookLevin.PolynomialMachine.width (polynomial u D kind)) ↪ Layout u D where
  toFun
    | .inl i => .inl (controlSlots kind i)
    | .inr i => .inr (coefficientBlock u D kind i)
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
      | inr b => exact congrArg Sum.inr ((coefficientBlock u D kind).injective (Sum.inr.inj h))

variable {u D : Nat} {K Λ σ : Type}

def control (slots : Layout u D ↪ K) (c : Control) : K := slots (.inl c)

def evalSlots (slots : Layout u D ↪ K) (kind : Kind) :
    MachineHorner.Layout (CookLevin.PolynomialMachine.width (polynomial u D kind)) ↪ K :=
  (localSlots u D kind).trans slots

@[simp] theorem evalSlots_radix (slots : Layout u D ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 0) = control slots (inputControl kind) := rfl
@[simp] theorem evalSlots_accA (slots : Layout u D ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 1) = control slots .accA := rfl
@[simp] theorem evalSlots_accB (slots : Layout u D ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 2) = control slots .accB := rfl
@[simp] theorem evalSlots_destination (slots : Layout u D ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 3) = control slots (outputControl kind) := rfl
@[simp] theorem evalSlots_counter (slots : Layout u D ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 4) = control slots .counter := rfl
@[simp] theorem evalSlots_scratch (slots : Layout u D ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 5) = control slots .scratch := rfl
@[simp] theorem evalSlots_digit (slots : Layout u D ↪ K) (kind : Kind)
    (i : Fin (CookLevin.PolynomialMachine.width (polynomial u D kind))) :
    evalSlots slots kind (.inr i) = slots (.inr (coefficientBlock u D kind i)) := rfl

@[simp] theorem control_eq_iff (slots : Layout u D ↪ K) (a b : Control) :
    control slots a = control slots b ↔ a = b := by
  simp [control, slots.injective.eq_iff]

structure Clean (slots : Layout u D ↪ K) (base : K → List Bool) : Prop where
  left : base (control slots .leftBlockSize) = []
  right : base (control slots .rightTemporary) = []
  dummy : base (control slots .dummyIndex) = []
  bits : base (control slots .bitCount) = []
  occurrences : base (control slots .occurrenceCount) = []
  accA : base (control slots .accA) = []
  accB : base (control slots .accB) = []
  counter : base (control slots .counter) = []
  scratch : base (control slots .scratch) = []
  coefficients : ∀ i : Coefficients u D, base (slots (.inr i)) = []

inductive Label (u D : Nat)
  | evaluate (kind : Kind) (localLabel : Eval.Label (polynomial u D kind))
  | copyLeftOut | copyLeftBack | addRight | clearTemporary
  | copyDummyOut | copyDummyBack | incrementBits
  deriving DecidableEq, Fintype

def evalStart (kind : Kind) : Label u D := .evaluate kind (Eval.start (polynomial u D kind))

def afterEval : Kind → Label u D
  | .left => evalStart .right | .right => evalStart .occurrences | .occurrences => .copyLeftOut

variable [DecidableEq K]

def statement (slots : Layout u D ↪ K) (labels : Label u D → Λ) (exit : Option Λ) :
    Label u D → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .evaluate kind l => Eval.statement (polynomial u D kind) (evalSlots slots kind)
      (fun l => labels (.evaluate kind l)) (some (labels (afterEval kind))) l
  | .copyLeftOut => Reduction.MachineTransfer.loopAt (control slots .leftBlockSize)
      (control slots .scratch) id false (labels .copyLeftOut) (some (labels .copyLeftBack))
  | .copyLeftBack => MachineCopy.forkLoop (control slots .scratch)
      (control slots .leftBlockSize) (control slots .dummyIndex) false
      (labels .copyLeftBack) (some (labels .addRight))
  | .addRight => MachineUnaryAddAt.loop (control slots .rightTemporary)
      (control slots .dummyIndex) (labels .addRight) (some (labels .clearTemporary))
  | .clearTemporary => .pop (control slots .rightTemporary) (fun state _ => state)
      (.goto fun _ => labels .copyDummyOut)
  | .copyDummyOut => Reduction.MachineTransfer.loopAt (control slots .dummyIndex)
      (control slots .scratch) id false (labels .copyDummyOut) (some (labels .copyDummyBack))
  | .copyDummyBack => MachineCopy.forkLoop (control slots .scratch)
      (control slots .dummyIndex) (control slots .bitCount) false
      (labels .copyDummyBack) (some (labels .incrementBits))
  | .incrementBits => .push (control slots .bitCount) (fun _ => true)
      (Reduction.MachineTransfer.exitAt (control slots .bitCount) exit)

def resultTapes (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (control slots .leftBlockSize) (encodeWord (leftValue u n)))
    (control slots .occurrenceCount) (encodeWord (occurrenceValue u D m)))
    (control slots .dummyIndex) (encodeWord (dummyValue u n m)))
    (control slots .bitCount) (encodeWord (bitValue u n m))

def steps (u D n m : Nat) : Nat :=
  Eval.steps (polynomial u D .left) n + Eval.steps (polynomial u D .right) m +
    Eval.steps (polynomial u D .occurrences) m +
    2 * leftValue u n + rightValue u m + 2 * dummyValue u n m + 11

structure WorkClean (slots : Layout u D ↪ K) (base : K → List Bool) : Prop where
  accA : base (control slots .accA) = []
  accB : base (control slots .accB) = []
  counter : base (control slots .counter) = []
  scratch : base (control slots .scratch) = []
  coefficients : ∀ i : Coefficients u D, base (slots (.inr i)) = []

omit [DecidableEq K] in
theorem Clean.work {slots : Layout u D ↪ K} {base : K → List Bool} (clean : Clean slots base) :
    WorkClean slots base :=
  ⟨clean.accA, clean.accB, clean.counter, clean.scratch, clean.coefficients⟩

theorem WorkClean.update_output {slots : Layout u D ↪ K} {base : K → List Bool}
    (clean : WorkClean slots base) (kind : Kind) (value : List Bool) :
    WorkClean slots (Function.update base (control slots (outputControl kind)) value) := by
  cases kind <;> constructor
  all_goals try { simpa [outputControl] using clean.accA }
  all_goals try { simpa [outputControl] using clean.accB }
  all_goals try { simpa [outputControl] using clean.counter }
  all_goals try { simpa [outputControl] using clean.scratch }
  all_goals intro i; simpa [control, slots.injective.eq_iff] using clean.coefficients i

theorem evalPhaseTrace (slots : Layout u D ↪ K) (labels : Label u D → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (kind : Kind) (base : K → List Bool) (n : Nat)
    (hinput : base (control slots (inputControl kind)) = encodeWord n)
    (hdest : base (control slots (outputControl kind)) = [])
    (clean : WorkClean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[Eval.steps (polynomial u D kind) n]
      (some ⟨some (labels (evalStart kind)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (afterEval kind)), ((ambient, ()), none),
        Function.update base (control slots (outputControl kind))
          (encodeWord ((polynomial u D kind).eval n))⟩ := by
  have h := Eval.trace (polynomial u D kind) (evalSlots slots kind)
    (fun l => labels (.evaluate kind l)) (some (labels (afterEval kind))) program
    (fun l => atLabels (.evaluate kind l)) base n (by simpa using hinput)
    (fun i => by simpa using clean.coefficients (coefficientBlock u D kind i))
    ⟨by simpa using clean.accA, by simpa using clean.accB,
      by simpa using clean.counter, by simpa using clean.scratch⟩ ambient register
  simpa only [evalStart, MachineHorner.resultTapes, evalSlots_destination,
    hdest, List.append_nil] using h

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem trace (slots : Layout u D ↪ K) (labels : Label u D → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .clauseCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps u D n m]
      (some ⟨some (labels (evalStart .left)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩ := by
  let t1 := Function.update base (control slots .leftBlockSize) (encodeWord (leftValue u n))
  let t2 := Function.update t1 (control slots .rightTemporary) (encodeWord (rightValue u m))
  let t3 := Function.update t2 (control slots .occurrenceCount) (encodeWord (occurrenceValue u D m))
  let t4 := Function.update t3 (control slots .dummyIndex) (encodeWord (leftValue u n))
  let t5 := Function.update (Function.update t4 (control slots .rightTemporary) [false])
    (control slots .dummyIndex) (encodeWord (dummyValue u n m))
  let t6 := Function.update t5 (control slots .rightTemporary) []
  let t7 := Function.update t6 (control slots .bitCount) (encodeWord (dummyValue u n m))
  have h1 := evalPhaseTrace slots labels exit program atLabels .left base n hn clean.left
    clean.work ambient register
  change (advance (TM2.step program))^[Eval.steps (polynomial u D .left) n]
      (some ⟨some (labels (evalStart .left)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (evalStart .right)), ((ambient, ()), none), _⟩ at h1
  simp only [polynomial_left_eval] at h1
  have cw1 : WorkClean slots t1 := clean.work.update_output .left _
  have h2 := evalPhaseTrace slots labels exit program atLabels .right t1 m
    (by simpa [t1, inputControl] using hm)
    (by simpa [t1, outputControl] using clean.right) cw1 ambient none
  change (advance (TM2.step program))^[Eval.steps (polynomial u D .right) m]
      (some ⟨some (labels (evalStart .right)), ((ambient, ()), none), t1⟩) =
      some ⟨some (labels (evalStart .occurrences)), ((ambient, ()), none), _⟩ at h2
  simp only [polynomial_right_eval] at h2
  have cw2 : WorkClean slots t2 := cw1.update_output .right _
  have h3 := evalPhaseTrace slots labels exit program atLabels .occurrences t2 m
    (by simpa [t2, t1, inputControl] using hm)
    (by simpa [t2, t1, outputControl] using clean.occurrences) cw2 ambient none
  change (advance (TM2.step program))^[Eval.steps (polynomial u D .occurrences) m]
      (some ⟨some (labels (evalStart .occurrences)), ((ambient, ()), none), t2⟩) =
      some ⟨some (labels .copyLeftOut), ((ambient, ()), none), _⟩ at h3
  simp only [polynomial_occurrences_eval] at h3
  have cw3 : WorkClean slots t3 := cw2.update_output .occurrences _
  have copyingLeft := MachineCopy.copyTrace (control slots .leftBlockSize)
    (control slots .dummyIndex) (control slots .scratch)
    (by simp) (by simp) (by simp) false (labels .copyLeftOut) (labels .copyLeftBack)
    (some (labels .addRight)) program (atLabels .copyLeftOut) (atLabels .copyLeftBack)
    t3 cw3.scratch (ambient, ()) none
  have hleft : t3 (control slots .leftBlockSize) = encodeWord (leftValue u n) := by
    simp [t3, t2, t1]
  have hdummy : t3 (control slots .dummyIndex) = [] := by
    simpa [t3, t2, t1] using clean.dummy
  rw [hleft, hdummy, List.append_nil, encodeWord_length] at copyingLeft
  have adding := MachineUnaryAddAt.addFromTapes (control slots .rightTemporary)
    (control slots .dummyIndex) (by simp) (labels .addRight) (some (labels .clearTemporary))
    program (atLabels .addRight) t4 (rightValue u m) (leftValue u n) [] []
    (by simp [t4, t3, t2]) (by simp [t4]) (ambient, ()) none
  have ha : MachineUnaryAddAt.unaryTapes (control slots .rightTemporary)
      (control slots .dummyIndex) t4 0 (rightValue u m + leftValue u n) [] [] = t5 := by
    simp [MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt, t5,
      encodeWord, dummyValue, Nat.add_comm]
  rw [ha] at adding
  have clearing : (advance (TM2.step program))^[1]
      (some ⟨some (labels .clearTemporary), ((ambient, ()), none), t5⟩) =
      some ⟨some (labels .copyDummyOut), ((ambient, ()), none), t6⟩ := by
    change some (TM2.stepAux (program (labels .clearTemporary)) _ _) = _
    rw [atLabels]
    simp [statement, TM2.stepAux, t6, t5]
  have copyingDummy := MachineCopy.copyTrace (control slots .dummyIndex)
    (control slots .bitCount) (control slots .scratch)
    (by simp) (by simp) (by simp) false (labels .copyDummyOut) (labels .copyDummyBack)
    (some (labels .incrementBits)) program (atLabels .copyDummyOut) (atLabels .copyDummyBack)
    t6 (by simpa [t6, t5, t4] using cw3.scratch) (ambient, ()) none
  have hdi : t6 (control slots .dummyIndex) = encodeWord (dummyValue u n m) := by
    simp [t6, t5]
  have hbi : t6 (control slots .bitCount) = [] := by
    simpa [t6, t5, t4, t3, t2, t1] using clean.bits
  rw [hdi, hbi, List.append_nil, encodeWord_length] at copyingDummy
  have increment : (advance (TM2.step program))^[1]
      (some ⟨some (labels .incrementBits), ((ambient, ()), none), t7⟩) =
      some ⟨exit, ((ambient, ()), none),
        Function.update t7 (control slots .bitCount) (encodeWord (bitValue u n m))⟩ := by
    change some (TM2.stepAux (program (labels .incrementBits)) _ _) = _
    rw [atLabels]
    cases exit <;> simp [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt,
      t7, bitValue, encodeWord, List.replicate_succ]
  have total := trace_trans _ (trace_trans _ (trace_trans _ (trace_trans _
    (trace_trans _ (trace_trans _ (trace_trans _ h1 h2) h3) copyingLeft) adding) clearing)
      copyingDummy) increment
  have htime :
      Eval.steps (polynomial u D .left) n + Eval.steps (polynomial u D .right) m +
        Eval.steps (polynomial u D .occurrences) m + 2 * (leftValue u n + 1 + 1) +
        (rightValue u m + 1) + 1 + 2 * (dummyValue u n m + 1 + 1) + 1 =
      steps u D n m := by unfold steps; omega
  rw [htime] at total
  have frame : Function.update t7 (control slots .bitCount) (encodeWord (bitValue u n m)) =
      resultTapes slots base n m := by
    funext k
    by_cases hr : k = control slots .rightTemporary
    · subst k
      simp [t7, t6, t5, t4, t3, t2, t1, resultTapes, clean.right]
    · simp [t7, t6, t5, t4, t3, t2, t1, resultTapes, Function.update_apply, hr]
      split_ifs <;> rfl
  rw [frame] at total
  exact total

def timePolynomial (u D : Nat) : Polynomial Nat :=
  CookLevin.PolynomialMachine.timePolynomial (polynomial u D .left) +
    CookLevin.PolynomialMachine.timePolynomial (polynomial u D .right) +
    CookLevin.PolynomialMachine.timePolynomial (polynomial u D .occurrences) +
    Polynomial.C 2 * polynomial u D .left + polynomial u D .right +
    Polynomial.C 2 * (polynomial u D .left + polynomial u D .right) + Polynomial.C 11

theorem steps_le_timePolynomial (u D n m L : Nat) (hn : n ≤ L) (hm : m ≤ L) :
    steps u D n m ≤ (timePolynomial u D).eval L := by
  have hEval (p : Polynomial Nat) (a : Nat) (ha : a ≤ L) :
      Eval.steps p a ≤ (CookLevin.PolynomialMachine.timePolynomial p).eval L := by
    apply Nat.le_trans (m := (CookLevin.PolynomialMachine.timePolynomial p).eval a)
    · rw [CookLevin.PolynomialMachine.timePolynomial_eval]
      unfold Eval.steps
      omega
    · exact natPolynomial_eval_mono _ ha
  have h1 := hEval (polynomial u D .left) n hn
  have h2 := hEval (polynomial u D .right) m hm
  have h3 := hEval (polynomial u D .occurrences) m hm
  have hl : leftValue u n ≤ leftValue u L :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn u)
  have hr : rightValue u m ≤ rightValue u L :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm u)
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    polynomial_left_eval, polynomial_right_eval]
  unfold steps dummyValue
  omega

def inTime (slots : Layout u D ↪ K) (labels : Label u D → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (n m : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .clauseCount) = encodeWord m)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (evalStart .left)), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩)
      (steps u D n m) where
  steps := steps u D n m
  evals_in_steps := trace slots labels exit program atLabels base n m hn hm clean ambient register
  steps_le_m := Nat.le_refl _

def inPolynomialTime (slots : Layout u D ↪ K) (labels : Label u D → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (n m L : Nat)
    (hn : base (control slots .variableCount) = encodeWord n)
    (hm : base (control slots .clauseCount) = encodeWord m)
    (clean : Clean slots base) (hnL : n ≤ L) (hmL : m ≤ L)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (evalStart .left)), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base n m⟩)
      ((timePolynomial u D).eval L) where
  steps := steps u D n m
  evals_in_steps := trace slots labels exit program atLabels base n m hn hm clean ambient register
  steps_le_m := steps_le_timePolynomial u D n m L hnL hmL

def formulaInTime (slots : Layout u D ↪ K) (labels : Label u D → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (F : Target.Formula)
    (hn : base (control slots .variableCount) = encodeWord F.«variables»)
    (hm : base (control slots .clauseCount) = encodeWord F.clauses.length)
    (clean : Clean slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (evalStart .left)), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base F.«variables» F.clauses.length⟩)
      ((timePolynomial u D).eval (formulaBits F).length) :=
  inPolynomialTime slots labels exit program atLabels base F.«variables» F.clauses.length
    (formulaBits F).length hn hm clean (SourceBounds.formulaBits_length_ge_variables F)
    (SourceBounds.formulaBits_length_ge_clauses F) ambient register

theorem result_frame (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) (k : K)
    (hl : k ≠ control slots .leftBlockSize) (ho : k ≠ control slots .occurrenceCount)
    (hd : k ≠ control slots .dummyIndex) (hb : k ≠ control slots .bitCount) :
    resultTapes slots base n m k = base k := by
  simp [resultTapes, hl, ho, hd, hb]

@[simp] theorem result_left (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (control slots .leftBlockSize) = encodeWord (leftValue u n) := by
  simp [resultTapes]
@[simp] theorem result_occurrences (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (control slots .occurrenceCount) = encodeWord (occurrenceValue u D m) := by
  simp [resultTapes]
@[simp] theorem result_dummy (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (control slots .dummyIndex) = encodeWord (dummyValue u n m) := by
  simp [resultTapes]
@[simp] theorem result_bits (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (control slots .bitCount) = encodeWord (bitValue u n m) := by
  simp [resultTapes]
@[simp] theorem result_variableCount (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (control slots .variableCount) = base (control slots .variableCount) := by
  simp [resultTapes]
@[simp] theorem result_clauseCount (slots : Layout u D ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (control slots .clauseCount) = base (control slots .clauseCount) := by
  simp [resultTapes]

theorem result_source_headers (slots : Layout u D ↪ K) (base : K → List Bool)
    (F : Target.Formula) (hm : 0 < F.clauses.length) :
    resultTapes slots base F.«variables» F.clauses.length (control slots .bitCount) =
      encodeWord (SourceOccurrences.nBits F u) ∧
    resultTapes slots base F.«variables» F.clauses.length (control slots .occurrenceCount) =
      encodeWord (SourceOccurrences.sourceList F u D).length := by
  simp only [result_bits, result_occurrences, bitValue_eq_nBits,
    occurrenceValue_eq_length F u D hm, and_self]

def program (slots : Layout u D ↪ K) : Label u D →
    TM2.Stmt (fun _ : K => Bool) (Label u D) (MachineHorner.State σ) :=
  statement slots id none

def machine (u D : Nat) : FinTM2 where
  K := Layout u D
  k₀ := .inl .variableCount
  k₁ := .inl .bitCount
  Γ _ := Bool
  Λ := Label u D
  main := evalStart .left
  σ := MachineHorner.State Unit
  initialState := (((), ()), none)
  m := program (Function.Embedding.refl _)

def afterInitializationInTime {Extra : Type} [DecidableEq Extra]
    (slots : Layout u D ↪ SourceLoopInit.Tape u Extra)
    (hnslot : control slots .variableCount = SourceLoopInit.variableHeader)
    (hmslot : control slots .clauseCount = SourceLoopInit.clauseHeader)
    (labels : Label u D → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : SourceLoopInit.Tape u Extra => Bool) Λ
      (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : SourceLoopInit.Tape u Extra → List Bool) (F : Target.Formula)
    (hn : base SourceLoopInit.variableHeader = [])
    (hm : base SourceLoopInit.clauseHeader = [])
    (clean : Clean slots (SourceLoopInit.outputTapes F base))
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (evalStart .left)), ((ambient, ()), register),
        SourceLoopInit.outputTapes F base⟩
      (some ⟨exit, ((ambient, ()), none),
        resultTapes slots (SourceLoopInit.outputTapes F base) F.«variables» F.clauses.length⟩)
      ((timePolynomial u D).eval (formulaBits F).length) :=
  formulaInTime slots labels exit program atLabels (SourceLoopInit.outputTapes F base) F
    (by rw [hnslot, SourceLoopInit.output_variableHeader, hn, List.append_nil])
    (by rw [hmslot, SourceLoopInit.output_clauseHeader, hm, List.append_nil])
    clean ambient register

end

end MinUncutGames.Foundations.Hastad.SourceHeaderCounts

end
section
namespace MinUncutGames.Foundations.Hastad.SourceGeneratorModel

open Turing Complexity SourceRuntimeModel

abbrev Extra (u D : Nat) := SourceHeaderCounts.Coefficients u D ⊕ Unit
abbrev Tape (u D : Nat) := SourceRuntimeModel.Arena u (Extra u D)
abbrev State (u D : Nat) := SourceRuntimeModel.State u D

def outputTape (u D : Nat) : Tape u D := workTape (.extra (.inr ()))
def accumulatorTape (u D : Nat) : Tape u D := workTape .accumulator

def headerControl (u D : Nat) : SourceHeaderCounts.Control ↪ Tape u D where
  toFun
    | .variableCount => variableHeader
    | .clauseCount => clauseHeader
    | .leftBlockSize => workTape .leftBlock
    | .rightTemporary => workTape .rank
    | .dummyIndex => workTape .dummy
    | .bitCount => workTape .bitCount
    | .occurrenceCount => workTape .occurrenceCount
    | .accA => workTape .accA
    | .accB => workTape .accB
    | .counter => workTape .counter
    | .scratch => workTape .arithScratch
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all [variableHeader, clauseHeader,
      SourceLoopInit.variableHeader, SourceLoopInit.clauseHeader, workTape]

def headerSlots (u D : Nat) : SourceHeaderCounts.Layout u D ↪ Tape u D where
  toFun
    | .inl c => headerControl u D c
    | .inr i => workTape (.extra (.inl i))
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl ((headerControl u D).injective h)
      | inr b => cases a <;> cases h
    | inr a =>
      cases b with
      | inl b => cases b <;> cases h
      | inr b => simpa [workTape] using h

abbrev ControlAmbient (u D : Nat) := (Unit × Unit) × ArithmeticMetadata u D

def controlStateEquiv (u D : Nat) :
    ControlAmbient u D × Option Bool ≃ State u D where
  toFun x := arithmeticStateEquiv u D ((x.1.1, x.2), x.1.2)
  invFun x :=
    let y := (arithmeticStateEquiv u D).symm x
    ((y.1.1, y.2), y.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def initialQuery (u D : Nat) (hD : 0 < D) : SourceQueryLoop.Query u D :=
  (fun _ => false, fun _ => ⟨0, hD⟩, fun _ => false)

def initialState (u D : Nat) (hD : 0 < D) : State u D :=
  canonicalState (initialQuery u D hD)

def initialAmbient (u D : Nat) (hD : 0 < D) : ControlAmbient u D :=
  ((controlStateEquiv u D).symm (initialState u D hD)).1

theorem control_initial (u D : Nat) (hD : 0 < D) :
    controlStateEquiv u D (initialAmbient u D hD, none) = initialState u D hD := rfl

noncomputable def coefficientKeys (u D : Nat) : List (SourceHeaderCounts.Coefficients u D) :=
  (List.finRange (CookLevin.PolynomialMachine.width
    (SourceHeaderCounts.polynomial u D .left))).map Sum.inl ++
  (List.finRange (CookLevin.PolynomialMachine.width
    (SourceHeaderCounts.polynomial u D .right))).map (fun i => Sum.inr (Sum.inl i)) ++
  (List.finRange (CookLevin.PolynomialMachine.width
    (SourceHeaderCounts.polynomial u D .occurrences))).map (fun i => Sum.inr (Sum.inr i))

theorem mem_coefficientKeys (u D : Nat) (i : SourceHeaderCounts.Coefficients u D) :
    i ∈ coefficientKeys u D := by
  cases i with
  | inl i => simp [coefficientKeys]
  | inr i => cases i <;> simp [coefficientKeys]

noncomputable def workKeys (u D : Nat) : List (BodyWork (Extra u D)) :=
  [.leftBlock, .dummy, .bitCount, .occurrenceCount, .zero, .rank, .rightBase, .leftBase,
    .accA, .accB, .counter, .arithScratch, .coefficient, .queryTemporary,
    .queryScratch, .accumulator] ++
  (coefficientKeys u D).map (fun i => .extra (.inl i)) ++ [.extra (.inr ())]

theorem mem_workKeys (u D : Nat) (i : BodyWork (Extra u D)) : i ∈ workKeys u D := by
  cases i
  case extra e =>
    cases e with
    | inl i =>
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨i, mem_coefficientKeys u D i, rfl⟩))
    | inr i => cases i; simp [workKeys]
  all_goals simp [workKeys]

noncomputable def allTapes (u D : Nat) : List (Tape u D) :=
  [.formula, .index, .work, .scratch, .copyScratch] ++
  (List.finRange u).map SourceContextLoad.Tape.current ++
  (List.finRange u).map SourceContextLoad.Tape.remaining ++
  (List.finRange u).flatMap (fun i =>
    (List.finRange 6).map (SourceContextLoad.Tape.field i)) ++
  [variableHeader, clauseHeader] ++ (workKeys u D).map workTape

theorem mem_allTapes (u D : Nat) (k : Tape u D) : k ∈ allTapes u D := by
  cases k with
  | formula => simp [allTapes]
  | index => simp [allTapes]
  | work => simp [allTapes]
  | scratch => simp [allTapes]
  | copyScratch => simp [allTapes]
  | current i => simp [allTapes]
  | remaining i => simp [allTapes]
  | field i j => simp [allTapes]
  | extra e =>
    cases e with
    | inl h => cases h <;> simp [allTapes, variableHeader, clauseHeader,
        SourceLoopInit.variableHeader, SourceLoopInit.clauseHeader]
    | inr w =>
      have h : workTape (u := u) w ∈ (workKeys u D).map (workTape (u := u)) :=
        List.mem_map.mpr ⟨w, mem_workKeys u D w, rfl⟩
      simp only [allTapes, List.mem_append]
      tauto

noncomputable def clearKeys (u D : Nat) : List (Tape u D) := by
  classical
  exact (allTapes u D).filter
    (fun k => decide (k ≠ accumulatorTape u D ∧ k ≠ outputTape u D))

theorem mem_clearKeys (u D : Nat) (k : Tape u D) :
    k ∈ clearKeys u D ↔ k ≠ accumulatorTape u D ∧ k ≠ outputTape u D := by
  classical
  simp [clearKeys, mem_allTapes]

theorem accumulator_ne_output (u D : Nat) : accumulatorTape u D ≠ outputTape u D := by
  simp [accumulatorTape, outputTape, workTape]

end MinUncutGames.Foundations.Hastad.SourceGeneratorModel

end

end OAI
