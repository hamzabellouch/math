import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.List.FinRange
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineDrainManyLemmas
import OAI.Computability.UniqueGames.Machines.MachineLookupDiscard
import OAI.Computability.UniqueGames.Machines.MachineLookupLemmas
import OAI.Computability.UniqueGames.Machines.MachineProductGatherBoundsLemmas
import OAI.Computability.UniqueGames.Machines.MachineRadixStepLemmas
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Machines.MachineUnaryMultiply

namespace OAI

/-! One actual product-output field: gather the fixed number of coordinate
values from the input table, evaluate their common-radix code by Horner, move
the resulting word into the reversed output accumulator, and clear the gather
work. All input fields and the input table are preserved. -/

namespace UniqueGamesTheorem.Explicit.MachineProductField

section

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K] {width : Nat}

/-- Gather's table/query/scan/scratch and coordinate tapes; then radix, two
Horner accumulators, counter, scratch, isolated field output, global output. -/
abbrev Layout (width : Nat) := MachineProductGather.Tape width ⊕ Fin 7

def gatherSlots (slots : Layout width ↪ K) : MachineProductGather.Tape width ↪ K :=
  Function.Embedding.trans (Function.Embedding.inl) slots

def hornerRole : MachineHorner.Layout width → Layout width
  | .inl 0 => .inr 0
  | .inl 1 => .inr 1
  | .inl 2 => .inr 2
  | .inl 3 => .inr 5
  | .inl 4 => .inr 3
  | .inl 5 => .inr 4
  | .inr i => .inl (.inr (.inr i.rev))

theorem hornerRole_injective : Function.Injective (hornerRole (width := width)) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => fin_cases a <;> fin_cases b <;> simp_all [hornerRole]
    | inr b => fin_cases a <;> simp [hornerRole] at h
  | inr a =>
    cases b with
    | inl b => fin_cases b <;> simp [hornerRole] at h
    | inr b => simpa [hornerRole] using h

def hornerSlots (slots : Layout width ↪ K) : MachineHorner.Layout width ↪ K :=
  Function.Embedding.trans ⟨hornerRole, hornerRole_injective⟩ slots

def clearTapes (slots : Layout width ↪ K) : List K :=
  [slots (.inl (.inl 1)), slots (.inl (.inl 2))] ++
    List.ofFn (fun i : Fin width => slots (.inl (.inr (.inr i))))

abbrev Label (slots : Layout width ↪ K) :=
  MachineProductGather.Label width ⊕
    (MachineHorner.Label width ⊕ (Unit ⊕ MachineDrainMany.Label (clearTapes slots)))

def entry (slots : Layout width ↪ K) : Label slots :=
  .inl (MachineProductGather.entry width)

def instruction (slots : Layout width ↪ K) (coefficient : Nat) (offsets : Fin width → Nat)
    (labels : Label slots → Λ) (exit : Option Λ) :
    Label slots → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .inl l => MachineProductGather.instruction width (gatherSlots slots) coefficient offsets
      (fun x => labels (.inl x)) (some (labels (.inr (.inl .start)))) l
  | .inr (.inl l) => MachineHorner.statement (hornerSlots slots)
      (fun x => labels (.inr (.inl x))) (some (labels (.inr (.inr (.inl ()))))) l
  | .inr (.inr (.inl _)) => loopAt (slots (.inr 5)) (slots (.inr 6)) id false
      (labels (.inr (.inr (.inl ()))))
      (MachineDrainMany.entry (clearTapes slots) (fun x => labels (.inr (.inr (.inr x)))) exit)
  | .inr (.inr (.inr l)) => MachineDrainMany.instruction (clearTapes slots)
      (fun x => labels (.inr (.inr (.inr x)))) exit l

/-- Conditions on real input/work stacks; arbitrary output suffixes remain
permitted. The two query/scan tapes are empty at a row boundary. -/
structure Ready (slots : Layout width ↪ K) (base : K → List Bool) : Prop where
  query : base (slots (.inl (.inl 1))) = []
  scan : base (slots (.inl (.inl 2))) = []
  gatherScratch : base (slots (.inl (.inl 3))) = []
  fields : ∀ i, base (slots (.inl (.inr (.inr i)))) = []
  accA : base (slots (.inr 1)) = []
  accB : base (slots (.inr 2)) = []
  counter : base (slots (.inr 3)) = []
  hornerScratch : base (slots (.inr 4)) = []
  output : base (slots (.inr 5)) = []

def gathered (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) : K → List Bool :=
  MachineProductGather.finalTapes values coefficient width (gatherSlots slots)
    indices offsets fields base

def evaluated (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (value : Nat) : K → List Bool :=
  MachineHorner.resultTapes (hornerSlots slots)
    (gathered slots values coefficient indices offsets fields base) value

def emitted (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (value : Nat) : K → List Bool :=
  tapesAt (slots (.inr 5)) (slots (.inr 6))
    (evaluated slots values coefficient indices offsets fields base value) []
    ((encodeWord value).reverse ++ base (slots (.inr 6)))

def finalTapes (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (value : Nat) : K → List Bool :=
  MachineDrainMany.finalTapes (clearTapes slots)
    (emitted slots values coefficient indices offsets fields base value)

def steps (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool)
    (radix : Nat) (digits : Nat → Nat) : Nat :=
  MachineProductGather.steps values coefficient width indices offsets +
    MachineHorner.steps radix digits width + (MachineHorner.value radix digits width + 2) +
    MachineDrainMany.steps (clearTapes slots)
      (emitted slots values coefficient indices offsets fields base
        (MachineHorner.value radix digits width))

theorem gathered_extra (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (i : Fin 7) :
    gathered slots values coefficient indices offsets fields base (slots (.inr i)) =
      base (slots (.inr i)) := by
  apply MachineProductGather.finalTapes_other
  · apply slots.injective.ne; simp
  · apply slots.injective.ne; simp
  · intro j; apply slots.injective.ne; simp

/-- Actual execution of the complete gather/Horner/emit/cleanup phase. The
field equality connects only mathematical tape contents; all transition work
is proved from the concrete instructions. -/
theorem fieldTrace (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (labels : Label slots → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = instruction slots coefficient offsets labels exit l)
    (base : K → List Bool) (suffixes : Fin width → List Bool) (ready : Ready slots base)
    (tableWord : base (slots (.inl (.inl 0))) = encodeWords values)
    (sourceWords : ∀ i, base (slots (.inl (.inr (.inl i)))) =
      encodeWord (indices i) ++ suffixes i)
    (radix : Nat) (digits : Nat → Nat)
    (radixWord : base (slots (.inr 0)) = encodeWord radix)
    (digitWords : ∀ i : Fin width, digits i.val = fields i.rev)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps slots values coefficient indices offsets fields base radix digits]
      (some ⟨some (labels (entry slots)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), finalTapes slots values coefficient indices offsets fields
        base (MachineHorner.value radix digits width)⟩ := by
  let middle := gathered slots values coefficient indices offsets fields base
  have gather := MachineProductGather.gatherTrace values coefficient width (gatherSlots slots)
    (gatherSlots slots).injective indices offsets fields selected (fun x => labels (.inl x))
    (some (labels (.inr (.inl .start)))) program (fun x => atLabels (.inl x))
    base suffixes tableWord ready.gatherScratch sourceWords (ambient, ()) register
  have preserved (i : Fin 7) : middle (slots (.inr i)) = base (slots (.inr i)) :=
    gathered_extra slots values coefficient indices offsets fields base i
  have middleRadix : middle (hornerSlots slots (.inl 0)) = encodeWord radix := by
    rw [show hornerSlots slots (.inl 0) = slots (.inr 0) from rfl, preserved]
    exact radixWord
  have middleDigits (i : Fin width) :
      middle (hornerSlots slots (.inr i)) = encodeWord (digits i.val) := by
    rw [show hornerSlots slots (.inr i) =
      gatherSlots slots (.inr (.inr i.rev)) from rfl]
    dsimp only [middle, gathered]
    rw [MachineProductGather.finalTapes_field values coefficient width (gatherSlots slots)
      (gatherSlots slots).injective indices offsets fields base i.rev]
    rw [show base (gatherSlots slots (.inr (.inr i.rev))) = [] from ready.fields i.rev,
      List.append_nil, digitWords i]
  have clean : MachineHorner.Clean (hornerSlots slots) middle := by
    constructor
    · change middle (slots (.inr 1)) = []; rw [preserved]; exact ready.accA
    · change middle (slots (.inr 2)) = []; rw [preserved]; exact ready.accB
    · change middle (slots (.inr 3)) = []; rw [preserved]; exact ready.counter
    · change middle (slots (.inr 4)) = []; rw [preserved]; exact ready.hornerScratch
  have horner := MachineHorner.hornerTrace (hornerSlots slots)
    (fun x => labels (.inr (.inl x))) (some (labels (.inr (.inr (.inl ())))))
    program (fun x => atLabels (.inr (.inl x))) middle radix digits middleRadix
    middleDigits clean ambient none
  let value := MachineHorner.value radix digits width
  let after := evaluated slots values coefficient indices offsets fields base value
  have outputWord : after (slots (.inr 5)) = encodeWord value := by
    change MachineHorner.resultTapes (hornerSlots slots) middle value
      (hornerSlots slots (.inl 3)) = _
    rw [MachineHorner.resultTapes_output]
    rw [show hornerSlots slots (.inl 3) = slots (.inr 5) from rfl,
      preserved, ready.output, List.append_nil]
  have accWord : after (slots (.inr 6)) = base (slots (.inr 6)) := by
    change MachineHorner.resultTapes (hornerSlots slots) middle value (slots (.inr 6)) = _
    rw [MachineHorner.resultTapes_other _ _ _ _ (slots.injective.ne (by simp [hornerRole])), preserved]
  have emit := transferAt_fromTapes (Γ := fun _ : K => Bool)
    (slots (.inr 5)) (slots (.inr 6)) (slots.injective.ne (by simp)) id false
    (labels (.inr (.inr (.inl ()))))
    (MachineDrainMany.entry (clearTapes slots) (fun x => labels (.inr (.inr (.inr x)))) exit)
    program (atLabels (.inr (.inr (.inl ())))) after (ambient, ()) none
  rw [outputWord, accWord, List.map_id] at emit
  simp only [encodeWord_length] at emit
  have drain := MachineDrainMany.trace (clearTapes slots)
    (fun x => labels (.inr (.inr (.inr x)))) exit program
    (fun x => atLabels (.inr (.inr (.inr x))))
    (emitted slots values coefficient indices offsets fields base value) (ambient, ()) none
  rw [MachineDrainMany.finalRegister_none] at drain
  have emit' : (advance (TM2.step program))^[value + 2]
      (some ⟨some (labels (.inr (.inr (.inl ())))), ((ambient, ()), none), after⟩) =
      some ⟨MachineDrainMany.entry (clearTapes slots) (fun x => labels (.inr (.inr (.inr x)))) exit,
        ((ambient, ()), none), emitted slots values coefficient indices offsets fields base value⟩ := emit
  have compose {a b : Nat} {x y z : Option (TM2.Cfg (fun _ : K => Bool) Λ (MachineHorner.State σ))}
      (first : (advance (TM2.step program))^[a] x = y)
      (second : (advance (TM2.step program))^[b] y = z) :
      (advance (TM2.step program))^[a + b] x = z := by
    rw [Nat.add_comm, Function.iterate_add_apply, first, second]
  have gh := compose gather horner
  have ghe := compose gh emit'
  have whole := compose ghe drain
  simpa only [steps, value, entry, finalTapes] using whole

end

/-! The product-field machine restores every work tape and appends precisely
one field to the reversed output. This boundary is strong enough to compose
all fields and every odometer visit without retaining an unbounded history. -/

open UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction.MachineTransfer

variable {K : Type} [DecidableEq K] {width : Nat}

omit [DecidableEq K] in
@[simp] theorem mem_clearTapes (slots : Layout width ↪ K) (k : K) :
    k ∈ clearTapes slots ↔ k = slots (.inl (.inl 1)) ∨
      k = slots (.inl (.inl 2)) ∨ ∃ i, k = slots (.inl (.inr (.inr i))) := by
  simp [clearTapes, List.mem_ofFn, eq_comm]

omit [DecidableEq K] in
theorem extra_not_mem_clearTapes (slots : Layout width ↪ K) (i : Fin 7) :
    slots (.inr i) ∉ clearTapes slots := by
  simp only [mem_clearTapes]
  rintro (h | h | ⟨j, h⟩)
  · exact slots.injective.ne (by simp) h
  · exact slots.injective.ne (by simp) h
  · exact slots.injective.ne (by simp) h

omit [DecidableEq K] in
theorem Ready.empty_clearTapes (slots : Layout width ↪ K) (base : K → List Bool)
    (ready : Ready slots base) (k : K) (member : k ∈ clearTapes slots) : base k = [] := by
  rcases (mem_clearTapes slots k).mp member with rfl | rfl | ⟨i, rfl⟩
  · exact ready.query
  · exact ready.scan
  · exact ready.fields i

theorem gathered_frame (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool)
    (k : K) (outside : k ∉ clearTapes slots) :
    gathered slots values coefficient indices offsets fields base k = base k := by
  rw [mem_clearTapes] at outside
  apply MachineProductGather.finalTapes_other
  · exact fun h => outside (Or.inl h)
  · exact fun h => outside (Or.inr (Or.inl h))
  · intro i h; exact outside (Or.inr (Or.inr ⟨i, h⟩))

/-- The complete row-field phase changes just the output accumulator. -/
theorem finalTapes_eq (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool)
    (ready : Ready slots base) (value : Nat) :
    finalTapes slots values coefficient indices offsets fields base value =
      Function.update base (slots (.inr 6))
        ((encodeWord value).reverse ++ base (slots (.inr 6))) := by
  funext k
  rw [finalTapes, MachineDrainMany.finalTapes_apply]
  by_cases member : k ∈ clearTapes slots
  · have notOutput : k ≠ slots (.inr 6) := by
      intro h; subst k; exact extra_not_mem_clearTapes slots 6 member
    simp [member, Function.update_of_ne notOutput, ready.empty_clearTapes slots base k member]
  · rw [ite_eq_right member]
    by_cases output : k = slots (.inr 6)
    · subst k
      simp [emitted, tapesAt]
    · by_cases field : k = slots (.inr 5)
      · subst k
        simp [emitted, tapesAt, output, ready.output]
      · have frame := gathered_frame slots values coefficient indices offsets fields base k member
        simp only [emitted, tapesAt, Function.update_of_ne output, Function.update_of_ne field,
          evaluated, MachineHorner.resultTapes]
        change Function.update (gathered slots values coefficient indices offsets fields base)
          (slots (.inr 5)) _ k = base k
        rw [Function.update_of_ne field, frame]

/-- The output update preserves all work-tape entry conditions. -/
theorem Ready.output_update (slots : Layout width ↪ K) (base : K → List Bool)
    (ready : Ready slots base) (word : List Bool) :
    Ready slots (Function.update base (slots (.inr 6)) word) := by
  have other (a : Layout width) (h : a ≠ .inr 6) :
      Function.update base (slots (.inr 6)) word (slots a) = base (slots a) :=
    Function.update_of_ne (slots.injective.ne h) _ _
  constructor
  · rw [other _ (by simp)]; exact ready.query
  · rw [other _ (by simp)]; exact ready.scan
  · rw [other _ (by simp)]; exact ready.gatherScratch
  · intro i; rw [other _ (by simp)]; exact ready.fields i
  · rw [other _ (by simp)]; exact ready.accA
  · rw [other _ (by simp)]; exact ready.accB
  · rw [other _ (by simp)]; exact ready.counter
  · rw [other _ (by simp)]; exact ready.hornerScratch
  · rw [other _ (by simp)]; exact ready.output

theorem final_ready (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool)
    (ready : Ready slots base) (value : Nat) :
    Ready slots (finalTapes slots values coefficient indices offsets fields base value) := by
  rw [finalTapes_eq slots values coefficient indices offsets fields base ready value]
  exact ready.output_update slots base _

/-- Cleanup only touches gather work; it never scans the global accumulator. -/
theorem emitted_clear_length (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (base : K → List Bool) (ready : Ready slots base) (value : Nat)
    (k : K) (member : k ∈ clearTapes slots) :
    (emitted slots values coefficient indices offsets fields base value k).length ≤
      width * ((encodeWords values).length + 1) := by
  have notExtra (i : Fin 7) : k ≠ slots (.inr i) := by
    intro h; subst k; exact extra_not_mem_clearTapes slots i member
  have h := MachineProductGather.finalTapes_length values coefficient width (gatherSlots slots)
    (gatherSlots slots).injective indices offsets fields selected base k
  rw [ready.empty_clearTapes slots base k member, List.length_nil, Nat.zero_add] at h
  simpa only [emitted, tapesAt, Function.update_of_ne (notExtra 6),
    Function.update_of_ne (notExtra 5), evaluated, MachineHorner.resultTapes,
    show hornerSlots slots (.inl 3) = slots (.inr 5) from rfl,
    Function.update_of_ne (notExtra 5), gathered] using h

omit [DecidableEq K] in
theorem clearTapes_length (slots : Layout width ↪ K) : (clearTapes slots).length = width + 2 := by
  simp [clearTapes]

theorem cleanup_steps_le (slots : Layout width ↪ K) (values : List Nat) (coefficient : Nat)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (base : K → List Bool) (ready : Ready slots base) (value : Nat) :
    MachineDrainMany.steps (clearTapes slots)
      (emitted slots values coefficient indices offsets fields base value) ≤
      (width + 2) * (width * ((encodeWords values).length + 1) + 1) := by
  have sumBound : MachineDrainMany.lengthSum (clearTapes slots)
      (emitted slots values coefficient indices offsets fields base value) ≤
      (clearTapes slots).length * (width * ((encodeWords values).length + 1)) := by
    have hs := List.sum_le_length_nsmul
      ((clearTapes slots).map (fun k => (emitted slots values coefficient indices offsets fields base value k).length))
      (width * ((encodeWords values).length + 1)) (by
        intro n hn
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hn
        exact emitted_clear_length slots values coefficient indices offsets fields selected base ready value k hk)
    simpa [MachineDrainMany.lengthSum, nsmul_eq_mul] using hs
  have h := MachineDrainMany.steps_le (clearTapes slots)
    (emitted slots values coefficient indices offsets fields base value)
  rw [clearTapes_length] at sumBound h
  rw [Nat.mul_add, Nat.mul_one]
  omega

end UniqueGamesTheorem.Explicit.MachineProductField

/-! Actual power-header emission by fixed-width Horner evaluation of
`[1,0,...,0]`, followed by physical transfer to the reverse accumulator. -/

namespace UniqueGamesTheorem.Explicit.MachineProductPower

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K] {exponent : Nat}

def digits (i : Nat) : Nat := if i = 0 then 1 else 0

theorem value_eq (radix exponent : Nat) : MachineHorner.value radix digits (exponent + 1) = radix ^ exponent := by
  induction exponent with
  | zero => simp [MachineHorner.value, digits]
  | succ exponent ih =>
    rw [MachineHorner.value, ih]
    simp [digits, pow_succ, Nat.mul_comm]

abbrev Label (exponent : Nat) := MachineHorner.Label (exponent + 1) ⊕ Unit

def instruction (slots : MachineHorner.Layout (exponent + 1) ↪ K) (output : K)
    (labels : Label exponent → Λ) (exit : Option Λ) :
    Label exponent → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ)
  | .inl l => MachineHorner.statement slots (fun x => labels (.inl x))
      (some (labels (.inr ()))) l
  | .inr _ => loopAt (slots (.inl 3)) output id false (labels (.inr ())) exit

def steps (radix exponent : Nat) : Nat :=
  MachineHorner.steps radix digits (exponent + 1) + radix ^ exponent + 2

/-- Header powers are computed from a unary input radix, not stored in an
unbounded register. Only the output accumulator changes at the boundary. -/
theorem powerTrace (slots : MachineHorner.Layout (exponent + 1) ↪ K) (output : K)
    (outside : ∀ i, output ≠ slots i) (labels : Label exponent → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = instruction slots output labels exit l)
    (base : K → List Bool) (radix : Nat)
    (radixWord : base (slots (.inl 0)) = encodeWord radix)
    (digitWords : ∀ i : Fin (exponent + 1), base (slots (.inr i)) = encodeWord (digits i.val))
    (clean : MachineHorner.Clean slots base) (fieldEmpty : base (slots (.inl 3)) = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps radix exponent]
      (some ⟨some (labels (.inl .start)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        Function.update base output ((encodeWord (radix ^ exponent)).reverse ++ base output)⟩ := by
  have horner := MachineHorner.hornerTrace slots (fun x => labels (.inl x))
    (some (labels (.inr ()))) program (fun x => atLabels (.inl x)) base radix digits
    radixWord digitWords clean ambient register
  rw [value_eq] at horner
  let after := MachineHorner.resultTapes slots base (radix ^ exponent)
  have hout : after (slots (.inl 3)) = encodeWord (radix ^ exponent) := by
    dsimp only [after]
    rw [MachineHorner.resultTapes_output, fieldEmpty, List.append_nil]
  have hacc : after output = base output :=
    MachineHorner.resultTapes_other slots base (radix ^ exponent) output (outside _)
  have emit := transferAt_fromTapes (Γ := fun _ : K => Bool)
    (slots (.inl 3)) output (Ne.symm (outside _)) id false (labels (.inr ())) exit
    program (atLabels (.inr ())) after (ambient, ()) none
  rw [hout, hacc, List.map_id, encodeWord_length] at emit
  have tapes_eq : tapesAt (slots (.inl 3)) output after []
      ((encodeWord (radix ^ exponent)).reverse ++ base output) =
      Function.update base output ((encodeWord (radix ^ exponent)).reverse ++ base output) := by
    funext k
    by_cases h1 : k = output
    · subst k; simp [tapesAt]
    · by_cases h2 : k = slots (.inl 3)
      · subst k; simp [tapesAt, h1, fieldEmpty]
      · simp [tapesAt, after, MachineHorner.resultTapes, h1, h2]
  rw [tapes_eq] at emit
  rw [show steps radix exponent = (radix ^ exponent + 2) +
    MachineHorner.steps radix digits (exponent + 1) by unfold steps; omega,
    Function.iterate_add_apply, horner]
  exact emit

noncomputable def timePolynomial (exponent : Nat) : Polynomial Nat :=
  MachineHorner.timePolynomial (exponent + 1) +
    (Polynomial.X + 1) ^ exponent + 2

theorem steps_le (radix exponent magnitude : Nat) (bounded : radix ≤ magnitude)
    (positive : 1 ≤ magnitude) : steps radix exponent ≤ (timePolynomial exponent).eval magnitude := by
  have digitBound : ∀ i, i < exponent + 1 → digits i ≤ magnitude := by
    intro i hi; unfold digits; split <;> omega
  have h := MachineHorner.steps_le_timePolynomial radix digits (exponent + 1) magnitude bounded digitBound
  have hp : radix ^ exponent ≤ (magnitude + 1) ^ exponent :=
    Nat.pow_le_pow_left (by omega) _
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_ofNat]
  unfold steps
  omega

end UniqueGamesTheorem.Explicit.MachineProductPower

/-! A finite row-field schedule. Endpoint fields use the input vertex radix;
permutation fields use the fixed alphabet radix. The complete list of columns
is in finite control, while all row indices, table entries and radix magnitudes
remain data on tapes. -/

namespace UniqueGamesTheorem.Explicit.MachineProductRow

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {width : Nat}

abbrev Layout (width : Nat) := MachineProductField.Layout width ⊕ Unit
abbrev Command (width : Nat) := Bool × (Fin width → Nat)

/-- Only the radix tape is switched between endpoint and alphabet fields. -/
def fieldRole (useAlphabet : Bool) : MachineProductField.Layout width → Layout width
  | .inr 0 => if useAlphabet then .inr () else .inl (.inr 0)
  | tape => .inl tape

theorem fieldRole_injective (useAlphabet : Bool) :
    Function.Injective (fieldRole (width := width) useAlphabet) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => simpa [fieldRole] using h
    | inr b => fin_cases b <;> cases useAlphabet <;> simp [fieldRole] at h
  | inr a =>
    cases b with
    | inl b => fin_cases a <;> cases useAlphabet <;> simp [fieldRole] at h
    | inr b => fin_cases a <;> fin_cases b <;> cases useAlphabet <;> simp_all [fieldRole]

def fieldSlots (slots : Layout width ↪ K) (useAlphabet : Bool) :
    MachineProductField.Layout width ↪ K :=
  Function.Embedding.trans ⟨fieldRole useAlphabet, fieldRole_injective useAlphabet⟩ slots

abbrev LocalLabel (slots : Layout width ↪ K) (command : Command width) :=
  MachineProductField.Label (fieldSlots slots command.1)

abbrev Label (slots : Layout width ↪ K) (commands : List (Command width)) :=
  MachineFiniteSequence.Label (LocalLabel slots) commands

def localMain (slots : Layout width ↪ K) (command : Command width) : LocalLabel slots command :=
  MachineProductField.entry (fieldSlots slots command.1)

def localInstruction (slots : Layout width ↪ K) (coefficient : Nat) (command : Command width)
    (labels : LocalLabel slots command → Λ) (exit : Option Λ) :
    LocalLabel slots command → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ) :=
  MachineProductField.instruction (fieldSlots slots command.1) coefficient command.2 labels exit

def entry (slots : Layout width ↪ K) (commands : List (Command width))
    (labels : Label slots commands → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (LocalLabel slots) (localMain slots) commands labels exit

def instruction (slots : Layout width ↪ K) (coefficient : Nat) (commands : List (Command width))
    (labels : Label slots commands → Λ) (exit : Option Λ) :
    Label slots commands → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ) :=
  MachineFiniteSequence.instruction (LocalLabel slots) (localMain slots)
    (localInstruction slots coefficient) commands labels exit

def outputTape (slots : Layout width ↪ K) : K := slots (.inl (.inr 6))

def appendField (slots : Layout width ↪ K) (value : Nat) (base : K → List Bool) : K → List Bool :=
  Function.update base (outputTape slots) ((encodeWord value).reverse ++ base (outputTape slots))

/-- Exact literal output of the command list in field order. -/
def rowBits (values : Command width → Nat) (commands : List (Command width)) : List Bool :=
  commands.flatMap (fun command => encodeWord (values command))

def result (slots : Layout width ↪ K) (values : Command width → Nat)
    (command : Command width) (base : K → List Bool) : K → List Bool :=
  appendField slots (values command) base

theorem resultOf_eq (slots : Layout width ↪ K) (values : Command width → Nat)
    (commands : List (Command width)) (base : K → List Bool) :
    MachineFiniteSequence.resultOf (result slots values) commands base =
      Function.update base (outputTape slots)
        ((rowBits values commands).reverse ++ base (outputTape slots)) := by
  induction commands generalizing base with
  | nil => simp [MachineFiniteSequence.resultOf, rowBits]
  | cons command commands ih =>
    rw [MachineFiniteSequence.resultOf, ih]
    simp [result, appendField, rowBits, List.reverse_append, List.append_assoc]

/-- The input-dependent data needed for one whole row, held invariant by
all physical field executions. -/
structure Ready (slots : Layout width ↪ K) (table : List Nat) (indices : Fin width → Nat)
    (radices : Bool → Nat) (base : K → List Bool) : Prop where
  work : ∀ useAlphabet, MachineProductField.Ready (fieldSlots slots useAlphabet) base
  tableWord : base (slots (.inl (.inl (.inl 0)))) = encodeWords table
  sourceWords : ∀ i, base (slots (.inl (.inl (.inr (.inl i))))) = encodeWord (indices i)
  radixWords : ∀ b, base (fieldSlots slots b (.inr 0)) = encodeWord (radices b)

theorem Ready.appendField (slots : Layout width ↪ K) (table : List Nat)
    (indices : Fin width → Nat) (radices : Bool → Nat) (base : K → List Bool)
    (ready : Ready slots table indices radices base) (value : Nat) :
    Ready slots table indices radices (appendField slots value base) := by
  constructor
  · intro b
    have h := MachineProductField.Ready.output_update (fieldSlots slots b) base (ready.work b)
      ((encodeWord value).reverse ++ base (outputTape slots))
    exact h
  · rw [MachineProductRow.appendField, outputTape, Function.update_of_ne (slots.injective.ne (by simp))]
    exact ready.tableWord
  · intro i
    rw [MachineProductRow.appendField, outputTape, Function.update_of_ne (slots.injective.ne (by simp))]
    exact ready.sourceWords i
  · intro b
    rw [MachineProductRow.appendField, Function.update_of_ne]
    · exact ready.radixWords b
    · apply slots.injective.ne
      cases b <;> simp [fieldRole]

/-- Complete row trace from the concrete field implementation. The only
premises concerning values are literal indexed-table identities and the
Horner interpretation of those values. -/
theorem rowTrace (slots : Layout width ↪ K) (table : List Nat) (coefficient : Nat)
    (indices : Fin width → Nat) (radices : Bool → Nat) (commands : List (Command width))
    (fields : Command width → Fin width → Nat) (digits : Command width → Nat → Nat)
    (selected : ∀ command ∈ commands, ∀ i,
      table[coefficient * indices i + command.2 i]? = some (fields command i))
    (reversed : ∀ command ∈ commands, ∀ i : Fin width,
      digits command i.val = fields command i.rev)
    (labels : Label slots commands → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = instruction slots coefficient commands labels exit l)
    (base : K → List Bool) (ready : Ready slots table indices radices base) (ambient : σ) :
    let values := fun c : Command width => MachineHorner.value (radices c.1) (digits c) width
    let cost := fun (c : Command width) (tapes : K → List Bool) =>
      MachineProductField.steps (fieldSlots slots c.1) table coefficient indices c.2 (fields c)
        tapes (radices c.1) (digits c)
    (advance (TM2.step program))^[MachineFiniteSequence.steps (result slots values) cost commands base]
      (some ⟨entry slots commands labels exit, ((ambient, ()), none), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        Function.update base (outputTape slots)
          ((rowBits values commands).reverse ++ base (outputTape slots))⟩ := by
  dsimp only
  let values := fun c : Command width => MachineHorner.value (radices c.1) (digits c) width
  let cost := fun (c : Command width) (tapes : K → List Bool) =>
    MachineProductField.steps (fieldSlots slots c.1) table coefficient indices c.2 (fields c)
      tapes (radices c.1) (digits c)
  have run := MachineFiniteSequence.trace (LocalLabel slots) (localMain slots)
    (localInstruction slots coefficient) (result slots values) cost program
    (Ready slots table indices radices) (fun _ => ((ambient, ()), none)) id commands
    (by intro c hc tapes ht; exact ht.appendField slots table indices radices tapes (values c))
    (by
      intro c hc fieldLabels fieldExit atField tapes ht
      have h := MachineProductField.fieldTrace (fieldSlots slots c.1) table coefficient
        indices c.2 (fields c) (selected c hc) fieldLabels fieldExit program atField tapes
        (fun _ => []) (ht.work c.1) ht.tableWord
        (fun i => by simpa [fieldSlots, fieldRole] using ht.sourceWords i) (radices c.1) (digits c)
        (ht.radixWords c.1) (reversed c hc) ambient none
      rw [MachineProductField.finalTapes_eq _ _ _ _ _ _ _ (ht.work c.1)] at h
      exact h)
    labels exit atLabels base ready
  rw [resultOf_eq] at run
  exact run

end UniqueGamesTheorem.Explicit.MachineProductRow

/-! Polynomial bounds for actual field and row traces. The output accumulator
is excluded from local cleanup and is never rescanned by row emission. -/

namespace UniqueGamesTheorem.Explicit.MachineProductBounds

open UniqueGamesTheorem.Foundations.Complexity

variable {K : Type} [DecidableEq K] {width : Nat}

noncomputable def fieldPolynomial (width : Nat) : Polynomial Nat :=
  Polynomial.C width * (7 * Polynomial.X + 6) + 1 +
    MachineHorner.timePolynomial width + (Polynomial.X + 1) ^ width + 2 +
    Polynomial.C (width + 2) * (Polynomial.C width * (Polynomial.X + 1) + 1)

@[simp] theorem fieldPolynomial_eval (width magnitude : Nat) :
    (fieldPolynomial width).eval magnitude =
      width * (7 * magnitude + 6) + 1 + (MachineHorner.timePolynomial width).eval magnitude +
        (magnitude + 1) ^ width + 2 + (width + 2) * (width * (magnitude + 1) + 1) := by
  simp [fieldPolynomial]

theorem field_steps_le (slots : MachineProductField.Layout width ↪ K) (table : List Nat)
    (coefficient : Nat) (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, table[coefficient * indices i + offsets i]? = some (fields i))
    (base : K → List Bool) (ready : MachineProductField.Ready slots base)
    (radix : Nat) (digits : Nat → Nat) (magnitude : Nat)
    (tableBound : (encodeWords table).length ≤ magnitude)
    (indexBound : ∀ i, indices i ≤ magnitude) (radixBound : radix ≤ magnitude)
    (digitBound : ∀ i, i < width → digits i ≤ magnitude) :
    MachineProductField.steps slots table coefficient indices offsets fields base radix digits ≤
      (fieldPolynomial width).eval magnitude := by
  have gather := MachineProductGather.steps_le table coefficient width magnitude indices offsets fields selected indexBound
  have horner := MachineHorner.steps_le_timePolynomial radix digits width magnitude radixBound digitBound
  have value := MachineHorner.value_le radix digits width magnitude radixBound digitBound width (Nat.le_refl _)
  have cleanup := MachineProductField.cleanup_steps_le slots table coefficient indices offsets fields selected
    base ready (MachineHorner.value radix digits width)
  have gatherBound : width * (2 * magnitude + 5 * (encodeWords table).length + 6) + 1 ≤
      width * (7 * magnitude + 6) + 1 := by gcongr; omega
  have cleanupBound : (width + 2) * (width * ((encodeWords table).length + 1) + 1) ≤
      (width + 2) * (width * (magnitude + 1) + 1) := by gcongr
  rw [fieldPolynomial_eval]
  unfold MachineProductField.steps
  omega

def rowCost (slots : MachineProductRow.Layout width ↪ K) (table : List Nat) (coefficient : Nat)
    (indices : Fin width → Nat) (radices : Bool → Nat)
    (fields : MachineProductRow.Command width → Fin width → Nat)
    (digits : MachineProductRow.Command width → Nat → Nat)
    (c : MachineProductRow.Command width) (base : K → List Bool) : Nat :=
  MachineProductField.steps (MachineProductRow.fieldSlots slots c.1) table coefficient indices c.2
    (fields c) base (radices c.1) (digits c)

theorem row_steps_le (slots : MachineProductRow.Layout width ↪ K) (table : List Nat)
    (coefficient : Nat) (indices : Fin width → Nat) (radices : Bool → Nat)
    (commands : List (MachineProductRow.Command width))
    (fields : MachineProductRow.Command width → Fin width → Nat)
    (digits : MachineProductRow.Command width → Nat → Nat)
    (selected : ∀ c ∈ commands, ∀ i, table[coefficient * indices i + c.2 i]? = some (fields c i))
    (base : K → List Bool) (ready : MachineProductRow.Ready slots table indices radices base)
    (magnitude : Nat) (tableBound : (encodeWords table).length ≤ magnitude)
    (indexBound : ∀ i, indices i ≤ magnitude) (radixBound : ∀ b, radices b ≤ magnitude)
    (digitBound : ∀ c ∈ commands, ∀ i, i < width → digits c i ≤ magnitude) :
    MachineFiniteSequence.steps
      (MachineProductRow.result slots (fun c => MachineHorner.value (radices c.1) (digits c) width))
      (rowCost slots table coefficient indices radices fields digits) commands base ≤
      commands.length * (fieldPolynomial width).eval magnitude := by
  induction commands generalizing base with
  | nil => simp [MachineFiniteSequence.steps]
  | cons command commands ih =>
    have first := field_steps_le (MachineProductRow.fieldSlots slots command.1) table coefficient
      indices command.2 (fields command) (selected command (by simp)) base (ready.work command.1)
      (radices command.1) (digits command) magnitude tableBound indexBound (radixBound command.1)
      (digitBound command (by simp))
    have nextReady := MachineProductRow.Ready.appendField slots table indices radices base ready
      (MachineHorner.value (radices command.1) (digits command) width)
    have rest := ih (fun c hc => selected c (by simp [hc]))
      (MachineProductRow.result slots (fun c => MachineHorner.value (radices c.1) (digits c) width)
        command base) nextReady (fun c hc => digitBound c (by simp [hc]))
    rw [MachineFiniteSequence.steps, List.length_cons, Nat.add_mul, Nat.one_mul]
    simpa only [Nat.add_comm, rowCost] using Nat.add_le_add first rest

end UniqueGamesTheorem.Explicit.MachineProductBounds

/-! Fixed natural polynomials are represented by literal Horner coefficients.
The coefficient representation is independent of the machine input. The actual
machine wrapper is built from the shared physical unary Horner subroutine. -/

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.PolynomialMachine

noncomputable def coefficientPolynomial : List Nat → Polynomial Nat
  | [] => 0
  | a :: rest => coefficientPolynomial rest * Polynomial.X + Polynomial.C a

theorem coefficientPolynomial_eval (cs : List Nat) (n : Nat) :
    (coefficientPolynomial cs).eval n = cs.foldr (fun digit value => value * n + digit) 0 := by
  induction cs with
  | nil => simp [coefficientPolynomial]
  | cons a rest ih => simp [coefficientPolynomial, ih]

theorem coefficientPolynomial_eval_reverse (cs : List Nat) (n : Nat) :
    (coefficientPolynomial cs).eval n =
      cs.reverse.foldl (fun value digit => value * n + digit) 0 := by
  rw [coefficientPolynomial_eval, List.foldr_eq_foldl_reverse]

/-- An actual finite coefficient list for every fixed natural polynomial.
No evaluation of an input is included in this static representation choice. -/
noncomputable def coefficients (p : Polynomial Nat) :
    {cs : List Nat // coefficientPolynomial cs = p} := by
  refine Polynomial.recOnHorner p ?_ ?_ ?_
  · exact ⟨[], rfl⟩
  · intro q a hq ha ih
    rcases ih with ⟨cs, hcs⟩
    cases cs with
    | nil =>
      refine ⟨[a], ?_⟩
      rw [← hcs]
      simp [coefficientPolynomial]
    | cons b rest =>
      refine ⟨(b + a) :: rest, ?_⟩
      rw [← hcs]
      simp only [coefficientPolynomial, Polynomial.C_add, add_assoc]
  · intro q hq ih
    rcases ih with ⟨cs, hcs⟩
    refine ⟨0 :: cs, ?_⟩
    simp only [coefficientPolynomial, Polynomial.C_0, add_zero, hcs]

noncomputable def highCoefficients (p : Polynomial Nat) : List Nat :=
  (coefficients p).val.reverse

noncomputable def width (p : Polynomial Nat) : Nat := (highCoefficients p).length

noncomputable def digit (p : Polynomial Nat) (i : Nat) : Nat :=
  if hi : i < width p then (highCoefficients p)[i] else 0

noncomputable def digitBound (p : Polynomial Nat) : Nat := (highCoefficients p).sum

theorem le_sum_of_mem {n : Nat} {xs : List Nat} (h : n ∈ xs) : n ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons a rest ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · simp
    · have hrest := ih hm
      simp only [List.sum_cons]
      omega

theorem digit_le_bound (p : Polynomial Nat) (i : Nat) : digit p i ≤ digitBound p := by
  unfold digit
  split
  · exact le_sum_of_mem (List.getElem_mem _)
  · exact Nat.zero_le _

theorem highCoefficients_foldl (p : Polynomial Nat) (n : Nat) :
    (highCoefficients p).foldl (fun value digit => value * n + digit) 0 = p.eval n := by
  calc
    _ = (coefficientPolynomial (coefficients p).val).eval n :=
      (coefficientPolynomial_eval_reverse (coefficients p).val n).symm
    _ = p.eval n := congrArg (fun q : Polynomial Nat => q.eval n) (coefficients p).property

theorem range_map_digit (p : Polynomial Nat) :
    (List.range (width p)).map (digit p) = highCoefficients p := by
  apply List.ext_getElem
  · simp [width]
  · intro i hi hj
    simp [digit, width, hj]

section LiteralFields

open Turing
open UniqueGamesTheorem.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

def prependFields (word : K → List Bool) : List K →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | [], continuation => continuation
  | k :: rest, continuation =>
      pushWord k (word k).reverse (prependFields word rest continuation)

def prependFieldsTapes (word : K → List Bool) : List K →
    (K → List Bool) → K → List Bool
  | [], tapes => tapes
  | k :: rest, tapes =>
      prependFieldsTapes word rest (Function.update tapes k (word k ++ tapes k))

theorem stepAux_prependFields (word : K → List Bool) (indices : List K)
    (continuation : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (prependFields word indices continuation) state tapes =
      TM2.stepAux continuation state (prependFieldsTapes word indices tapes) := by
  induction indices generalizing tapes with
  | nil => rfl
  | cons k rest ih =>
    simp only [prependFields, stepAux_pushWord, List.reverse_reverse, prependFieldsTapes]
    exact ih _

theorem prependFieldsTapes_apply (word : K → List Bool) (indices : List K)
    (hn : indices.Nodup) (tapes : K → List Bool) (k : K) :
    prependFieldsTapes word indices tapes k =
      if k ∈ indices then word k ++ tapes k else tapes k := by
  induction indices generalizing tapes with
  | nil => simp [prependFieldsTapes]
  | cons j rest ih =>
    have hnodup := List.nodup_cons.mp hn
    rw [prependFieldsTapes, ih hnodup.2]
    by_cases hkj : k = j
    · subst k
      simp [hnodup.1]
    · simp [hkj]

def popN (k : K) : Nat → TM2.Stmt (fun _ : K => Bool) Λ σ →
    TM2.Stmt (fun _ : K => Bool) Λ σ
  | 0, continuation => continuation
  | n + 1, continuation => .pop k (fun state _ => state) (popN k n continuation)

theorem stepAux_popN (k : K) (n : Nat)
    (continuation : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (popN k n continuation) state tapes =
      TM2.stepAux continuation state (Function.update tapes k ((tapes k).drop n)) := by
  induction n generalizing tapes with
  | zero => simp [popN]
  | succ n ih =>
    simp only [popN, TM2.stepAux]
    rw [ih]
    simp only [Function.update_self, Function.update_idem, List.drop_tail]

def clearFields (count : K → Nat) : List K →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | [], continuation => continuation
  | k :: rest, continuation => popN k (count k) (clearFields count rest continuation)

def clearFieldsTapes (count : K → Nat) : List K → (K → List Bool) → K → List Bool
  | [], tapes => tapes
  | k :: rest, tapes => clearFieldsTapes count rest
      (Function.update tapes k ((tapes k).drop (count k)))

theorem stepAux_clearFields (count : K → Nat) (indices : List K)
    (continuation : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (clearFields count indices continuation) state tapes =
      TM2.stepAux continuation state (clearFieldsTapes count indices tapes) := by
  induction indices generalizing tapes with
  | nil => rfl
  | cons k rest ih =>
    simp only [clearFields, stepAux_popN, clearFieldsTapes]
    exact ih _

theorem clearFieldsTapes_apply (count : K → Nat) (indices : List K)
    (hn : indices.Nodup) (tapes : K → List Bool) (k : K) :
    clearFieldsTapes count indices tapes k =
      if k ∈ indices then (tapes k).drop (count k) else tapes k := by
  induction indices generalizing tapes with
  | nil => simp [clearFieldsTapes]
  | cons j rest ih =>
    have hnodup := List.nodup_cons.mp hn
    rw [clearFieldsTapes, ih hnodup.2]
    by_cases hkj : k = j
    · subst k
      simp [hnodup.1]
    · simp [hkj]

end LiteralFields

noncomputable section

abbrev Layout (p : Polynomial Nat) := MachineHorner.Layout (width p)
abbrev Label (p : Polynomial Nat) := Unit ⊕ (MachineHorner.Label (width p) ⊕ Bool)
abbrev State := MachineHorner.State Unit

def fieldWord (p : Polynomial Nat) : Layout p → List Bool
  | .inl _ => []
  | .inr i => encodeWord (digit p i.val)

def fieldIndices (p : Polynomial Nat) : List (Layout p) :=
  (List.finRange (width p)).map Sum.inr

theorem fieldIndices_nodup (p : Polynomial Nat) : (fieldIndices p).Nodup :=
  (List.nodup_finRange _).map Sum.inr_injective

@[simp] theorem inl_not_mem_fields (p : Polynomial Nat) (i : Fin 6) :
    Sum.inl i ∉ fieldIndices p := by simp [fieldIndices]

@[simp] theorem inr_mem_fields (p : Polynomial Nat) (i : Fin (width p)) :
    Sum.inr i ∈ fieldIndices p := by simp [fieldIndices]

def initialTapes (p : Polynomial Nat) (n : Nat) (k : Layout p) : List Bool :=
  if k = .inl 0 then encodeWord n else []

def preparedTapes (p : Polynomial Nat) (n : Nat) : Layout p → List Bool :=
  prependFieldsTapes (fieldWord p) (fieldIndices p) (initialTapes p n)

@[simp] theorem preparedTapes_inl (p : Polynomial Nat) (n : Nat) (i : Fin 6) :
    preparedTapes p n (.inl i) = if i = 0 then encodeWord n else [] := by
  rw [preparedTapes, prependFieldsTapes_apply _ _ (fieldIndices_nodup p)]
  simp [initialTapes]

@[simp] theorem preparedTapes_inr (p : Polynomial Nat) (n : Nat) (i : Fin (width p)) :
    preparedTapes p n (.inr i) = encodeWord (digit p i.val) := by
  rw [preparedTapes, prependFieldsTapes_apply _ _ (fieldIndices_nodup p)]
  simp [initialTapes, fieldWord]

def slots (p : Polynomial Nat) : Layout p ↪ Layout p := Function.Embedding.refl _

theorem preparedTapes_clean (p : Polynomial Nat) (n : Nat) :
    MachineHorner.Clean (slots p) (preparedTapes p n) := by
  constructor <;> simp [slots]

def innerLabels (p : Polynomial Nat) (l : MachineHorner.Label (width p)) : Label p :=
  .inr (.inl l)

def program (p : Polynomial Nat) : Label p →
    Turing.TM2.Stmt (fun _ : Layout p => Bool) (Label p) State
  | .inl _ => prependFields (fieldWord p) (fieldIndices p)
      (.goto fun _ => innerLabels p .start)
  | .inr (.inl l) => MachineHorner.statement (slots p) (innerLabels p)
      (some (.inr (.inr false))) l
  | .inr (.inr false) => MachineLookup.discard (.inl 0)
      (.inr (.inr false)) (.inr (.inr true))
  | .inr (.inr true) => clearFields (fun k => (fieldWord p k).length) (fieldIndices p) .halt

abbrev machine (p : Polynomial Nat) : Turing.FinTM2 where
  K := Layout p
  k₀ := .inl 0
  k₁ := .inl 3
  Γ _ := Bool
  Λ := Label p
  main := .inl ()
  σ := State
  initialState := (((), ()), none)
  m := program p

def afterHornerTapes (p : Polynomial Nat) (n result : Nat) : Layout p → List Bool :=
  Function.update (preparedTapes p n) (.inl 3) (encodeWord result)

def afterInputTapes (p : Polynomial Nat) (n result : Nat) : Layout p → List Bool :=
  Function.update (afterHornerTapes p n result) (.inl 0) []

def finalTapes (p : Polynomial Nat) (result : Nat) (k : Layout p) : List Bool :=
  if k = .inl 3 then encodeWord result else []

theorem clearFields_final (p : Polynomial Nat) (n result : Nat) :
    clearFieldsTapes (fun k => (fieldWord p k).length) (fieldIndices p)
      (afterInputTapes p n result) = finalTapes p result := by
  funext k
  rw [clearFieldsTapes_apply _ _ (fieldIndices_nodup p)]
  cases k with
  | inl i =>
    fin_cases i <;> simp [afterInputTapes, afterHornerTapes, finalTapes]
  | inr i =>
    simp [afterInputTapes, afterHornerTapes, fieldWord, finalTapes]

theorem initList_eq (p : Polynomial Nat) (n : Nat) :
    Turing.initList (machine p) (encodeWord n) =
      ⟨some (.inl ()), (((), ()), none), initialTapes p n⟩ := by
  unfold Turing.initList
  congr 1

theorem haltList_eq (p : Polynomial Nat) (result : Nat) :
    Turing.haltList (machine p) (encodeWord result) =
      ⟨none, (((), ()), none), finalTapes p result⟩ := by
  unfold Turing.haltList
  congr 1

theorem initializationTrace (p : Polynomial Nat) (n : Nat) :
    (MachineComposition.advance (machine p).step)^[1]
      (some (Turing.initList (machine p) (encodeWord n))) =
      some ⟨some (innerLabels p .start), (((), ()), none), preparedTapes p n⟩ := by
  rw [initList_eq]
  change some (Turing.TM2.stepAux (program p (.inl ()))
    (((), ()), none) (initialTapes p n)) = _
  rw [program, stepAux_prependFields]
  rfl

theorem cleanupTrace (p : Polynomial Nat) (n result : Nat) :
    (MachineComposition.advance (machine p).step)^[n + 2]
      (some ⟨some (.inr (.inr false)), (((), ()), none), afterHornerTapes p n result⟩) =
      some (Turing.haltList (machine p) (encodeWord result)) := by
  have hd := MachineLookup.discardTrace (Sum.inl (0 : Fin 6))
    (Sum.inr (Sum.inr false)) (Sum.inr (Sum.inr true)) (program p) rfl
    (afterHornerTapes p n result) n [] (by simp [afterHornerTapes]) ((), ()) none
  have hc : (MachineComposition.advance (machine p).step)^[1]
      (some ⟨some (.inr (.inr true)), (((), ()), none), afterInputTapes p n result⟩) =
      some (Turing.haltList (machine p) (encodeWord result)) := by
    change some (Turing.TM2.stepAux (program p (.inr (.inr true)))
      (((), ()), none) (afterInputTapes p n result)) = _
    rw [program, stepAux_clearFields, clearFields_final, haltList_eq]
    rfl
  rw [show n + 2 = 1 + (n + 1) by omega, Function.iterate_add_apply]
  exact (congrArg ((MachineComposition.advance (Turing.TM2.step (program p)))^[1]) hd).trans hc

def prefixValuePolynomial (digits : Nat → Nat) : Nat → Polynomial Nat
  | 0 => 0
  | i + 1 => Polynomial.X * prefixValuePolynomial digits i + Polynomial.C (digits i)

def prefixCostPolynomial (digits : Nat → Nat) : Nat → Polynomial Nat
  | 0 => 0
  | i + 1 => prefixCostPolynomial digits i +
      Polynomial.C 3 * Polynomial.X * prefixValuePolynomial digits i +
      Polynomial.C 9 * prefixValuePolynomial digits i + Polynomial.C (3 * digits i + 14)

theorem prefixValuePolynomial_eval (digits : Nat → Nat) (i n : Nat) :
    (prefixValuePolynomial digits i).eval n = MachineHorner.value n digits i := by
  induction i with
  | zero => simp [prefixValuePolynomial, MachineHorner.value]
  | succ i ih => simp [prefixValuePolynomial, MachineHorner.value, ih]

theorem prefixCostPolynomial_eval (digits : Nat → Nat) (i n : Nat) :
    (prefixCostPolynomial digits i).eval n = MachineHorner.prefixSteps n digits i := by
  induction i with
  | zero => simp [prefixCostPolynomial, MachineHorner.prefixSteps]
  | succ i ih =>
    simp only [prefixCostPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, prefixValuePolynomial_eval, ih,
      MachineHorner.prefixSteps, MachineHorner.stepCost, MachineRadixStep.steps]
    ring

def timePolynomial (p : Polynomial Nat) : Polynomial Nat :=
  prefixCostPolynomial (digit p) (width p) +
    Polynomial.C 2 * prefixValuePolynomial (digit p) (width p) + Polynomial.X + Polynomial.C 8

theorem timePolynomial_eval (p : Polynomial Nat) (n : Nat) :
    (timePolynomial p).eval n = MachineHorner.steps n (digit p) (width p) + n + 3 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, prefixValuePolynomial_eval,
    prefixCostPolynomial_eval, MachineHorner.steps]
  omega

theorem hornerValue_eq_eval (p : Polynomial Nat) (n : Nat) :
    MachineHorner.value n (digit p) (width p) = p.eval n := by
  rw [MachineHorner.value_eq_foldl, range_map_digit]
  have hh := highCoefficients_foldl p n
  simpa only [Nat.mul_comm] using hh

theorem hornerStageTrace (p : Polynomial Nat) (n : Nat) :
    (MachineComposition.advance (machine p).step)^[MachineHorner.steps n (digit p) (width p)]
      (some ⟨some (innerLabels p .start), (((), ()), none), preparedTapes p n⟩) =
      some ⟨some (.inr (.inr false)), (((), ()), none), afterHornerTapes p n (p.eval n)⟩ := by
  have h := MachineHorner.hornerTrace (slots p) (innerLabels p)
    (some (.inr (.inr false))) (program p) (fun _ => rfl) (preparedTapes p n) n (digit p)
    (by simp [slots]) (fun i => by simp [slots]) (preparedTapes_clean p n) () none
  rw [hornerValue_eq_eval] at h
  have ht : MachineHorner.resultTapes (slots p) (preparedTapes p n) (p.eval n) =
      afterHornerTapes p n (p.eval n) := by
    simp [MachineHorner.resultTapes, afterHornerTapes, slots]
  rw [ht] at h
  exact h

/-- Exact execution includes literal initialization, the physical Horner
subroutine, input consumption, and cleanup of every coefficient tape. -/
def outputsInTime (p : Polynomial Nat) (n : Nat) :
    Turing.TM2OutputsInTime (machine p) (encodeWord n) (some (encodeWord (p.eval n)))
      ((timePolynomial p).eval n) where
  steps := MachineHorner.steps n (digit p) (width p) + n + 3
  evals_in_steps := by
    change (MachineComposition.advance (machine p).step)^[MachineHorner.steps n (digit p) (width p) + n + 3]
      (some (Turing.initList (machine p) (encodeWord n))) =
        some (Turing.haltList (machine p) (encodeWord (p.eval n)))
    have h01 : (MachineComposition.advance (machine p).step)^[
        MachineHorner.steps n (digit p) (width p) + 1]
        (some (Turing.initList (machine p) (encodeWord n))) =
          some ⟨some (.inr (.inr false)), (((), ()), none),
            afterHornerTapes p n (p.eval n)⟩ := by
      rw [Function.iterate_add_apply, initializationTrace, hornerStageTrace]
    rw [show MachineHorner.steps n (digit p) (width p) + n + 3 =
      (n + 2) + (MachineHorner.steps n (digit p) (width p) + 1) by omega,
      Function.iterate_add_apply, h01, cleanupTrace]
  steps_le_m := by rw [timePolynomial_eval]

/-- A genuine finite Boolean-stack machine for evaluating any fixed natural
polynomial on zero-delimited unary input, with a polynomial transition bound. -/
def computableInPolyTime (p : Polynomial Nat) :
    Turing.TM2ComputableInPolyTime encodeWord encodeWord p.eval where
  tm := machine p
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial p
  outputsFun n := by
    change Turing.TM2OutputsInTime (machine p) ((encodeWord n).map id)
      (some ((encodeWord (p.eval n)).map id)) ((timePolynomial p).eval (encodeWord n).length)
    rw [List.map_id, List.map_id, encodeWord_length]
    let h := outputsInTime p n
    exact {
      toEvalsTo := h.toEvalsTo
      steps_le_m := h.steps_le_m.trans
        (MachineComposition.natPolynomial_eval_mono (timePolynomial p) (by omega : n ≤ n + 1)) }

end

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.PolynomialMachine

end OAI
