import Mathlib
import OAI.Computability.DirectedFeedback.Games.CanonicalAddress

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

namespace DFVSGames.Reduction.MachineTemplateAddress

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad

inductive Tape (q width : Nat)
  | field (i : Fin q)
  | radix | output | reversed | forward | copyScratch
  | accA | accB | counter | hornerScratch
  | digit (i : Fin width)
  deriving DecidableEq, Fintype

abbrev State (σ : Type) := (σ × Unit) × Option Bool
abbrev Alphabet {K : Type} (_ : K) := Bool

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

def hornerLayout : MachineHorner.Layout width ↪ Tape q width where
  toFun
    | .inl 0 => .radix
    | .inl 1 => .accA
    | .inl 2 => .accB
    | .inl 3 => .output
    | .inl 4 => .counter
    | .inl 5 => .hornerScratch
    | .inr i => .digit i
  inj' := by
    rintro (a | a) (b | b) h
    · fin_cases a <;> fin_cases b <;> simp_all
    · fin_cases a <;> simp_all
    · fin_cases b <;> simp_all
    · exact congrArg Sum.inr (Tape.digit.inj h)

def hornerSlots (slots : Tape q width ↪ K) : MachineHorner.Layout width ↪ K :=
  hornerLayout.trans slots

def chosen (slots : Tape q width ↪ K) : List K := List.ofFn (fun i => slots (.digit i))

omit [DecidableEq K] in
@[simp] theorem mem_chosen (slots : Tape q width ↪ K) (tape : K) :
    tape ∈ chosen slots ↔ ∃ i, slots (.digit i) = tape := by
  simp [chosen, List.mem_ofFn]

abbrev Label (m width : Nat) (cleanup : List K) :=
  MachineFieldTemplate.Label m ⊕ Unit ⊕ (Fin (width + 1) × Bool) ⊕
    MachineHorner.Label width ⊕ MachineDrainMany.Label cleanup

def emitLabel {m : Nat} {cleanup : List K} (l : MachineFieldTemplate.Label m) :
    Label m width cleanup := .inl l
def reverseLabel {m : Nat} {cleanup : List K} : Label m width cleanup := .inr (.inl ())
def parseLabel {m : Nat} {cleanup : List K} (l : Fin (width + 1) × Bool) :
    Label m width cleanup := .inr (.inr (.inl l))
def hornerLabel {m : Nat} {cleanup : List K} (l : MachineHorner.Label width) :
    Label m width cleanup := .inr (.inr (.inr (.inl l)))
def cleanupLabel {m : Nat} {cleanup : List K} (l : MachineDrainMany.Label cleanup) :
    Label m width cleanup := .inr (.inr (.inr (.inr l)))

def parseDestination (slots : Tape q width ↪ K) (i : Nat) : K :=
  if h : i < width then slots (.digit ⟨i, h⟩) else slots .forward

omit [DecidableEq K] in
@[simp] theorem parseDestination_below (slots : Tape q width ↪ K) (i : Nat) (hi : i < width) :
    parseDestination slots i = slots (.digit ⟨i, hi⟩) := by simp [parseDestination, hi]

def instruction (tokens : List (MachineFieldTemplate.Token q)) (slots : Tape q width ↪ K)
    (place : Label tokens.length width (chosen slots) → Λ) (exit : Option Λ) :
    Label tokens.length width (chosen slots) → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .inl l => MachineFieldTemplate.instruction tokens (fun j => slots (.field j))
      (slots .copyScratch) (slots .reversed) (fun l => place (emitLabel l))
      (some (place reverseLabel)) l
  | .inr (.inl _) => MachineTransfer.loopAt (slots .reversed) (slots .forward) id false
      (place reverseLabel) (some (place (parseLabel (SourceFieldArray.startLabel width 0))))
  | .inr (.inr (.inl l)) =>
      if h : l.1.val < width then
        if l.2 then
          SourceMachine.fieldLoop (slots .forward) (slots (.digit ⟨l.1.val, h⟩))
            (place (parseLabel (l.1, true)))
            (some (place (parseLabel (SourceFieldArray.startLabel width (l.1.val + 1)))))
        else SourceMachine.fieldStart (slots (.digit ⟨l.1.val, h⟩))
          (place (parseLabel (l.1, true)))
      else SourceFieldArray.finish (slots .forward) (some (place (hornerLabel .start)))
  | .inr (.inr (.inr (.inl l))) => MachineHorner.statement (hornerSlots slots)
      (fun l => place (hornerLabel l))
      (MachineDrainMany.entry (chosen slots) (fun l => place (cleanupLabel l)) exit) l
  | .inr (.inr (.inr (.inr l))) => MachineDrainMany.instruction (chosen slots)
      (fun l => place (cleanupLabel l)) exit l

def program (tokens : List (MachineFieldTemplate.Token q)) (slots : Tape q width ↪ K)
    (exit : Option (Label tokens.length width (chosen slots))) :
    Label tokens.length width (chosen slots) →
      TM2.Stmt (Alphabet (K := K)) (Label tokens.length width (chosen slots)) (State σ) :=
  instruction tokens slots id exit

structure Clean (slots : Tape q width ↪ K) (base : K → List Bool) : Prop where
  reversed : base (slots .reversed) = []
  forward : base (slots .forward) = []
  copyScratch : base (slots .copyScratch) = []
  accA : base (slots .accA) = []
  accB : base (slots .accB) = []
  counter : base (slots .counter) = []
  hornerScratch : base (slots .hornerScratch) = []
  digit : ∀ j, base (slots (.digit j)) = []

def digits (values : List Nat) (i : Nat) : Nat := values[i]?.getD 0

def forwardTapes (slots : Tape q width ↪ K) (base : K → List Bool) (values : List Nat) :
    K → List Bool := Function.update base (slots .forward) (encodeWords values)

def parsedTapes (slots : Tape q width ↪ K) (base : K → List Bool) (values : List Nat) :
    K → List Bool :=
  SourceFieldArray.sequenceTapes (slots .forward) (parseDestination slots)
    (forwardTapes slots base values) 0 values []

def resultTapes (slots : Tape q width ↪ K) (base : K → List Bool) (value : Nat) :
    K → List Bool := Function.update base (slots .output) (encodeWord value ++ base (slots .output))

def afterHorner (slots : Tape q width ↪ K) (base : K → List Bool) (B : Nat) (values : List Nat) :
    K → List Bool :=
  MachineHorner.resultTapes (hornerSlots slots) (parsedTapes slots base values)
    (MachineHorner.value B (digits values) width)

def phaseSteps (tokens : List (MachineFieldTemplate.Token q)) (slots : Tape q width ↪ K)
    (base : K → List Bool) (B : Nat) (values : List Nat) : Nat :=
  MachineFieldTemplate.templateSteps tokens (fun j => base (slots (.field j))) +
    ((encodeWords values).length + 1) + (values.sum + 2 * values.length + 1) +
    MachineHorner.steps B (digits values) width +
    MachineDrainMany.steps (chosen slots) (afterHorner slots base B values)

@[simp] theorem resultTapes_output (slots : Tape q width ↪ K) (base : K → List Bool) (value : Nat) :
    resultTapes slots base value (slots .output) = encodeWord value ++ base (slots .output) := by
  simp [resultTapes]

theorem resultTapes_other (slots : Tape q width ↪ K) (base : K → List Bool) (value : Nat)
    (tape : K) (hne : tape ≠ slots .output) : resultTapes slots base value tape = base tape := by
  simp [resultTapes, hne]

theorem hornerValue_eq_radix (B : Nat) (values : List Nat) :
    MachineHorner.value B (digits values) values.length = CanonicalAddress.radix B values := by
  rw [MachineHorner.value_eq_foldl, CanonicalAddress.radix_eq_foldl]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range, digits,
      List.getElem?_eq_getElem hj, Option.getD_some]

theorem parsedTapes_other (slots : Tape q width ↪ K) (base : K → List Bool)
    (values : List Nat) (hlen : values.length = width) (tape : K)
    (notForward : tape ≠ slots .forward) (notDigit : ∀ i, tape ≠ slots (.digit i)) :
    parsedTapes slots base values tape = base tape := by
  rw [parsedTapes, SourceFieldArray.sequenceTapes_other]
  · exact Function.update_of_ne notForward _ _
  · exact notForward
  · intro r hr
    simp only [Nat.zero_add, parseDestination_below slots r (by omega)]
    exact notDigit _

theorem parsedTapes_source (slots : Tape q width ↪ K) (base : K → List Bool)
    (values : List Nat) (hlen : values.length = width) :
    parsedTapes slots base values (slots .forward) = [] := by
  apply SourceFieldArray.sequenceTapes_source
  · intro r hr
    simp only [Nat.zero_add, parseDestination_below slots r (by omega)]
    exact slots.injective.ne (by simp)
  · simp [forwardTapes]

theorem parsedTapes_digit (slots : Tape q width ↪ K) (base : K → List Bool)
    (values : List Nat) (hlen : values.length = width) (clean : Clean slots base) (i : Fin width) :
    parsedTapes slots base values (slots (.digit i)) = encodeWord (digits values i.val) := by
  have hi : i.val < values.length := by omega
  have h := SourceFieldArray.sequenceTapes_selected (slots .forward) (parseDestination slots)
    (forwardTapes slots base values) 0 values [] i.val hi
    (by
      intro r hr
      simp only [Nat.zero_add, parseDestination_below slots r (by omega)]
      exact slots.injective.ne (by simp))
    (by
      intro r s hr hs h
      simp only [Nat.zero_add, parseDestination_below slots r (by omega),
        parseDestination_below slots s (by omega)] at h
      exact congrArg Fin.val (Tape.digit.inj (slots.injective h)))
  simpa [parsedTapes, parseDestination, i.isLt, forwardTapes, clean.digit,
    slots.injective.ne (show Tape.digit i ≠ Tape.forward by simp), digits,
    List.getElem?_eq_getElem hi] using h

theorem parsedTapes_clean (slots : Tape q width ↪ K) (base : K → List Bool)
    (values : List Nat) (hlen : values.length = width) (clean : Clean slots base) :
    MachineHorner.Clean (hornerSlots slots) (parsedTapes slots base values) := by
  constructor
  · rw [show hornerSlots slots (.inl 1) = slots .accA from rfl,
      parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp))
        (fun _ => slots.injective.ne (by simp))]
    exact clean.accA
  · rw [show hornerSlots slots (.inl 2) = slots .accB from rfl,
      parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp))
        (fun _ => slots.injective.ne (by simp))]
    exact clean.accB
  · rw [show hornerSlots slots (.inl 4) = slots .counter from rfl,
      parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp))
        (fun _ => slots.injective.ne (by simp))]
    exact clean.counter
  · rw [show hornerSlots slots (.inl 5) = slots .hornerScratch from rfl,
      parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp))
        (fun _ => slots.injective.ne (by simp))]
    exact clean.hornerScratch

theorem cleanup_result (slots : Tape q width ↪ K) (base : K → List Bool)
    (B : Nat) (values : List Nat) (hlen : values.length = width) (clean : Clean slots base) :
    MachineDrainMany.finalTapes (chosen slots) (afterHorner slots base B values) =
      resultTapes slots base (CanonicalAddress.radix B values) := by
  have hv : MachineHorner.value B (digits values) width = CanonicalAddress.radix B values := by
    rw [← hlen, hornerValue_eq_radix]
  funext tape
  rw [MachineDrainMany.finalTapes_apply]
  by_cases hd : tape ∈ chosen slots
  · rw [ite_eq_left hd]
    obtain ⟨i, rfl⟩ := (mem_chosen slots tape).mp hd
    simp [resultTapes, slots.injective.ne (show Tape.digit i ≠ Tape.output by simp), clean.digit]
  · rw [ite_eq_right hd]
    have notDigit : ∀ i, tape ≠ slots (.digit i) := by
      intro i hi
      exact hd ((mem_chosen slots tape).mpr ⟨i, hi.symm⟩)
    by_cases ho : tape = slots .output
    · subst tape
      simp only [afterHorner, MachineHorner.resultTapes,
        show hornerSlots slots (.inl 3) = slots .output from rfl,
        Function.update_self, resultTapes_output, hv]
      rw [parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp)) notDigit]
    · simp only [afterHorner, MachineHorner.resultTapes,
        show hornerSlots slots (.inl 3) = slots .output from rfl,
        resultTapes, Function.update_of_ne ho]
      by_cases hf : tape = slots .forward
      · subst tape
        rw [parsedTapes_source slots base values hlen, clean.forward]
      · exact parsedTapes_other slots base values hlen tape hf notDigit

section Execution

variable (tokens : List (MachineFieldTemplate.Token q)) (slots : Tape q width ↪ K)
variable (place : Label tokens.length width (chosen slots) → Λ) (exit : Option Λ)
variable (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
variable (atInstruction : ∀ l, P (place l) = instruction tokens slots place exit l)

include atInstruction

omit [DecidableEq K] in
theorem parse_atStart (r : Nat) (hr : r < width) :
    P (place (parseLabel (SourceFieldArray.startLabel width r))) =
      SourceMachine.fieldStart (parseDestination slots r)
        (place (parseLabel (SourceFieldArray.loopLabel width r))) := by
  rw [atInstruction]
  simp [instruction, parseLabel, SourceFieldArray.startLabel, SourceFieldArray.loopLabel,
    SourceFieldArray.boundedIndex_val hr.le, hr]

omit [DecidableEq K] in
theorem parse_atLoop (r : Nat) (hr : r < width) :
    P (place (parseLabel (SourceFieldArray.loopLabel width r))) =
      SourceMachine.fieldLoop (slots .forward) (parseDestination slots r)
        (place (parseLabel (SourceFieldArray.loopLabel width r)))
        (some (place (parseLabel (SourceFieldArray.startLabel width (r + 1))))) := by
  rw [atInstruction]
  simp [instruction, parseLabel, SourceFieldArray.startLabel, SourceFieldArray.loopLabel,
    SourceFieldArray.boundedIndex_val hr.le, hr]

omit [DecidableEq K] in
theorem parse_atDone :
    P (place (parseLabel (SourceFieldArray.startLabel width width))) =
      SourceFieldArray.finish (slots .forward) (some (place (hornerLabel .start))) := by
  rw [atInstruction]
  simp [instruction, parseLabel, SourceFieldArray.startLabel]

theorem phaseTrace (base : K → List Bool) (B : Nat) (values : List Nat)
    (hlen : values.length = width) (clean : Clean slots base)
    (baseField : base (slots .radix) = encodeWord B)
    (wordCorrect : MachineFieldTemplate.templateOutput tokens (fun j => base (slots (.field j))) =
      encodeWords values) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step P))^[phaseSteps tokens slots base B values]
      (some ⟨some (place (emitLabel (MachineFieldTemplate.startAt tokens.length 0))),
        ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (CanonicalAddress.radix B values)⟩ := by
  let emitted := MachineFieldTemplate.outputTapes base (slots .reversed) (encodeWords values)
  have emitRun := MachineFieldTemplate.phaseTrace tokens (fun j => slots (.field j))
    (slots .copyScratch) (slots .reversed)
    (fun _ => slots.injective.ne (by simp)) (fun _ => slots.injective.ne (by simp))
    (slots.injective.ne (by simp)) (fun l => place (emitLabel l))
    (some (place reverseLabel)) P (fun l => atInstruction (emitLabel l))
    base clean.copyScratch ((ambient, ()), register)
  rw [wordCorrect] at emitRun
  change (MachineComposition.advance (TM2.step P))^[_] _ =
    some ⟨some (place reverseLabel), ((ambient, ()), none), emitted⟩ at emitRun
  have reverseRun := MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Unit)
    (slots .reversed) (slots .forward) (slots.injective.ne (by simp)) id false
    (place reverseLabel) (some (place (parseLabel (SourceFieldArray.startLabel width 0))))
    P (atInstruction reverseLabel) emitted (ambient, ()) none
  have reverseResult : MachineTransfer.tapesAt (slots .reversed) (slots .forward) emitted []
      ((emitted (slots .reversed)).reverse.map id ++ emitted (slots .forward)) =
      forwardTapes slots base values := by
    funext tape
    by_cases hr : tape = slots .reversed
    · subst tape
      simp [emitted, MachineFieldTemplate.outputTapes, MachineTransfer.tapesAt, forwardTapes,
        slots.injective.ne (show Tape.reversed ≠ Tape.forward by simp), clean.reversed]
    · by_cases hf : tape = slots .forward
      · subst tape
        simp [emitted, MachineFieldTemplate.outputTapes, MachineTransfer.tapesAt, forwardTapes,
          slots.injective.ne (show Tape.forward ≠ Tape.reversed by simp),
          clean.reversed, clean.forward]
      · simp [emitted, MachineFieldTemplate.outputTapes, MachineTransfer.tapesAt,
          forwardTapes, hr, hf]
  rw [reverseResult] at reverseRun
  have reverseLength : (emitted (slots .reversed)).length + 1 = (encodeWords values).length + 1 := by
    simp [emitted, MachineFieldTemplate.outputTapes, clean.reversed]
  rw [reverseLength] at reverseRun
  change (MachineComposition.advance (TM2.step P))^[(encodeWords values).length + 1]
    (some ⟨some (place reverseLabel), ((ambient, ()), none), emitted⟩) =
    some ⟨some (place (parseLabel (SourceFieldArray.startLabel width 0))),
      ((ambient, ()), none), forwardTapes slots base values⟩ at reverseRun
  have parseRun := SourceFieldArray.sequenceTrace (slots .forward) (parseDestination slots)
    (fun r => place (parseLabel (SourceFieldArray.startLabel width r)))
    (fun r => place (parseLabel (SourceFieldArray.loopLabel width r)))
    (some (place (hornerLabel .start))) P (forwardTapes slots base values) 0 values []
    (by
      intro r hr
      simp only [Nat.zero_add, parseDestination_below slots r (by omega)]
      exact slots.injective.ne (by simp))
    (by intro r hr; simpa using parse_atStart tokens slots place exit P atInstruction r (by omega))
    (by intro r hr; simpa using parse_atLoop tokens slots place exit P atInstruction r (by omega))
    (by simpa only [Nat.zero_add, hlen] using parse_atDone tokens slots place exit P atInstruction)
    (by simp [forwardTapes]) (ambient, ()) none
  change (MachineComposition.advance (TM2.step P))^[values.sum + 2 * values.length + 1]
    (some ⟨some (place (parseLabel (SourceFieldArray.startLabel width 0))),
      ((ambient, ()), none), forwardTapes slots base values⟩) =
    some ⟨some (place (hornerLabel .start)), ((ambient, ()), none),
      parsedTapes slots base values⟩ at parseRun
  have hbase : parsedTapes slots base values (hornerSlots slots (.inl 0)) = encodeWord B := by
    change parsedTapes slots base values (slots .radix) = _
    rw [parsedTapes_other slots base values hlen _ (slots.injective.ne (by simp))
      (fun _ => slots.injective.ne (by simp))]
    exact baseField
  have hornerRun := MachineHorner.hornerTrace (hornerSlots slots) (fun l => place (hornerLabel l))
    (MachineDrainMany.entry (chosen slots) (fun l => place (cleanupLabel l)) exit)
    P (fun l => atInstruction (hornerLabel l)) (parsedTapes slots base values) B (digits values)
    hbase (parsedTapes_digit slots base values hlen clean)
    (parsedTapes_clean slots base values hlen clean) ambient none
  have cleanupRun := MachineDrainMany.trace (chosen slots) (fun l => place (cleanupLabel l)) exit
    P (fun l => atInstruction (cleanupLabel l)) (afterHorner slots base B values) (ambient, ()) none
  rw [MachineDrainMany.finalRegister_none, cleanup_result slots base B values hlen clean] at cleanupRun
  rw [show phaseSteps tokens slots base B values =
    MachineDrainMany.steps (chosen slots) (afterHorner slots base B values) +
      (MachineHorner.steps B (digits values) width +
      ((values.sum + 2 * values.length + 1) +
      (((encodeWords values).length + 1) +
      MachineFieldTemplate.templateSteps tokens (fun j => base (slots (.field j)))))) by
        unfold phaseSteps; omega]
  rw [Function.iterate_add_apply]
  rw [Function.iterate_add_apply (m := MachineHorner.steps B (digits values) width)]
  rw [Function.iterate_add_apply (m := values.sum + 2 * values.length + 1)]
  rw [Function.iterate_add_apply (m := (encodeWords values).length + 1)]
  rw [emitRun, reverseRun, parseRun, hornerRun]
  exact cleanupRun

end Execution

theorem programTrace (tokens : List (MachineFieldTemplate.Token q)) (slots : Tape q width ↪ K)
    (exit : Option (Label tokens.length width (chosen slots)))
    (base : K → List Bool) (B : Nat) (values : List Nat) (hlen : values.length = width)
    (clean : Clean slots base) (baseField : base (slots .radix) = encodeWord B)
    (wordCorrect : MachineFieldTemplate.templateOutput tokens (fun j => base (slots (.field j))) =
      encodeWords values) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program tokens slots exit)))^[phaseSteps tokens slots base B values]
      (some ⟨some (emitLabel (MachineFieldTemplate.startAt tokens.length 0)),
        ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (CanonicalAddress.radix B values)⟩ :=
  phaseTrace tokens slots id exit (program tokens slots exit) (fun _ => rfl)
    base B values hlen clean baseField wordCorrect ambient register

def phaseInTime (tokens : List (MachineFieldTemplate.Token q)) (slots : Tape q width ↪ K)
    (place : Label tokens.length width (chosen slots) → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atInstruction : ∀ l, P (place l) = instruction tokens slots place exit l)
    (base : K → List Bool) (B : Nat) (values : List Nat) (hlen : values.length = width)
    (clean : Clean slots base) (baseField : base (slots .radix) = encodeWord B)
    (wordCorrect : MachineFieldTemplate.templateOutput tokens (fun j => base (slots (.field j))) =
      encodeWords values) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (place (emitLabel (MachineFieldTemplate.startAt tokens.length 0))),
        ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base (CanonicalAddress.radix B values)⟩)
      (phaseSteps tokens slots base B values) where
  steps := phaseSteps tokens slots base B values
  evals_in_steps := phaseTrace tokens slots place exit P atInstruction
    base B values hlen clean baseField wordCorrect ambient register
  steps_le_m := Nat.le_refl _

omit [DecidableEq K] in
private theorem copiedLength_le_inline_MachineTemplateAddress (tokens : List (MachineFieldTemplate.Token q))
    (fields : Fin q → List Bool) (M : Nat) (bounded : ∀ j, (fields j).length ≤ M) :
    MachineFieldTemplate.copiedLength tokens fields ≤ tokens.length * M := by
  induction tokens with
  | nil => simp [MachineFieldTemplate.copiedLength]
  | cons token tokens ih =>
    cases token with
    | literal bits =>
      simp only [MachineFieldTemplate.copiedLength, List.map_cons, List.sum_cons,
        List.length_cons, Nat.zero_add] at *
      nlinarith
    | copy j =>
      simp only [MachineFieldTemplate.copiedLength, List.map_cons, List.sum_cons,
        List.length_cons] at *
      have h := bounded j
      nlinarith

omit [DecidableEq K] in
private theorem lengthSum_le_inline_MachineTemplateAddress (selected : List K) (base : K → List Bool) (bound : Nat)
    (bounded : ∀ tape ∈ selected, (base tape).length ≤ bound) :
    MachineDrainMany.lengthSum selected base ≤ selected.length * bound := by
  induction selected with
  | nil => simp [MachineDrainMany.lengthSum]
  | cons tape selected ih =>
    have ht := bounded tape (by simp)
    have hs := ih (fun t ht => bounded t (by simp [ht]))
    simp only [MachineDrainMany.lengthSum, List.map_cons, List.sum_cons,
      List.length_cons] at *
    nlinarith

noncomputable def timePolynomial (tokenCount width : Nat) : Polynomial Nat :=
  MachineHorner.timePolynomial width +
    Polynomial.C (3 * tokenCount + width + 2) * Polynomial.X +
    Polynomial.C (3 * tokenCount + 3 * width + 3)

omit [DecidableEq K] in
theorem timePolynomial_eval (tokenCount width M : Nat) :
    (timePolynomial tokenCount width).eval M =
      (MachineHorner.timePolynomial width).eval M +
      (3 * tokenCount + width + 2) * M + (3 * tokenCount + 3 * width + 3) := by
  simp [timePolynomial]

theorem phaseSteps_le_timePolynomial (tokens : List (MachineFieldTemplate.Token q))
    (slots : Tape q width ↪ K) (base : K → List Bool) (B : Nat) (values : List Nat)
    (hlen : values.length = width) (clean : Clean slots base) (M : Nat)
    (fieldsBound : ∀ j, (base (slots (.field j))).length ≤ M)
    (wordsBound : (encodeWords values).length ≤ M) (radixBound : B ≤ M)
    (digitBound : ∀ i, i < width → digits values i ≤ M) :
    phaseSteps tokens slots base B values ≤ (timePolynomial tokens.length width).eval M := by
  have hcopied := copiedLength_le_inline_MachineTemplateAddress tokens (fun j => base (slots (.field j))) M fieldsBound
  have htemplate := MachineFieldTemplate.templateSteps_le tokens (fun j => base (slots (.field j)))
  have hhorner := MachineHorner.steps_le_timePolynomial B (digits values) width M radixBound digitBound
  have hselected : ∀ tape ∈ chosen slots, (afterHorner slots base B values tape).length ≤ M + 1 := by
    intro tape ht
    obtain ⟨i, rfl⟩ := (mem_chosen slots tape).mp ht
    have heq : afterHorner slots base B values (slots (.digit i)) =
        encodeWord (digits values i.val) := by
      simp only [afterHorner, MachineHorner.resultTapes,
        show hornerSlots slots (.inl 3) = slots .output from rfl,
        Function.update_of_ne (slots.injective.ne (show Tape.digit i ≠ Tape.output by simp))]
      exact parsedTapes_digit slots base values hlen clean i
    rw [heq]
    simpa only [encodeWord, List.length_append, List.length_replicate, List.length_singleton] using
      Nat.add_le_add_right (digitBound i.val i.isLt) 1
  have hsum := lengthSum_le_inline_MachineTemplateAddress (chosen slots) (afterHorner slots base B values) (M + 1) hselected
  have hcleanup := MachineDrainMany.steps_le (chosen slots) (afterHorner slots base B values)
  have hchosen : (chosen slots).length = width := by simp [chosen]
  rw [hchosen] at hsum hcleanup
  have hparse := SourceFieldArray.sequence_time_eq_length values
  rw [hlen] at hparse
  rw [timePolynomial_eval]
  unfold phaseSteps
  rw [hlen]
  nlinarith

def phaseInPolynomialTime (tokens : List (MachineFieldTemplate.Token q))
    (slots : Tape q width ↪ K) (place : Label tokens.length width (chosen slots) → Λ)
    (exit : Option Λ) (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atInstruction : ∀ l, P (place l) = instruction tokens slots place exit l)
    (base : K → List Bool) (B : Nat) (values : List Nat) (hlen : values.length = width)
    (clean : Clean slots base) (baseField : base (slots .radix) = encodeWord B)
    (wordCorrect : MachineFieldTemplate.templateOutput tokens (fun j => base (slots (.field j))) =
      encodeWords values) (ambient : σ) (register : Option Bool) (M : Nat)
    (fieldsBound : ∀ j, (base (slots (.field j))).length ≤ M)
    (wordsBound : (encodeWords values).length ≤ M) (radixBound : B ≤ M)
    (digitBound : ∀ i, i < width → digits values i ≤ M) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (place (emitLabel (MachineFieldTemplate.startAt tokens.length 0))),
        ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base (CanonicalAddress.radix B values)⟩)
      ((timePolynomial tokens.length width).eval M) where
  steps := phaseSteps tokens slots base B values
  evals_in_steps := phaseTrace tokens slots place exit P atInstruction
    base B values hlen clean baseField wordCorrect ambient register
  steps_le_m := phaseSteps_le_timePolynomial tokens slots base B values hlen clean M
    fieldsBound wordsBound radixBound digitBound

end DFVSGames.Reduction.MachineTemplateAddress
end

section

namespace DFVSGames.Reduction.MachineAddressEdge

open Turing
open DFVSGames.Foundations.Complexity
open MachineSubstitution (pushWord stepAux_pushWord)

abbrev Tape (q width : Nat) := MachineTemplateAddress.Tape q width ⊕ Fin 2
abbrev State (σ : Type) := (σ × Unit) × Option Bool
abbrev Alphabet {K : Type} (_ : K) := Bool

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

def addressSlots (slots : Tape q width ↪ K) : MachineTemplateAddress.Tape q width ↪ K where
  toFun tape := slots (.inl tape)
  inj' := by intro a b h; exact Sum.inl.inj (slots.injective h)

def capacityTape (slots : Tape q width ↪ K) : K := slots (.inr 0)
def outputTape (slots : Tape q width ↪ K) : K := slots (.inr 1)
def workTape (slots : Tape q width ↪ K) : K := addressSlots slots .output
def tempTape (slots : Tape q width ↪ K) : K := addressSlots slots .forward
def scratchTape (slots : Tape q width ↪ K) : K := addressSlots slots .copyScratch

omit [DecidableEq K] in
theorem address_ne_output (slots : Tape q width ↪ K) (tape : MachineTemplateAddress.Tape q width) :
    addressSlots slots tape ≠ outputTape slots := slots.injective.ne (by simp)

omit [DecidableEq K] in
theorem capacity_ne_output (slots : Tape q width ↪ K) :
    capacityTape slots ≠ outputTape slots := slots.injective.ne (by simp)

omit [DecidableEq K] in
theorem work_ne_output (slots : Tape q width ↪ K) :
    workTape slots ≠ outputTape slots := address_ne_output slots _

omit [DecidableEq K] in
theorem temp_ne_work (slots : Tape q width ↪ K) :
    tempTape slots ≠ workTape slots := slots.injective.ne (by simp)

abbrev Label (leftLength rightLength width : Nat) (cleanup : List K) :=
  MachineTemplateAddress.Label leftLength width cleanup ⊕ MachineTemplateAddress.Label rightLength width cleanup ⊕ Fin 7

def leftLabel {ml mr : Nat} {cleanup : List K} (label : MachineTemplateAddress.Label ml width cleanup) :
    Label ml mr width cleanup := .inl label
def rightLabel {ml mr : Nat} {cleanup : List K} (label : MachineTemplateAddress.Label mr width cleanup) :
    Label ml mr width cleanup := .inr (.inl label)
def plumbing {ml mr : Nat} {cleanup : List K} (index : Fin 7) :
    Label ml mr width cleanup := .inr (.inr index)

def instruction (left right : List (MachineFieldTemplate.Token q))
    (permutation : List Bool) (slots : Tape q width ↪ K)
    (place : Label left.length right.length width (MachineTemplateAddress.chosen (addressSlots slots)) → Λ)
    (exit : Option Λ) :
    Label left.length right.length width (MachineTemplateAddress.chosen (addressSlots slots)) →
      TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .inl label => MachineTemplateAddress.instruction left (addressSlots slots) (fun l => place (leftLabel l))
      (some (place (plumbing 0))) label
  | .inr (.inl label) => MachineTemplateAddress.instruction right (addressSlots slots)
      (fun l => place (rightLabel l)) (some (place (plumbing 1))) label
  | .inr (.inr 0) => MachineTransfer.loopAt (workTape slots) (outputTape slots) id false
      (place (plumbing 0))
      (some (place (rightLabel (MachineTemplateAddress.emitLabel (MachineFieldTemplate.startAt right.length 0)))))
  | .inr (.inr 1) => MachineTransfer.loopAt (capacityTape slots) (scratchTape slots) id false
      (place (plumbing 1)) (some (place (plumbing 2)))
  | .inr (.inr 2) => MachineCopy.forkLoop (scratchTape slots) (capacityTape slots)
      (tempTape slots) false (place (plumbing 2)) (some (place (plumbing 3)))
  | .inr (.inr 3) => MachineUnaryAddAt.loop (tempTape slots) (workTape slots)
      (place (plumbing 3)) (some (place (plumbing 4)))
  | .inr (.inr 4) => MachineDrain.drain (tempTape slots)
      (place (plumbing 4)) (some (place (plumbing 5)))
  | .inr (.inr 5) => MachineTransfer.loopAt (workTape slots) (outputTape slots) id false
      (place (plumbing 5)) (some (place (plumbing 6)))
  | .inr (.inr 6) => .load MachineFieldTemplate.reset
      (pushWord (outputTape slots) permutation (MachineFieldTemplate.jump exit))

def program (left right : List (MachineFieldTemplate.Token q)) (permutation : List Bool)
    (slots : Tape q width ↪ K)
    (exit : Option (Label left.length right.length width (MachineTemplateAddress.chosen (addressSlots slots)))) :=
  instruction (σ := σ) left right permutation slots id exit

structure Clean (slots : Tape q width ↪ K) (base : K → List Bool) : Prop where
  address : MachineTemplateAddress.Clean (addressSlots slots) base
  work : base (workTape slots) = []

def appended (slots : Tape q width ↪ K) (base : K → List Bool) (bits : List Bool) :
    K → List Bool := MachineFieldTemplate.outputTapes base (outputTape slots) bits

@[simp] theorem appended_address (slots : Tape q width ↪ K) (base : K → List Bool)
    (bits : List Bool) (tape : MachineTemplateAddress.Tape q width) :
    appended slots base bits (addressSlots slots tape) = base (addressSlots slots tape) :=
  MachineFieldTemplate.outputTapes_other base (outputTape slots) bits _
    (address_ne_output slots tape)

@[simp] theorem appended_capacity (slots : Tape q width ↪ K) (base : K → List Bool)
    (bits : List Bool) : appended slots base bits (capacityTape slots) = base (capacityTape slots) :=
  MachineFieldTemplate.outputTapes_other base (outputTape slots) bits _ (capacity_ne_output slots)

@[simp] theorem appended_output (slots : Tape q width ↪ K) (base : K → List Bool)
    (bits : List Bool) :
    appended slots base bits (outputTape slots) = bits.reverse ++ base (outputTape slots) := by
  exact MachineFieldTemplate.outputTapes_output _ _ _

theorem appended_other (slots : Tape q width ↪ K) (base : K → List Bool)
    (bits : List Bool) (tape : K) (hne : tape ≠ outputTape slots) :
    appended slots base bits tape = base tape :=
  MachineFieldTemplate.outputTapes_other _ _ _ _ hne

theorem appended_append (slots : Tape q width ↪ K) (base : K → List Bool)
    (first second : List Bool) :
    appended slots (appended slots base first) second = appended slots base (first ++ second) :=
  MachineFieldTemplate.outputTapes_append _ _ _ _

theorem Clean.appended (slots : Tape q width ↪ K) (base : K → List Bool)
    (clean : Clean slots base) (bits : List Bool) : Clean slots (appended slots base bits) := by
  constructor
  · constructor
    · simpa only [appended_address] using clean.address.reversed
    · simpa only [appended_address] using clean.address.forward
    · simpa only [appended_address] using clean.address.copyScratch
    · simpa only [appended_address] using clean.address.accA
    · simpa only [appended_address] using clean.address.accB
    · simpa only [appended_address] using clean.address.counter
    · simpa only [appended_address] using clean.address.hornerScratch
    · intro j; simpa only [appended_address] using clean.address.digit j
  · simpa only [workTape, appended_address] using clean.work

def edgeBits (B C : Nat) (leftValues rightValues : List Nat) (permutation : List Bool) :
    List Bool :=
  encodeWords [CanonicalAddress.radix B leftValues, C + CanonicalAddress.radix B rightValues] ++
    permutation

def phaseSteps (left right : List (MachineFieldTemplate.Token q))
    (slots : Tape q width ↪ K) (base : K → List Bool)
    (B C : Nat) (leftValues rightValues : List Nat) : Nat :=
  MachineTemplateAddress.phaseSteps left (addressSlots slots) base B leftValues +
    MachineTemplateAddress.phaseSteps right (addressSlots slots)
      (appended slots base (encodeWord (CanonicalAddress.radix B leftValues))) B rightValues +
    CanonicalAddress.radix B leftValues + CanonicalAddress.radix B rightValues + 4 * C + 12

theorem addressResult_eq (slots : Tape q width ↪ K) (base : K → List Bool) (value : Nat) :
    MachineTemplateAddress.resultTapes (addressSlots slots) base value =
      Function.update base (workTape slots) (encodeWord value ++ base (workTape slots)) := rfl

theorem transfer_result (slots : Tape q width ↪ K) (base : K → List Bool)
    (value : Nat) (empty : base (workTape slots) = []) :
    MachineTransfer.tapesAt (workTape slots) (outputTape slots)
      (MachineTemplateAddress.resultTapes (addressSlots slots) base value) []
      (((MachineTemplateAddress.resultTapes (addressSlots slots) base value) (workTape slots)).reverse.map id ++
        (MachineTemplateAddress.resultTapes (addressSlots slots) base value) (outputTape slots)) =
      appended slots base (encodeWord value) := by
  funext tape
  by_cases hw : tape = workTape slots
  · subst tape
    simp [MachineTransfer.tapesAt, addressResult_eq, appended,
      MachineFieldTemplate.outputTapes, work_ne_output, empty]
  · by_cases ho : tape = outputTape slots
    · subst tape
      simp [MachineTransfer.tapesAt, addressResult_eq, appended,
        MachineFieldTemplate.outputTapes, Ne.symm (work_ne_output slots), empty]
    · simp [MachineTransfer.tapesAt, addressResult_eq, appended,
        MachineFieldTemplate.outputTapes, hw, ho]

section Execution

variable (left right : List (MachineFieldTemplate.Token q)) (permutation : List Bool)
variable (slots : Tape q width ↪ K)
variable (place : Label left.length right.length width (MachineTemplateAddress.chosen (addressSlots slots)) → Λ)
variable (exit : Option Λ)
variable (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
variable (atInstruction : ∀ label,
  P (place label) = instruction left right permutation slots place exit label)

include atInstruction

theorem literalStep (base : K → List Bool) (state : State σ) :
    TM2.step P ⟨some (place (plumbing 6)), state, base⟩ =
      some ⟨exit, MachineFieldTemplate.reset state, appended slots base permutation⟩ := by
  change some (TM2.stepAux (P (place (plumbing 6))) state base) = _
  rw [atInstruction (plumbing 6)]
  simp only [instruction, plumbing, TM2.stepAux]
  rw [stepAux_pushWord]
  cases exit <;> rfl

theorem phaseTrace (base : K → List Bool) (B C : Nat)
    (leftValues rightValues : List Nat)
    (leftLength : leftValues.length = width) (rightLength : rightValues.length = width)
    (clean : Clean slots base)
    (baseField : base (addressSlots slots .radix) = encodeWord B)
    (capacityField : base (capacityTape slots) = encodeWord C)
    (leftCorrect : MachineFieldTemplate.templateOutput left
      (fun j => base (addressSlots slots (.field j))) = encodeWords leftValues)
    (rightCorrect : MachineFieldTemplate.templateOutput right
      (fun j => base (addressSlots slots (.field j))) = encodeWords rightValues)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step P))^[phaseSteps left right slots base B C leftValues rightValues]
      (some ⟨some (place (leftLabel (MachineTemplateAddress.emitLabel (MachineFieldTemplate.startAt left.length 0)))),
        ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        appended slots base (edgeBits B C leftValues rightValues permutation)⟩ := by
  let L := CanonicalAddress.radix B leftValues
  let R := CanonicalAddress.radix B rightValues
  let afterLeft := appended slots base (encodeWord L)
  have cleanLeft : Clean slots afterLeft := Clean.appended slots base clean (encodeWord L)
  let rightResult := MachineTemplateAddress.resultTapes (addressSlots slots) afterLeft R
  let copied := Function.update rightResult (tempTape slots) (encodeWord C)
  let added := MachineUnaryAddAt.unaryTapes (tempTape slots) (workTape slots) copied 0 (C + R) [] []
  let shifted := MachineTemplateAddress.resultTapes (addressSlots slots) afterLeft (C + R)
  have leftRun := MachineTemplateAddress.phaseTrace left (addressSlots slots) (fun l => place (leftLabel l))
    (some (place (plumbing 0))) P (fun l => atInstruction (leftLabel l))
    base B leftValues leftLength clean.address baseField leftCorrect ambient register
  have transferLeft := MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Unit)
    (workTape slots) (outputTape slots) (work_ne_output slots) id false
    (place (plumbing 0))
    (some (place (rightLabel (MachineTemplateAddress.emitLabel (MachineFieldTemplate.startAt right.length 0)))))
    P (atInstruction (plumbing 0)) (MachineTemplateAddress.resultTapes (addressSlots slots) base L) (ambient, ()) none
  rw [transfer_result slots base L clean.work] at transferLeft
  have leftWork : MachineTemplateAddress.resultTapes (addressSlots slots) base L (workTape slots) = encodeWord L := by
    simp only [addressResult_eq, Function.update_self, clean.work, List.append_nil]
  rw [leftWork] at transferLeft
  change (MachineComposition.advance (TM2.step P))^[(encodeWord L).length + 1]
    (some ⟨some (place (plumbing 0)), ((ambient, ()), none),
      MachineTemplateAddress.resultTapes (addressSlots slots) base L⟩) =
    some ⟨some (place (rightLabel (MachineTemplateAddress.emitLabel
      (MachineFieldTemplate.startAt right.length 0)))), ((ambient, ()), none), afterLeft⟩ at transferLeft
  have rightRun := MachineTemplateAddress.phaseTrace right (addressSlots slots) (fun l => place (rightLabel l))
    (some (place (plumbing 1))) P (fun l => atInstruction (rightLabel l))
    afterLeft B rightValues rightLength cleanLeft.address
    (by simpa [afterLeft] using baseField)
    (by simpa [afterLeft] using rightCorrect) ambient none
  have rightWork : rightResult (workTape slots) = encodeWord R := by
    simp only [rightResult, addressResult_eq, Function.update_self, cleanLeft.work, List.append_nil]
  have rightTemp : rightResult (tempTape slots) = [] := by
    dsimp only [rightResult]
    rw [MachineTemplateAddress.resultTapes_other]
    · exact cleanLeft.address.forward
    · exact temp_ne_work slots
  have rightScratch : rightResult (scratchTape slots) = [] := by
    dsimp only [rightResult]
    rw [MachineTemplateAddress.resultTapes_other]
    · exact cleanLeft.address.copyScratch
    · exact slots.injective.ne (by simp)
  have rightCapacity : rightResult (capacityTape slots) = encodeWord C := by
    dsimp only [rightResult]
    rw [MachineTemplateAddress.resultTapes_other]
    · simpa [afterLeft] using capacityField
    · exact slots.injective.ne (by simp)
  have copyRun := MachineCopy.copyTrace (capacityTape slots) (tempTape slots) (scratchTape slots)
    (slots.injective.ne (by simp)) (slots.injective.ne (by simp))
    (slots.injective.ne (by simp)) false (place (plumbing 1)) (place (plumbing 2))
    (some (place (plumbing 3))) P (atInstruction (plumbing 1)) (atInstruction (plumbing 2))
    rightResult rightScratch (ambient, ()) none
  rw [rightCapacity, rightTemp, List.append_nil] at copyRun
  have addRun := MachineUnaryAddAt.addFromTapes (tempTape slots) (workTape slots)
    (temp_ne_work slots) (place (plumbing 3)) (some (place (plumbing 4)))
    P (atInstruction (plumbing 3)) copied C R [] []
    (by simp [copied])
    (by simp [copied, Ne.symm (temp_ne_work slots), rightWork]) (ambient, ()) none
  have addedTemp : added (tempTape slots) = encodeWord 0 := by
    simp [added, temp_ne_work]
  have drainResult : Function.update added (tempTape slots) [] = shifted := by
    funext tape
    by_cases ht : tape = tempTape slots
    · subst tape
      simp [shifted, addressResult_eq, temp_ne_work, show afterLeft (tempTape slots) = [] from cleanLeft.address.forward]
    · by_cases hw : tape = workTape slots
      · subst tape
        simp [added, MachineUnaryAddAt.unaryTapes, MachineTransfer.tapesAt, shifted,
          addressResult_eq, Ne.symm (temp_ne_work slots), cleanLeft.work]
      · simp [added, MachineUnaryAddAt.unaryTapes, MachineTransfer.tapesAt, copied,
          rightResult, shifted, addressResult_eq, ht, hw]
  have drainRun := (MachineDrain.drainInTime (tempTape slots) (place (plumbing 4))
    (some (place (plumbing 5))) P (atInstruction (plumbing 4)) added (ambient, ()) none).evals_in_steps
  change (MachineComposition.advance (TM2.step P))^[(added (tempTape slots)).length + 1]
    (some ⟨some (place (plumbing 4)), ((ambient, ()), none), added⟩) = _ at drainRun
  rw [addedTemp, drainResult] at drainRun
  have transferRight := MachineTransfer.transferAt_fromTapes
    (Γ := fun _ : K => Bool) (σ := σ × Unit)
    (workTape slots) (outputTape slots) (work_ne_output slots) id false
    (place (plumbing 5)) (some (place (plumbing 6))) P (atInstruction (plumbing 5))
    shifted (ambient, ()) none
  rw [transfer_result slots afterLeft (C + R) cleanLeft.work] at transferRight
  have shiftedWork : shifted (workTape slots) = encodeWord (C + R) := by
    simp only [shifted, addressResult_eq, Function.update_self, cleanLeft.work, List.append_nil]
  rw [shiftedWork] at transferRight
  change (MachineComposition.advance (TM2.step P))^[(encodeWord (C + R)).length + 1]
    (some ⟨some (place (plumbing 5)), ((ambient, ()), none), shifted⟩) =
    some ⟨some (place (plumbing 6)), ((ambient, ()), none),
      appended slots afterLeft (encodeWord (C + R))⟩ at transferRight
  have finishRun := literalStep left right permutation slots place exit P atInstruction
    (appended slots afterLeft (encodeWord (C + R))) ((ambient, ()), none)
  have fullSteps : phaseSteps left right slots base B C leftValues rightValues =
      1 + (((encodeWord (C + R)).length + 1) + ((encodeWord 0).length + 1 +
      ((C + 1) + (2 * ((encodeWord C).length + 1) +
      (MachineTemplateAddress.phaseSteps right (addressSlots slots) afterLeft B rightValues +
      (((encodeWord L).length + 1) + MachineTemplateAddress.phaseSteps left (addressSlots slots) base B leftValues)))))) := by
    simp only [encodeWord_length]
    dsimp only [phaseSteps, L, R, afterLeft]
    omega
  rw [fullSteps]
  rw [Function.iterate_add_apply]
  rw [Function.iterate_add_apply (m := (encodeWord (C + R)).length + 1)]
  rw [Function.iterate_add_apply (m := (encodeWord 0).length + 1)]
  rw [Function.iterate_add_apply (m := C + 1)]
  rw [Function.iterate_add_apply (m := 2 * ((encodeWord C).length + 1))]
  rw [Function.iterate_add_apply (m := MachineTemplateAddress.phaseSteps right (addressSlots slots)
    afterLeft B rightValues)]
  rw [Function.iterate_add_apply (m := (encodeWord L).length + 1)]
  rw [leftRun, transferLeft, rightRun, copyRun, addRun, drainRun, transferRight]
  simp only [Function.iterate_one, MachineComposition.advance_some]
  rw [finishRun]
  simp only [MachineFieldTemplate.reset, afterLeft, appended_append]
  simp [edgeBits, encodeWords, L, R, List.append_assoc]

end Execution

theorem programTrace (left right : List (MachineFieldTemplate.Token q))
    (permutation : List Bool) (slots : Tape q width ↪ K)
    (exit : Option (Label left.length right.length width (MachineTemplateAddress.chosen (addressSlots slots))))
    (base : K → List Bool) (B C : Nat) (leftValues rightValues : List Nat)
    (leftLength : leftValues.length = width) (rightLength : rightValues.length = width)
    (clean : Clean slots base)
    (baseField : base (addressSlots slots .radix) = encodeWord B)
    (capacityField : base (capacityTape slots) = encodeWord C)
    (leftCorrect : MachineFieldTemplate.templateOutput left
      (fun j => base (addressSlots slots (.field j))) = encodeWords leftValues)
    (rightCorrect : MachineFieldTemplate.templateOutput right
      (fun j => base (addressSlots slots (.field j))) = encodeWords rightValues)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program left right permutation slots exit)))^[
      phaseSteps left right slots base B C leftValues rightValues]
      (some ⟨some (leftLabel (MachineTemplateAddress.emitLabel (MachineFieldTemplate.startAt left.length 0))),
        ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        appended slots base (edgeBits B C leftValues rightValues permutation)⟩ :=
  phaseTrace left right permutation slots id exit (program left right permutation slots exit)
    (fun _ => rfl) base B C leftValues rightValues leftLength rightLength clean baseField
    capacityField leftCorrect rightCorrect ambient register

def phaseInTime (left right : List (MachineFieldTemplate.Token q))
    (permutation : List Bool) (slots : Tape q width ↪ K)
    (place : Label left.length right.length width (MachineTemplateAddress.chosen (addressSlots slots)) → Λ)
    (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atInstruction : ∀ label,
      P (place label) = instruction left right permutation slots place exit label)
    (base : K → List Bool) (B C : Nat) (leftValues rightValues : List Nat)
    (leftLength : leftValues.length = width) (rightLength : rightValues.length = width)
    (clean : Clean slots base)
    (baseField : base (addressSlots slots .radix) = encodeWord B)
    (capacityField : base (capacityTape slots) = encodeWord C)
    (leftCorrect : MachineFieldTemplate.templateOutput left
      (fun j => base (addressSlots slots (.field j))) = encodeWords leftValues)
    (rightCorrect : MachineFieldTemplate.templateOutput right
      (fun j => base (addressSlots slots (.field j))) = encodeWords rightValues)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (place (leftLabel (MachineTemplateAddress.emitLabel
        (MachineFieldTemplate.startAt left.length 0)))), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none),
        appended slots base (edgeBits B C leftValues rightValues permutation)⟩)
      (phaseSteps left right slots base B C leftValues rightValues) where
  steps := phaseSteps left right slots base B C leftValues rightValues
  evals_in_steps := phaseTrace left right permutation slots place exit P atInstruction
    base B C leftValues rightValues leftLength rightLength clean baseField capacityField
    leftCorrect rightCorrect ambient register
  steps_le_m := Nat.le_refl _

noncomputable def timePolynomial (leftCount rightCount width : Nat) : Polynomial Nat :=
  MachineTemplateAddress.timePolynomial leftCount width +
    MachineTemplateAddress.timePolynomial rightCount width +
    2 * (Polynomial.X + 1) ^ width + 4 * Polynomial.X + 12

omit [DecidableEq K] in
theorem timePolynomial_eval (leftCount rightCount width M : Nat) :
    (timePolynomial leftCount rightCount width).eval M =
      (MachineTemplateAddress.timePolynomial leftCount width).eval M +
      (MachineTemplateAddress.timePolynomial rightCount width).eval M +
      2 * (M + 1) ^ width + 4 * M + 12 := by
  simp [timePolynomial]

omit [DecidableEq K] in
theorem radix_le_magnitude (B : Nat) (values : List Nat) (width M : Nat)
    (hlen : values.length = width) (radixBound : B ≤ M)
    (digitBound : ∀ i, i < width → MachineTemplateAddress.digits values i ≤ M) :
    CanonicalAddress.radix B values ≤ (M + 1) ^ width := by
  have h := MachineHorner.value_le B (MachineTemplateAddress.digits values) values.length M
    radixBound (by simpa only [hlen] using digitBound) values.length (Nat.le_refl _)
  rw [MachineTemplateAddress.hornerValue_eq_radix, hlen] at h
  exact h

theorem phaseSteps_le_timePolynomial (left right : List (MachineFieldTemplate.Token q))
    (slots : Tape q width ↪ K) (base : K → List Bool) (B C : Nat)
    (leftValues rightValues : List Nat)
    (leftLength : leftValues.length = width) (rightLength : rightValues.length = width)
    (clean : Clean slots base) (M : Nat)
    (fieldsBound : ∀ j, (base (addressSlots slots (.field j))).length ≤ M)
    (leftWordsBound : (encodeWords leftValues).length ≤ M)
    (rightWordsBound : (encodeWords rightValues).length ≤ M)
    (radixBound : B ≤ M) (capacityBound : C ≤ M)
    (leftDigitBound : ∀ i, i < width → MachineTemplateAddress.digits leftValues i ≤ M)
    (rightDigitBound : ∀ i, i < width → MachineTemplateAddress.digits rightValues i ≤ M) :
    phaseSteps left right slots base B C leftValues rightValues ≤
      (timePolynomial left.length right.length width).eval M := by
  have hleft := MachineTemplateAddress.phaseSteps_le_timePolynomial left (addressSlots slots)
    base B leftValues leftLength clean.address M fieldsBound leftWordsBound radixBound leftDigitBound
  have hright := MachineTemplateAddress.phaseSteps_le_timePolynomial right (addressSlots slots)
    (appended slots base (encodeWord (CanonicalAddress.radix B leftValues))) B rightValues
    rightLength (Clean.appended slots base clean _).address M
    (by simpa only [appended_address] using fieldsBound) rightWordsBound radixBound rightDigitBound
  have hlrank := radix_le_magnitude B leftValues width M leftLength radixBound leftDigitBound
  have hrrank := radix_le_magnitude B rightValues width M rightLength radixBound rightDigitBound
  rw [timePolynomial_eval]
  unfold phaseSteps
  omega

end DFVSGames.Reduction.MachineAddressEdge
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
