import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineCopy
import OAI.Computability.UniqueGames.Machines.MachineDrain
import OAI.Computability.UniqueGames.Machines.MachineUnaryAddAt
import OAI.Computability.UniqueGames.Reduction.MachineRhsLoad
import OAI.Computability.UniqueGames.Reduction.MachineTemplateAddress

namespace OAI

/-! Actual edge emission from two fixed address templates. Capacity is copied
before unary addition, so the original capacity tape is preserved. All local
labels and literal instructions depend only on fixed templates and layout. -/

namespace UniqueGamesTheorem.Reduction.MachineAddressEdge

open Turing
open UniqueGamesTheorem.Foundations.Complexity
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

/-- Both actual address computations, a preserved-capacity copy, unary addition,
cleanup, two reverse transfers, and the fixed permutation instruction. -/
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

/-- A fixed polynomial in a common magnitude bound for the input fields,
serialized words, radix, capacity, and digits. -/
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

end UniqueGamesTheorem.Reduction.MachineAddressEdge

/-! Execute all fixed outcome rows after the existing RHS loader. A single
dispatcher freezes the loaded finite RHS vector into labels. Every row is an
actual address-edge phase; no row-run or whole-loop execution is assumed.
Program definitions contain only fixed templates, literal permutations, and
tape/label placement. Numeric names, radix, and capacity occur only in tapes
and the semantic correctness hypotheses. -/

namespace UniqueGamesTheorem.Reduction.MachineOutcomeRows

open Turing
open UniqueGamesTheorem.Foundations.Complexity

structure Spec (q width : Nat) where
  left : List (MachineFieldTemplate.Token q)
  right : List (MachineFieldTemplate.Token q)
  permutation : List Bool

/-- Numeric interpretations are proof-side data, separate from the program. -/
structure Values (width : Nat) where
  left : List Nat
  right : List Nat
  left_length : left.length = width
  right_length : right.length = width

abbrev Rhs (k : Nat) := Fin k → Bool
abbrev Row (k q width : Nat) := Rhs k → Spec q width
abbrev State (k : Nat) (σ : Type) := MachineRhsLoad.State k σ
abbrev Alphabet {K : Type} (_ : K) := Bool

variable {k q width : Nat} {K Λ σ : Type} [DecidableEq K]

abbrev LocalLabel (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :=
  MachineAddressEdge.Label row.left.length row.right.length width
    (MachineTemplateAddress.chosen (MachineAddressEdge.addressSlots slots))

def localMain (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :
    LocalLabel slots row :=
  MachineAddressEdge.leftLabel (MachineTemplateAddress.emitLabel
    (MachineFieldTemplate.startAt row.left.length 0))

def localInstruction (slots : MachineAddressEdge.Tape q width ↪ K)
    (row : Spec q width) (place : LocalLabel slots row → Λ) (exit : Option Λ) :
    LocalLabel slots row → TM2.Stmt (Alphabet (K := K)) Λ (MachineAddressEdge.State σ) :=
  MachineAddressEdge.instruction row.left row.right row.permutation slots place exit

def payload (B C : Nat) (values : Spec q width → Values width) (row : Spec q width) :
    List Bool :=
  MachineAddressEdge.edgeBits B C (values row).left (values row).right row.permutation

def rowResult (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (row : Spec q width)
    (base : K → List Bool) : K → List Bool :=
  MachineAddressEdge.appended slots base (payload B C values row)

def rowCost (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (row : Spec q width)
    (base : K → List Bool) : Nat :=
  MachineAddressEdge.phaseSteps row.left row.right slots base B C
    (values row).left (values row).right

/-- Exact per-row costs at their actual accumulated output frames. -/
def rowCosts (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) :
    List (Spec q width) → (K → List Bool) → List Nat
  | [], _ => []
  | row :: rows, base => rowCost slots B C values row base ::
      rowCosts slots B C values rows (rowResult slots B C values row base)

theorem rowCosts_length (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width)
    (rows : List (Spec q width)) (base : K → List Bool) :
    (rowCosts slots B C values rows base).length = rows.length := by
  induction rows generalizing base with
  | nil => rfl
  | cons row rows ih => simp only [rowCosts, List.length_cons, ih]

structure Invariant (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) : Prop where
  clean : MachineAddressEdge.Clean slots base
  radix : base (MachineAddressEdge.addressSlots slots .radix) = encodeWord B
  capacity : base (MachineAddressEdge.capacityTape slots) = encodeWord C
  correct : ∀ row ∈ rows,
    MachineFieldTemplate.templateOutput row.left
      (fun j => base (MachineAddressEdge.addressSlots slots (.field j))) =
        encodeWords (values row).left ∧
    MachineFieldTemplate.templateOutput row.right
      (fun j => base (MachineAddressEdge.addressSlots slots (.field j))) =
        encodeWords (values row).right

theorem Invariant.appended (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) (valid : Invariant slots B C values rows base) (bits : List Bool) :
    Invariant slots B C values rows (MachineAddressEdge.appended slots base bits) := by
  constructor
  · exact MachineAddressEdge.Clean.appended slots base valid.clean bits
  · simpa only [MachineAddressEdge.appended_address] using valid.radix
  · simpa only [MachineAddressEdge.appended_capacity] using valid.capacity
  · intro row hrow
    simpa only [MachineAddressEdge.appended_address] using valid.correct row hrow

theorem appended_nil (slots : MachineAddressEdge.Tape q width ↪ K) (base : K → List Bool) :
    MachineAddressEdge.appended slots base [] = base := by
  simp [MachineAddressEdge.appended, MachineFieldTemplate.outputTapes]

theorem sequence_result (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) :
    MachineFiniteSequence.resultOf (rowResult slots B C values) rows base =
      MachineAddressEdge.appended slots base (rows.flatMap (payload B C values)) := by
  induction rows generalizing base with
  | nil => simpa only [MachineFiniteSequence.resultOf, List.flatMap_nil] using
      (appended_nil slots base).symm
  | cons row rows ih =>
    rw [MachineFiniteSequence.resultOf, ih]
    exact MachineAddressEdge.appended_append slots base _ _

theorem sequence_steps (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) :
    MachineFiniteSequence.steps (rowResult slots B C values) (rowCost slots B C values)
      rows base = (rowCosts slots B C values rows base).sum := by
  induction rows generalizing base with
  | nil => rfl
  | cons row rows ih => simp only [MachineFiniteSequence.steps, rowCosts, List.sum_cons, ih]

def sequenceInstruction (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width))
    (place : MachineFiniteSequence.Label (LocalLabel slots) rows → Λ) (exit : Option Λ) :=
  MachineFiniteSequence.instruction (LocalLabel slots) (localMain slots)
    (localInstruction (σ := σ) slots) rows place exit

/-- The generic finite-sequence local obligation is discharged by the concrete
edge program, including its address arithmetic and capacity restoration. -/
theorem sequenceTrace (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width))
    (place : MachineFiniteSequence.Label (LocalLabel slots) rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (MachineAddressEdge.State σ))
    (atInstruction : ∀ label, P (place label) = sequenceInstruction slots rows place exit label)
    (base : K → List Bool) (B C : Nat) (values : Spec q width → Values width)
    (valid : Invariant slots B C values rows base) (ambient : σ) :
    (MachineComposition.advance (TM2.step P))^[(rowCosts slots B C values rows base).sum]
      (some ⟨MachineFiniteSequence.entry (LocalLabel slots) (localMain slots) rows place exit,
        ((ambient, ()), none), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        MachineAddressEdge.appended slots base (rows.flatMap (payload B C values))⟩ := by
  have h := MachineFiniteSequence.trace (LocalLabel slots) (localMain slots)
    (localInstruction (σ := σ) slots) (rowResult slots B C values) (rowCost slots B C values)
    P (Invariant slots B C values rows) (fun _ => ((ambient, ()), none)) id rows
    (by
      intro row _ frame hframe
      exact Invariant.appended slots B C values rows frame hframe (payload B C values row))
    (by
      intro row hrow labels next placement frame hframe
      exact MachineAddressEdge.phaseTrace row.left row.right row.permutation slots
        labels next P placement frame B C (values row).left (values row).right
        (values row).left_length (values row).right_length hframe.clean hframe.radix
        hframe.capacity (hframe.correct row hrow).1 (hframe.correct row hrow).2 ambient none)
    place exit atInstruction base valid
  simpa only [sequence_steps, sequence_result, id_eq] using h

def selected (rows : List (Row k q width)) (rhs : Rhs k) : List (Spec q width) :=
  rows.map (fun row => row rhs)

@[simp] theorem selected_length (rows : List (Row k q width)) (rhs : Rhs k) :
    (selected rows rhs).length = rows.length := by simp [selected]

abbrev Label (slots : MachineAddressEdge.Tape q width ↪ K) (rows : List (Row k q width)) :=
  Unit ⊕ (Σ rhs : Rhs k, MachineFiniteSequence.Label (LocalLabel slots) (selected rows rhs))

instance localLabelFintype (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :
    Fintype (LocalLabel slots row) := by unfold LocalLabel; infer_instance

instance localLabelDecidableEq (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :
    DecidableEq (LocalLabel slots row) := by
  letI : DecidableEq (MachineTemplateAddress.Label row.left.length width
      (MachineTemplateAddress.chosen (MachineAddressEdge.addressSlots slots))) := by
    infer_instance
  letI : DecidableEq (MachineTemplateAddress.Label row.right.length width
      (MachineTemplateAddress.chosen (MachineAddressEdge.addressSlots slots))) := by
    infer_instance
  dsimp only [LocalLabel, MachineAddressEdge.Label]
  infer_instance

instance labelFintype (slots : MachineAddressEdge.Tape q width ↪ K) (rows : List (Row k q width)) :
    Fintype (Label slots rows) := by unfold Label; infer_instance

instance labelDecidableEq (slots : MachineAddressEdge.Tape q width ↪ K) (rows : List (Row k q width)) :
    DecidableEq (Label slots rows) := by unfold Label; infer_instance

def sequenceEntry (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (rhs : Rhs k)
    (place : Label slots rows → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (LocalLabel slots) (localMain slots) (selected rows rhs)
    (fun label => place (.inr ⟨rhs, label⟩)) exit

/-- Reuse the RHS vector already loaded by `MachineRhsLoad`; dispatch takes
one real transition, and resets only the optional temporary bit. -/
def dispatcher (slots : MachineAddressEdge.Tape q width ↪ K) :
    (rows : List (Row k q width)) → (Label slots rows → Λ) → Option Λ →
      TM2.Stmt (Alphabet (K := K)) Λ (State k σ)
  | [], _, exit => .load MachineFieldTemplate.reset (MachineFieldTemplate.jump exit)
  | row :: _rows, place, _ => .load MachineFieldTemplate.reset
      (.goto fun state => place (.inr ⟨MachineRhsLoad.rhs state,
        .inl (localMain slots (row (MachineRhsLoad.rhs state)))⟩))

def instruction (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ) :
    Label slots rows → TM2.Stmt (Alphabet (K := K)) Λ (State k σ)
  | .inl _ => dispatcher slots rows place exit
  | .inr ⟨rhs, label⟩ => sequenceInstruction slots (selected rows rhs)
      (fun l => place (.inr ⟨rhs, l⟩)) exit label

def program (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (exit : Option (Label slots rows)) :=
  instruction (σ := σ) slots rows id exit

theorem dispatcherStep (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atDispatcher : P (place (.inl ())) = dispatcher slots rows place exit)
    (base : K → List Bool) (rhs : Rhs k) (ambient : σ) (register : Option Bool) :
    TM2.step P ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩ =
      some ⟨sequenceEntry slots rows rhs place exit, (((rhs, ambient), ()), none), base⟩ := by
  change some (TM2.stepAux (P (place (.inl ()))) (((rhs, ambient), ()), register) base) = _
  rw [atDispatcher]
  cases rows with
  | nil => cases exit <;> rfl
  | cons row rows => rfl

theorem phaseTrace (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atInstruction : ∀ label, P (place label) = instruction slots rows place exit label)
    (base : K → List Bool) (rhs : Rhs k) (ambient : σ) (register : Option Bool)
    (B C : Nat) (values : Spec q width → Values width)
    (valid : Invariant slots B C values (selected rows rhs) base) :
    (MachineComposition.advance (TM2.step P))^[
      (rowCosts slots B C values (selected rows rhs) base).sum + 1]
      (some ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩) =
      some ⟨exit, (((rhs, ambient), ()), none), MachineAddressEdge.appended slots base
        ((selected rows rhs).flatMap (payload B C values))⟩ := by
  have first := dispatcherStep slots rows place exit P (atInstruction (.inl ()))
    base rhs ambient register
  have rest := sequenceTrace slots (selected rows rhs) (fun l => place (.inr ⟨rhs, l⟩))
    exit P (fun l => atInstruction (.inr ⟨rhs, l⟩)) base B C values valid (rhs, ambient)
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step P))^[_]
    (TM2.step P ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩) = _
  rw [first]
  exact rest

def phaseInTime (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atInstruction : ∀ label, P (place label) = instruction slots rows place exit label)
    (base : K → List Bool) (rhs : Rhs k) (ambient : σ) (register : Option Bool)
    (B C : Nat) (values : Spec q width → Values width)
    (valid : Invariant slots B C values (selected rows rhs) base) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩
      (some ⟨exit, (((rhs, ambient), ()), none), MachineAddressEdge.appended slots base
        ((selected rows rhs).flatMap (payload B C values))⟩)
      ((rowCosts slots B C values (selected rows rhs) base).sum + 1) where
  steps := (rowCosts slots B C values (selected rows rhs) base).sum + 1
  evals_in_steps := phaseTrace slots rows place exit P atInstruction base rhs ambient register
    B C values valid
  steps_le_m := Nat.le_refl _

theorem emitted_output (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (rhs : Rhs k) (base : K → List Bool)
    (B C : Nat) (values : Spec q width → Values width) :
    MachineAddressEdge.appended slots base ((selected rows rhs).flatMap (payload B C values))
        (MachineAddressEdge.outputTape slots) =
      ((selected rows rhs).flatMap (payload B C values)).reverse ++
        base (MachineAddressEdge.outputTape slots) :=
  MachineAddressEdge.appended_output slots base _

theorem exact_row_count (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (rhs : Rhs k) (base : K → List Bool)
    (B C : Nat) (values : Spec q width → Values width) :
    (rowCosts slots B C values (selected rows rhs) base).length = rows.length := by
  rw [rowCosts_length, selected_length]

/-- Sum of fixed row polynomials; the additional constant is the dispatcher.
This proof-side polynomial contains no runtime input field values. -/
noncomputable def timePolynomial (rows : List (Spec q width)) : Polynomial Nat :=
  (rows.map (fun row => MachineAddressEdge.timePolynomial
    row.left.length row.right.length width)).sum + 1

theorem rowCosts_sum_le (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width)) (base : K → List Bool)
    (B C : Nat) (values : Spec q width → Values width) (M : Nat)
    (clean : MachineAddressEdge.Clean slots base)
    (fieldsBound : ∀ j, (base (MachineAddressEdge.addressSlots slots (.field j))).length ≤ M)
    (radixBound : B ≤ M) (capacityBound : C ≤ M)
    (valuesBound : ∀ row ∈ rows,
      (encodeWords (values row).left).length ≤ M ∧
      (encodeWords (values row).right).length ≤ M ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).left i ≤ M) ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).right i ≤ M)) :
    (rowCosts slots B C values rows base).sum ≤
      ((rows.map (fun row => MachineAddressEdge.timePolynomial
        row.left.length row.right.length width)).sum).eval M := by
  induction rows generalizing base with
  | nil => simp [rowCosts]
  | cons row rows ih =>
    have bounds := valuesBound row (by simp)
    have first := MachineAddressEdge.phaseSteps_le_timePolynomial row.left row.right
      slots base B C (values row).left (values row).right
      (values row).left_length (values row).right_length clean M fieldsBound
      bounds.1 bounds.2.1 radixBound capacityBound bounds.2.2.1 bounds.2.2.2
    have rest := ih (rowResult slots B C values row base)
      (MachineAddressEdge.Clean.appended slots base clean (payload B C values row))
      (by simpa only [rowResult, MachineAddressEdge.appended_address] using fieldsBound)
      (fun r hr => valuesBound r (List.mem_cons_of_mem row hr))
    simpa only [rowCosts, List.sum_cons, List.map_cons, Polynomial.eval_add, rowCost] using
      Nat.add_le_add first rest

/-- The actual dispatcher-and-rows count is bounded by a fixed polynomial in
explicit tape and digit magnitudes, using the checked edge arithmetic bound. -/
theorem phaseCost_le_timePolynomial (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width)) (base : K → List Bool)
    (B C : Nat) (values : Spec q width → Values width) (M : Nat)
    (clean : MachineAddressEdge.Clean slots base)
    (fieldsBound : ∀ j, (base (MachineAddressEdge.addressSlots slots (.field j))).length ≤ M)
    (radixBound : B ≤ M) (capacityBound : C ≤ M)
    (valuesBound : ∀ row ∈ rows,
      (encodeWords (values row).left).length ≤ M ∧
      (encodeWords (values row).right).length ≤ M ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).left i ≤ M) ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).right i ≤ M)) :
    (rowCosts slots B C values rows base).sum + 1 ≤ (timePolynomial rows).eval M := by
  have h := rowCosts_sum_le slots rows base B C values M clean fieldsBound
    radixBound capacityBound valuesBound
  simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one] using
    Nat.add_le_add_right h 1

end UniqueGamesTheorem.Reduction.MachineOutcomeRows

end OAI
