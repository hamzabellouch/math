import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineUnaryAdd

namespace OAI


namespace DFVSGames.Explicit.MachineProductField

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition
open DFVSGames.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K] {width : Nat}

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
  · apply slots.injective.ne; simp []
  · apply slots.injective.ne; simp []
  · intro j; apply slots.injective.ne; simp []

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
    (slots (.inr 5)) (slots (.inr 6)) (slots.injective.ne (by simp [])) id false
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

end DFVSGames.Explicit.MachineProductField


namespace DFVSGames.Explicit.MachineProductGather

open DFVSGames.Foundations.Complexity

variable {K : Type} [DecidableEq K]

theorem affine_final_length (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (values : List Nat) (index value : Nat) (selected : values[index]? = some value)
    (base : K → List Bool) (k : K) :
    (MachineAffineLookup.finalTapes tape base values index value k).length ≤
      (base k).length + (encodeWords values).length + 1 := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b := fun h => hne (distinct h)
  have hov := MachineLookupSpec.output_length_le values index value selected
  have hdrop : (encodeWords (values.drop (index + 1))).length ≤ (encodeWords values).length := by
    have split : encodeWords (values.take (index + 1)) ++
        encodeWords (values.drop (index + 1)) = encodeWords values := by
      rw [← encodeWords_append, List.take_append_drop]
    have h := congrArg List.length split
    simp only [List.length_append] at h
    omega
  by_cases h1 : k = tape 1
  · subst k
    simp only [MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
      MachineLookup.tapes_index _ _ _ (hd 1 2 (by decide)) (hd 1 3 (by decide)),
      List.length_append, encodeWord_length]
    omega
  · by_cases h2 : k = tape 2
    · subst k
      simp only [MachineAffineLookup.finalTapes, MachinePreservingLookup.finalTapes,
        MachineLookup.tapes_source _ _ _ (hd 2 3 (by decide)), List.length_append]
      omega
    · by_cases h3 : k = tape 3
      · subst k
        rw [MachineAffineLookup.finalTapes_output, List.length_append]
        omega
      · rw [MachineAffineLookup.finalTapes_other _ _ _ _ _ _ h1 h2 h3]
        omega

theorem finalTapes_length (values : List Nat) (coefficient width : Nat)
    (placement : Tape width → K) (distinct : Function.Injective placement)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (base : K → List Bool) (k : K) :
    (finalTapes values coefficient width placement indices offsets fields base k).length ≤
      (base k).length + width * ((encodeWords values).length + 1) := by
  induction width generalizing base with
  | zero => simp [finalTapes]
  | succ width ih =>
    let mid := MachineAffineLookup.finalTapes (placement ∘ lookupRole width) base values
      (coefficient * indices 0 + offsets 0) (fields 0)
    have first := affine_final_length (placement ∘ lookupRole width)
      (distinct.comp (lookupRole_injective width)) values
      (coefficient * indices 0 + offsets 0) (fields 0) (selected 0) base k
    have rest := ih (placement ∘ shift width) (distinct.comp (shift_injective width))
      (fun i => indices i.succ) (fun i => offsets i.succ) (fun i => fields i.succ)
      (fun i => selected i.succ) mid
    change (finalTapes values coefficient width (placement ∘ shift width)
      (fun i => indices i.succ) (fun i => offsets i.succ) (fun i => fields i.succ) mid k).length ≤ _
    rw [Nat.add_mul, Nat.one_mul]
    dsimp only [mid] at rest
    dsimp only [mid]
    omega

end DFVSGames.Explicit.MachineProductGather


namespace DFVSGames.Explicit.MachineProductField

open DFVSGames.Foundations.Complexity
open DFVSGames.Reduction.MachineTransfer

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

end DFVSGames.Explicit.MachineProductField


namespace DFVSGames.Explicit.MachineProductRow

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {width : Nat}

abbrev Layout (width : Nat) := MachineProductField.Layout width ⊕ Unit
abbrev Command (width : Nat) := Bool × (Fin width → Nat)

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

end DFVSGames.Explicit.MachineProductRow


namespace DFVSGames.Explicit.ProductMachineSemantics

open DFVSGames.Foundations
open Target
open Complexity
open MachineOutputContract

variable {n q t : ℕ}

theorem row_table_lookup (constraints : List (Constraint n q))
    (e : Fin constraints.length) (field : Fin (q + 2)) :
    (constraints.flatMap constraintWords)[(q + 2) * e.val + field.val]? =
      (constraintWords constraints[e])[field.val]? := by
  induction constraints with
  | nil => exact Fin.elim0 e
  | cons c constraints ih =>
    refine Fin.cases ?_ (fun i => ?_) e
    · simp [List.flatMap_cons, List.getElem?_append, constraintWords_length, field.isLt]
    · rw [List.flatMap_cons, List.getElem?_append]
      have hlarge : ¬ (q + 2) * i.succ.val + field.val < (constraintWords c).length := by
        simp only [Fin.val_succ, constraintWords_length, Nat.mul_succ]
        omega
      rw [ite_eq_right hlarge]
      have hindex : (q + 2) * i.succ.val + field.val - (constraintWords c).length =
          (q + 2) * i.val + field.val := by
        simp only [Fin.val_succ, constraintWords_length, Nat.mul_succ]
        omega
      rw [hindex]
      exact ih i

def inputTable (H : Instance q) : List ℕ := H.constraints.flatMap constraintWords

theorem inputTable_source (H : Instance q) (e : Fin H.constraints.length) :
    (inputTable H)[(q + 2) * e.val]? = some H.constraints[e].source.val := by
  have h := row_table_lookup H.constraints e (⟨0, by omega⟩ : Fin (q + 2))
  simpa [inputTable, constraintWords] using h

theorem inputTable_target (H : Instance q) (e : Fin H.constraints.length) :
    (inputTable H)[(q + 2) * e.val + 1]? = some H.constraints[e].target.val := by
  have h := row_table_lookup H.constraints e (⟨1, by omega⟩ : Fin (q + 2))
  simpa [inputTable, constraintWords] using h

theorem inputTable_image (H : Instance q) (e : Fin H.constraints.length) (a : Fin q) :
    (inputTable H)[(q + 2) * e.val + (2 + a.val)]? =
      some (H.constraints[e].permutation.images[a]).val := by
  have h := row_table_lookup H.constraints e (⟨2 + a.val, by omega⟩ : Fin (q + 2))
  simpa [inputTable, constraintWords, tableWords, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using h

def reverseDigits (fields : Fin t → ℕ) (i : ℕ) : ℕ :=
  if h : i < t then fields (Fin.rev ⟨i, h⟩) else 0

@[simp] theorem reverseDigits_at (fields : Fin t → ℕ) (i : Fin t) :
    reverseDigits fields i.val = fields i.rev := by simp [reverseDigits, i.isLt]

theorem reverseDigits_words (fields : Fin t → ℕ) :
    (List.range t).map (reverseDigits fields) = (List.ofFn fields).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i < t := by simpa using hi
    simp only [List.getElem_map, List.getElem_range, reverseDigits, hi', ↓reduceDIte,
      List.getElem_reverse, List.getElem_ofFn, List.length_ofFn, Fin.rev]
    apply congrArg fields
    apply Fin.ext
    change t - (i + 1) = t - 1 - i
    omega

theorem horner_ofFin {radix : ℕ} (fields : Fin t → Fin radix) :
    MachineHorner.value radix (reverseDigits (fun i => (fields i : ℕ))) t =
      (finFunctionFinEquiv fields : ℕ) := by
  rw [MachineHorner.value_eq_foldl, reverseDigits_words,
    ← ProductTarget.address_eq_horner]

def sourceCommand (t : ℕ) : MachineProductRow.Command t := (false, fun _ => 0)
def targetCommand (t : ℕ) : MachineProductRow.Command t := (false, fun _ => 1)
def imageCommand (q t : ℕ) (a : Fin (q ^ t)) : MachineProductRow.Command t :=
  (true, fun i => 2 + (finFunctionFinEquiv.symm a i).val)

def commands (q t : ℕ) : List (MachineProductRow.Command t) :=
  sourceCommand t :: targetCommand t :: (List.finRange (q ^ t)).map (imageCommand q t)

theorem commands_length (q t : ℕ) : (commands q t).length = q ^ t + 2 := by
  simp [commands]

def fields (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (command : MachineProductRow.Command t) : Fin t → ℕ := fun j =>
  ((inputTable H)[(q + 2) * (edges j).val + command.2 j]?).getD 0

def fieldValue (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (command : MachineProductRow.Command t) : ℕ :=
  MachineHorner.value (if command.1 then q else H.vertices)
    (reverseDigits (fields H edges command)) t

theorem source_fields (H : Instance q) (edges : Fin t → Fin H.constraints.length) :
    fields H edges (sourceCommand t) = fun j => H.constraints[edges j].source.val := by
  funext j
  simp [fields, sourceCommand, inputTable_source]

theorem target_fields (H : Instance q) (edges : Fin t → Fin H.constraints.length) :
    fields H edges (targetCommand t) = fun j => H.constraints[edges j].target.val := by
  funext j
  simp [fields, targetCommand, inputTable_target]

theorem image_fields (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (a : Fin (q ^ t)) :
    fields H edges (imageCommand q t a) = fun j =>
      (H.constraints[edges j].permutation.images[finFunctionFinEquiv.symm a j]).val := by
  funext j
  unfold fields imageCommand
  rw [inputTable_image H (edges j) (finFunctionFinEquiv.symm a j)]
  rfl

theorem selected (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (c : MachineProductRow.Command t) (hc : c ∈ commands q t) (i : Fin t) :
    (inputTable H)[(q + 2) * (edges i).val + c.2 i]? =
      some (fields H edges c i) := by
  rcases List.mem_cons.mp hc with rfl | hc
  · simp [fields, sourceCommand, inputTable_source]
  rcases List.mem_cons.mp hc with rfl | hc
  · simp [fields, targetCommand, inputTable_target]
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
  rw [image_fields]
  exact inputTable_image H (edges i) (finFunctionFinEquiv.symm a i)

theorem command_offset_lt (c : MachineProductRow.Command t)
    (hc : c ∈ commands q t) (i : Fin t) : c.2 i < q + 2 := by
  rcases List.mem_cons.mp hc with rfl | hc
  · simp [sourceCommand]
  rcases List.mem_cons.mp hc with rfl | hc
  · simp [targetCommand]
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
  have h := (finFunctionFinEquiv.symm a i).isLt
  simp only [imageCommand]
  omega

theorem fields_lt (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (c : MachineProductRow.Command t) (hc : c ∈ commands q t) (i : Fin t) :
    fields H edges c i < if c.1 then q else H.vertices := by
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [source_fields]
    exact H.constraints[edges i].source.isLt
  rcases List.mem_cons.mp hc with rfl | hc
  · rw [target_fields]
    exact H.constraints[edges i].target.isLt
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
  rw [image_fields]
  exact (H.constraints[edges i].permutation.images[finFunctionFinEquiv.symm a i]).isLt

theorem source_value (H : Instance q) (edges : Fin t → Fin H.constraints.length) :
    fieldValue H edges (sourceCommand t) =
      (finFunctionFinEquiv (fun j => H.constraints[edges j].source) : ℕ) := by
  unfold fieldValue
  rw [source_fields]
  exact horner_ofFin (fun j => H.constraints[edges j].source)

theorem target_value (H : Instance q) (edges : Fin t → Fin H.constraints.length) :
    fieldValue H edges (targetCommand t) =
      (finFunctionFinEquiv (fun j => H.constraints[edges j].target) : ℕ) := by
  unfold fieldValue
  rw [target_fields]
  exact horner_ofFin (fun j => H.constraints[edges j].target)

theorem image_value (H : Instance q) (edges : Fin t → Fin H.constraints.length)
    (a : Fin (q ^ t)) :
    fieldValue H edges (imageCommand q t a) =
      (finFunctionFinEquiv (fun j =>
        H.constraints[edges j].permutation.images[finFunctionFinEquiv.symm a j]) : ℕ) := by
  unfold fieldValue
  rw [image_fields]
  exact horner_ofFin (fun j =>
    H.constraints[edges j].permutation.images[finFunctionFinEquiv.symm a j])

private theorem encodeWords_map_inline_ProductMachineSemantics {X : Type*} (xs : List X) (f : X → ℕ) :
    encodeWords (xs.map f) = xs.flatMap (fun x => encodeWord (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeWords, ih]

theorem rowBits_eq (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) (i : Fin (H.constraints.length ^ t)) :
    MachineProductRow.rowBits (fieldValue H (finFunctionFinEquiv.symm i)) (commands q t) =
      encodeWords (constraintWords (ProductPaddedOutput.outputRow H presentation t ht i)) := by
  have hsource : fieldValue H (finFunctionFinEquiv.symm i) (sourceCommand t) =
      (ProductPaddedOutput.outputRow H presentation t ht i).source.val := source_value _ _
  have htarget : fieldValue H (finFunctionFinEquiv.symm i) (targetCommand t) =
      (ProductPaddedOutput.outputRow H presentation t ht i).target.val := target_value _ _
  have himage (a : Fin (q ^ t)) :
      fieldValue H (finFunctionFinEquiv.symm i) (imageCommand q t a) =
      ((ProductPaddedOutput.outputRow H presentation t ht i).permutation.images[a]).val := by
    rw [ProductPaddedOutput.outputRow_images]
    exact image_value _ _ _
  simp only [MachineProductRow.rowBits, commands, List.flatMap_cons, List.flatMap_map,
    hsource, htarget, himage, constraintWords, encodeWords_append, encodeWords,
    List.append_nil, List.append_assoc]
  congr 2
  have htable : tableWords (ProductPaddedOutput.outputRow H presentation t ht i).permutation =
      (List.finRange (q ^ t)).map
        (fun a => ((ProductPaddedOutput.outputRow H presentation t ht i).permutation.images[a]).val) := by
    apply List.ext_getElem
    · simp [tableWords]
    · intro j hj hk
      simp [tableWords, Fin.getElem_fin]
  rw [htable, encodeWords_map_inline_ProductMachineSemantics]

private theorem encodeWords_flatMap_inline_ProductMachineSemantics {X : Type*} (xs : List X) (f : X → List ℕ) :
    encodeWords (xs.flatMap f) = xs.flatMap (fun x => encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeWords_append, ih]

def allRowsBits (H : Instance q) (t : ℕ) : List Bool :=
  (List.finRange (H.constraints.length ^ t)).flatMap (fun i =>
    MachineProductRow.rowBits (fieldValue H (finFunctionFinEquiv.symm i)) (commands q t))

theorem allRowsBits_eq (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) :
    allRowsBits H t = encodeWords
      ((ProductPaddedOutput.output H presentation t ht).constraints.flatMap constraintWords) := by
  change allRowsBits H t = encodeWords
    ((List.ofFn (ProductPaddedOutput.outputRow H presentation t ht)).flatMap constraintWords)
  unfold allRowsBits
  simp_rw [rowBits_eq H presentation t ht]
  have hrows : List.ofFn (ProductPaddedOutput.outputRow H presentation t ht) =
      (List.finRange (H.constraints.length ^ t)).map
        (ProductPaddedOutput.outputRow H presentation t ht) := by
    simp [List.finRange, List.map_ofFn, Function.comp_def]
  rw [hrows, List.flatMap_map, encodeWords_flatMap_inline_ProductMachineSemantics]

theorem gameBits_eq (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) :
    encodeWords [H.vertices ^ t, q ^ t, H.constraints.length ^ t] ++ allRowsBits H t =
      gameBits (ProductPaddedOutput.output H presentation t ht) := by
  rw [gameBits, ProductPaddedOutput.output_gameWords, encodeWords_append,
    allRowsBits_eq H presentation t ht, ProductPaddedOutput.output_constraints]
  rfl

end DFVSGames.Explicit.ProductMachineSemantics

end OAI
