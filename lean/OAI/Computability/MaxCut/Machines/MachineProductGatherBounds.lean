import Mathlib
import OAI.Computability.MaxCut.Games.Product
import OAI.Computability.MaxCut.Machines.MachineHorner

namespace OAI

/-! Bounds on the actual work stacks left by the preserving gather. These
bounds justify clearing the query/scan remnants after each product field;
they are consequences of the exact tape formulas, not runtime assumptions. -/

namespace MaxCutGames.Explicit.MachineProductGather

open MaxCutGames.Foundations.Complexity

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

/-- One field query adds at most one table's worth of bits to any tape.
A width-fold gather therefore has a uniform linear-in-width space bound. -/
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

end MaxCutGames.Explicit.MachineProductGather

/-! The product-field machine restores every work tape and appends precisely
one field to the reversed output. This boundary is strong enough to compose
all fields and every odometer visit without retaining an unbounded history. -/

namespace MaxCutGames.Explicit.MachineProductField

open MaxCutGames.Foundations.Complexity
open MaxCutGames.Reduction.MachineTransfer

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

end MaxCutGames.Explicit.MachineProductField

/-! A finite row-field schedule. Endpoint fields use the input vertex radix;
permutation fields use the fixed alphabet radix. The complete list of columns
is in finite control, while all row indices, table entries and radix magnitudes
remain data on tapes. -/

namespace MaxCutGames.Explicit.MachineProductRow

open Turing
open MaxCutGames.Foundations.Complexity
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

end MaxCutGames.Explicit.MachineProductRow

/-!
The exact table lookups and field schedule consumed by the product machine.
The table contains rows only: the three input header words have already been
consumed, so each affine lookup has coefficient `q+2` and no header offset.
-/

namespace MaxCutGames.Explicit.ProductMachineSemantics

open MaxCutGames.Foundations
open Target
open Complexity
open MachineOutputContract

variable {n q t : ℕ}

/-- Indexing a flattened constant-width row list preserves the literal field
position, not merely the multiset of row contents. -/
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

/-- The complete fixed-alphabet row schedule: two endpoints followed by every
forward-table entry in increasing numeric label order. -/
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

/-- Every scheduled lookup selects an actual word in the input table. -/
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

/-- The controller's literal field-command output is the serialized semantic
row, including every forward permutation-table entry. -/
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

/-- Product rows are emitted in ascending radix address, exactly the literal
order of the output constraint list. -/
def allRowsBits (H : Instance q) (t : ℕ) : List Bool :=
  (List.finRange (H.constraints.length ^ t)).flatMap (fun i =>
    MachineProductRow.rowBits (fieldValue H (finFunctionFinEquiv.symm i)) (commands q t))

theorem allRowsBits_eq (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) :
    allRowsBits H t = encodeWords
      ((ProductPaddedOutput.output H presentation t ht).constraints.flatMap constraintWords) := by
  unfold allRowsBits
  simp_rw [rowBits_eq H presentation t ht]
  rw [ProductPaddedOutput.output_constraints]
  have hrows : List.ofFn (ProductPaddedOutput.outputRow H presentation t ht) =
      (List.finRange (H.constraints.length ^ t)).map
        (ProductPaddedOutput.outputRow H presentation t ht) := by
    simp [List.finRange, List.map_ofFn, Function.comp_def]
  erw [hrows, List.flatMap_map, encodeWords_flatMap_inline_ProductMachineSemantics]
  rfl

/-- Concatenating the three computed headers and all physical row fields yields
precisely the target serialization, including list order and full tables. -/
theorem gameBits_eq (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) :
    encodeWords [H.vertices ^ t, q ^ t, H.constraints.length ^ t] ++ allRowsBits H t =
      gameBits (ProductPaddedOutput.output H presentation t ht) := by
  rw [gameBits, ProductPaddedOutput.output_gameWords, encodeWords_append,
    allRowsBits_eq H presentation t ht, ProductPaddedOutput.output_constraints]
  rfl

end MaxCutGames.Explicit.ProductMachineSemantics

/-! Actual power-header emission by fixed-width Horner evaluation of
`[1,0,...,0]`, followed by physical transfer to the reverse accumulator. -/

namespace MaxCutGames.Explicit.MachineProductPower

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer

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

end MaxCutGames.Explicit.MachineProductPower

end OAI
