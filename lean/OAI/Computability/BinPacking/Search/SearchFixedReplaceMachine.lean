import Mathlib.Tactic.DeriveFintype
import OAI.Computability.BinPacking.Search.SearchInitializeEncoding

namespace OAI

namespace BinPackingGap.SearchFixedReplaceMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinaryEncoding SearchEncoding

inductive Slot
  | source | index | payload | reversed
  deriving DecidableEq

protected abbrev Slot.enumList : List Slot := [.source, .index, .payload, .reversed]

protected theorem Slot.enumList_getElem?_ctorIdx_eq (x : Slot) :
    Slot.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Slot.enumList_nodup : Slot.enumList.Nodup := by decide

instance : Fintype Slot where
  elems := ⟨Slot.enumList, Slot.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Action
  | before | after | discard
  deriving DecidableEq

protected abbrev Action.enumList : List Action := [.before, .after, .discard]

protected theorem Action.enumList_getElem?_ctorIdx_eq (x : Action) :
    Action.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Action.enumList_nodup : Action.enumList.Nodup := by decide

instance : Fintype Action where
  elems := ⟨Action.enumList, Action.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Label
  | entry (searching : Bool)
  | index
  | option (action : Action)
  | name (action : Action)
  | digit (action : Action)
  | payload | payloadDigit
  | drainIndex | drainPayload | drainPayloadDigit
  deriving DecidableEq, Fintype

def Action.writes : Action → Bool
  | .before | .after => true
  | .discard => false

def Action.next : Action → Label
  | .before => .entry true
  | .after | .discard => .entry false

abbrev Words := Slot → List Bool
abbrev Register (A : Type) := A × Option Bool

def put (words : Words) (slot : Slot) (value : List Bool) : Words :=
  Function.update words slot value

def consume (words : Words) (slot : Slot) : Words := put words slot (words slot).tail

def emit (words : Words) (bit : Bool) : Words :=
  put words .reversed (bit :: words .reversed)

def saved (action : Action) (bits acc : List Bool) : List Bool :=
  if action.writes then bits.reverse ++ acc else acc

section Program

variable {K Λ A : Type} [DecidableEq K]

def finish (next : Option Λ) : TM2.Stmt (fun _ : K => Bool) Λ (Register A) :=
  .load (fun state => (state.1, none))
    (match next with | none => .halt | some label => .goto (fun _ => label))

def copyIf (action : Action) (output : K)
    (rest : TM2.Stmt (fun _ : K => Bool) Λ (Register A)) :
    TM2.Stmt (fun _ : K => Bool) Λ (Register A) :=
  if action.writes then .push output (fun state => state.2.getD false) rest else rest

def instruction (place : Slot → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (fun _ : K => Bool) Λ (Register A)
  | .entry searching => .pop (place .source) (fun state head => (state.1, head))
      (.push (place .reversed) (fun state => state.2.getD false)
        (.branch (fun state => state.2.getD false)
          (finish (some (labels (if searching then .index else .option .after))))
          (finish (if searching then some (labels .drainIndex) else exit))))
  | .index => .pop (place .index) (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (finish (some (labels (.option .before))))
        (.push (place .reversed) (fun _ => true) (finish (some (labels .payload)))))
  | .option action => .pop (place .source) (fun state head => (state.1, head))
      (copyIf action (place .reversed)
        (.branch (fun state => state.2.getD false)
          (finish (some (labels (.name action)))) (finish (some (labels action.next)))))
  | .name action => .pop (place .source) (fun state head => (state.1, head))
      (copyIf action (place .reversed)
        (.branch (fun state => state.2.getD false)
          (finish (some (labels (.digit action)))) (finish (some (labels action.next)))))
  | .digit action => .pop (place .source) (fun state head => (state.1, head))
      (copyIf action (place .reversed) (finish (some (labels (.name action)))))
  | .payload => .pop (place .payload) (fun state head => (state.1, head))
      (.push (place .reversed) (fun state => state.2.getD false)
        (.branch (fun state => state.2.getD false)
          (finish (some (labels .payloadDigit)))
          (finish (some (labels (.option .discard))))))
  | .payloadDigit => .pop (place .payload) (fun state head => (state.1, head))
      (.push (place .reversed) (fun state => state.2.getD false)
        (finish (some (labels .payload))))
  | .drainIndex => .pop (place .index) (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (finish (some (labels .drainIndex))) (finish (some (labels .drainPayload))))
  | .drainPayload => .pop (place .payload) (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (finish (some (labels .drainPayloadDigit))) (finish exit))
  | .drainPayloadDigit => .pop (place .payload) (fun state head => (state.1, head))
      (finish (some (labels .drainPayload)))

def tapes (place : Slot → K) (base : K → List Bool) (words : Words) : K → List Bool :=
  fun k => if k = place .source then words .source
    else if k = place .index then words .index
    else if k = place .payload then words .payload
    else if k = place .reversed then words .reversed else base k

variable (place : Slot → K) (distinct : Function.Injective place)

include distinct in
@[simp] theorem tapes_at (base : K → List Bool) (words : Words) (slot : Slot) :
    tapes place base words (place slot) = words slot := by
  cases slot <;> simp [tapes, distinct.eq_iff]

theorem tapes_other (base : K → List Bool) (words : Words) (k : K)
    (other : ∀ slot, k ≠ place slot) : tapes place base words k = base k := by
  simp [tapes, other]

include distinct in
theorem update_tapes (base : K → List Bool) (words : Words) (slot : Slot)
    (value : List Bool) :
    Function.update (tapes place base words) (place slot) value =
      tapes place base (put words slot value) := by
  funext k
  by_cases hs : k = place .source
  · subst k; cases slot <;> simp [tapes, put, distinct.eq_iff]
  by_cases hi : k = place .index
  · subst k; cases slot <;> simp [tapes, put, distinct.eq_iff]
  by_cases hp : k = place .payload
  · subst k; cases slot <;> simp [tapes, put, distinct.eq_iff]
  by_cases hr : k = place .reversed
  · subst k; cases slot <;> simp [tapes, put, distinct.eq_iff]
  cases slot <;> simp [tapes, hs, hi, hp, hr]

def configuration (labels : Label → Λ) (exit : Option Λ) (base : K → List Bool)
    (ambient : A) (label : Option Label) (words : Words) :
    TM2.Cfg (fun _ : K => Bool) Λ (Register A) :=
  ⟨match label with | none => exit | some label => some (labels label),
    (ambient, none), tapes place base words⟩

end Program

def next (label : Label) (words : Words) : Option Label × Words :=
  let input := (words .source).head?.getD false
  let payload := (words .payload).head?.getD false
  let index := (words .index).head?.getD false
  match label with
  | .entry searching =>
      (if input then some (if searching then .index else .option .after)
        else if searching then some .drainIndex else none,
       emit (consume words .source) input)
  | .index =>
      if index then (some (.option .before), consume words .index)
      else (some .payload, emit (consume words .index) true)
  | .option action | .name action =>
      let words := consume words .source
      let words := if action.writes then emit words input else words
      (some (if input then
          match label with | .option _ => .name action | _ => .digit action
        else action.next), words)
  | .digit action =>
      let words := consume words .source
      (some (.name action), if action.writes then emit words input else words)
  | .payload =>
      (some (if payload then .payloadDigit else .option .discard),
        emit (consume words .payload) payload)
  | .payloadDigit => (some .payload, emit (consume words .payload) payload)
  | .drainIndex =>
      (some (if index then .drainIndex else .drainPayload), consume words .index)
  | .drainPayload =>
      (if payload then some .drainPayloadDigit else none, consume words .payload)
  | .drainPayloadDigit => (some .drainPayload, consume words .payload)

variable {K Λ A : Type} [DecidableEq K]
variable (place : Slot → K) (distinct : Function.Injective place)
variable (labels : Label → Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (Register A))
variable (atLabels : ∀ l, program (labels l) = instruction place labels exit l)
variable (base : K → List Bool) (ambient : A)

local notation "C" => configuration place labels exit base ambient
local notation "tick" => advance (TM2.step program)

include distinct atLabels in
theorem step_eq (label : Label) (words : Words) :
    TM2.step program (C (some label) words) =
      some (C (next label words).1 (next label words).2) := by
  change some (TM2.stepAux (program (labels label)) _ _) = _
  rw [atLabels label]
  cases exit <;> cases label with
  | entry searching =>
      cases searching <;> cases head : (words .source).head?.getD false <;>
      simp [instruction, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, emit, put, *]
  | index =>
      cases head : (words .index).head?.getD false <;>
      simp [instruction, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, emit, put, *]
  | option action =>
      cases action <;> cases head : (words .source).head?.getD false <;>
      simp [instruction, copyIf, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, emit, put,
        Action.writes, Action.next, *]
  | name action =>
      cases action <;> cases head : (words .source).head?.getD false <;>
      simp [instruction, copyIf, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, emit, put,
        Action.writes, Action.next, *]
  | digit action =>
      cases action <;>
      simp [instruction, copyIf, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, emit, put,
        Action.writes, *]
  | payload =>
      cases head : (words .payload).head?.getD false <;>
      simp [instruction, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, emit, put, *]
  | payloadDigit =>
      simp [instruction, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, emit, put, *]
  | drainIndex =>
      cases head : (words .index).head?.getD false <;>
      simp [instruction, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, put, *]
  | drainPayload =>
      cases head : (words .payload).head?.getD false <;>
      simp [instruction, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, put, *]
  | drainPayloadDigit =>
      simp [instruction, finish, TM2.stepAux, configuration,
        tapes_at, update_tapes, next, consume, put, *]

private theorem oneStepTrace {X : Type} {f : X → Option X} {a b : X}
    (h : f a = some b) : (advance f)^[1] (some a) = some b := by
  simpa only [Function.iterate_one, advance_some] using h

private theorem frame_cons_clock (bit : Bool) (bits : List Bool) :
    1 + 1 + (BinPackingCompleteness.BinaryEncoding.frame bits).length =
      (BinPackingCompleteness.BinaryEncoding.frame (bit :: bits)).length := by
  simp only [BinPackingCompleteness.BinaryEncoding.frame, List.length_cons]
  omega

private theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def words (source index payload reversed : List Bool) : Words
  | .source => source
  | .index => index
  | .payload => payload
  | .reversed => reversed

private theorem put_words (source index payload reversed value : List Bool) (slot : Slot) :
    put (words source index payload reversed) slot value =
      match slot with
      | .source => words value index payload reversed
      | .index => words source value payload reversed
      | .payload => words source index value reversed
      | .reversed => words source index payload value := by
  funext k; cases slot <;> cases k <;> rfl

include distinct atLabels

theorem one (label : Label) (w : Words) :
    tick^[1] (some (C (some label) w)) = some (C (next label w).1 (next label w).2) := by
  simpa only [Function.iterate_one, advance_some] using
    step_eq place distinct labels exit program atLabels base ambient label w

theorem nameTrace (action : Action) (bits source index payload reversed : List Bool) :
    tick^[(BinPackingCompleteness.BinaryEncoding.frame bits).length]
      (some (C (some (.name action))
        (words (BinPackingCompleteness.BinaryEncoding.frame bits ++ source)
          index payload reversed))) =
      some (C (some action.next)
        (words source index payload
          (saved action (BinPackingCompleteness.BinaryEncoding.frame bits) reversed))) := by
  induction bits generalizing reversed with
  | nil =>
      have h := one place distinct labels exit program atLabels base ambient
        (.name action) (words (false :: source) index payload reversed)
      cases action <;> simpa [next, consume, emit, put_words, words, saved,
        Action.writes, Action.next, BinPackingCompleteness.BinaryEncoding.frame] using h
  | cons bit bits ih =>
      have first := one place distinct labels exit program atLabels base ambient
        (.name action) (words (true :: bit ::
          (BinPackingCompleteness.BinaryEncoding.frame bits ++ source)) index payload reversed)
      have second := one place distinct labels exit program atLabels base ambient
        (.digit action) (words (bit ::
          (BinPackingCompleteness.BinaryEncoding.frame bits ++ source)) index payload
          (if action.writes then true :: reversed else reversed))
      have third := ih (if action.writes then bit :: true :: reversed else reversed)
      cases action <;>
        simp only [saved, Action.writes, Action.next, Bool.false_eq_true,
          ↓reduceIte] at third ⊢ <;>
        simp [next, consume, emit, put_words, words, Action.writes] at first second <;>
        have full := joinTrace (joinTrace (oneStepTrace first) (oneStepTrace second)) third <;>
        rw [frame_cons_clock bit bits] at full <;>
        simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append,
          List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using full

theorem optionTrace (action : Action) (entry : Option Nat)
    (source index payload reversed : List Bool) :
    tick^[(optionBits natBits entry).length]
      (some (C (some (.option action))
        (words (optionBits natBits entry ++ source) index payload reversed))) =
      some (C (some action.next)
        (words source index payload (saved action (optionBits natBits entry) reversed))) := by
  cases entry with
  | none =>
      have h := one place distinct labels exit program atLabels base ambient
        (.option action) (words (false :: source) index payload reversed)
      cases action <;> simpa [next, consume, emit, put_words, words, saved,
        optionBits, Action.writes, Action.next] using h
  | some value =>
      have first := one place distinct labels exit program atLabels base ambient
        (.option action) (words (true :: (natBits value ++ source)) index payload reversed)
      have second := nameTrace place distinct labels exit program atLabels base ambient
        action value.bits source index payload
        (if action.writes then true :: reversed else reversed)
      have clock : 1 + (BinPackingCompleteness.BinaryEncoding.frame value.bits).length =
          (optionBits natBits (some value)).length := by
        simp only [optionBits, natBits, BinPackingCompleteness.BinaryEncoding.nameBits,
          List.length_cons]
        omega
      cases action <;>
        simp only [saved, Action.writes, Action.next, Bool.false_eq_true,
          ↓reduceIte] at second ⊢ <;>
        simp [next, consume, emit, put_words, words, Action.writes,
          natBits, BinPackingCompleteness.BinaryEncoding.nameBits] at first <;>
        have full := joinTrace (oneStepTrace first) second <;>
        rw [clock] at full <;>
        simpa only [optionBits, natBits, BinPackingCompleteness.BinaryEncoding.nameBits,
          List.cons_append, List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using full

theorem copyTrace (fixed : List (Option Nat)) (source index payload reversed : List Bool) :
    tick^[(fixedBits fixed).length]
      (some (C (some (.entry false)) (words (fixedBits fixed ++ source) index payload reversed))) =
      some (C none (words source index payload ((fixedBits fixed).reverse ++ reversed))) := by
  induction fixed generalizing reversed with
  | nil =>
      simpa [next, consume, emit, put_words, words, fixedBits, listBits] using
        one place distinct labels exit program atLabels base ambient (.entry false)
          (words (false :: source) index payload reversed)
  | cons entry fixed ih =>
      have first := one place distinct labels exit program atLabels base ambient (.entry false)
        (words (true :: (optionBits natBits entry ++ fixedBits fixed ++ source))
          index payload reversed)
      have second := optionTrace place distinct labels exit program atLabels base ambient .after
        entry (fixedBits fixed ++ source) index payload (true :: reversed)
      have third := ih ((optionBits natBits entry).reverse ++ true :: reversed)
      simp [next, consume, emit, put_words, words, saved, Action.writes,
        Action.next] at first second
      have full := joinTrace (joinTrace (oneStepTrace first) second) third
      simpa [fixedBits, listBits, List.reverse_cons, List.reverse_append,
        List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

theorem payloadTrace (bits source index payload reversed : List Bool) :
    tick^[(BinPackingCompleteness.BinaryEncoding.frame bits).length]
      (some (C (some .payload) (words source index
        (BinPackingCompleteness.BinaryEncoding.frame bits ++ payload) reversed))) =
      some (C (some (.option .discard)) (words source index payload
        ((BinPackingCompleteness.BinaryEncoding.frame bits).reverse ++ reversed))) := by
  induction bits generalizing reversed with
  | nil =>
      simpa [next, consume, emit, put_words, words, BinPackingCompleteness.BinaryEncoding.frame] using
        one place distinct labels exit program atLabels base ambient .payload
          (words source index (false :: payload) reversed)
  | cons bit bits ih =>
      have first := one place distinct labels exit program atLabels base ambient .payload
        (words source index (true :: bit ::
          (BinPackingCompleteness.BinaryEncoding.frame bits ++ payload)) reversed)
      have second := one place distinct labels exit program atLabels base ambient .payloadDigit
        (words source index (bit :: (BinPackingCompleteness.BinaryEncoding.frame bits ++ payload))
          (true :: reversed))
      have third := ih (bit :: true :: reversed)
      simp [next, consume, emit, put_words, words] at first second
      have full := joinTrace (joinTrace (oneStepTrace first) (oneStepTrace second)) third
      rw [frame_cons_clock bit bits] at full
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append,
        List.reverse_cons, List.append_assoc, List.singleton_append, List.nil_append] using full

theorem drainPayloadTrace (bits source index payload reversed : List Bool) :
    tick^[(BinPackingCompleteness.BinaryEncoding.frame bits).length]
      (some (C (some .drainPayload) (words source index
        (BinPackingCompleteness.BinaryEncoding.frame bits ++ payload) reversed))) =
      some (C none (words source index payload reversed)) := by
  induction bits with
  | nil =>
      simpa [next, consume, put_words, words, BinPackingCompleteness.BinaryEncoding.frame] using
        one place distinct labels exit program atLabels base ambient .drainPayload
          (words source index (false :: payload) reversed)
  | cons bit bits ih =>
      have first := one place distinct labels exit program atLabels base ambient .drainPayload
        (words source index (true :: bit ::
          (BinPackingCompleteness.BinaryEncoding.frame bits ++ payload)) reversed)
      have second := one place distinct labels exit program atLabels base ambient .drainPayloadDigit
        (words source index (bit :: (BinPackingCompleteness.BinaryEncoding.frame bits ++ payload)) reversed)
      simp [next, consume, put_words, words] at first second
      have full := joinTrace (joinTrace (oneStepTrace first) (oneStepTrace second)) ih
      rw [frame_cons_clock bit bits] at full
      simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append] using full

theorem drainIndexTrace (n : Nat) (source index payload reversed : List Bool) :
    tick^[n + 1]
      (some (C (some .drainIndex) (words source (encodeWord n ++ index) payload reversed))) =
      some (C (some .drainPayload) (words source index payload reversed)) := by
  induction n with
  | zero =>
      simpa [next, consume, put_words, words, encodeWord] using
        one place distinct labels exit program atLabels base ambient .drainIndex
          (words source (false :: index) payload reversed)
  | succ n ih =>
      have first := one place distinct labels exit program atLabels base ambient .drainIndex
        (words source (true :: (encodeWord n ++ index)) payload reversed)
      simp [next, consume, put_words, words] at first
      have full := joinTrace (oneStepTrace first) ih
      simpa [encodeWord, List.replicate_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

theorem replaceTrace (fixed : List (Option Nat)) (i value : Nat)
    (source index payload reversed : List Bool) :
    tick^[(fixedBits fixed).length + (i + 1) + (natBits value).length]
      (some (C (some (.entry true)) (words (fixedBits fixed ++ source)
        (encodeWord i ++ index) (natBits value ++ payload) reversed))) =
      some (C none (words source index payload
        ((fixedBits (fixed.set i (some value))).reverse ++ reversed))) := by
  induction fixed generalizing i reversed with
  | nil =>
      have first := one place distinct labels exit program atLabels base ambient (.entry true)
        (words (false :: source) (encodeWord i ++ index) (natBits value ++ payload) reversed)
      have second := drainIndexTrace place distinct labels exit program atLabels base ambient
        i source index (natBits value ++ payload) (false :: reversed)
      have third := drainPayloadTrace place distinct labels exit program atLabels base ambient
        value.bits source index payload (false :: reversed)
      simp [next, consume, emit, put_words, words] at first
      have full := joinTrace (joinTrace (oneStepTrace first) second) third
      simpa [fixedBits, listBits, natBits, BinPackingCompleteness.BinaryEncoding.nameBits] using full
  | cons entry fixed ih =>
      cases i with
      | zero =>
          have first := one place distinct labels exit program atLabels base ambient (.entry true)
            (words (true :: (optionBits natBits entry ++ fixedBits fixed ++ source))
              (false :: index) (natBits value ++ payload) reversed)
          have second := one place distinct labels exit program atLabels base ambient .index
            (words (optionBits natBits entry ++ fixedBits fixed ++ source)
              (false :: index) (natBits value ++ payload) (true :: reversed))
          have third := payloadTrace place distinct labels exit program atLabels base ambient
            value.bits (optionBits natBits entry ++ fixedBits fixed ++ source)
              index payload (true :: true :: reversed)
          have fourth := optionTrace place distinct labels exit program atLabels base ambient .discard
            entry (fixedBits fixed ++ source) index payload
              ((natBits value).reverse ++ true :: true :: reversed)
          have fifth := copyTrace place distinct labels exit program atLabels base ambient
            fixed source index payload ((natBits value).reverse ++ true :: true :: reversed)
          simp [next, consume, emit, put_words, words] at first second
          simp only [List.append_assoc] at third
          simp only [saved, Action.writes, Bool.false_eq_true, ↓reduceIte, Action.next] at fourth
          have full := joinTrace (joinTrace (joinTrace (joinTrace (oneStepTrace first) (oneStepTrace second)) third) fourth) fifth
          have clock : 1 + 1 + (BinPackingCompleteness.BinaryEncoding.frame value.bits).length +
              (optionBits natBits entry).length + (fixedBits fixed).length =
              (fixedBits (entry :: fixed)).length + (0 + 1) + (natBits value).length := by
            simp only [fixedBits, listBits, List.length_cons, List.length_append,
              natBits, BinPackingCompleteness.BinaryEncoding.nameBits]
            omega
          rw [clock] at full
          simpa [fixedBits, listBits, optionBits, natBits,
            BinPackingCompleteness.BinaryEncoding.nameBits, encodeWord,
            List.reverse_cons, List.reverse_append, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full
      | succ i =>
          have first := one place distinct labels exit program atLabels base ambient (.entry true)
            (words (true :: (optionBits natBits entry ++ fixedBits fixed ++ source))
              (true :: (encodeWord i ++ index)) (natBits value ++ payload) reversed)
          have second := one place distinct labels exit program atLabels base ambient .index
            (words (optionBits natBits entry ++ fixedBits fixed ++ source)
              (true :: (encodeWord i ++ index)) (natBits value ++ payload) (true :: reversed))
          have third := optionTrace place distinct labels exit program atLabels base ambient .before
            entry (fixedBits fixed ++ source) (encodeWord i ++ index) (natBits value ++ payload)
              (true :: reversed)
          have fourth := ih i ((optionBits natBits entry).reverse ++ true :: reversed)
          simp [next, consume, emit, put_words, words] at first second
          simp only [saved, Action.writes, ↓reduceIte, Action.next] at third
          have full := joinTrace (joinTrace (joinTrace (oneStepTrace first) (oneStepTrace second)) third) fourth
          simpa [fixedBits, listBits, encodeWord, List.replicate_succ,
            List.reverse_cons, List.reverse_append, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

def replaceInTime (fixed : List (Option Nat)) (i value : Nat)
    (source index payload reversed : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      (C (some (.entry true)) (words (fixedBits fixed ++ source)
        (encodeWord i ++ index) (natBits value ++ payload) reversed))
      (some (C none (words source index payload
        ((fixedBits (fixed.set i (some value))).reverse ++ reversed))))
      ((fixedBits fixed).length + (encodeWord i).length + (natBits value).length) where
  steps := (fixedBits fixed).length + (i + 1) + (natBits value).length
  evals_in_steps := by
    change (advance (TM2.step program))^[
      (fixedBits fixed).length + (i + 1) + (natBits value).length] _ = _
    exact replaceTrace place distinct labels exit program atLabels base ambient
      fixed i value source index payload reversed
  steps_le_m := by simp

end BinPackingGap.SearchFixedReplaceMachine

end OAI
