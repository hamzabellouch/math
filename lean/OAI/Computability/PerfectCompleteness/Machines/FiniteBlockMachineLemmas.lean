import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.OfFn
import OAI.Computability.PerfectCompleteness.Foundations.CanonicalKeys
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineFiniteTable
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas

namespace OAI


namespace PerfectCompleteness.FiniteBlockMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineFixedBlockMap
open scoped Classical

noncomputable section

variable {α β : Type} {N M : Nat}

def encode (enum : α ≃ Fin N) (a : α) : Buffer N :=
  fun i => decide (enum a = i)

theorem encode_injective (enum : α ≃ Fin N) : Function.Injective (encode enum) := by
  intro a b h
  have ha : encode enum a (enum a) = true := by simp [encode]
  have hb : encode enum b (enum a) = true := by rw [← h]; exact ha
  exact enum.injective (of_decide_eq_true hb).symm

def decode (enum : α ≃ Fin N) (fallback : α) (bits : Buffer N) : α :=
  if h : ∃ a, encode enum a = bits then Classical.choose h else fallback

@[simp] theorem decode_encode (enum : α ≃ Fin N) (fallback a : α) :
    decode enum fallback (encode enum a) = a := by
  have h : ∃ b, encode enum b = encode enum a := ⟨a, rfl⟩
  simp only [decode, dite_eq_left h]
  exact encode_injective enum (Classical.choose_spec h)

def word (enum : α ≃ Fin N) (a : α) : List Bool := List.ofFn (encode enum a)

@[simp] theorem word_length (enum : α ≃ Fin N) (a : α) : (word enum a).length = N :=
  List.length_ofFn

def transform (input : α ≃ Fin N) (output : β ≃ Fin M) (fallback : α)
    (f : α → β) : Buffer N → Buffer M :=
  fun bits => encode output (f (decode input fallback bits))

@[simp] theorem transform_encode (input : α ≃ Fin N) (output : β ≃ Fin M)
    (fallback a : α) (f : α → β) :
    transform input output fallback f (encode input a) = encode output (f a) := by
  rw [transform, decode_encode]

def statement {K Λ A : Type} (src dst : K) (exit : Option Λ)
    (input : α ≃ Fin N) (output : β ≃ Fin M) (fallback : α) (f : α → β) :
    TM2.Stmt (fun _ : K => Bool) Λ (A × Buffer N) :=
  blockMapAt src dst (transform input output fallback f) exit

theorem statement_trace {K Λ A : Type} [DecidableEq K]
    (src dst : K) (exit : Option Λ) (hne : src ≠ dst)
    (input : α ≃ Fin N) (output : β ≃ Fin M) (fallback a : α) (f : α → β)
    (suffix : List Bool) (state : A × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = word input a ++ suffix) :
    TM2.stepAux (statement src dst exit input output fallback f) state tapes =
      { l := exit, var := (state.1, emptyBuffer N),
        stk := Function.update (Function.update tapes src suffix) dst
          (word output (f a) ++ tapes dst) } := by
  simpa only [statement, transform_encode, word] using
    stepAux_blockMapAt src dst (transform input output fallback f) exit hne
      (encode input a) suffix state tapes hinput

theorem statement_pushBound {K Λ A : Type} (src dst : K) (exit : Option Λ)
    (input : α ≃ Fin N) (output : β ≃ Fin M) (fallback : α) (f : α → β) :
    Runtime.statementPushBound
      (statement (A := A) src dst exit input output fallback f) = M :=
  statementPushBound_blockMapAt src dst (transform input output fallback f) exit

def machine (input : α ≃ Fin N) (output : β ≃ Fin M) (fallback : α)
    (f : α → β) : FinTM2 :=
  MachineFixedBlockMap.machine (transform input output fallback f)

theorem machine_step (input : α ≃ Fin N) (output : β ≃ Fin M)
    (fallback a : α) (f : α → β) :
    (machine input output fallback f).step
        (initList (machine input output fallback f) (word input a)) =
      some (haltList (machine input output fallback f) (word output (f a))) := by
  let tapes : Bool → List Bool := fun k => if k = false then word input a else []
  have hinput : tapes false = List.ofFn (encode input a) ++ [] := by simp [tapes, word]
  have hstep := stepAux_blockMapAt (σ := Unit) (Λ := Unit) false true
    (transform input output fallback f) none (by decide)
    (encode input a) [] ((), emptyBuffer N) tapes hinput
  have htapes : Function.update (Function.update tapes false []) true
      (List.ofFn (transform input output fallback f (encode input a)) ++ tapes true) =
      fun k : Bool => if k = true then word output (f a) else [] := by
    funext k
    cases k <;> simp [tapes, transform_encode, word]
  change some (TM2.stepAux
      (blockMapAt false true (transform input output fallback f) none)
      ((), emptyBuffer N) tapes) =
    some {
      l := none
      var := ((), emptyBuffer N)
      stk := fun k : Bool => if k = true then word output (f a) else []
    }
  erw [hstep, htapes]
  rfl

def computation (input : α ≃ Fin N) (output : β ≃ Fin M) (fallback : α)
    (f : α → β) : TM2ComputableInPolyTime (word input) (word output) f where
  tm := machine input output fallback f
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun a := {
    steps := 1
    evals_in_steps := by
      change (machine input output fallback f).step
          (initList (machine input output fallback f) ((word input a).map id)) =
        some (haltList (machine input output fallback f) ((word output (f a)).map id))
      erw [List.map_id, List.map_id]
      exact machine_step input output fallback a f
    steps_le_m := by simp
  }

theorem machine_pushBound (input : α ≃ Fin N) (output : β ≃ Fin M)
    (fallback : α) (f : α → β) :
    Runtime.statementPushBound ((machine input output fallback f).m ()) = M :=
  MachineFixedBlockMap.machine_statementPushBound (transform input output fallback f)

theorem machine_workAlphabet_finite (input : α ≃ Fin N) (output : β ≃ Fin M)
    (fallback : α) (f : α → β) (k : (machine input output fallback f).K) :
    Finite ((machine input output fallback f).Γ k) := by
  change Finite Bool
  infer_instance

end
end PerfectCompleteness.FiniteBlockMachine


namespace PerfectCompleteness.FiniteReadMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineFixedBlockMap
open scoped Classical

noncomputable section

variable {α A K Λ : Type} {N : Nat}

abbrev State (A : Type) (N : Nat) := A × Buffer N

theorem state_finite [Finite A] : Finite (State A N) := by
  infer_instance

def saveFinish (exit : Option Λ) (input : α ≃ Fin N) (fallback : α)
    (save : A → α → A) : TM2.Stmt (fun _ : K => Bool) Λ (State A N) :=
  .load (fun state =>
    (save state.1 (FiniteBlockMachine.decode input fallback state.2), emptyBuffer N))
    (finishAt exit)

theorem saveFinish_pushBound (exit : Option Λ) (input : α ≃ Fin N)
    (fallback : α) (save : A → α → A) :
    Runtime.statementPushBound (saveFinish (K := K) exit input fallback save) = 0 := by
  cases exit <;> rfl

theorem stepAux_saveFinish [DecidableEq K] (exit : Option Λ)
    (input : α ≃ Fin N) (fallback a : α) (save : A → α → A)
    (ambient : A) (tapes : K → List Bool) :
    TM2.stepAux (saveFinish exit input fallback save)
        (ambient, FiniteBlockMachine.encode input a) tapes = {
      l := exit
      var := (save ambient a, emptyBuffer N)
      stk := tapes
    } := by
  cases exit <;>
    simp only [saveFinish, TM2.stepAux, finishAt, FiniteBlockMachine.decode_encode]

def statement (src : K) (exit : Option Λ) (input : α ≃ Fin N)
    (fallback : α) (save : A → α → A) :
    TM2.Stmt (fun _ : K => Bool) Λ (State A N) :=
  readSlots src (List.ofFn id) (saveFinish exit input fallback save)

theorem statement_trace [DecidableEq K] (src : K) (exit : Option Λ)
    (input : α ≃ Fin N) (fallback a : α) (save : A → α → A)
    (suffix : List Bool) (state : State A N) (tapes : K → List Bool)
    (hinput : tapes src = FiniteBlockMachine.word input a ++ suffix) :
    TM2.stepAux (statement src exit input fallback save) state tapes = {
      l := exit
      var := (save state.1 a, emptyBuffer N)
      stk := Function.update tapes src suffix
    } := by
  have hin : tapes src = List.ofFn (FiniteBlockMachine.encode input a) ++ suffix := hinput
  unfold statement
  rw [stepAux_readAll src _ state (FiniteBlockMachine.encode input a) tapes suffix hin]
  exact stepAux_saveFinish exit input fallback a save state.1 _

theorem statement_pushBound (src : K) (exit : Option Λ)
    (input : α ≃ Fin N) (fallback : α) (save : A → α → A) :
    Runtime.statementPushBound (statement src exit input fallback save) = 0 := by
  rw [statement, statementPushBound_readSlots, saveFinish_pushBound]

theorem step [DecidableEq K] (src : K) (exit : Option Λ)
    (input : α ≃ Fin N) (fallback a : α) (save : A → α → A)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A N))
    (entry : Λ) (atEntry : program entry = statement src exit input fallback save)
    (suffix : List Bool) (state : State A N) (tapes : K → List Bool)
    (hinput : tapes src = FiniteBlockMachine.word input a ++ suffix) :
    TM2.step program { l := some entry, var := state, stk := tapes } =
      some {
        l := exit
        var := (save state.1 a, emptyBuffer N)
        stk := Function.update tapes src suffix
      } := by
  change some (TM2.stepAux (program entry) state tapes) = _
  rw [atEntry, statement_trace src exit input fallback a save suffix state tapes hinput]

def inTime [DecidableEq K] (src : K) (exit : Option Λ)
    (input : α ≃ Fin N) (fallback a : α) (save : A → α → A)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A N))
    (entry : Λ) (atEntry : program entry = statement src exit input fallback save)
    (suffix : List Bool) (state : State A N) (tapes : K → List Bool)
    (hinput : tapes src = FiniteBlockMachine.word input a ++ suffix) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some entry, state, tapes⟩
      (some ⟨exit, (save state.1 a, emptyBuffer N), Function.update tapes src suffix⟩) 1 where
  steps := 1
  evals_in_steps := step src exit input fallback a save program entry atEntry
    suffix state tapes hinput
  steps_le_m := Nat.le_refl 1

end
end PerfectCompleteness.FiniteReadMachine


namespace PerfectCompleteness.FiniteWordMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineFixedBlockMap
open scoped Classical

noncomputable section

variable {α : Type} {N : Nat}

abbrev State (N : Nat) := Unit × Buffer N

def keys (N : Nat) : List (State N) := (Finset.univ : Finset (State N)).toList

theorem keys_complete (N : Nat) (state : State N) : state ∈ keys N := by
  simp [keys]

def literalTable (input : α ≃ Fin N) (fallback : α) (emit : α → List Bool)
    (state : State N) : List Bool :=
  emit (FiniteBlockMachine.decode input fallback state.2)

def cleanFinish {K Λ : Type} (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (State N) :=
  .load (fun _ => ((), emptyBuffer N)) (finishAt exit)

theorem cleanFinish_pushBound {K Λ : Type} (exit : Option Λ) :
    Runtime.statementPushBound (cleanFinish (K := K) (N := N) exit) = 0 := by
  cases exit <;> rfl

theorem stepAux_cleanFinish {K Λ : Type} [DecidableEq K]
    (exit : Option Λ) (state : State N) (tapes : K → List Bool) :
    TM2.stepAux (cleanFinish exit) state tapes = {
      l := exit
      var := ((), emptyBuffer N)
      stk := tapes
    } := by
  cases exit <;> rfl

def statement {K Λ : Type} (src dst : K) (exit : Option Λ)
    (input : α ≃ Fin N) (fallback : α) (emit : α → List Bool) :
    TM2.Stmt (fun _ : K => Bool) Λ (State N) :=
  readSlots src (List.ofFn id)
    (MachineFiniteTable.emit dst (literalTable input fallback emit) (keys N)
      (cleanFinish exit))

theorem statement_trace {K Λ : Type} [DecidableEq K]
    (src dst : K) (exit : Option Λ) (hne : src ≠ dst)
    (input : α ≃ Fin N) (fallback a : α) (emit : α → List Bool)
    (suffix : List Bool) (state : State N) (tapes : K → List Bool)
    (hinput : tapes src = FiniteBlockMachine.word input a ++ suffix) :
    TM2.stepAux (statement src dst exit input fallback emit) state tapes = {
      l := exit
      var := ((), emptyBuffer N)
      stk := Function.update (Function.update tapes src suffix) dst (emit a ++ tapes dst)
    } := by
  have hin : tapes src = List.ofFn (FiniteBlockMachine.encode input a) ++ suffix := hinput
  unfold statement
  rw [stepAux_readAll src _ state (FiniteBlockMachine.encode input a) tapes suffix hin]
  rw [MachineFiniteTable.stepAux_emit (Γ := fun _ : K => Bool) (Λ := Λ) (σ := State N)
    dst (literalTable input fallback emit) (keys N) (keys_complete N)
    (cleanFinish (K := K) (N := N) exit)
    (state.1, FiniteBlockMachine.encode input a) (Function.update tapes src suffix)]
  rw [stepAux_cleanFinish]
  simp only [literalTable, FiniteBlockMachine.decode_encode,
    Function.update_of_ne (Ne.symm hne)]

theorem statement_pushBound {K Λ : Type} (src dst : K) (exit : Option Λ)
    (input : α ≃ Fin N) (fallback : α) (emit : α → List Bool) :
    Runtime.statementPushBound (statement src dst exit input fallback emit) ≤
      MachineFiniteTable.tableBound (Γ := fun _ : K => Bool)
        dst (literalTable input fallback emit) (keys N) := by
  have h := MachineFiniteTable.emit_push_bound (Γ := fun _ : K => Bool)
    dst (literalTable input fallback emit) (keys N)
    (cleanFinish (K := K) (Λ := Λ) (N := N) exit)
  simpa only [statement, statementPushBound_readSlots, cleanFinish_pushBound,
    Nat.add_zero] using h

def machine (input : α ≃ Fin N) (fallback : α) (emit : α → List Bool) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := State N
  initialState := ((), emptyBuffer N)
  m _ := statement false true none input fallback emit

theorem machine_step (input : α ≃ Fin N) (fallback a : α) (emit : α → List Bool) :
    (machine input fallback emit).step
        (initList (machine input fallback emit) (FiniteBlockMachine.word input a)) =
      some (haltList (machine input fallback emit) (emit a)) := by
  let tapes : Bool → List Bool :=
    fun k => if k = false then FiniteBlockMachine.word input a else []
  have hinput : tapes false = FiniteBlockMachine.word input a ++ [] := by simp [tapes]
  have hstep := statement_trace (Λ := Unit) false true none (by decide)
    input fallback a emit [] ((), emptyBuffer N) tapes hinput
  have htapes : Function.update (Function.update tapes false []) true (emit a ++ tapes true) =
      fun k : Bool => if k = true then emit a else [] := by
    funext k
    cases k <;> simp [tapes]
  change some (TM2.stepAux
      (statement false true none input fallback emit) ((), emptyBuffer N) tapes) =
    some {
      l := none
      var := ((), emptyBuffer N)
      stk := fun k : Bool => if k = true then emit a else []
    }
  erw [hstep, htapes]
  rfl

def computation (input : α ≃ Fin N) (fallback : α) (emit : α → List Bool) :
    TM2ComputableInPolyTime (FiniteBlockMachine.word input) (id : List Bool → List Bool) emit where
  tm := machine input fallback emit
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun a := {
    steps := 1
    evals_in_steps := by
      change (machine input fallback emit).step
          (initList (machine input fallback emit) ((FiniteBlockMachine.word input a).map id)) =
        some (haltList (machine input fallback emit) ((emit a).map id))
      erw [List.map_id, List.map_id]
      exact machine_step input fallback a emit
    steps_le_m := by simp
  }

theorem machine_pushBound (input : α ≃ Fin N) (fallback : α) (emit : α → List Bool) :
    Runtime.statementPushBound ((machine input fallback emit).m ()) ≤
      MachineFiniteTable.tableBound (Γ := fun _ : Bool => Bool)
        true (literalTable input fallback emit) (keys N) :=
  statement_pushBound (Λ := Unit) false true none input fallback emit

theorem machine_workAlphabet_finite (input : α ≃ Fin N) (fallback : α)
    (emit : α → List Bool) (k : (machine input fallback emit).K) :
    Finite ((machine input fallback emit).Γ k) := by
  change Finite Bool
  infer_instance

end
end PerfectCompleteness.FiniteWordMachine


namespace PerfectCompleteness.KeyMetadataEncoding

open ClauseSupport

variable {n : Nat}

def bitWord (b : Bool) : Nat := if b then 1 else 0

@[simp] theorem bitWord_eq_iff (a b : Bool) : bitWord a = bitWord b ↔ a = b := by
  cases a <;> cases b <;> decide

theorem bitWord_le (b : Bool) : bitWord b ≤ 1 := by
  cases b <;> decide

def entryID : SlotKey → Nat
  | .dropped => 0
  | .bit variableID => variableID
  | .full occurrence _ => occurrence

def entryWords (entry : Fin n × SlotKey) : List Nat :=
  entry.1.val :: match entry.2 with
    | .dropped => [0, 0, 0, 0, 0]
    | .bit variableID => [1, variableID, 0, 0, 0]
    | .full occurrence signs =>
        [2, occurrence, bitWord signs.1, bitWord signs.2.1, bitWord signs.2.2]

@[simp] theorem entryWords_length (entry : Fin n × SlotKey) :
    (entryWords entry).length = 6 := by
  rcases entry with ⟨position, key⟩
  cases key <;> rfl

theorem entryWords_injective (n : Nat) :
    Function.Injective (entryWords (n := n)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hij : i = j := Fin.ext (List.cons.inj h).1
  subst j
  apply congrArg (Prod.mk i)
  cases a <;> cases b <;> simp_all [entryWords, Prod.ext_iff]

def metadataWords (entries : List (Fin n × SlotKey)) : List Nat :=
  entries.flatMap entryWords

@[simp] theorem metadataWords_nil : metadataWords ([] : List (Fin n × SlotKey)) = [] := rfl

@[simp] theorem metadataWords_cons (entry : Fin n × SlotKey)
    (entries : List (Fin n × SlotKey)) :
    metadataWords (entry :: entries) = entryWords entry ++ metadataWords entries := rfl

@[simp] theorem metadataWords_length (entries : List (Fin n × SlotKey)) :
    (metadataWords entries).length = 6 * entries.length := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rw [metadataWords_cons, List.length_append, entryWords_length, ih,
        List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem metadataWords_injective (n : Nat) :
    Function.Injective (metadataWords (n := n)) := by
  intro entries
  induction entries with
  | nil =>
      intro other h
      have hlength := congrArg List.length h
      simp only [metadataWords_length, List.length_nil] at hlength
      have hz : other.length = 0 := by omega
      cases other with
      | nil => rfl
      | cons entry entries => simp at hz
  | cons entry entries ih =>
      intro other h
      cases other with
      | nil =>
          have hlength := congrArg List.length h
          simp only [metadataWords_length, List.length_cons, List.length_nil] at hlength
          omega
      | cons next rest =>
          have hblocks : entryWords entry ++ metadataWords entries =
              entryWords next ++ metadataWords rest := h
          obtain ⟨hhead, htail⟩ := List.append_inj hblocks
            ((entryWords_length entry).trans (entryWords_length next).symm)
          exact congrArg₂ List.cons (entryWords_injective n hhead) (ih htail)

theorem entryWords_le (entry : Fin n × SlotKey) (M : Nat)
    (hID : entryID entry.2 ≤ M) :
    ∀ word ∈ entryWords entry, word ≤ max n (max M 2) := by
  rcases entry with ⟨position, key⟩
  have hn : n ≤ max n (max M 2) := le_max_left _ _
  have hM : M ≤ max n (max M 2) := (le_max_left M 2).trans (le_max_right n _)
  have htwo : 2 ≤ max n (max M 2) := (le_max_right M 2).trans (le_max_right n _)
  have hposition := position.isLt
  intro word hw
  cases key with
  | dropped =>
      simp only [entryWords, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  | bit variableID =>
      change variableID ≤ M at hID
      simp only [entryWords, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  | full occurrence signs =>
      change occurrence ≤ M at hID
      have hs₀ := bitWord_le signs.1
      have hs₁ := bitWord_le signs.2.1
      have hs₂ := bitWord_le signs.2.2
      simp only [entryWords, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem metadataWords_le (entries : List (Fin n × SlotKey)) (M : Nat)
    (hIDs : ∀ entry ∈ entries, entryID entry.2 ≤ M) :
    ∀ word ∈ metadataWords entries, word ≤ max n (max M 2) := by
  intro word hw
  obtain ⟨entry, hentry, hword⟩ := List.mem_flatMap.mp hw
  exact entryWords_le entry M (hIDs entry hentry) word hword

end PerfectCompleteness.KeyMetadataEncoding


namespace PerfectCompleteness.CanonicalKeyEncoding

open ClauseSupport CanonicalKeys
open UniqueGamesTheorem.Foundations.Complexity
open scoped Classical

noncomputable section

def reducedValueEquiv : ReducedValue ≃ Option (Bool ⊕ SourceClause.Triple) where
  toFun
    | .dropped => none
    | .bit b => some (.inl b)
    | .full triple => some (.inr triple)
  invFun
    | none => .dropped
    | some (.inl b) => .bit b
    | some (.inr triple) => .full triple
  left_inv value := by cases value <;> rfl
  right_inv value := by
    cases value with
    | none => rfl
    | some value => cases value <;> rfl

local instance : Fintype ReducedValue := Fintype.ofEquiv _ reducedValueEquiv.symm

theorem reducedValue_card : Fintype.card ReducedValue = 11 := by
  rw [Fintype.card_congr reducedValueEquiv]
  simp [SourceClause.Triple]

abbrev Assignment (n : Nat) := Fin n → ReducedValue

def partitionWidth (n : Nat) : Nat := Fintype.card (Set (Assignment n))

theorem partitionWidth_eq (n : Nat) : partitionWidth n = 2 ^ (11 ^ n) := by
  simp only [partitionWidth, Fintype.card_set, Assignment, Fintype.card_fun,
    reducedValue_card, Fintype.card_fin]

def partEnum (n : Nat) : Set (Assignment n) ≃ Fin (partitionWidth n) :=
  Fintype.equivFin _

def partitionMask {n : Nat} (partition : Set (Set (Assignment n))) :
    Fin (partitionWidth n) → Bool :=
  fun i => decide ((partEnum n).symm i ∈ partition)

def partitionOfMask {n : Nat} (mask : Fin (partitionWidth n) → Bool) :
    Set (Set (Assignment n)) := {part | mask (partEnum n part) = true}

@[simp] theorem partitionOfMask_partitionMask {n : Nat}
    (partition : Set (Set (Assignment n))) :
    partitionOfMask (partitionMask partition) = partition := by
  ext part
  simp [partitionOfMask, partitionMask]

theorem partitionMask_injective (n : Nat) : Function.Injective (partitionMask (n := n)) := by
  intro a b h
  have hdecoded := congrArg partitionOfMask h
  simpa only [partitionOfMask_partitionMask] using hdecoded

def boolWord (b : Bool) : Nat := if b then 1 else 0

theorem boolWord_injective : Function.Injective boolWord := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolWord]

theorem boolWord_le_one (b : Bool) : boolWord b ≤ 1 := by
  cases b <;> decide

def partitionWords {n : Nat} (partition : Set (Set (Assignment n))) : List Nat :=
  List.ofFn (fun i => boolWord (partitionMask partition i))

@[simp] theorem partitionWords_length {n : Nat} (partition : Set (Set (Assignment n))) :
    (partitionWords partition).length = partitionWidth n := List.length_ofFn

theorem partitionWords_injective (n : Nat) :
    Function.Injective (partitionWords (n := n)) := by
  intro a b h
  apply partitionMask_injective n
  have hfun := List.ofFn_injective h
  funext i
  exact boolWord_injective (congrFun hfun i)

def sideWord : Side → Nat
  | .left => 0
  | .right => 1

theorem sideWord_injective : Function.Injective sideWord := by
  intro a b h
  cases a <;> cases b <;> simp_all [sideWord]

def words {n : Nat} (key : Key n) : List Nat :=
  sideWord key.side ::
    (partitionWords key.partition ++ KeyMetadataEncoding.metadataWords key.retained)

def bits {n : Nat} (key : Key n) : List Bool := encodeWords (words key)

theorem words_length {n : Nat} (key : Key n) :
    (words key).length = 1 + partitionWidth n + 6 * key.retained.length := by
  simp only [words, List.length_cons, List.length_append, partitionWords_length,
    KeyMetadataEncoding.metadataWords_length]
  omega

theorem bits_length_le {n : Nat} (key : Key n) (bound : Nat)
    (hIDs : ∀ entry ∈ key.retained, KeyMetadataEncoding.entryID entry.2 ≤ bound) :
    (bits key).length ≤
      (1 + partitionWidth n + 6 * key.retained.length) * (max n (max bound 2) + 1) := by
  have htwo : 2 ≤ max n (max bound 2) := (le_max_right bound 2).trans (le_max_right n _)
  have hbound : ∀ word ∈ words key, word ≤ max n (max bound 2) := by
    intro word hword
    rcases List.mem_cons.mp hword with hside | htail
    · have hs : sideWord key.side ≤ 1 := by cases key.side <;> decide
      omega
    · rcases List.mem_append.mp htail with hpart | hmeta
      · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hpart
        have hb := boolWord_le_one (partitionMask key.partition i)
        omega
      · exact KeyMetadataEncoding.metadataWords_le key.retained bound hIDs word hmeta
  simpa only [bits, words_length] using encodeWords_length_le (words key) _ hbound

theorem words_injective (n : Nat) : Function.Injective (words (n := n)) := by
  intro a b h
  have hfields := List.cons.inj h
  have hlen : (partitionWords a.partition).length = (partitionWords b.partition).length := by
    simp only [partitionWords_length]
  have hside := sideWord_injective hfields.1
  have hpart := partitionWords_injective n (List.append_inj_left hfields.2 hlen)
  have hmeta := KeyMetadataEncoding.metadataWords_injective n
    (List.append_inj_right hfields.2 hlen)
  cases a
  cases b
  cases hside
  cases hpart
  cases hmeta
  rfl

theorem bits_injective (n : Nat) : Function.Injective (bits (n := n)) := by
  intro a b h
  exact words_injective n (encodeWords_injective h)

def sameEncoding {n : Nat} (a b : Key n) : Bool := decide (bits a = bits b)

theorem sameEncoding_eq_true_iff {n : Nat} (a b : Key n) :
    sameEncoding a b = true ↔ a = b := by
  simp only [sameEncoding, decide_eq_true_iff]
  exact ⟨fun h => bits_injective n h, fun h => congrArg bits h⟩

theorem bits_eq_iff {n : Nat} (a b : Key n) : bits a = bits b ↔ a = b :=
  ⟨fun h => bits_injective n h, fun h => congrArg bits h⟩

theorem key_retained_length_le {n : Nat} {Y : Type*} (side : Side)
    (slots : Fin n → MixedSupport.Slot) (f : MixedSupport.Assignment slots → Y) :
    (CanonicalKeys.key side slots f).retained.length ≤ n := by
  change (MixedSupport.retainedKeys slots f).length ≤ n
  have h := List.length_filter_le
    (fun entry : Fin n × SlotKey => decide (entry.2 ≠ .dropped))
    ((List.finRange n).map (fun i => (i, MixedSupport.keyFields slots f i)))
  simpa only [MixedSupport.retainedKeys, List.length_map, List.length_finRange] using h

theorem key_bits_length_le {n : Nat} {Y : Type*} (side : Side)
    (slots : Fin n → MixedSupport.Slot) (f : MixedSupport.Assignment slots → Y)
    (bound : Nat)
    (hIDs : ∀ entry ∈ (CanonicalKeys.key side slots f).retained,
      KeyMetadataEncoding.entryID entry.2 ≤ bound) :
    (bits (CanonicalKeys.key side slots f)).length ≤
      (1 + 2 ^ (11 ^ n) + 6 * n) * (max n (max bound 2) + 1) := by
  apply (bits_length_le (CanonicalKeys.key side slots f) bound hIDs).trans
  apply Nat.mul_le_mul_right
  rw [partitionWidth_eq]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left 6 (key_retained_length_le side slots f)) _

theorem bits_projection {n : Nat} {Y : Type*} (side : Side)
    {slots projected : Fin n → MixedSupport.Slot}
    (p : ∀ i, MixedSupport.Projection (slots i) (projected i))
    (f : MixedSupport.Assignment projected → Y) :
    bits (CanonicalKeys.key side slots (f ∘ MixedSupport.projectionMap p)) =
      bits (CanonicalKeys.key side projected f) := by
  rw [CanonicalKeys.key_projection side p f]

end
end PerfectCompleteness.CanonicalKeyEncoding

end OAI
