import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineFixedBlockMap

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.FinalCNFMachine

open Turing
open PCP

abbrev Buffer (N : Nat) := MachineFixedBlockMap.Buffer N

section RelationReader

variable {K Λ σ : Type} {N : Nat}

def readUnarySlots (source : K) : List (Fin N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)
  | [], next => next
  | i :: slots, next =>
      .pop source (fun state head =>
        (state.1, Function.update state.2 i (head.getD false)))
        (.branch (fun state => state.2 i)
          (.pop source (fun state _ => state) (readUnarySlots source slots next))
          (readUnarySlots source slots next))

def unaryBits (slots : List (Fin N)) (bits : Buffer N) : List Bool :=
  slots.flatMap fun i => encodeWord (GraphTables.bitWord (bits i))

theorem unaryBits_eq_encodeWords (slots : List (Fin N)) (bits : Buffer N) :
    unaryBits slots bits = encodeWords (slots.map fun i => GraphTables.bitWord (bits i)) := by
  induction slots with
  | nil => rfl
  | cons i slots ih => simpa only [unaryBits, List.flatMap_cons, List.map_cons,
      encodeWords] using congrArg (encodeWord (GraphTables.bitWord (bits i)) ++ ·) ih

theorem unaryBits_length_le (slots : List (Fin N)) (bits : Buffer N) :
    (unaryBits slots bits).length ≤ 2 * slots.length := by
  induction slots with
  | nil => simp [unaryBits]
  | cons i slots ih =>
      have hi : (encodeWord (GraphTables.bitWord (bits i))).length ≤ 2 := by
        cases bits i <;> simp [GraphTables.bitWord, encodeWord_length]
      simp only [unaryBits, List.flatMap_cons, List.length_append, List.length_cons] at *
      omega

theorem statementPushBound_readUnarySlots (source : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    Runtime.statementPushBound (readUnarySlots source slots next) =
      Runtime.statementPushBound next := by
  induction slots with
  | nil => rfl
  | cons i slots ih =>
      simp only [readUnarySlots, Runtime.statementPushBound, ih, max_self]

variable [DecidableEq K]

theorem stepAux_readUnarySlots (source : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (ambient : σ) (bits buffer : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) :
    TM2.stepAux (readUnarySlots source slots next) (ambient, buffer)
        (Function.update tapes source (unaryBits slots bits ++ suffix)) =
      TM2.stepAux next (ambient, MachineFixedBlockMap.fill slots bits buffer)
        (Function.update tapes source suffix) := by
  induction slots generalizing buffer tapes with
  | nil => simp [readUnarySlots, unaryBits, MachineFixedBlockMap.fill]
  | cons i slots ih =>
      cases hi : bits i <;>
        simp only [readUnarySlots, unaryBits, List.flatMap_cons, hi,
          GraphTables.bitWord, Bool.false_eq_true, ite_false, ite_true, encodeWord,
          List.replicate_zero, List.replicate_succ, List.nil_append,
          List.cons_append,
          TM2.stepAux, Function.update_self, List.head?_cons, Option.getD_some,
          List.tail_cons, Function.update_idem, MachineFixedBlockMap.fill,
          List.foldl_cons]
      · simpa [unaryBits, MachineFixedBlockMap.fill, hi, encodeWord, GraphTables.bitWord] using
          ih (Function.update buffer i false) tapes
      · simpa [unaryBits, MachineFixedBlockMap.fill, hi, encodeWord, GraphTables.bitWord] using
          ih (Function.update buffer i true) tapes

theorem stepAux_readUnaryAll (source : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool)
    (hinput : tapes source = unaryBits (List.ofFn id) bits ++ suffix) :
    TM2.stepAux (readUnarySlots source (List.ofFn id) next) state tapes =
      TM2.stepAux next (state.1, bits) (Function.update tapes source suffix) := by
  have h := stepAux_readUnarySlots source (List.ofFn id) next state.1 bits state.2 tapes suffix
  have hin : Function.update tapes source (unaryBits (List.ofFn id) bits ++ suffix) = tapes := by
    simpa only [← hinput] using Function.update_eq_self source tapes
  rw [hin, MachineFixedBlockMap.fill_all] at h
  exact h

def unaryBlockMapAt {M : Nat} (source destination : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  readUnarySlots source (List.ofFn id)
    (MachineFixedBlockMap.writeSlots destination (fun state => F state.2)
      (List.ofFn id).reverse
      (.load (fun state => (state.1, MachineFixedBlockMap.emptyBuffer N))
        (MachineFixedBlockMap.finishAt exit)))

theorem stepAux_unaryBlockMapAt {M : Nat} (source destination : K)
    (F : Buffer N → Buffer M) (exit : Option Λ) (hne : source ≠ destination)
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool) (suffix : List Bool)
    (hinput : tapes source = unaryBits (List.ofFn id) bits ++ suffix) :
    TM2.stepAux (unaryBlockMapAt source destination F exit) state tapes =
      { l := exit, var := (state.1, MachineFixedBlockMap.emptyBuffer N),
        stk := Function.update (Function.update tapes source suffix) destination
          (List.ofFn (F bits) ++ tapes destination) } := by
  unfold unaryBlockMapAt
  rw [stepAux_readUnaryAll source _ state bits tapes suffix hinput,
    MachineFixedBlockMap.stepAux_writeSlots]
  simp only [List.map_reverse, List.map_ofFn, Function.comp_id, List.reverse_reverse,
    Function.update_of_ne (Ne.symm hne), TM2.stepAux]
  cases exit <;> rfl

theorem step_unaryBlockMapAt {M : Nat} (source destination : K)
    (F : Buffer N → Buffer M) (exit : Option Λ) (hne : source ≠ destination)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (label : Λ) (atLabel : program label = unaryBlockMapAt source destination F exit)
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool) (suffix : List Bool)
    (hinput : tapes source = unaryBits (List.ofFn id) bits ++ suffix) :
    TM2.step program ⟨some label, state, tapes⟩ =
      some ⟨exit, (state.1, MachineFixedBlockMap.emptyBuffer N),
        Function.update (Function.update tapes source suffix) destination
          (List.ofFn (F bits) ++ tapes destination)⟩ := by
  simp only [TM2.step, atLabel,
    stepAux_unaryBlockMapAt source destination F exit hne state bits tapes suffix hinput]

def unaryBlockInTime {M : Nat} (source destination : K)
    (F : Buffer N → Buffer M) (exit : Option Λ) (hne : source ≠ destination)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (label : Λ) (atLabel : program label = unaryBlockMapAt source destination F exit)
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool) (suffix : List Bool)
    (hinput : tapes source = unaryBits (List.ofFn id) bits ++ suffix) :
    StateTransition.EvalsToInTime (TM2.step program) ⟨some label, state, tapes⟩
      (some ⟨exit, (state.1, MachineFixedBlockMap.emptyBuffer N),
        Function.update (Function.update tapes source suffix) destination
          (List.ofFn (F bits) ++ tapes destination)⟩) 1 where
  steps := 1
  evals_in_steps := step_unaryBlockMapAt source destination F exit hne program label
    atLabel state bits tapes suffix hinput
  steps_le_m := Nat.le_refl _

end RelationReader

theorem unaryBits_relation (relation : GraphTables.RelationTable) :
    unaryBits (List.ofFn id) (fun i => relation[i]) =
      encodeWords (GraphTables.relationWords relation) := by
  have h : List.ofFn (fun i : Fin 4096 => relation[i]) = relation.toList := by
    change List.ofFn (fun i : Fin 4096 => relation[i.val]) = relation.toList
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
  rw [unaryBits_eq_encodeWords]
  unfold GraphTables.relationWords
  rw [← h]
  simp only [List.map_ofFn, Function.comp_def, id_eq]

def readerStateEquiv (σ : Type) (N : Nat) :
    (((σ × Unit) × Option Bool) × Buffer N) ≃ (((σ × Buffer N) × Unit) × Option Bool) where
  toFun state := (((state.1.1.1, state.2), state.1.1.2), state.1.2)
  invFun state := (((state.1.1.1, state.1.2), state.2), state.1.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

end IndependentSetsGames.Foundations.Complexity.FinalCNFMachine

end OAI
