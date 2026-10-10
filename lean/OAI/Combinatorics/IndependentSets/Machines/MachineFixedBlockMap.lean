import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.RawInitialMachineBudget

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineFixedBlockMap

open Turing

abbrev Buffer (N : Nat) := Fin N → Bool

def emptyBuffer (N : Nat) : Buffer N := fun _ => false

section Chains

variable {K Λ σ : Type} {N : Nat}

def readSlots (src : K) : List (Fin N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)
  | [], next => next
  | i :: slots, next =>
      .pop src (fun state head =>
        (state.1, Function.update state.2 i (head.getD false)))
        (readSlots src slots next)

def fill (slots : List (Fin N)) (bits buffer : Buffer N) : Buffer N :=
  slots.foldl (fun buffer i => Function.update buffer i (bits i)) buffer

theorem fill_apply (slots : List (Fin N)) (bits buffer : Buffer N) (i : Fin N) :
    fill slots bits buffer i = if i ∈ slots then bits i else buffer i := by
  induction slots generalizing buffer with
  | nil => simp [fill]
  | cons j slots ih =>
      change fill slots bits (Function.update buffer j (bits j)) i = _
      rw [ih]
      by_cases hm : i ∈ slots
      · simp [hm]
      · by_cases he : i = j <;> simp [hm, he]

@[simp] theorem fill_all (bits buffer : Buffer N) :
    fill (List.ofFn id) bits buffer = bits := by
  funext i
  simp [fill_apply, List.mem_ofFn]

variable [DecidableEq K]

theorem stepAux_readSlots (src : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (ambient : σ) (bits buffer : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) :
    TM2.stepAux (readSlots src slots next) (ambient, buffer)
        (Function.update tapes src (slots.map bits ++ suffix)) =
      TM2.stepAux next (ambient, fill slots bits buffer)
        (Function.update tapes src suffix) := by
  induction slots generalizing buffer tapes with
  | nil => simp [readSlots, fill]
  | cons i slots ih =>
      simpa only [readSlots, List.map_cons, List.cons_append, TM2.stepAux,
        Function.update_self, List.head?_cons, Option.getD_some, List.tail_cons,
        Function.update_idem, fill, List.foldl_cons] using
        ih (Function.update buffer i (bits i)) tapes

theorem stepAux_readAll (src : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) (hinput : tapes src = List.ofFn bits ++ suffix) :
    TM2.stepAux (readSlots src (List.ofFn id) next) state tapes =
      TM2.stepAux next (state.1, bits) (Function.update tapes src suffix) := by
  have h := stepAux_readSlots src (List.ofFn id) next state.1 bits state.2 tapes suffix
  have hin : Function.update tapes src ((List.ofFn id).map bits ++ suffix) = tapes := by
    simpa only [List.map_ofFn, Function.comp_id, ← hinput] using
      Function.update_eq_self src tapes
  rw [hin, fill_all] at h
  exact h

omit [DecidableEq K] in
theorem statementPushBound_readSlots (src : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    Runtime.statementPushBound (readSlots src slots next) =
      Runtime.statementPushBound next := by
  induction slots with
  | nil => rfl
  | cons i slots ih => exact ih

def writeSlots {M : Nat} (dst : K) (emit : σ → Buffer M) : List (Fin M) →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | [], next => next
  | i :: slots, next => .push dst (fun state => emit state i) (writeSlots dst emit slots next)

theorem stepAux_writeSlots {M : Nat} (dst : K) (emit : σ → Buffer M)
    (slots : List (Fin M)) (next : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (writeSlots dst emit slots next) state tapes =
      TM2.stepAux next state
        (Function.update tapes dst ((slots.map (emit state)).reverse ++ tapes dst)) := by
  induction slots generalizing tapes with
  | nil => simp [writeSlots]
  | cons i slots ih =>
      simp only [writeSlots, TM2.stepAux]
      rw [ih]
      simp only [Function.update_self, Function.update_idem, List.map_cons,
        List.reverse_cons, List.append_assoc, List.singleton_append]

omit [DecidableEq K] in
theorem statementPushBound_writeSlots {M : Nat} (dst : K) (emit : σ → Buffer M)
    (slots : List (Fin M)) (next : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    Runtime.statementPushBound (writeSlots dst emit slots next) =
      slots.length + Runtime.statementPushBound next := by
  induction slots with
  | nil => simp [writeSlots]
  | cons i slots ih =>
      simp only [writeSlots, Runtime.statementPushBound, ih, List.length_cons]
      omega

end Chains

section Block

variable {K Λ σ : Type} {N M : Nat}

def blockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  readSlots src (List.ofFn id)
    (writeSlots dst (fun state => F state.2) (List.ofFn id).reverse
      (.load (fun state => (state.1, emptyBuffer N)) next))

def finishAt (exit : Option Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def blockMapAt (src dst : K) (F : Buffer N → Buffer M) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  blockStmt src dst F (finishAt exit)

theorem statementPushBound_blockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    Runtime.statementPushBound (blockStmt src dst F next) =
      M + Runtime.statementPushBound next := by
  simp only [blockStmt, statementPushBound_readSlots, statementPushBound_writeSlots,
    Runtime.statementPushBound, List.length_reverse, List.length_ofFn]

theorem statementPushBound_blockMapAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) :
    Runtime.statementPushBound (blockMapAt (σ := σ) src dst F exit) = M := by
  cases exit <;> simp [blockMapAt, statementPushBound_blockStmt, finishAt,
    Runtime.statementPushBound]

variable [DecidableEq K]

theorem stepAux_blockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = List.ofFn bits ++ suffix) :
    TM2.stepAux (blockStmt src dst F next) state tapes =
      TM2.stepAux next (state.1, emptyBuffer N)
        (Function.update (Function.update tapes src suffix) dst
          (List.ofFn (F bits) ++ tapes dst)) := by
  unfold blockStmt
  rw [stepAux_readAll src _ state bits tapes suffix hinput, stepAux_writeSlots]
  simp only [List.map_reverse, List.map_ofFn, Function.comp_id, List.reverse_reverse,
    Function.update_of_ne (Ne.symm hne), TM2.stepAux]

theorem stepAux_blockMapAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = List.ofFn bits ++ suffix) :
    TM2.stepAux (blockMapAt src dst F exit) state tapes =
      { l := exit, var := (state.1, emptyBuffer N),
        stk := Function.update (Function.update tapes src suffix) dst
          (List.ofFn (F bits) ++ tapes dst) } := by
  rw [blockMapAt, stepAux_blockStmt src dst F _ hne bits suffix state tapes hinput]
  cases exit <;> rfl

theorem step_blockMapAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (label : Λ) (hprogram : program label = blockMapAt src dst F exit)
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = List.ofFn bits ++ suffix) :
    TM2.step program { l := some label, var := state, stk := tapes } =
      some { l := exit
             var := (state.1, emptyBuffer N)
             stk := Function.update (Function.update tapes src suffix) dst
               (List.ofFn (F bits) ++ tapes dst) } := by
  simp only [TM2.step, hprogram,
    stepAux_blockMapAt src dst F exit hne bits suffix state tapes hinput]

end Block

def machine {N M : Nat} (F : Buffer N → Buffer M) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit × Buffer N
  initialState := ((), emptyBuffer N)
  m _ := blockMapAt false true F none

theorem machine_statementPushBound {N M : Nat} (F : Buffer N → Buffer M) :
    Runtime.statementPushBound ((machine F).m ()) = M :=
  statementPushBound_blockMapAt false true F none

end IndependentSetsGames.Foundations.Complexity.MachineFixedBlockMap

end OAI
