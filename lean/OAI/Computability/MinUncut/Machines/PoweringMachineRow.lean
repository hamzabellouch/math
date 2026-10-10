import Mathlib
import OAI.Computability.MinUncut.Machines.MachineLookup

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.PoweringMachineRow

open Turing
open MachineFixedBlockMap
open MinUncutGames.Foundations.PCP

abbrev Field (S : Nat) := (GraphTables.Label × GraphTables.Label) ⊕ (Fin S ⊕ Fin S)

def inputSize (t S : Nat) : Nat := t * (4096 + (S + S))

def fieldEquiv (S : Nat) : Field S ≃ Fin (4096 + (S + S)) :=
  (Equiv.sumCongr GraphTables.relationIndex
    (finSumFinEquiv : (Fin S ⊕ Fin S) ≃ Fin (S + S))).trans finSumFinEquiv

def inputEquiv (t S : Nat) : (Fin t × Field S) ≃ Fin (inputSize t S) :=
  (Equiv.prodCongr (Equiv.refl (Fin t)) (fieldEquiv S)).trans finProdFinEquiv

def packData {t S : Nat} (data : Fin t → Field S → Bool) : Buffer (inputSize t S) :=
  fun i => data ((inputEquiv t S).symm i).1 ((inputEquiv t S).symm i).2

@[simp] theorem packData_inputEquiv {t S : Nat}
    (data : Fin t → Field S → Bool) (k : Fin t) (f : Field S) :
    packData data (inputEquiv t S (k, f)) = data k f := by
  simp [packData]

def basePredicate {t S : Nat} (bits : Buffer (inputSize t S))
    (k : Fin t) (a b : GraphTables.Label) : Bool :=
  bits (inputEquiv t S (k, .inl (a, b)))

def leftMatches {t S : Nat} (bits : Buffer (inputSize t S))
    (k : Fin t) (i : Fin S) : Bool :=
  bits (inputEquiv t S (k, .inr (.inl i)))

def rightMatches {t S : Nat} (bits : Buffer (inputSize t S))
    (k : Fin t) (i : Fin S) : Bool :=
  bits (inputEquiv t S (k, .inr (.inr i)))

def firstMatch {S : Nat} (mask : Fin S → Bool) : Option (Fin S) :=
  (List.ofFn id).find? mask

theorem firstMatch_spec {S : Nat} (mask : Fin S → Bool) (i : Fin S) :
    firstMatch mask = some i ↔
      mask i = true ∧ ∃ before after,
        List.ofFn id = before ++ i :: after ∧ ∀ j ∈ before, mask j = false := by
  simpa only [firstMatch, Bool.not_eq_eq_eq_not, Bool.not_true] using
    (List.find?_eq_some_iff_append (xs := List.ofFn id) (p := mask) (b := i))

theorem firstMatch_none {S : Nat} (mask : Fin S → Bool) :
    firstMatch mask = none ↔ ∀ i, mask i = false := by
  simp [firstMatch, List.find?_eq_none, List.mem_ofFn]

def edgeAccept {t S q : Nat} (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (k : Fin t) (a b : Fin q) : Bool :=
  match firstMatch (leftMatches bits k), firstMatch (rightMatches bits k) with
  | some i, some j => basePredicate bits k (labelAt a i) (labelAt b j)
  | _, _ => false

theorem edgeAccept_of_matches {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (k : Fin t) (a b : Fin q) (i j : Fin S)
    (hl : firstMatch (leftMatches bits k) = some i)
    (hr : firstMatch (rightMatches bits k) = some j) :
    edgeAccept labelAt bits k a b = basePredicate bits k (labelAt a i) (labelAt b j) := by
  simp [edgeAccept, hl, hr]

def rowAccept {t S q : Nat} (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (a b : Fin q) : Bool :=
  (List.ofFn id).all (fun k : Fin t => edgeAccept labelAt bits k a b)

theorem rowAccept_eq_true {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (a b : Fin q) :
    rowAccept labelAt bits a b = true ↔ ∀ k, edgeAccept labelAt bits k a b = true := by
  simp [rowAccept, List.all_eq_true, List.mem_ofFn]

def rowBlock {t S q : Nat} (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) : Buffer (q * q) :=
  fun i => rowAccept labelAt bits
    ((GenericGraphTables.relationIndex q).symm i).1
    ((GenericGraphTables.relationIndex q).symm i).2

@[simp] theorem rowBlock_at {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (a b : Fin q) :
    rowBlock labelAt bits (GenericGraphTables.relationIndex q (a, b)) =
      rowAccept labelAt bits a b := by
  simp [rowBlock]

def encodeBit (b : Bool) : List Bool := if b then [true, false] else [false]

def encodeBits : List Bool → List Bool
  | [] => []
  | b :: bits => encodeBit b ++ encodeBits bits

@[simp] theorem encodeBits_append (xs ys : List Bool) :
    encodeBits (xs ++ ys) = encodeBits xs ++ encodeBits ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [encodeBits, ih, List.append_assoc]

theorem encodeBits_graphWords (bits : List Bool) :
    encodeBits bits = encodeWords (bits.map GraphTables.bitWord) := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [encodeBits, encodeBit, encodeWords,
      GraphTables.bitWord, encodeWord, ih]

theorem encodeBits_length_le (bits : List Bool) :
    (encodeBits bits).length ≤ 2 * bits.length := by
  induction bits with
  | nil => simp [encodeBits]
  | cons b bits ih =>
      cases b <;> simp only [encodeBits, encodeBit, Bool.false_eq_true,
        ite_false, ite_true, List.length_append, List.length_cons, List.length_nil] <;> omega

section Chains

variable {K Λ σ : Type} {N : Nat}

def readEncodedSlots (src : K) : List (Fin N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)
  | [], next => next
  | i :: slots, next =>
      .pop src (fun state head =>
        (state.1, Function.update state.2 i (head.getD false)))
        (.branch (fun state => state.2 i)
          (.pop src (fun state _ => state) (readEncodedSlots src slots next))
          (readEncodedSlots src slots next))

variable [DecidableEq K]

theorem stepAux_readEncodedSlots (src : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (ambient : σ) (bits buffer : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) :
    TM2.stepAux (readEncodedSlots src slots next) (ambient, buffer)
        (Function.update tapes src (encodeBits (slots.map bits) ++ suffix)) =
      TM2.stepAux next (ambient, fill slots bits buffer)
        (Function.update tapes src suffix) := by
  induction slots generalizing buffer tapes with
  | nil => simp [readEncodedSlots, encodeBits, fill]
  | cons i slots ih =>
      cases hb : bits i <;>
        simpa only [readEncodedSlots, List.map_cons, encodeBits, encodeBit, hb,
          Bool.false_eq_true, ite_false, ite_true, List.cons_append,
          List.nil_append, TM2.stepAux, Function.update_self, List.head?_cons,
          Option.getD_some, List.tail_cons, Function.update_idem, Bool.cond_false,
          Bool.cond_true, fill, List.foldl_cons] using
          ih (Function.update buffer i (bits i)) tapes

theorem stepAux_readEncodedAll (src : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) (hinput : tapes src = encodeBits (List.ofFn bits) ++ suffix) :
    TM2.stepAux (readEncodedSlots src (List.ofFn id) next) state tapes =
      TM2.stepAux next (state.1, bits) (Function.update tapes src suffix) := by
  have h := stepAux_readEncodedSlots src (List.ofFn id) next
    state.1 bits state.2 tapes suffix
  have hin : Function.update tapes src
      (encodeBits ((List.ofFn id).map bits) ++ suffix) = tapes := by
    simpa only [List.map_ofFn, Function.comp_id, ← hinput] using
      Function.update_eq_self src tapes
  rw [hin, fill_all] at h
  exact h

omit [DecidableEq K] in
theorem statementPushBound_readEncodedSlots (src : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    Runtime.statementPushBound (readEncodedSlots src slots next) =
      Runtime.statementPushBound next := by
  induction slots with
  | nil => rfl
  | cons i slots ih => simp [readEncodedSlots, Runtime.statementPushBound, ih]

def writeEncodedSlots {M : Nat} (dst : K) (emit : σ → Buffer M) : List (Fin M) →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | [], next => next
  | i :: slots, next => .push dst (fun _ => false)
      (.branch (fun state => emit state i)
        (.push dst (fun _ => true) (writeEncodedSlots dst emit slots next))
        (writeEncodedSlots dst emit slots next))

theorem stepAux_writeEncodedSlots {M : Nat} (dst : K) (emit : σ → Buffer M)
    (slots : List (Fin M)) (next : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (writeEncodedSlots dst emit slots next) state tapes =
      TM2.stepAux next state
        (Function.update tapes dst
          (encodeBits ((slots.map (emit state)).reverse) ++ tapes dst)) := by
  induction slots generalizing tapes with
  | nil => simp [writeEncodedSlots, encodeBits]
  | cons i slots ih =>
      cases hb : emit state i <;>
        simp only [writeEncodedSlots, TM2.stepAux, hb, Bool.cond_false, Bool.cond_true]
      all_goals rw [ih]
      all_goals simp [Function.update_idem, List.map_cons, List.reverse_cons,
        encodeBits_append, encodeBits, encodeBit, hb, List.append_assoc]

omit [DecidableEq K] in
theorem statementPushBound_writeEncodedSlots {M : Nat}
    (dst : K) (emit : σ → Buffer M) (slots : List (Fin M))
    (next : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    Runtime.statementPushBound (writeEncodedSlots dst emit slots next) =
      2 * slots.length + Runtime.statementPushBound next := by
  induction slots with
  | nil => simp [writeEncodedSlots]
  | cons i slots ih =>
      simp only [writeEncodedSlots, Runtime.statementPushBound, ih, List.length_cons]
      omega

end Chains

section Block

variable {K Λ σ : Type} {N M : Nat}

def encodedBlockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  readEncodedSlots src (List.ofFn id)
    (writeEncodedSlots dst (fun state => F state.2) (List.ofFn id).reverse
      (.load (fun state => (state.1, emptyBuffer N)) next))

def encodedBlockAt (src dst : K) (F : Buffer N → Buffer M) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  encodedBlockStmt src dst F (finishAt exit)

theorem statementPushBound_encodedBlockAt (src dst : K)
    (F : Buffer N → Buffer M) (exit : Option Λ) :
    Runtime.statementPushBound (encodedBlockAt (σ := σ) src dst F exit) = 2 * M := by
  cases exit <;> simp [encodedBlockAt, encodedBlockStmt,
    statementPushBound_readEncodedSlots, statementPushBound_writeEncodedSlots,
    finishAt, Runtime.statementPushBound]

variable [DecidableEq K]

theorem stepAux_encodedBlockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = encodeBits (List.ofFn bits) ++ suffix) :
    TM2.stepAux (encodedBlockStmt src dst F next) state tapes =
      TM2.stepAux next (state.1, emptyBuffer N)
        (Function.update (Function.update tapes src suffix) dst
          (encodeBits (List.ofFn (F bits)) ++ tapes dst)) := by
  unfold encodedBlockStmt
  rw [stepAux_readEncodedAll src _ state bits tapes suffix hinput,
    stepAux_writeEncodedSlots]
  simp only [List.map_reverse, List.map_ofFn, Function.comp_id, List.reverse_reverse,
    Function.update_of_ne (Ne.symm hne), TM2.stepAux]

theorem stepAux_encodedBlockAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = encodeBits (List.ofFn bits) ++ suffix) :
    TM2.stepAux (encodedBlockAt src dst F exit) state tapes =
      { l := exit, var := (state.1, emptyBuffer N),
        stk := Function.update (Function.update tapes src suffix) dst
          (encodeBits (List.ofFn (F bits)) ++ tapes dst) } := by
  rw [encodedBlockAt, stepAux_encodedBlockStmt src dst F _ hne bits suffix state tapes hinput]
  cases exit <;> rfl

theorem step_encodedBlockAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (label : Λ) (hprogram : program label = encodedBlockAt src dst F exit)
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = encodeBits (List.ofFn bits) ++ suffix) :
    TM2.step program { l := some label, var := state, stk := tapes } =
      some { l := exit
             var := (state.1, emptyBuffer N)
             stk := Function.update (Function.update tapes src suffix) dst
               (encodeBits (List.ofFn (F bits)) ++ tapes dst) } := by
  simp only [TM2.step, hprogram,
    stepAux_encodedBlockAt src dst F exit hne bits suffix state tapes hinput]

end Block

def rowAt {K Λ σ : Type} {t S q : Nat} (src dst : K)
    (labelAt : Fin q → Fin S → GraphTables.Label) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer (inputSize t S)) :=
  encodedBlockAt src dst (rowBlock labelAt) exit

def machine {t S q : Nat} (labelAt : Fin q → Fin S → GraphTables.Label) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit × Buffer (inputSize t S)
  initialState := ((), emptyBuffer (inputSize t S))
  m _ := rowAt false true labelAt none

theorem machine_statementPushBound {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label) :
    Runtime.statementPushBound ((machine (t := t) labelAt).m ()) = 2 * (q * q) :=
  statementPushBound_encodedBlockAt false true (rowBlock labelAt) none

def machineInTime {t S q : Nat} (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (suffix : List Bool)
    (register : Buffer (inputSize t S)) (tapes : Bool → List Bool)
    (hinput : tapes false = encodeBits (List.ofFn bits) ++ suffix) :
    StateTransition.EvalsToInTime (machine (t := t) labelAt).step
      ⟨some (), ((), register), tapes⟩
      (some ⟨none, ((), emptyBuffer (inputSize t S)),
        Function.update (Function.update tapes false suffix) true
          (encodeBits (List.ofFn (rowBlock labelAt bits)) ++ tapes true)⟩) 1 where
  steps := 1
  evals_in_steps := by
    change TM2.step (fun _ : Unit => rowAt false true labelAt none)
        { l := some (), var := ((), register), stk := tapes } =
      some { l := none
             var := ((), emptyBuffer (inputSize t S))
             stk := Function.update (Function.update tapes false suffix) true
               (encodeBits (List.ofFn (rowBlock labelAt bits)) ++ tapes true) }
    exact step_encodedBlockAt false true (rowBlock labelAt) (none : Option Unit)
      (fun _ => rowAt false true labelAt none) () rfl (by decide)
      bits suffix ((), register) tapes hinput
  steps_le_m := le_rfl

end MinUncutGames.Foundations.Complexity.PoweringMachineRow

end
section
namespace MinUncutGames.Foundations.Complexity.PoweringMachineLoop

open Turing

inductive HeaderTape
  | source | counter | vertices | darts
  deriving DecidableEq

protected abbrev HeaderTape.enumList : List HeaderTape := [.source, .counter, .vertices, .darts]

protected theorem HeaderTape.enumList_getElem?_ctorIdx_eq (x : HeaderTape) :
    HeaderTape.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem HeaderTape.enumList_nodup : HeaderTape.enumList.Nodup := by decide

instance : Fintype HeaderTape where
  elems := ⟨HeaderTape.enumList, HeaderTape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive HeaderLabel
  | initialize | scan
  deriving DecidableEq

protected abbrev HeaderLabel.enumList : List HeaderLabel := [.initialize, .scan]

protected theorem HeaderLabel.enumList_getElem?_ctorIdx_eq (x : HeaderLabel) :
    HeaderLabel.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem HeaderLabel.enumList_nodup : HeaderLabel.enumList.Nodup := by decide

instance : Fintype HeaderLabel where
  elems := ⟨HeaderLabel.enumList, HeaderLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev HeaderAlphabet (_ : HeaderTape) := Bool
abbrev HeaderState (σ : Type) := σ × Option Bool

def pushTrue {K Λ σ : Type} (destination : K) : Nat →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | 0, next => next
  | count + 1, next => pushTrue destination count (.push destination (fun _ => true) next)

theorem stepAux_pushTrue {K Λ σ : Type} [DecidableEq K]
    (destination : K) (count : Nat) (next : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (pushTrue destination count next) state tapes =
      TM2.stepAux next state
        (Function.update tapes destination (List.replicate count true ++ tapes destination)) := by
  induction count generalizing next with
  | zero => simp [pushTrue]
  | succ count ih =>
    rw [pushTrue, ih]
    simp [TM2.stepAux, List.replicate_succ, Function.update_idem]

theorem pushTrue_pushBound {K Λ σ : Type} (destination : K) (count : Nat)
    (next : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    Runtime.statementPushBound (pushTrue destination count next) =
      count + Runtime.statementPushBound next := by
  induction count generalizing next with
  | zero => simp [pushTrue]
  | succ count ih => simp only [pushTrue, ih, Runtime.statementPushBound]; omega

def headerProgram {σ : Type} (B : Nat) :
    HeaderLabel → TM2.Stmt HeaderAlphabet HeaderLabel (HeaderState σ)
  | .initialize =>
      .push .counter (fun _ => false)
        (.push .vertices (fun _ => false)
          (.push .darts (fun _ => false)
            (.load (fun state => (state.1, none)) (.goto fun _ => .scan))))
  | .scan =>
      .pop .source (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.push .counter (fun _ => true)
            (.push .vertices (fun _ => true)
              (pushTrue .darts B
                (.load (fun state => (state.1, none)) (.goto fun _ => .scan)))))
          (.load (fun state => (state.1, none)) .halt))

def headerMachine (B : Nat) : FinTM2 where
  K := HeaderTape
  k₀ := .source
  k₁ := .darts
  Γ := HeaderAlphabet
  Λ := HeaderLabel
  main := .initialize
  σ := HeaderState Unit
  initialState := ((), none)
  m := headerProgram B

def initialTapes (n : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => encodeWord n ++ suffix
  | _ => []

def scanTapes (B remaining processed : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => encodeWord remaining ++ suffix
  | .counter => encodeWord processed
  | .vertices => encodeWord processed
  | .darts => encodeWord (B * processed)

def finalTapes (B n : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => suffix
  | .counter => encodeWord n
  | .vertices => encodeWord n
  | .darts => encodeWord (B * n)

def scanConfiguration {σ : Type} (B remaining processed : Nat)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.Cfg HeaderAlphabet HeaderLabel (HeaderState σ) :=
  ⟨some .scan, (ambient, register), scanTapes B remaining processed suffix⟩

def finalConfiguration {σ : Type} (B n : Nat) (suffix : List Bool) (ambient : σ) :
    TM2.Cfg HeaderAlphabet HeaderLabel (HeaderState σ) :=
  ⟨none, (ambient, none), finalTapes B n suffix⟩

theorem initializeStep {σ : Type} (B n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (headerProgram B)
      ⟨some .initialize, (ambient, register), initialTapes n suffix⟩ =
        some (scanConfiguration B n 0 suffix ambient none) := by
  simp only [TM2.step, headerProgram, TM2.stepAux]
  congr 2
  funext tape
  cases tape <;> simp [initialTapes, scanTapes, encodeWord]

theorem scanStep_zero {σ : Type} (B processed : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (headerProgram B) (scanConfiguration B 0 processed suffix ambient register) =
      some (finalConfiguration B processed suffix ambient) := by
  simp only [TM2.step, scanConfiguration, headerProgram, TM2.stepAux,
    scanTapes, encodeWord, List.replicate_zero, List.nil_append, List.singleton_append,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_false]
  congr 2
  funext tape
  cases tape <;> simp [finalTapes, scanTapes]

theorem scanStep_succ {σ : Type} (B remaining processed : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (headerProgram B)
      (scanConfiguration B (remaining + 1) processed suffix ambient register) =
      some (scanConfiguration B remaining (processed + 1) suffix ambient none) := by
  simp only [TM2.step, scanConfiguration, headerProgram, TM2.stepAux,
    scanTapes, encodeWord, List.replicate_succ, List.cons_append,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_true]
  rw [stepAux_pushTrue]
  simp only [TM2.stepAux]
  congr 2
  funext tape
  cases tape <;>
    simp [scanTapes, encodeWord, Nat.mul_add, List.replicate_add,
      List.replicate_succ, List.append_assoc, Nat.add_comm,
      -List.replicate_append_replicate]

theorem scanTrace {σ : Type} (B remaining processed : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (headerProgram B)))^[remaining + 1]
      (some (scanConfiguration B remaining processed suffix ambient register)) =
      some (finalConfiguration B (processed + remaining) suffix ambient) := by
  induction remaining generalizing processed register with
  | zero =>
    simpa only [Nat.add_zero, Nat.zero_add, Function.iterate_one, MachineComposition.advance_some] using
      scanStep_zero B processed suffix ambient register
  | succ remaining ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step (headerProgram B)))^[remaining + 1]
      (TM2.step (headerProgram B)
        (scanConfiguration B (remaining + 1) processed suffix ambient register)) = _
    rw [scanStep_succ, ih]
    simp only [Nat.add_comm, Nat.add_left_comm]

theorem headerTrace {σ : Type} (B n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (headerProgram B)))^[n + 2]
      (some ⟨some .initialize, (ambient, register), initialTapes n suffix⟩) =
      some (finalConfiguration B n suffix ambient) := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (headerProgram B)))^[n + 1]
    (TM2.step (headerProgram B)
      ⟨some .initialize, (ambient, register), initialTapes n suffix⟩) = _
  rw [initializeStep]
  simpa only [Nat.zero_add] using scanTrace B n 0 suffix ambient none

def headerInTime {σ : Type} (B n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (headerProgram B))
      ⟨some .initialize, (ambient, register), initialTapes n suffix⟩
      (some (finalConfiguration B n suffix ambient)) (n + 2) where
  steps := n + 2
  evals_in_steps := headerTrace B n suffix ambient register
  steps_le_m := Nat.le_refl _

def remainingRows (rowBlock : Nat → List Bool) (n r : Nat) : List Bool :=
  (List.range' r (n - r)).flatMap rowBlock

@[simp] theorem remainingRows_top (rowBlock : Nat → List Bool) (n : Nat) :
    remainingRows rowBlock n n = [] := by simp [remainingRows]

theorem remainingRows_step (rowBlock : Nat → List Bool) (n r : Nat) (hr : r < n) :
    remainingRows rowBlock n r = rowBlock r ++ remainingRows rowBlock n (r + 1) := by
  have h : n - r = (n - (r + 1)) + 1 := by omega
  simp only [remainingRows, h, List.range'_succ, List.flatMap_cons]

section Enumeration

variable {K Λ σ : Type} [DecidableEq K]

def rowBase (output : K) (base : K → List Bool)
    (rowBlock : Nat → List Bool) (n r : Nat) : K → List Bool :=
  Function.update base output (remainingRows rowBlock n r ++ base output)

def VertexBodyTraces (counter output : K) (guardLabel bodyLabel : Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (rowBlock : Nat → List Bool) (cost : Nat → Nat) (n : Nat) : Prop :=
  ∀ r, r < n → ∀ accumulator : List Bool,
    (MachineComposition.advance (TM2.step program))^[cost r]
      (some ⟨some bodyLabel, (ambient, none),
        MachineUnaryCounter.counterTapes counter
          (Function.update base output accumulator) r suffix⟩) =
      some ⟨some guardLabel, (ambient, none),
        MachineUnaryCounter.counterTapes counter
          (Function.update base output (rowBlock r ++ accumulator)) r suffix⟩

theorem vertexBodyTraces_to_counted (counter output : K) (guardLabel bodyLabel : Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (rowBlock : Nat → List Bool) (cost : Nat → Nat) (n : Nat)
    (bodies : VertexBodyTraces counter output guardLabel bodyLabel program
      base suffix ambient rowBlock cost n) :
    MachineCountedLoop.BodyTraces counter guardLabel bodyLabel program suffix
      (fun _ => ambient) (fun _ => none) (rowBase output base rowBlock n) cost n := by
  intro r hr
  have h := bodies r hr (remainingRows rowBlock n (r + 1) ++ base output)
  simpa only [MachineCountedLoop.bodyConfiguration, MachineCountedLoop.guardConfiguration,
    rowBase, remainingRows_step rowBlock n r hr, List.append_assoc] using h

def vertexLoopInTime (counter output : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atGuard : program guardLabel = MachineUnaryCounter.guard counter bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool) (ambient : σ)
    (rowBlock : Nat → List Bool) (cost : Nat → Nat) (n bodyBound : Nat)
    (bodies : VertexBodyTraces counter output guardLabel bodyLabel program
      base suffix ambient rowBlock cost n)
    (bounded : ∀ r, r < n → cost r ≤ bodyBound) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, (ambient, none),
        MachineUnaryCounter.counterTapes counter base n suffix⟩
      (some ⟨some exitLabel, (ambient, none),
        MachineUnaryCounter.counterTapes counter
          (rowBase output base rowBlock n 0) 0 suffix⟩)
      (n * (bodyBound + 1) + 1) := by
  have h := MachineCountedLoop.loopInTime counter guardLabel bodyLabel exitLabel
    program atGuard suffix (fun _ => ambient) (fun _ => none)
    (rowBase output base rowBlock n) cost n bodyBound
    (vertexBodyTraces_to_counted counter output guardLabel bodyLabel program
      base suffix ambient rowBlock cost n bodies) bounded
  simpa [MachineCountedLoop.guardConfiguration, MachineCountedLoop.exitConfiguration,
    rowBase] using h

theorem vertexLoop_output (counter output : K) (different : output ≠ counter)
    (base : K → List Bool) (suffix : List Bool) (rowBlock : Nat → List Bool) (n : Nat) :
    MachineUnaryCounter.counterTapes counter (rowBase output base rowBlock n 0) 0 suffix output =
      remainingRows rowBlock n 0 ++ base output := by
  simp [MachineUnaryCounter.counterTapes, rowBase, different]

def varyingRowBase (output : K) (base : Nat → K → List Bool)
    (rowBlock : Nat → List Bool) (n r : Nat) : K → List Bool :=
  Function.update (base r) output (remainingRows rowBlock n r ++ base n output)

def VaryingVertexBodyTraces (counter output : K) (guardLabel bodyLabel : Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (base : Nat → K → List Bool) (suffix : List Bool) (ambient : Nat → σ)
    (rowBlock : Nat → List Bool) (cost : Nat → Nat) (n : Nat) : Prop :=
  ∀ r, r < n → ∀ accumulator : List Bool,
    (MachineComposition.advance (TM2.step program))^[cost r]
      (some ⟨some bodyLabel, (ambient (r + 1), none),
        MachineUnaryCounter.counterTapes counter
          (Function.update (base (r + 1)) output accumulator) r suffix⟩) =
      some ⟨some guardLabel, (ambient r, none),
        MachineUnaryCounter.counterTapes counter
          (Function.update (base r) output (rowBlock r ++ accumulator)) r suffix⟩

theorem varyingVertexBodyTraces_to_counted (counter output : K) (guardLabel bodyLabel : Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (base : Nat → K → List Bool) (suffix : List Bool) (ambient : Nat → σ)
    (rowBlock : Nat → List Bool) (cost : Nat → Nat) (n : Nat)
    (bodies : VaryingVertexBodyTraces counter output guardLabel bodyLabel program
      base suffix ambient rowBlock cost n) :
    MachineCountedLoop.BodyTraces counter guardLabel bodyLabel program suffix
      ambient (fun _ => none) (varyingRowBase output base rowBlock n) cost n := by
  intro r hr
  have h := bodies r hr (remainingRows rowBlock n (r + 1) ++ base n output)
  simpa only [MachineCountedLoop.bodyConfiguration, MachineCountedLoop.guardConfiguration,
    varyingRowBase, remainingRows_step rowBlock n r hr, List.append_assoc] using h

def vertexLoopInTime_varying (counter output : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atGuard : program guardLabel = MachineUnaryCounter.guard counter bodyLabel exitLabel)
    (base : Nat → K → List Bool) (suffix : List Bool) (ambient : Nat → σ)
    (rowBlock : Nat → List Bool) (cost : Nat → Nat) (n bodyBound : Nat)
    (bodies : VaryingVertexBodyTraces counter output guardLabel bodyLabel program
      base suffix ambient rowBlock cost n)
    (bounded : ∀ r, r < n → cost r ≤ bodyBound) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, (ambient n, none),
        MachineUnaryCounter.counterTapes counter (base n) n suffix⟩
      (some ⟨some exitLabel, (ambient 0, none),
        MachineUnaryCounter.counterTapes counter
          (varyingRowBase output base rowBlock n 0) 0 suffix⟩)
      (n * (bodyBound + 1) + 1) := by
  have h := MachineCountedLoop.loopInTime counter guardLabel bodyLabel exitLabel
    program atGuard suffix ambient (fun _ => none)
    (varyingRowBase output base rowBlock n) cost n bodyBound
    (varyingVertexBodyTraces_to_counted counter output guardLabel bodyLabel program
      base suffix ambient rowBlock cost n bodies) bounded
  simpa [MachineCountedLoop.guardConfiguration, MachineCountedLoop.exitConfiguration,
    varyingRowBase] using h

theorem vertexLoop_varying_output (counter output : K) (different : output ≠ counter)
    (base : Nat → K → List Bool) (suffix : List Bool)
    (rowBlock : Nat → List Bool) (n : Nat) :
    MachineUnaryCounter.counterTapes counter
        (varyingRowBase output base rowBlock n 0) 0 suffix output =
      remainingRows rowBlock n 0 ++ base n output := by
  simp [MachineUnaryCounter.counterTapes, varyingRowBase, different]

end Enumeration

end MinUncutGames.Foundations.Complexity.PoweringMachineLoop

end

end OAI
