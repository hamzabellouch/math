import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.PCP.GenericGraphTables

namespace OAI

section

/-!
# Finite tape program for a powered relation row

The radius, address count, and powered alphabet size are fixed machine
parameters. The machine consumes live base predicate bits and endpoint-match
bits. Its finite register selects the first matching address, looks up the two
fixed powered labels, and conjoins the bounded list of base predicates.

Both input and output bits use the graph-table unary natural-word codec.
The theorems below describe actual TM2 transitions, not assumed execution
costs. Producing this input block from live graph rotor lookups is a separate
frontend composition obligation; no graph table occurs in the machine's
finite transition function.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRow

open Turing
open MachineFixedBlockMap
open UniqueGamesTheorem.Foundations.PCP

abbrev Field (S : Nat) := (GraphTables.Label × GraphTables.Label) ⊕ (Fin S ⊕ Fin S)

def inputSize (t S : Nat) : Nat := t * (4096 + (S + S))

def fieldEquiv (S : Nat) : Field S ≃ Fin (4096 + (S + S)) :=
  (Equiv.sumCongr GraphTables.relationIndex
    (finSumFinEquiv : (Fin S ⊕ Fin S) ≃ Fin (S + S))).trans finSumFinEquiv

def inputEquiv (t S : Nat) : (Fin t × Field S) ≃ Fin (inputSize t S) :=
  (Equiv.prodCongr (Equiv.refl (Fin t)) (fieldEquiv S)).trans finProdFinEquiv

/-- Proof-level organization of exactly the finite bits physically read. -/
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

/-- The scan order is the fixed increasing finite-index order. -/
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

/-- `labelAt` is a fixed finite lookup table determined by the reduction
parameters, for example `decodeLabel a (allAddresses.get i)`. -/
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

/-- Every powered-label pair is written in the canonical row-major order. -/
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

/-- Read one zero-delimited unary Boolean field for each fixed register slot.
The second pop occurs exactly when the value is one. -/
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

/-- The delimiter is pushed first, then the optional unary one; writing slots
in reverse order gives the canonical field order on the destination stack. -/
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

/-- The input predicate/match block is consumed. The exact unary predicate
row is prepended; the remaining input, old output, and ambient register are
accounted for in the actual transition witness. -/
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

end UniqueGamesTheorem.Foundations.Complexity.PoweringMachineRow

end

end OAI
