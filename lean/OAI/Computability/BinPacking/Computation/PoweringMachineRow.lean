import Mathlib.Computability.TuringMachine.Computable
import OAI.Computability.BinPacking.PCP.RawInitialMachineBudget

namespace OAI

namespace BinPackingGames.Foundations.Complexity.Runtime

def statementPushBound {K : Type} {Γ : K → Type} {Λ σ : Type} :
    Turing.TM2.Stmt Γ Λ σ → Nat
  | .push _ _ next => statementPushBound next + 1
  | .peek _ _ next => statementPushBound next
  | .pop _ _ next => statementPushBound next
  | .load _ next => statementPushBound next
  | .branch _ yes no => max (statementPushBound yes) (statementPushBound no)
  | .goto _ => 0
  | .halt => 0

def maxLabelPushes {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) : List Λ → Nat
  | [] => 0
  | label :: rest => max (statementPushBound (program label)) (maxLabelPushes program rest)

theorem maxLabelPushes_ge {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) (labels : List Λ) (label : Λ)
    (member : label ∈ labels) :
    statementPushBound (program label) ≤ maxLabelPushes program labels := by
  induction labels with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

noncomputable def programPushBound (tm : Turing.FinTM2) : Nat :=
  maxLabelPushes tm.m tm.ΛFin.elems.toList

theorem statement_le_programPushBound (tm : Turing.FinTM2) (label : tm.Λ) :
    statementPushBound (tm.m label) ≤ programPushBound tm := by
  apply maxLabelPushes_ge
  simpa using tm.ΛFin.complete label

theorem stepAuxStackLength {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]
    (stmt : Turing.TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) (k : K) :
    ((Turing.TM2.stepAux stmt state tapes).stk k).length ≤
      (tapes k).length + statementPushBound stmt := by
  induction stmt generalizing state tapes with
  | push j f next ih =>
      have changed : ((Function.update tapes j (f state :: tapes j)) k).length ≤
          (tapes k).length + 1 := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      have h := ih state (Function.update tapes j (f state :: tapes j))
      simp only [Turing.TM2.stepAux, statementPushBound]
      omega
  | peek j f next ih =>
      simpa only [Turing.TM2.stepAux, statementPushBound] using
        ih (f state (tapes j).head?) tapes
  | pop j f next ih =>
      have changed : ((Function.update tapes j (tapes j).tail) k).length ≤
          (tapes k).length := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      have h := ih (f state (tapes j).head?) (Function.update tapes j (tapes j).tail)
      simp only [Turing.TM2.stepAux, statementPushBound]
      omega
  | load f next ih =>
      simpa only [Turing.TM2.stepAux, statementPushBound] using ih (f state) tapes
  | branch condition yes no ihYes ihNo =>
      cases decision : condition state with
      | false =>
          have h := ihNo state tapes
          have hm := Nat.le_max_right (statementPushBound yes) (statementPushBound no)
          simp only [Turing.TM2.stepAux, statementPushBound, decision, Bool.cond_false]
          omega
      | true =>
          have h := ihYes state tapes
          have hm := Nat.le_max_left (statementPushBound yes) (statementPushBound no)
          simp only [Turing.TM2.stepAux, statementPushBound, decision, Bool.cond_true]
          omega
  | goto f => simp [Turing.TM2.stepAux, statementPushBound]
  | halt => simp [Turing.TM2.stepAux, statementPushBound]

private theorem iterateSizeBound {α : Type} (f : α → α) (size : α → Nat) (C : Nat)
    (oneStep : ∀ x, size (f x) ≤ size x + C) (n : Nat) (x : α) :
    size ((f^[n]) x) ≤ size x + n * C := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := oneStep ((f^[n]) x)
      have bound : size (f ((f^[n]) x)) ≤ size x + (n + 1) * C := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [Function.iterate_succ_apply'] using bound

theorem executionSizeBound {σ : Type} (step : σ → Option σ) (size : σ → Nat) (C : Nat)
    (oneStep : ∀ a b, step a = some b → size b ≤ size a + C)
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime step start (some finish) budget) :
    size finish ≤ size start + budget * C := by
  let liftedSize : Option σ → Nat := fun state => (state.map size).getD 0
  have liftedStep : ∀ state : Option σ,
      liftedSize (state.bind step) ≤ liftedSize state + C := by
    intro state
    cases state with
    | none => simp [liftedSize]
    | some a =>
        cases transition : step a with
        | none => simp [liftedSize, transition]
        | some b => simpa [liftedSize, transition] using oneStep a b transition
  have bound := iterateSizeBound (fun state : Option σ => state.bind step)
    liftedSize C liftedStep execution.steps (some start)
  change liftedSize ((flip bind step)^[execution.steps] (some start)) ≤ _ at bound
  rw [execution.evals_in_steps] at bound
  simp only [liftedSize, Option.map_some, Option.getD_some] at bound
  exact Nat.le_trans bound (Nat.add_le_add_left
    (Nat.mul_le_mul_right C execution.steps_le_m) _)

theorem stepStackLength (tm : Turing.FinTM2) (k : tm.K) (a b : tm.Cfg)
    (transition : tm.step a = some b) :
    (b.stk k).length ≤ (a.stk k).length + programPushBound tm := by
  cases a with
  | mk label state tapes =>
      cases label with
      | none => simp [Turing.FinTM2.step, Turing.TM2.step] at transition
      | some label =>
          have result := Option.some.inj transition
          rw [← result]
          exact Nat.le_trans (stepAuxStackLength _ _ _ _)
            (Nat.add_le_add_left (statement_le_programPushBound tm label) _)

theorem initialStackLength (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((Turing.initList tm input).stk k).length ≤ input.length := by
  simp only [Turing.initList]
  split
  next same => subst k; exact Nat.le_refl _
  next _ => simp

@[simp] theorem haltedOutputLength (tm : Turing.FinTM2) (output : List (tm.Γ tm.k₁)) :
    ((Turing.haltList tm output).stk tm.k₁).length = output.length := by
  simp [Turing.haltList]

theorem outputLength_le (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (budget : Nat)
    (execution : Turing.TM2OutputsInTime tm input (some output) budget) :
    output.length ≤ input.length + budget * programPushBound tm := by
  have bound := executionSizeBound tm.step (fun cfg => (cfg.stk tm.k₁).length)
    (programPushBound tm) (stepStackLength tm tm.k₁) execution
  calc
    output.length = ((Turing.haltList tm output).stk tm.k₁).length := (haltedOutputLength tm output).symm
    _ ≤ ((Turing.initList tm input).stk tm.k₁).length + budget * programPushBound tm := bound
    _ ≤ input.length + budget * programPushBound tm :=
      Nat.add_le_add_right (initialStackLength tm input tm.k₁) _

theorem encodedOutputLength {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (certificate : Turing.TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤
      (Polynomial.X + Polynomial.C (programPushBound certificate.tm) * certificate.time).eval
        (ea a).length := by
  have bound := outputLength_le certificate.tm _ _ _ (certificate.outputsFun a)
  simpa only [List.length_map, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, Nat.mul_comm] using bound

end BinPackingGames.Foundations.Complexity.Runtime

namespace BinPackingGames.Foundations.Complexity.MachineFixedBlockMap

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

end BinPackingGames.Foundations.Complexity.MachineFixedBlockMap

namespace BinPackingGames.Foundations.Complexity.PoweringMachineRow

open Turing
open MachineFixedBlockMap
open BinPackingGames.Foundations.PCP

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

end BinPackingGames.Foundations.Complexity.PoweringMachineRow

end OAI
