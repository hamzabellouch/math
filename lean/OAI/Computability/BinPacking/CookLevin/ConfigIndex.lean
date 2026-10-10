import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import OAI.Computability.BinPacking.CookLevin.BoundedExecution

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.StackEncoding

variable {Γ : Type*}

abbrev Cells (Γ : Type*) (S : Nat) := Fin S → Option Γ

def encode (S : Nat) (xs : List Γ) : Cells Γ S := fun i => xs[i.val]?

def read {S : Nat} (cells : Cells Γ S) (n : Nat) : Option Γ :=
  if h : n < S then cells ⟨n, h⟩ else none

def head {S : Nat} (cells : Cells Γ S) : Option Γ := read cells 0

def isEmpty {S : Nat} (cells : Cells Γ S) : Bool := (head cells).isNone

def popShift {S : Nat} (cells : Cells Γ S) : Cells Γ S :=
  fun i => read cells (i.val + 1)

def pushShift {S : Nat} (a : Γ) (cells : Cells Γ S) : Cells Γ S :=
  fun i => if h : i.val = 0 then some a else cells ⟨i.val - 1, by omega⟩

@[simp] theorem encode_apply (S : Nat) (xs : List Γ) (i : Fin S) :
    encode S xs i = xs[i.val]? := rfl

@[simp] theorem encode_nil (S : Nat) : encode S ([] : List Γ) = fun _ => none := by
  funext i
  simp [encode]

@[simp] theorem read_at {S : Nat} (cells : Cells Γ S) (i : Fin S) :
    read cells i.val = cells i := by
  simp [read, i.isLt]

theorem read_of_capacity_le {S : Nat} (cells : Cells Γ S) (n : Nat) (h : S ≤ n) :
    read cells n = none := by
  simp [read, Nat.not_lt.mpr h]

theorem read_encode {S : Nat} (xs : List Γ) (hlen : xs.length ≤ S) (n : Nat) :
    read (encode S xs) n = xs[n]? := by
  by_cases hn : n < S
  · simp [read, encode, hn]
  · have hx : xs.length ≤ n := by omega
    simp [read, hn, List.getElem?_eq_none hx]

theorem head_encode {S : Nat} (xs : List Γ) (hlen : xs.length ≤ S) :
    head (encode S xs) = xs.head? := by
  rw [head, read_encode xs hlen, List.head?_eq_getElem?]

theorem head_encode_eq_none_iff {S : Nat} (xs : List Γ) (hlen : xs.length ≤ S) :
    head (encode S xs) = none ↔ xs = [] := by
  rw [head_encode xs hlen, List.head?_eq_none_iff]

theorem isEmpty_encode {S : Nat} (xs : List Γ) (hlen : xs.length ≤ S) :
    isEmpty (encode S xs) = xs.isEmpty := by
  rw [isEmpty, head_encode xs hlen]
  cases xs <;> rfl

theorem isEmpty_encode_eq_true_iff {S : Nat} (xs : List Γ) (hlen : xs.length ≤ S) :
    isEmpty (encode S xs) = true ↔ xs = [] := by
  rw [isEmpty_encode xs hlen]
  cases xs <;> simp

theorem encode_tail {S : Nat} (xs : List Γ) (hlen : xs.length ≤ S) :
    encode S xs.tail = popShift (encode S xs) := by
  funext i
  change xs.tail[i.val]? = read (encode S xs) (i.val + 1)
  rw [read_encode xs hlen, List.getElem?_tail]

theorem encode_cons {S : Nat} (a : Γ) (xs : List Γ) :
    encode S (a :: xs) = pushShift a (encode S xs) := by
  funext i
  by_cases hi : i.val = 0 <;> simp [encode, pushShift, List.getElem?_cons, hi]

theorem tail_length_le {S : Nat} (xs : List Γ) (hlen : xs.length ≤ S) :
    xs.tail.length ≤ S := by
  have ht : xs.tail.length ≤ xs.length := by simp
  omega

theorem cons_length_le {S : Nat} (a : Γ) (xs : List Γ) (hroom : xs.length < S) :
    (a :: xs).length ≤ S := by
  simp only [List.length_cons]
  omega

theorem encode_injective {S : Nat} {xs ys : List Γ}
    (hx : xs.length ≤ S) (hy : ys.length ≤ S)
    (h : encode S xs = encode S ys) : xs = ys := by
  apply List.ext_getElem?
  intro n
  rw [← read_encode xs hx n, ← read_encode ys hy n, h]

theorem encode_eq_iff {S : Nat} {xs ys : List Γ}
    (hx : xs.length ≤ S) (hy : ys.length ≤ S) :
    encode S xs = encode S ys ↔ xs = ys :=
  ⟨encode_injective hx hy, fun h => congrArg (encode S) h⟩

abbrev BoundedStack (Γ : Type*) (S : Nat) := {xs : List Γ // xs.length ≤ S}

def boundedEncoding (S : Nat) : BoundedStack Γ S ↪ Cells Γ S where
  toFun xs := encode S xs.val
  inj' := by
    intro xs ys h
    apply Subtype.ext
    exact encode_injective xs.property ys.property h

def boundedPop {S : Nat} (xs : BoundedStack Γ S) : BoundedStack Γ S :=
  ⟨xs.val.tail, tail_length_le xs.val xs.property⟩

def boundedPush {S : Nat} (a : Γ) (xs : BoundedStack Γ S)
    (hroom : xs.val.length < S) : BoundedStack Γ S :=
  ⟨a :: xs.val, cons_length_le a xs.val hroom⟩

theorem boundedPop_correct {S : Nat} (xs : BoundedStack Γ S) :
    boundedEncoding S (boundedPop xs) = popShift (boundedEncoding S xs) :=
  encode_tail xs.val xs.property

theorem boundedPush_correct {S : Nat} (a : Γ) (xs : BoundedStack Γ S)
    (hroom : xs.val.length < S) :
    boundedEncoding S (boundedPush a xs hroom) = pushShift a (boundedEncoding S xs) :=
  encode_cons a xs.val

variable {K : Type} {Alphabet : K → Type} [DecidableEq K]

def encodeTapes (S : Nat) (tapes : ∀ k, List (Alphabet k)) :
    ∀ k, Cells (Alphabet k) S := fun k => encode S (tapes k)

theorem encodeTapes_update (S : Nat) (tapes : ∀ k, List (Alphabet k))
    (k : K) (replacement : List (Alphabet k)) :
    encodeTapes S (Function.update tapes k replacement) =
      Function.update (encodeTapes S tapes) k (encode S replacement) := by
  funext j
  by_cases h : j = k
  · subst j; simp [encodeTapes]
  · simp [encodeTapes, h]

theorem encodeTapes_pop {S : Nat} (tapes : ∀ k, List (Alphabet k)) (k : K)
    (hlen : (tapes k).length ≤ S) :
    encodeTapes S (Function.update tapes k (tapes k).tail) =
      Function.update (encodeTapes S tapes) k (popShift (encode S (tapes k))) := by
  rw [encodeTapes_update, encode_tail (tapes k) hlen]

theorem encodeTapes_push (S : Nat) (tapes : ∀ k, List (Alphabet k)) (k : K)
    (a : Alphabet k) :
    encodeTapes S (Function.update tapes k (a :: tapes k)) =
      Function.update (encodeTapes S tapes) k (pushShift a (encode S (tapes k))) := by
  rw [encodeTapes_update, encode_cons]

omit [DecidableEq K] in
theorem encodeTapes_injective {S : Nat} {tapes other : ∀ k, List (Alphabet k)}
    (h : ∀ k, (tapes k).length ≤ S) (ho : ∀ k, (other k).length ≤ S)
    (heq : encodeTapes S tapes = encodeTapes S other) : tapes = other := by
  funext k
  exact encode_injective (h k) (ho k) (congrFun heq k)

end BinPackingGames.Foundations.Complexity.CookLevin.StackEncoding

namespace BinPackingGames.Foundations.Complexity.CookLevin

open Target

inductive Gate where
  | const (value : Bool)
  | not (input : Nat)
  | and (left right : Nat)
  | or (left right : Nat)
  deriving DecidableEq

def Gate.Bounded (g : Gate) (bound : Nat) : Prop :=
  match g with
  | .const _ => True
  | .not x => x < bound
  | .and x y | .or x y => x < bound ∧ y < bound

def Gate.eval (g : Gate) (wires : Nat → Bool) : Bool :=
  match g with
  | .const b => b
  | .not x => !(wires x)
  | .and x y => wires x && wires y
  | .or x y => wires x || wires y

theorem Gate.bounded_mono (g : Gate) {a b : Nat} (hab : a ≤ b)
    (h : g.Bounded a) : g.Bounded b := by
  cases g with
  | const _ => trivial
  | not _ => exact Nat.lt_of_lt_of_le h hab
  | and _ _ => exact ⟨Nat.lt_of_lt_of_le h.1 hab, Nat.lt_of_lt_of_le h.2 hab⟩
  | or _ _ => exact ⟨Nat.lt_of_lt_of_le h.1 hab, Nat.lt_of_lt_of_le h.2 hab⟩

theorem Gate.eval_congr (g : Gate) {bound : Nat} (hg : g.Bounded bound)
    (A B : Nat → Bool) (h : ∀ j, j < bound → A j = B j) :
    g.eval A = g.eval B := by
  cases g with
  | const b => rfl
  | not x => simp only [Gate.eval, h x hg]
  | and x y => simp only [Gate.eval, h x hg.1, h y hg.2]
  | or x y => simp only [Gate.eval, h x hg.1, h y hg.2]

def Ordered (start : Nat) (gates : List Gate) : Prop :=
  ∀ i (hi : i < gates.length), gates[i].Bounded (start + i)

def Consistent (start : Nat) (gates : List Gate) (wires : Nat → Bool) : Prop :=
  ∀ i (hi : i < gates.length), wires (start + i) = gates[i].eval wires

@[simp] theorem ordered_nil (start : Nat) : Ordered start [] := by
  intro i hi
  simp at hi

theorem ordered_cons (start : Nat) (g : Gate) (gs : List Gate) :
    Ordered start (g :: gs) ↔ g.Bounded start ∧ Ordered (start + 1) gs := by
  unfold Ordered
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 := h 0 (by simp)
      change g.Bounded (start + 0) at h0
      simpa only [Nat.add_zero] using h0
    · intro i hi
      have ht := h (i + 1) (by simpa using hi)
      change gs[i].Bounded (start + (i + 1)) at ht
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
  · rintro ⟨hg, hgs⟩ i hi
    cases i with
    | zero => simpa using hg
    | succ i =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hgs i (by simpa using hi)

@[simp] theorem consistent_nil (start : Nat) (A : Nat → Bool) :
    Consistent start [] A := by
  intro i hi
  simp at hi

theorem consistent_cons (start : Nat) (g : Gate) (gs : List Gate) (A : Nat → Bool) :
    Consistent start (g :: gs) A ↔ A start = g.eval A ∧ Consistent (start + 1) gs A := by
  unfold Consistent
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 := h 0 (by simp)
      change A (start + 0) = g.eval A at h0
      simpa only [Nat.add_zero] using h0
    · intro i hi
      have ht := h (i + 1) (by simpa using hi)
      change A (start + (i + 1)) = gs[i].eval A at ht
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
  · rintro ⟨hg, hgs⟩ i hi
    cases i with
    | zero => simpa using hg
    | succ i =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hgs i (by simpa using hi)

theorem consistent_append (start : Nat) (gs hs : List Gate) (A : Nat → Bool) :
    Consistent start (gs ++ hs) A ↔
      Consistent start gs A ∧ Consistent (start + gs.length) hs A := by
  induction gs generalizing start with
  | nil => simp [Consistent]
  | cons g gs ih =>
    simp only [List.cons_append, consistent_cons, ih, List.length_cons]
    simp only [Nat.add_comm, Nat.add_left_comm, and_assoc]

def run (start : Nat) : List Gate → (Nat → Bool) → (Nat → Bool)
  | [], A => A
  | g :: gs, A => run (start + 1) gs (Function.update A start (g.eval A))

theorem run_eq_of_lt (start : Nat) (gs : List Gate) (A : Nat → Bool)
    (j : Nat) (hj : j < start) : run start gs A j = A j := by
  induction gs generalizing start A with
  | nil => rfl
  | cons g gs ih =>
    rw [run, ih (start + 1) _ (by omega)]
    exact Function.update_of_ne (by omega) _ _

theorem run_append (start : Nat) (gs hs : List Gate) (A : Nat → Bool) :
    run start (gs ++ hs) A = run (start + gs.length) hs (run start gs A) := by
  induction gs generalizing start A with
  | nil => simp [run]
  | cons g gs ih =>
    simpa [run, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (start + 1) (Function.update A start (g.eval A))

@[simp] theorem run_singleton (start : Nat) (g : Gate) (A : Nat → Bool) :
    run start [g] A = Function.update A start (g.eval A) := rfl

@[simp] theorem run_singleton_here (start : Nat) (g : Gate) (A : Nat → Bool) :
    run start [g] A start = g.eval A := by simp

theorem run_singleton_other (start : Nat) (g : Gate) (A : Nat → Bool)
    (j : Nat) (hj : j ≠ start) : run start [g] A j = A j := by
  simp [hj]

theorem Ordered.append {start : Nat} {gs hs : List Gate}
    (hg : Ordered start gs) (hh : Ordered (start + gs.length) hs) :
    Ordered start (gs ++ hs) := by
  induction gs generalizing start with
  | nil => simpa using hh
  | cons g gs ih =>
    rcases (ordered_cons start g gs).mp hg with ⟨h0, ht⟩
    apply (ordered_cons start g (gs ++ hs)).mpr
    refine ⟨h0, ih ht ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem run_consistent (start : Nat) (gs : List Gate) (A : Nat → Bool)
    (h : Ordered start gs) : Consistent start gs (run start gs A) := by
  induction gs generalizing start A with
  | nil => exact consistent_nil start A
  | cons g gs ih =>
    rcases (ordered_cons start g gs).mp h with ⟨hg, hgs⟩
    apply (consistent_cons start g gs _).mpr
    constructor
    · have hout : run start (g :: gs) A start = g.eval A := by
        rw [run, run_eq_of_lt (start + 1) gs _ start (by omega)]
        exact Function.update_self start _ _
      rw [hout]
      exact Gate.eval_congr g hg A (run start (g :: gs) A)
        (fun j hj => (run_eq_of_lt start (g :: gs) A j hj).symm)
    · exact ih (start + 1) _ hgs

theorem run_unique (start : Nat) (gs : List Gate) (A B : Nat → Bool)
    (ho : Ordered start gs) (hc : Consistent start gs B)
    (ha : ∀ j, j < start → A j = B j) :
    ∀ j, j < start + gs.length → run start gs A j = B j := by
  induction gs generalizing start A with
  | nil =>
    intro j hj
    exact ha j (by simpa using hj)
  | cons g gs ih =>
    rcases (ordered_cons start g gs).mp ho with ⟨hg, hgs⟩
    rcases (consistent_cons start g gs B).mp hc with ⟨hb, hbs⟩
    have hnext : ∀ j, j < start + 1 →
        Function.update A start (g.eval A) j = B j := by
      intro j hj
      by_cases heq : j = start
      · subst j
        rw [Function.update_self]
        exact (Gate.eval_congr g hg A B ha).trans hb.symm
      · rw [Function.update_of_ne heq]
        exact ha j (by omega)
    intro j hj
    exact ih (start + 1) _ hgs hbs hnext j (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj)

structure Circuit where
  inputs : Nat
  gates : List Gate
  ordered : Ordered inputs gates
  output : Fin (inputs + gates.length)

abbrev Circuit.wires (C : Circuit) : Nat := C.inputs + C.gates.length

def inputEnv {n : Nat} (input : Fin n → Bool) : Nat → Bool :=
  fun j => if h : j < n then input ⟨j, h⟩ else false

def Circuit.evalWires (C : Circuit) (input : Fin C.inputs → Bool) : Nat → Bool :=
  run C.inputs C.gates (inputEnv input)

def Circuit.eval (C : Circuit) (input : Fin C.inputs → Bool) : Bool :=
  C.evalWires input C.output.val

theorem Circuit.evalWires_input (C : Circuit) (input : Fin C.inputs → Bool)
    (j : Fin C.inputs) : C.evalWires input j.val = input j := by
  rw [Circuit.evalWires, run_eq_of_lt _ _ _ _ j.isLt]
  simp [inputEnv, j.isLt]

theorem Circuit.evalWires_consistent (C : Circuit) (input : Fin C.inputs → Bool) :
    Consistent C.inputs C.gates (C.evalWires input) :=
  run_consistent C.inputs C.gates (inputEnv input) C.ordered

theorem Consistent.congr {start : Nat} {gs : List Gate} {A B : Nat → Bool}
    (hc : Consistent start gs A) (ho : Ordered start gs)
    (hab : ∀ j, j < start + gs.length → A j = B j) :
    Consistent start gs B := by
  intro i hi
  have hbound := Gate.bounded_mono gs[i] (by omega : start + i ≤ start + gs.length)
    (ho i hi)
  calc
    B (start + i) = A (start + i) := (hab _ (by omega)).symm
    _ = gs[i].eval A := hc i hi
    _ = gs[i].eval B := Gate.eval_congr gs[i] hbound A B hab

def unitClause {n : Nat} (wire : Fin n) (positive : Bool) : Clause n :=
  #v[⟨wire, positive⟩, ⟨wire, positive⟩, ⟨wire, positive⟩]

def gateClauses {n : Nat} (output : Fin n) : (g : Gate) → g.Bounded n → List (Clause n)
  | .const b, _ => [unitClause output b, unitClause output b, unitClause output b]
  | .not x, h =>
    let v : Fin n := ⟨x, h⟩
    [#v[⟨output, true⟩, ⟨v, true⟩, ⟨v, true⟩],
     #v[⟨output, false⟩, ⟨v, false⟩, ⟨v, false⟩],
     #v[⟨output, true⟩, ⟨v, true⟩, ⟨v, true⟩]]
  | .and x y, h =>
    let vx : Fin n := ⟨x, h.1⟩
    let vy : Fin n := ⟨y, h.2⟩
    [#v[⟨output, false⟩, ⟨vx, true⟩, ⟨vx, true⟩],
     #v[⟨output, false⟩, ⟨vy, true⟩, ⟨vy, true⟩],
     #v[⟨output, true⟩, ⟨vx, false⟩, ⟨vy, false⟩]]
  | .or x y, h =>
    let vx : Fin n := ⟨x, h.1⟩
    let vy : Fin n := ⟨y, h.2⟩
    [#v[⟨output, true⟩, ⟨vx, false⟩, ⟨vx, false⟩],
     #v[⟨output, true⟩, ⟨vy, false⟩, ⟨vy, false⟩],
     #v[⟨output, false⟩, ⟨vx, true⟩, ⟨vy, true⟩]]

@[simp] theorem gateClauses_length {n : Nat} (output : Fin n)
    (g : Gate) (h : g.Bounded n) : (gateClauses output g h).length = 3 := by
  cases g <;> rfl

theorem gateClauses_correct {n : Nat} (output : Fin n) (g : Gate)
    (h : g.Bounded n) (A : Fin n → Bool) :
    (∀ c ∈ gateClauses output g h, c.eval A = true) ↔
      A output = g.eval (inputEnv A) := by
  cases g with
  | const b =>
    simp only [gateClauses, List.forall_mem_cons]
    cases b <;> cases ho : A output <;>
      simp [unitClause, Clause.eval, Literal.eval, Gate.eval, ho]
  | not x =>
    change x < n at h
    simp only [gateClauses, List.forall_mem_cons]
    cases ho : A output <;> cases hx : A ⟨x, h⟩ <;>
      simp [Clause.eval, Literal.eval, Gate.eval, inputEnv, h, ho, hx]
  | and x y =>
    change x < n ∧ y < n at h
    simp only [gateClauses, List.forall_mem_cons]
    cases ho : A output <;> cases hx : A ⟨x, h.1⟩ <;> cases hy : A ⟨y, h.2⟩ <;>
      simp [Clause.eval, Literal.eval, Gate.eval, inputEnv, h.1, h.2,
        ho, hx, hy]
  | or x y =>
    change x < n ∧ y < n at h
    simp only [gateClauses, List.forall_mem_cons]
    cases ho : A output <;> cases hx : A ⟨x, h.1⟩ <;> cases hy : A ⟨y, h.2⟩ <;>
      simp [Clause.eval, Literal.eval, Gate.eval, inputEnv, h.1, h.2,
        ho, hx, hy]

def Circuit.gateAt (C : Circuit) (i : Fin C.gates.length) : Gate := C.gates[i.val]

def Circuit.gateOutput (C : Circuit) (i : Fin C.gates.length) : Fin C.wires :=
  ⟨C.inputs + i.val, by have hi := i.isLt; simp only [Circuit.wires]; omega⟩

theorem Circuit.gateBounded (C : Circuit) (i : Fin C.gates.length) :
    (C.gateAt i).Bounded C.wires :=
  Gate.bounded_mono _ (by have hi := i.isLt; simp only [Circuit.wires]; omega)
    (C.ordered i.val i.isLt)

def Circuit.gateBlock (C : Circuit) (i : Fin C.gates.length) : List (Clause C.wires) :=
  gateClauses (C.gateOutput i) (C.gateAt i) (C.gateBounded i)

def Circuit.toFormula (C : Circuit) : Formula where
  «variables» := C.wires
  clauses := (List.finRange C.gates.length).flatMap C.gateBlock ++ [unitClause C.output true]

@[simp] theorem Circuit.toFormula_variables (C : Circuit) :
    C.toFormula.variables = C.inputs + C.gates.length := rfl

@[simp] theorem Circuit.toFormula_clause_count (C : Circuit) :
    C.toFormula.clauses.length = 3 * C.gates.length + 1 := by
  have h : ∀ is : List (Fin C.gates.length),
      (is.flatMap C.gateBlock).length = 3 * is.length := by
    intro is
    induction is with
    | nil => rfl
    | cons i is ih =>
      simp only [List.flatMap_cons, List.length_append, Circuit.gateBlock,
        gateClauses_length, List.length_cons] at *
      omega
  simp [Circuit.toFormula, h]

theorem Circuit.toFormula_satisfied_iff (C : Circuit) (A : Fin C.wires → Bool) :
    (∀ c ∈ C.toFormula.clauses, c.eval A = true) ↔
      Consistent C.inputs C.gates (inputEnv A) ∧ A C.output = true := by
  constructor
  · intro h
    constructor
    · intro i hi
      let idx : Fin C.gates.length := ⟨i, hi⟩
      have hblock : ∀ c ∈ C.gateBlock idx, c.eval A = true := by
        intro c hc
        apply h c
        apply List.mem_append.mpr
        left
        exact List.mem_flatMap.mpr ⟨idx, by simp, hc⟩
      have heq := (gateClauses_correct (C.gateOutput idx) (C.gateAt idx)
        (C.gateBounded idx) A).mp hblock
      have hlt : C.inputs + i < C.wires := by simp only [Circuit.wires]; omega
      simpa [inputEnv, hlt, Circuit.gateOutput, Circuit.gateAt, idx] using heq
    · have hu := h (unitClause C.output true)
        (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
      simpa [unitClause, Clause.eval, Literal.eval] using hu
  · rintro ⟨hc, ho⟩ c hmem
    rcases List.mem_append.mp hmem with hblock | hunit
    · obtain ⟨i, _, hci⟩ := List.mem_flatMap.mp hblock
      apply (gateClauses_correct (C.gateOutput i) (C.gateAt i)
        (C.gateBounded i) A).mpr ?_ c hci
      have heq := hc i.val i.isLt
      have hlt : C.inputs + i.val < C.wires := (C.gateOutput i).isLt
      simpa [inputEnv, hlt, Circuit.gateOutput, Circuit.gateAt] using heq
    · have heq : c = unitClause C.output true := List.mem_singleton.mp hunit
      subst c
      simpa [unitClause, Clause.eval, Literal.eval] using ho

def Circuit.restrictAssignment (C : Circuit) (A : Fin C.wires → Bool) :
    Fin C.inputs → Bool := fun j =>
  A ⟨j.val, by have hj := j.isLt; simp only [Circuit.wires]; omega⟩

theorem Circuit.toFormula_satisfiable_iff_eval (C : Circuit) :
    C.toFormula.Satisfiable ↔ ∃ input : Fin C.inputs → Bool, C.eval input = true := by
  constructor
  · rintro ⟨A, hA⟩
    rcases (C.toFormula_satisfied_iff A).mp hA with ⟨hc, ho⟩
    refine ⟨C.restrictAssignment A, ?_⟩
    have hinput : ∀ j, j < C.inputs →
        inputEnv (C.restrictAssignment A) j = inputEnv A j := by
      intro j hj
      have ht : j < C.wires := by simp only [Circuit.wires]; omega
      simp [inputEnv, hj, ht, Circuit.restrictAssignment]
    have hu := run_unique C.inputs C.gates (inputEnv (C.restrictAssignment A))
      (inputEnv A) C.ordered hc hinput C.output.val C.output.isLt
    have heval : C.eval (C.restrictAssignment A) = A C.output := by
      have hout : C.output.val < C.wires := C.output.isLt
      simpa [Circuit.eval, Circuit.evalWires, inputEnv, hout] using hu
    exact heval.trans ho
  · rintro ⟨input, hinput⟩
    let A : Fin C.wires → Bool := fun j => C.evalWires input j.val
    refine ⟨A, (C.toFormula_satisfied_iff A).mpr ⟨?_, hinput⟩⟩
    apply Consistent.congr (C.evalWires_consistent input) C.ordered
    intro j hj
    have ht : j < C.wires := hj
    simp [inputEnv, ht, A]

theorem Circuit.toFormula_extending_iff_eval (C : Circuit) (input : Fin C.inputs → Bool) :
    (∃ A : Fin C.wires → Bool, C.restrictAssignment A = input ∧
      ∀ c ∈ C.toFormula.clauses, c.eval A = true) ↔ C.eval input = true := by
  constructor
  · rintro ⟨A, hext, hA⟩
    rcases (C.toFormula_satisfied_iff A).mp hA with ⟨hc, ho⟩
    have hinput : ∀ j, j < C.inputs → inputEnv input j = inputEnv A j := by
      intro j hj
      rw [← hext]
      have ht : j < C.wires := by simp only [Circuit.wires]; omega
      simp [inputEnv, hj, ht, Circuit.restrictAssignment]
    have hu := run_unique C.inputs C.gates (inputEnv input) (inputEnv A)
      C.ordered hc hinput C.output.val C.output.isLt
    have heval : C.eval input = A C.output := by
      have hout : C.output.val < C.wires := C.output.isLt
      simpa [Circuit.eval, Circuit.evalWires, inputEnv, hout] using hu
    exact heval.trans ho
  · intro hinput
    let A : Fin C.wires → Bool := fun j => C.evalWires input j.val
    refine ⟨A, ?_, (C.toFormula_satisfied_iff A).mpr ⟨?_, hinput⟩⟩
    · funext j
      simpa [Circuit.restrictAssignment, A] using C.evalWires_input input j
    · apply Consistent.congr (C.evalWires_consistent input) C.ordered
      intro j hj
      have ht : j < C.wires := hj
      simp [inputEnv, ht, A]

end BinPackingGames.Foundations.Complexity.CookLevin

namespace BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

open Turing
open StackEncoding BoundedExecution

inductive Expr (ι : Type*) where
  | input (index : ι)
  | const (value : Bool)
  | not (arg : Expr ι)
  | and (left right : Expr ι)
  | or (left right : Expr ι)

namespace Expr

variable {ι : Type*}

def eval (input : ι → Bool) : Expr ι → Bool
  | .input i => input i
  | .const b => b
  | .not e => !(eval input e)
  | .and e f => eval input e && eval input f
  | .or e f => eval input e || eval input f

theorem eval_congr (e : Expr ι) (u v : ι → Bool) (h : ∀ i, u i = v i) :
    e.eval u = e.eval v := by
  have : u = v := funext h
  rw [this]

def rename {κ : Type*} (f : ι → κ) : Expr ι → Expr κ
  | .input i => .input (f i)
  | .const b => .const b
  | .not e => .not (e.rename f)
  | .and e g => .and (e.rename f) (g.rename f)
  | .or e g => .or (e.rename f) (g.rename f)

@[simp] theorem eval_rename {κ : Type*} (f : ι → κ) (e : Expr ι) (input : κ → Bool) :
    (e.rename f).eval input = e.eval (fun i => input (f i)) := by
  induction e <;> simp_all [rename, eval]

def size : Expr ι → Nat
  | .input _ | .const _ => 1
  | .not e => e.size + 1
  | .and e f | .or e f => e.size + f.size + 1

theorem size_pos (e : Expr ι) : 0 < e.size := by
  cases e <;> simp [size]

@[simp] theorem size_rename {κ : Type*} (f : ι → κ) (e : Expr ι) :
    (e.rename f).size = e.size := by
  induction e <;> simp_all [rename, size]

def root (start : Nat) (e : Expr ι) : Nat := start + e.size - 1

theorem root_lt (start : Nat) (e : Expr ι) : e.root start < start + e.size := by
  have := e.size_pos
  unfold root
  omega

@[simp] theorem root_not (start : Nat) (e : Expr ι) :
    (Expr.not e).root start = start + e.size := by
  simp only [root, size]
  omega

@[simp] theorem root_and (start : Nat) (e f : Expr ι) :
    (Expr.and e f).root start = start + (e.size + f.size) := by
  simp only [root, size]
  omega

@[simp] theorem root_or (start : Nat) (e f : Expr ι) :
    (Expr.or e f).root start = start + (e.size + f.size) := by
  simp only [root, size]
  omega

def gates (wire : ι → Nat) (start : Nat) : Expr ι → List Gate
  | .input i => [.or (wire i) (wire i)]
  | .const b => [.const b]
  | .not e => e.gates wire start ++ [.not (e.root start)]
  | .and e f => e.gates wire start ++ f.gates wire (start + e.size) ++
      [.and (e.root start) (f.root (start + e.size))]
  | .or e f => e.gates wire start ++ f.gates wire (start + e.size) ++
      [.or (e.root start) (f.root (start + e.size))]

@[simp] theorem gates_length (e : Expr ι) (wire : ι → Nat) (start : Nat) :
    (e.gates wire start).length = e.size := by
  induction e generalizing start <;> simp_all [gates, size, Nat.add_assoc]

private theorem ordered_singleton (start : Nat) (g : Gate) (h : g.Bounded start) :
    Ordered start [g] := by
  exact (ordered_cons start g []).mpr ⟨h, ordered_nil _⟩

theorem gates_ordered (e : Expr ι) (wire : ι → Nat) (start : Nat)
    (hw : ∀ i, wire i < start) : Ordered start (e.gates wire start) := by
  induction e generalizing start with
  | input i => exact ordered_singleton start _ ⟨hw i, hw i⟩
  | const b => exact ordered_singleton start _ trivial
  | not e ih =>
    apply (ih start hw).append
    simpa only [gates_length] using
      ordered_singleton (start + e.size) (.not (e.root start)) (e.root_lt start)
  | and e f ihe ihf =>
    have hf := ihf (start + e.size) (fun i => lt_of_lt_of_le (hw i) (by omega))
    have hp : Ordered start (e.gates wire start ++ f.gates wire (start + e.size)) :=
      (ihe start hw).append (by simpa only [gates_length] using hf)
    apply hp.append
    simp only [List.length_append, gates_length]
    apply ordered_singleton
    exact ⟨lt_of_lt_of_le (e.root_lt start) (by omega), by
      simpa only [Nat.add_assoc] using f.root_lt (start + e.size)⟩
  | or e f ihe ihf =>
    have hf := ihf (start + e.size) (fun i => lt_of_lt_of_le (hw i) (by omega))
    have hp : Ordered start (e.gates wire start ++ f.gates wire (start + e.size)) :=
      (ihe start hw).append (by simpa only [gates_length] using hf)
    apply hp.append
    simp only [List.length_append, gates_length]
    apply ordered_singleton
    exact ⟨lt_of_lt_of_le (e.root_lt start) (by omega), by
      simpa only [Nat.add_assoc] using f.root_lt (start + e.size)⟩

private theorem consistent_singleton (start : Nat) (g : Gate) (A : Nat → Bool)
    (h : Consistent start [g] A) : A start = g.eval A := by
  exact ((consistent_cons start g [] A).mp h).1

theorem eval_of_consistent (e : Expr ι) (wire : ι → Nat) (start : Nat)
    (A : Nat → Bool) (h : Consistent start (e.gates wire start) A) :
    A (e.root start) = e.eval (fun i => A (wire i)) := by
  induction e generalizing start with
  | input i =>
    simpa [gates, root, size, Gate.eval, eval] using
      consistent_singleton start (.or (wire i) (wire i)) A h
  | const b =>
    simpa [gates, root, size, Gate.eval, eval] using
      consistent_singleton start (.const b) A h
  | not e ih =>
    obtain ⟨he, hg⟩ := (consistent_append start _ _ A).mp h
    simp only [gates_length] at hg
    have hg' := consistent_singleton _ _ _ hg
    simpa only [root_not, Gate.eval, eval, ih start he] using hg'
  | and e f ihe ihf =>
    obtain ⟨hef, hg⟩ := (consistent_append start _ _ A).mp h
    obtain ⟨he, hf⟩ := (consistent_append start _ _ A).mp hef
    simp only [gates_length] at hf
    simp only [List.length_append, gates_length] at hg
    have hg' := consistent_singleton _ _ _ hg
    have he' := ihe start he
    have hf' := ihf (start + e.size) hf
    simpa only [root_and, Gate.eval, eval,
      he', hf'] using hg'
  | or e f ihe ihf =>
    obtain ⟨hef, hg⟩ := (consistent_append start _ _ A).mp h
    obtain ⟨he, hf⟩ := (consistent_append start _ _ A).mp hef
    simp only [gates_length] at hf
    simp only [List.length_append, gates_length] at hg
    have hg' := consistent_singleton _ _ _ hg
    have he' := ihe start he
    have hf' := ihf (start + e.size) hf
    simpa only [root_or, Gate.eval, eval,
      he', hf'] using hg'

def circuit {n : Nat} (wire : ι → Fin n) (e : Expr ι) : Circuit where
  inputs := n
  gates := e.gates (fun i => (wire i).val) n
  ordered := e.gates_ordered _ _ (fun i => (wire i).isLt)
  output := ⟨e.root n, by simpa only [gates_length] using e.root_lt n⟩

theorem circuit_eval {n : Nat} (wire : ι → Fin n) (e : Expr ι) (input : Fin n → Bool) :
    (e.circuit wire).eval input = e.eval (fun i => input (wire i)) := by
  have h := e.eval_of_consistent (fun i => (wire i).val) n
    ((e.circuit wire).evalWires input) ((e.circuit wire).evalWires_consistent input)
  change (e.circuit wire).eval input = _ at h
  rw [h]
  apply eval_congr
  intro i
  exact (e.circuit wire).evalWires_input input (wire i)

def mux (condition yes no : Expr ι) : Expr ι :=
  .or (.and condition yes) (.and (.not condition) no)

@[simp] theorem eval_mux (input : ι → Bool) (c x y : Expr ι) :
    (mux c x y).eval input = if c.eval input then x.eval input else y.eval input := by
  cases hc : c.eval input <;> simp [mux, eval, hc]

def disjoin : List (Expr ι) → Expr ι
  | [] => .const false
  | e :: rest => .or e (disjoin rest)

theorem eval_disjoin_true (input : ι → Bool) (es : List (Expr ι)) :
    (disjoin es).eval input = true ↔ ∃ e ∈ es, e.eval input = true := by
  induction es with
  | nil => simp [disjoin, eval]
  | cons e es ih => simp [disjoin, eval, ih]

theorem size_disjoin_le (es : List (Expr ι)) (C : Nat)
    (h : ∀ e ∈ es, e.size ≤ C) : (disjoin es).size ≤ es.length * (C + 1) + 1 := by
  induction es generalizing C with
  | nil => simp [disjoin, size]
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih C (fun f hf => h f (by simp [hf]))
    simp only [disjoin, size, List.length_cons, Nat.succ_mul]
    omega

end Expr

private theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

noncomputable def table {ι A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (x : A → Expr ι) (b : B) : Expr ι :=
  Expr.disjoin (Finset.univ.toList.map (fun a => .and (x a) (.const (decide (f a = b)))))

theorem eval_table {ι A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (input : ι → Bool) (f : A → B) (x : A → Expr ι) (a : A)
    (hx : ∀ z, (x z).eval input = decide (a = z)) (b : B) :
    (table f x b).eval input = decide (f a = b) := by
  apply bool_ext
  simp only [table, Expr.eval_disjoin_true, List.mem_map]
  constructor
  · rintro ⟨_, ⟨z, _, rfl⟩, hz⟩
    simp only [Expr.eval, hx, Bool.and_eq_true, decide_eq_true_eq] at hz
    rcases hz with ⟨rfl, hz⟩
    exact decide_eq_true hz
  · intro h
    refine ⟨.and (x a) (.const (decide (f a = b))), ?_, ?_⟩
    · exact ⟨a, by simp, rfl⟩
    · simp [Expr.eval, hx, h]

noncomputable def table₂ {ι A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    (f : A → B → C) (x : A → Expr ι) (y : B → Expr ι) (c : C) : Expr ι :=
  table (fun p : A × B => f p.1 p.2) (fun p => .and (x p.1) (y p.2)) c

theorem eval_table₂ {ι A B C : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (input : ι → Bool) (f : A → B → C) (x : A → Expr ι) (y : B → Expr ι)
    (a : A) (b : B) (hx : ∀ z, (x z).eval input = decide (a = z))
    (hy : ∀ z, (y z).eval input = decide (b = z)) (c : C) :
    (table₂ f x y c).eval input = decide (f a b = c) := by
  apply eval_table input _ _ (a, b)
  rintro ⟨za, zb⟩
  simp [Expr.eval, hx, hy, Prod.mk.injEq]

theorem size_table_le {ι A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (x : A → Expr ι) (b : B) (C : Nat) (h : ∀ a, (x a).size ≤ C) :
    (table f x b).size ≤ Fintype.card A * (C + 3) + 1 := by
  unfold table
  have hb : ∀ e ∈ Finset.univ.toList.map (fun a => Expr.and (x a)
      (.const (decide (f a = b)))), e.size ≤ C + 2 := by
    intro e he
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
    simpa only [Expr.size, Nat.add_assoc] using Nat.add_le_add_right (h a) 2
  simpa [Nat.add_assoc] using Expr.size_disjoin_le _ (C + 2) hb

theorem size_table₂_le {ι A B D : Type*} [Fintype A] [Fintype B] [DecidableEq D]
    (f : A → B → D) (x : A → Expr ι) (y : B → Expr ι) (d : D) (C : Nat)
    (hx : ∀ a, (x a).size ≤ C) (hy : ∀ b, (y b).size ≤ C) :
    (table₂ f x y d).size ≤ (Fintype.card A * Fintype.card B) * (2 * C + 4) + 1 := by
  have h := size_table_le (fun p : A × B => f p.1 p.2)
    (fun p => Expr.and (x p.1) (y p.2)) d (2 * C + 1) (fun p => by
      have := hx p.1
      have := hy p.2
      simp only [Expr.size]
      omega)
  simpa only [table₂, Fintype.card_prod, Nat.add_assoc] using h

section Statements

variable {K : Type} {Γ : K → Type} {Λ σ ι : Type}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)] [DecidableEq Λ]

structure DataBits (ι : Type) (Γ : K → Type) (σ : Type) (S : Nat) where
  state : σ → Expr ι
  cells : ∀ k, Fin S → Option (Γ k) → Expr ι

structure ResultBits (ι : Type) (Γ : K → Type) (Λ σ : Type) (S : Nat)
    extends DataBits ι Γ σ S where
  label : Option Λ → Expr ι

def DataBits.Realizes {S : Nat} (bits : DataBits ι Γ σ S) (input : ι → Bool)
    (state : σ) (tapes : ∀ k, List (Γ k)) : Prop :=
  (∀ v, (bits.state v).eval input = decide (state = v)) ∧
  ∀ k i a, (bits.cells k i a).eval input = decide (encode S (tapes k) i = a)

def ResultBits.Realizes {S : Nat} (bits : ResultBits ι Γ Λ σ S) (input : ι → Bool)
    (cfg : TM2.Cfg Γ Λ σ) : Prop :=
  bits.toDataBits.Realizes input cfg.var cfg.stk ∧
  ∀ label, (bits.label label).eval input = decide (cfg.l = label)

def readBits {A : Type} [DecidableEq A] {S : Nat}
    (cells : Fin S → Option A → Expr ι) (n : Nat) (a : Option A) : Expr ι :=
  if h : n < S then cells ⟨n, h⟩ a else .const (decide ((none : Option A) = a))

theorem eval_readBits {A : Type} [DecidableEq A] {S : Nat}
    (input : ι → Bool) (bits : Fin S → Option A → Expr ι) (xs : List A)
    (hlen : xs.length ≤ S)
    (hbits : ∀ i a, (bits i a).eval input = decide (encode S xs i = a))
    (n : Nat) (a : Option A) :
    (readBits bits n a).eval input = decide (xs[n]? = a) := by
  by_cases hn : n < S
  · simp only [readBits, dite_eq_left hn]
    exact hbits ⟨n, hn⟩ a
  · have hx : xs[n]? = none := List.getElem?_eq_none (by omega)
    simp only [readBits, dite_eq_right hn, Expr.eval, hx]

noncomputable def pushBits {S : Nat} (bits : DataBits ι Γ σ S) (k : K)
    (f : σ → Γ k) : DataBits ι Γ σ S where
  state := bits.state
  cells := Function.update bits.cells k (fun i a =>
    if h : i.val = 0 then table (fun v => some (f v)) bits.state a
    else bits.cells k ⟨i.val - 1, by omega⟩ a)

noncomputable def peekBits {S : Nat} (bits : DataBits ι Γ σ S) (k : K)
    (f : σ → Option (Γ k) → σ) : DataBits ι Γ σ S where
  state := table₂ f bits.state (readBits (bits.cells k) 0)
  cells := bits.cells

noncomputable def popBits {S : Nat} (bits : DataBits ι Γ σ S) (k : K)
    (f : σ → Option (Γ k) → σ) : DataBits ι Γ σ S where
  state := table₂ f bits.state (readBits (bits.cells k) 0)
  cells := Function.update bits.cells k (fun i a => readBits (bits.cells k) (i.val + 1) a)

noncomputable def loadBits {S : Nat} (bits : DataBits ι Γ σ S)
    (f : σ → σ) : DataBits ι Γ σ S where
  state := table f bits.state
  cells := bits.cells

def muxResult {S : Nat} (condition : Expr ι) (yes no : ResultBits ι Γ Λ σ S) :
    ResultBits ι Γ Λ σ S where
  state := fun v => .mux condition (yes.state v) (no.state v)
  cells := fun k i a => .mux condition (yes.cells k i a) (no.cells k i a)
  label := fun l => .mux condition (yes.label l) (no.label l)

omit [∀ stack, Fintype (Γ stack)] in
theorem realizes_pushBits {S : Nat} (bits : DataBits ι Γ σ S) (input : ι → Bool)
    (v : σ) (tapes : ∀ k, List (Γ k)) (h : bits.Realizes input v tapes)
    (k : K) (f : σ → Γ k) :
    (pushBits bits k f).Realizes input v (Function.update tapes k (f v :: tapes k)) := by
  refine ⟨h.1, ?_⟩
  intro j i a
  by_cases hj : j = k
  · subst j
    simp only [pushBits, Function.update_self]
    by_cases hi : i.val = 0
    · rw [dite_eq_left hi, eval_table input _ _ v h.1]
      simp [encode, hi]
    · rw [dite_eq_right hi, h.2]
      apply bool_ext
      simp [encode, List.getElem?_cons, hi]
      exact ⟨of_decide_eq_true, decide_eq_true⟩
  · simpa only [pushBits, Function.update_of_ne hj] using h.2 j i a

omit [DecidableEq K] in
theorem realizes_peekBits {S : Nat} (bits : DataBits ι Γ σ S) (input : ι → Bool)
    (v : σ) (tapes : ∀ k, List (Γ k)) (h : bits.Realizes input v tapes)
    (k : K) (f : σ → Option (Γ k) → σ) (hlen : (tapes k).length ≤ S) :
    (peekBits bits k f).Realizes input (f v (tapes k).head?) tapes := by
  refine ⟨?_, h.2⟩
  intro w
  apply eval_table₂ input _ _ _ v (tapes k).head? h.1
  intro a
  simpa [List.head?_eq_getElem?] using
    eval_readBits input (bits.cells k) (tapes k) hlen (h.2 k) 0 a

theorem realizes_popBits {S : Nat} (bits : DataBits ι Γ σ S) (input : ι → Bool)
    (v : σ) (tapes : ∀ k, List (Γ k)) (h : bits.Realizes input v tapes)
    (k : K) (f : σ → Option (Γ k) → σ) (hlen : (tapes k).length ≤ S) :
    (popBits bits k f).Realizes input (f v (tapes k).head?)
      (Function.update tapes k (tapes k).tail) := by
  refine ⟨(realizes_peekBits bits input v tapes h k f hlen).1, ?_⟩
  intro j i a
  by_cases hj : j = k
  · subst j
    simp only [popBits, Function.update_self]
    rw [eval_readBits input (bits.cells k) (tapes k) hlen (h.2 k)]
    simp [encode, List.getElem?_tail]
  · simpa only [popBits, Function.update_of_ne hj] using h.2 j i a

omit [DecidableEq K] [∀ stack, Fintype (Γ stack)] in
theorem realizes_loadBits {S : Nat} (bits : DataBits ι Γ σ S) (input : ι → Bool)
    (v : σ) (tapes : ∀ k, List (Γ k)) (h : bits.Realizes input v tapes)
    (f : σ → σ) : (loadBits bits f).Realizes input (f v) tapes := by
  exact ⟨fun w => eval_table input f bits.state v h.1 w, h.2⟩

omit [DecidableEq K] [Fintype σ] [∀ stack, Fintype (Γ stack)] in
theorem realizes_muxResult {S : Nat} (input : ι → Bool) (condition : Expr ι)
    (yes no : ResultBits ι Γ Λ σ S) (decision : Bool) (hc : condition.eval input = decision)
    (yesCfg noCfg : TM2.Cfg Γ Λ σ)
    (hy : decision = true → yes.Realizes input yesCfg)
    (hn : decision = false → no.Realizes input noCfg) :
    (muxResult condition yes no).Realizes input (if decision then yesCfg else noCfg) := by
  cases decision with
  | false =>
    rcases hn rfl with ⟨⟨hv, hs⟩, hl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro v; simpa only [muxResult, Expr.eval_mux, hc, Bool.false_eq_true, ite_false, ite_true] using hv v
    · intro k i a; simpa only [muxResult, Expr.eval_mux, hc, Bool.false_eq_true, ite_false, ite_true] using hs k i a
    · intro l; simpa only [muxResult, Expr.eval_mux, hc, Bool.false_eq_true, ite_false, ite_true] using hl l
  | true =>
    rcases hy rfl with ⟨⟨hv, hs⟩, hl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro v; simpa only [muxResult, Expr.eval_mux, hc, Bool.false_eq_true, ite_false, ite_true] using hv v
    · intro k i a; simpa only [muxResult, Expr.eval_mux, hc, Bool.false_eq_true, ite_false, ite_true] using hs k i a
    · intro l; simpa only [muxResult, Expr.eval_mux, hc, Bool.false_eq_true, ite_false, ite_true] using hl l

noncomputable def compileAux {S : Nat} :
    TM2.Stmt Γ Λ σ → DataBits ι Γ σ S → ResultBits ι Γ Λ σ S
  | .push k f next, bits => compileAux next (pushBits bits k f)
  | .peek k f next, bits => compileAux next (peekBits bits k f)
  | .pop k f next, bits => compileAux next (popBits bits k f)
  | .load f next, bits => compileAux next (loadBits bits f)
  | .branch guard yes no, bits =>
      muxResult (table guard bits.state true) (compileAux yes bits) (compileAux no bits)
  | .goto label, bits =>
      { toDataBits := bits, label := table (fun v => some (label v)) bits.state }
  | .halt, bits =>
      { toDataBits := bits, label := fun l => .const (decide ((none : Option Λ) = l)) }

theorem compileAux_correct {S : Nat} (stmt : TM2.Stmt Γ Λ σ)
    (bits : DataBits ι Γ σ S) (input : ι → Bool) (v : σ) (tapes : ∀ k, List (Γ k))
    (safe : StatementSafe S stmt v tapes) (h : bits.Realizes input v tapes) :
    (compileAux stmt bits).Realizes input (TM2.stepAux stmt v tapes) := by
  induction stmt generalizing bits v tapes with
  | push k f next ih =>
    exact ih _ _ _ safe.2.2 (realizes_pushBits bits input v tapes h k f)
  | peek k f next ih =>
    exact ih _ _ _ safe.2 (realizes_peekBits bits input v tapes h k f (safe.1 k))
  | pop k f next ih =>
    exact ih _ _ _ safe.2 (realizes_popBits bits input v tapes h k f (safe.1 k))
  | load f next ih =>
    exact ih _ _ _ safe.2 (realizes_loadBits bits input v tapes h f)
  | branch guard yes no ihy ihn =>
    have hc : (table guard bits.state true).eval input = guard v := by
      rw [eval_table input guard bits.state v h.1]
      cases guard v <;> rfl
    have hy : guard v = true → (compileAux yes bits).Realizes input (TM2.stepAux yes v tapes) := by
      intro hg
      apply ihy bits v tapes _ h
      simpa [StatementSafe, hg] using safe.2
    have hn : guard v = false → (compileAux no bits).Realizes input (TM2.stepAux no v tapes) := by
      intro hg
      apply ihn bits v tapes _ h
      simpa [StatementSafe, hg] using safe.2
    have hm := realizes_muxResult input _ _ _ (guard v) hc _ _ hy hn
    cases hg : guard v <;> simpa [compileAux, TM2.stepAux, hg] using hm
  | goto label =>
    exact ⟨h, fun l => eval_table input _ bits.state v h.1 l⟩
  | halt => exact ⟨h, fun _ => rfl⟩

end Statements

section Encoding

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)] [DecidableEq Λ]

abbrev InputBit (Γ : K → Type) (σ : Type) (S : Nat) :=
  σ ⊕ (Σ k, Fin S × Option (Γ k))

abbrev ConfigBit (Γ : K → Type) (Λ σ : Type) (S : Nat) :=
  Option Λ ⊕ InputBit Γ σ S

def inputBits (S : Nat) : DataBits (InputBit Γ σ S) Γ σ S where
  state := fun v => .input (.inl v)
  cells := fun k i a => .input (.inr ⟨k, i, a⟩)

def inputEncoding (S : Nat) (v : σ) (tapes : ∀ k, List (Γ k)) : InputBit Γ σ S → Bool
  | .inl w => decide (v = w)
  | .inr ⟨k, i, a⟩ => decide (encode S (tapes k) i = a)

def configEncoding (S : Nat) (cfg : TM2.Cfg Γ Λ σ) : ConfigBit Γ Λ σ S → Bool
  | .inl label => decide (cfg.l = label)
  | .inr i => inputEncoding S cfg.var cfg.stk i

def resultExpr {ι : Type} {S : Nat} (bits : ResultBits ι Γ Λ σ S) :
    ConfigBit Γ Λ σ S → Expr ι
  | .inl label => bits.label label
  | .inr (.inl v) => bits.state v
  | .inr (.inr ⟨k, i, a⟩) => bits.cells k i a

omit [DecidableEq K] [Fintype σ] [∀ stack, Fintype (Γ stack)] in
theorem inputBits_realizes (S : Nat) (v : σ) (tapes : ∀ k, List (Γ k)) :
    (inputBits S).Realizes (inputEncoding S v tapes) v tapes := by
  exact ⟨fun _ => rfl, fun _ _ _ => rfl⟩

omit [DecidableEq K] [Fintype σ] [∀ stack, Fintype (Γ stack)] in
theorem resultExpr_eval {ι : Type} {S : Nat} (bits : ResultBits ι Γ Λ σ S)
    (input : ι → Bool) (cfg : TM2.Cfg Γ Λ σ) (h : bits.Realizes input cfg)
    (bit : ConfigBit Γ Λ σ S) :
    (resultExpr bits bit).eval input = configEncoding S cfg bit := by
  rcases bit with label | (v | ⟨k, i, a⟩)
  · exact h.2 label
  · exact h.1.1 v
  · exact h.1.2 k i a

noncomputable def transitionExpr (S : Nat) (stmt : TM2.Stmt Γ Λ σ) :
    ConfigBit Γ Λ σ S → Expr (InputBit Γ σ S) :=
  resultExpr (compileAux stmt (inputBits S))

theorem transitionExpr_eval (S : Nat) (stmt : TM2.Stmt Γ Λ σ)
    (v : σ) (tapes : ∀ k, List (Γ k)) (safe : StatementSafe S stmt v tapes)
    (bit : ConfigBit Γ Λ σ S) :
    (transitionExpr S stmt bit).eval (inputEncoding S v tapes) =
      configEncoding S (TM2.stepAux stmt v tapes) bit :=
  resultExpr_eval _ _ _ (compileAux_correct stmt _ _ v tapes safe
    (inputBits_realizes S v tapes)) bit

noncomputable def outputCircuit [Fintype K] (S : Nat) (stmt : TM2.Stmt Γ Λ σ)
    (bit : ConfigBit Γ Λ σ S) : Circuit :=
  (transitionExpr S stmt bit).circuit (Fintype.equivFin (InputBit Γ σ S))

theorem outputCircuit_eval [Fintype K] (S : Nat) (stmt : TM2.Stmt Γ Λ σ)
    (v : σ) (tapes : ∀ k, List (Γ k)) (safe : StatementSafe S stmt v tapes)
    (bit : ConfigBit Γ Λ σ S) :
    (outputCircuit S stmt bit).eval (fun i => inputEncoding S v tapes
      ((Fintype.equivFin (InputBit Γ σ S)).symm i)) =
      configEncoding S (TM2.stepAux stmt v tapes) bit := by
  have he := Expr.circuit_eval (Fintype.equivFin (InputBit Γ σ S))
    (transitionExpr S stmt bit)
    (fun (i : Fin (Fintype.card (InputBit Γ σ S))) => inputEncoding S v tapes
      ((Fintype.equivFin (InputBit Γ σ S)).symm i))
  apply he.trans
  simpa only [Equiv.symm_apply_apply] using transitionExpr_eval S stmt v tapes safe bit

end Encoding

variable {K : Type} {Γ : K → Type} {Λ σ ι : Type}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)] [DecidableEq Λ]

def DataBits.Bounded {S : Nat} (bits : DataBits ι Γ σ S) (C : Nat) : Prop :=
  (∀ v, (bits.state v).size ≤ C) ∧ ∀ k i a, (bits.cells k i a).size ≤ C

def ResultBits.Bounded {S : Nat} (bits : ResultBits ι Γ Λ σ S) (C : Nat) : Prop :=
  bits.toDataBits.Bounded C ∧ ∀ l, (bits.label l).size ≤ C

theorem size_readBits_le {A : Type} [DecidableEq A] {S : Nat}
    (bits : Fin S → Option A → Expr ι) (C : Nat) (hC : 1 ≤ C)
    (h : ∀ i a, (bits i a).size ≤ C) (n : Nat) (a : Option A) :
    (readBits bits n a).size ≤ C := by
  unfold readBits
  split
  · exact h _ _
  · exact hC

noncomputable def unaryCost (σ : Type) [Fintype σ] (C : Nat) : Nat :=
  Fintype.card σ * (C + 3) + 1

noncomputable def headCost (σ A : Type) [Fintype σ] [Fintype A] (C : Nat) : Nat :=
  (Fintype.card σ * Fintype.card (Option A)) * (2 * C + 4) + 1

noncomputable def statementCost : TM2.Stmt Γ Λ σ → Nat → Nat
  | .push _ _ next, C => statementCost next (max C (unaryCost σ C))
  | .peek k _ next, C => statementCost next (max C (headCost σ (Γ k) C))
  | .pop k _ next, C => statementCost next (max C (headCost σ (Γ k) C))
  | .load _ next, C => statementCost next (max C (unaryCost σ C))
  | .branch _ yes no, C =>
      2 * unaryCost σ C + statementCost yes C + statementCost no C + 4
  | .goto _, C => max C (unaryCost σ C)
  | .halt, C => max C 1

omit [DecidableEq σ] [∀ stack, Fintype (Γ stack)] in
theorem pushBits_bounded {S : Nat} (bits : DataBits ι Γ σ S) (C : Nat)
    (h : bits.Bounded C) (k : K) (f : σ → Γ k) :
    (pushBits bits k f).Bounded (max C (unaryCost σ C)) := by
  refine ⟨fun v => (h.1 v).trans (Nat.le_max_left _ _), ?_⟩
  intro j i a
  by_cases hj : j = k
  · subst j
    simp only [pushBits, Function.update_self]
    split
    · exact (size_table_le _ _ _ C h.1).trans (Nat.le_max_right _ _)
    · exact (h.2 _ _ _).trans (Nat.le_max_left _ _)
  · simpa only [pushBits, Function.update_of_ne hj] using
      (h.2 j i a).trans (Nat.le_max_left C (unaryCost σ C))

omit [DecidableEq K] in
theorem peekBits_bounded {S : Nat} (bits : DataBits ι Γ σ S) (C : Nat) (hC : 1 ≤ C)
    (h : bits.Bounded C) (k : K) (f : σ → Option (Γ k) → σ) :
    (peekBits bits k f).Bounded (max C (headCost σ (Γ k) C)) := by
  refine ⟨?_, fun j i a => (h.2 j i a).trans (Nat.le_max_left _ _)⟩
  intro v
  exact (size_table₂_le _ _ _ v C h.1
    (fun a => size_readBits_le _ C hC (h.2 k) 0 a)).trans (Nat.le_max_right _ _)

theorem popBits_bounded {S : Nat} (bits : DataBits ι Γ σ S) (C : Nat) (hC : 1 ≤ C)
    (h : bits.Bounded C) (k : K) (f : σ → Option (Γ k) → σ) :
    (popBits bits k f).Bounded (max C (headCost σ (Γ k) C)) := by
  refine ⟨(peekBits_bounded bits C hC h k f).1, ?_⟩
  intro j i a
  by_cases hj : j = k
  · subst j
    simpa only [popBits, Function.update_self] using
      (size_readBits_le _ C hC (h.2 k) (i.val + 1) a).trans
        (Nat.le_max_left C (headCost σ (Γ k) C))
  · simpa only [popBits, Function.update_of_ne hj] using
      (h.2 j i a).trans (Nat.le_max_left C (headCost σ (Γ k) C))

omit [DecidableEq K] [∀ stack, Fintype (Γ stack)] [∀ stack, DecidableEq (Γ stack)] in
theorem loadBits_bounded {S : Nat} (bits : DataBits ι Γ σ S) (C : Nat)
    (h : bits.Bounded C) (f : σ → σ) :
    (loadBits bits f).Bounded (max C (unaryCost σ C)) := by
  exact ⟨fun v => (size_table_le f bits.state v C h.1).trans (Nat.le_max_right _ _),
    fun k i a => (h.2 k i a).trans (Nat.le_max_left _ _)⟩

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [∀ stack, Fintype (Γ stack)]
  [∀ stack, DecidableEq (Γ stack)] [DecidableEq Λ] in
theorem muxResult_bounded {S : Nat} (condition : Expr ι) (yes no : ResultBits ι Γ Λ σ S)
    (G Y N : Nat) (hc : condition.size ≤ G) (hy : yes.Bounded Y) (hn : no.Bounded N) :
    (muxResult condition yes no).Bounded (2 * G + Y + N + 4) := by
  have hm (x y : Expr ι) (hx : x.size ≤ Y) (hy : y.size ≤ N) :
      (Expr.mux condition x y).size ≤ 2 * G + Y + N + 4 := by
    simp only [Expr.mux, Expr.size]
    omega
  exact ⟨⟨fun v => hm _ _ (hy.1.1 v) (hn.1.1 v),
    fun k i a => hm _ _ (hy.1.2 k i a) (hn.1.2 k i a)⟩,
    fun l => hm _ _ (hy.2 l) (hn.2 l)⟩

theorem compileAux_bounded {S : Nat} (stmt : TM2.Stmt Γ Λ σ)
    (bits : DataBits ι Γ σ S) (C : Nat) (hC : 1 ≤ C) (h : bits.Bounded C) :
    (compileAux stmt bits).Bounded (statementCost stmt C) := by
  induction stmt generalizing bits C with
  | push k f next ih =>
    exact ih _ _ (hC.trans (Nat.le_max_left _ _)) (pushBits_bounded bits C h k f)
  | peek k f next ih =>
    exact ih _ _ (hC.trans (Nat.le_max_left _ _)) (peekBits_bounded bits C hC h k f)
  | pop k f next ih =>
    exact ih _ _ (hC.trans (Nat.le_max_left _ _)) (popBits_bounded bits C hC h k f)
  | load f next ih =>
    exact ih _ _ (hC.trans (Nat.le_max_left _ _)) (loadBits_bounded bits C h f)
  | branch guard yes no ihy ihn =>
    exact muxResult_bounded _ _ _ _ _ _ (size_table_le guard bits.state true C h.1)
      (ihy bits C hC h) (ihn bits C hC h)
  | goto label =>
    exact ⟨⟨fun v => (h.1 v).trans (Nat.le_max_left _ _),
      fun k i a => (h.2 k i a).trans (Nat.le_max_left _ _)⟩,
      fun l => (size_table_le _ _ l C h.1).trans (Nat.le_max_right _ _)⟩
  | halt =>
    exact ⟨⟨fun v => (h.1 v).trans (Nat.le_max_left _ _),
      fun k i a => (h.2 k i a).trans (Nat.le_max_left _ _)⟩,
      fun _ => Nat.le_max_right _ _⟩

theorem transitionExpr_size_le (S : Nat) (stmt : TM2.Stmt Γ Λ σ)
    (bit : ConfigBit Γ Λ σ S) :
    (transitionExpr S stmt bit).size ≤ statementCost stmt 1 := by
  have h := compileAux_bounded stmt (inputBits S) 1 (by decide)
    ⟨fun _ => Nat.le_refl _, fun _ _ _ => Nat.le_refl _⟩
  rcases bit with label | (v | ⟨k, i, a⟩)
  · exact h.2 label
  · exact h.1.1 v
  · exact h.1.2 k i a

theorem outputCircuit_gates_le [Fintype K] (S : Nat) (stmt : TM2.Stmt Γ Λ σ)
    (bit : ConfigBit Γ Λ σ S) :
    (outputCircuit S stmt bit).gates.length ≤ statementCost stmt 1 := by
  simpa only [outputCircuit, Expr.circuit, Expr.gates_length] using
    transitionExpr_size_le S stmt bit

end BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

namespace BinPackingGames.Foundations.Complexity.CookLevin.ConfigIndex

open StatementCircuit

variable {K : Type} (Γ : K → Type) (Λ σ : Type)

abbrev SymbolBit := Σ k, Option (Γ k)

structure Indexing where
  labelCount : Nat
  stateCount : Nat
  symbolCount : Nat
  labels : Option Λ ≃ Fin labelCount
  states : σ ≃ Fin stateCount
  symbols : SymbolBit Γ ≃ Fin symbolCount

variable {Γ Λ σ}

def Indexing.width (indexing : Indexing Γ Λ σ) (S : Nat) : Nat :=
  indexing.labelCount + indexing.stateCount + S * indexing.symbolCount

def cellReorder (S : Nat) : (Σ k, Fin S × Option (Γ k)) ≃ (Fin S × SymbolBit Γ) where
  toFun cell := (cell.2.1, ⟨cell.1, cell.2.2⟩)
  invFun cell := ⟨cell.2.1, cell.1, cell.2.2⟩
  left_inv cell := by rcases cell with ⟨k, i, a⟩; rfl
  right_inv cell := by rcases cell with ⟨i, k, a⟩; rfl

def Indexing.configIndexEquiv (indexing : Indexing Γ Λ σ) (S : Nat) :
    ConfigBit Γ Λ σ S ≃ Fin (indexing.width S) :=
  (Equiv.sumCongr indexing.labels
    (Equiv.sumCongr indexing.states
      ((cellReorder S).trans
        ((Equiv.prodCongr (Equiv.refl (Fin S)) indexing.symbols).trans finProdFinEquiv)))).trans
    ((Equiv.sumAssoc (Fin indexing.labelCount) (Fin indexing.stateCount)
      (Fin (S * indexing.symbolCount))).symm.trans
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin (S * indexing.symbolCount)))).trans
        finSumFinEquiv))

@[simp] theorem Indexing.configIndex_label (indexing : Indexing Γ Λ σ)
    (S : Nat) (label : Option Λ) :
    (indexing.configIndexEquiv S (.inl label)).val = (indexing.labels label).val := by
  rfl

@[simp] theorem Indexing.configIndex_state (indexing : Indexing Γ Λ σ)
    (S : Nat) (state : σ) :
    (indexing.configIndexEquiv S (.inr (.inl state))).val =
      indexing.labelCount + (indexing.states state).val := by
  rfl

@[simp] theorem Indexing.configIndex_cell (indexing : Indexing Γ Λ σ)
    (S : Nat) (k : K) (i : Fin S) (symbol : Option (Γ k)) :
    (indexing.configIndexEquiv S (.inr (.inr ⟨k, i, symbol⟩))).val =
      indexing.labelCount + indexing.stateCount + i.val * indexing.symbolCount +
        (indexing.symbols ⟨k, symbol⟩).val := by
  change indexing.labelCount + indexing.stateCount +
    ((indexing.symbols ⟨k, symbol⟩).val + indexing.symbolCount * i.val) = _
  rw [Nat.mul_comm indexing.symbolCount i.val]
  omega

noncomputable def ofMachine (machine : Turing.FinTM2)
    [∀ k, Fintype (machine.Γ k)] : Indexing machine.Γ machine.Λ machine.σ := by
  letI := machine.kFin
  letI := machine.ΛFin
  letI := machine.σFin
  exact {
    labelCount := Fintype.card (Option machine.Λ)
    stateCount := Fintype.card machine.σ
    symbolCount := Fintype.card (SymbolBit machine.Γ)
    labels := Fintype.equivFin (Option machine.Λ)
    states := Fintype.equivFin machine.σ
    symbols := Fintype.equivFin (SymbolBit machine.Γ) }

end BinPackingGames.Foundations.Complexity.CookLevin.ConfigIndex

end OAI
