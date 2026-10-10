import Mathlib.Data.List.FinRange
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.DeriveFintype
import OAI.Computability.PerfectCompleteness.Machines.BoundedExecution
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineLemmas
import OAI.Computability.UniqueGames.Machines.MachineSubroutineLemmas
import OAI.Computability.UniqueGames.Machines.MachineTransducerCopy
import OAI.Computability.UniqueGames.Machines.Runtime
import OAI.Computability.UniqueGames.PCP.SourceMachine

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin

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

end UniqueGamesTheorem.Foundations.Complexity.CookLevin

end

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.Bounds

open Polynomial

noncomputable def pairLengthPolynomial (q : Polynomial ℕ) : Polynomial ℕ :=
  C 2 * X + q + 1

noncomputable def horizonPolynomial (p q : Polynomial ℕ) : Polynomial ℕ :=
  p.comp (pairLengthPolynomial q)

noncomputable def capacityPolynomial (p q : Polynomial ℕ) (pushes : ℕ) : Polynomial ℕ :=
  pairLengthPolynomial q + C pushes * horizonPolynomial p q

@[simp] theorem pairLengthPolynomial_eval (q : Polynomial ℕ) (n : ℕ) :
    (pairLengthPolynomial q).eval n = 2 * n + q.eval n + 1 := by
  simp [pairLengthPolynomial]

@[simp] theorem horizonPolynomial_eval (p q : Polynomial ℕ) (n : ℕ) :
    (horizonPolynomial p q).eval n = p.eval (2 * n + q.eval n + 1) := by
  simp [horizonPolynomial, Polynomial.eval_comp]

@[simp] theorem capacityPolynomial_eval (p q : Polynomial ℕ) (pushes n : ℕ) :
    (capacityPolynomial p q pushes).eval n =
      2 * n + q.eval n + 1 + pushes * p.eval (2 * n + q.eval n + 1) := by
  simp [capacityPolynomial]

theorem paired_length_le (q : Polynomial ℕ) (n witnessLength : ℕ)
    (hw : witnessLength ≤ q.eval n) :
    2 * n + witnessLength + 1 ≤ (pairLengthPolynomial q).eval n := by
  rw [pairLengthPolynomial_eval]
  omega

theorem one_le_pairLength (q : Polynomial ℕ) (n : ℕ) :
    1 ≤ (pairLengthPolynomial q).eval n := by
  rw [pairLengthPolynomial_eval]
  omega

theorem pairLength_le_capacity (p q : Polynomial ℕ) (pushes n : ℕ) :
    (pairLengthPolynomial q).eval n ≤ (capacityPolynomial p q pushes).eval n := by
  simp only [capacityPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  exact Nat.le_add_right _ _

theorem one_le_capacity (p q : Polynomial ℕ) (pushes n : ℕ) :
    1 ≤ (capacityPolynomial p q pushes).eval n :=
  (one_le_pairLength q n).trans (pairLength_le_capacity p q pushes n)

theorem transition_prefix_le_capacity (p q : Polynomial ℕ) (pushes n inputLength used extra : ℕ)
    (hi : inputLength ≤ (pairLengthPolynomial q).eval n)
    (ht : used < (horizonPolynomial p q).eval n) (he : extra ≤ pushes) :
    inputLength + used * pushes + extra ≤ (capacityPolynomial p q pushes).eval n := by
  have hu := Nat.mul_le_mul_right pushes (Nat.succ_le_of_lt ht)
  simp only [capacityPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  calc
    inputLength + used * pushes + extra ≤
        (pairLengthPolynomial q).eval n + (used + 1) * pushes := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    _ ≤ (pairLengthPolynomial q).eval n + (horizonPolynomial p q).eval n * pushes :=
      Nat.add_le_add_left hu _
    _ = _ := by rw [Nat.mul_comm ((horizonPolynomial p q).eval n) pushes]

theorem verifier_time_le_horizon (p q : Polynomial ℕ) (n witnessLength : ℕ)
    (hw : witnessLength ≤ q.eval n) :
    p.eval (2 * n + witnessLength + 1) ≤ (horizonPolynomial p q).eval n := by
  rw [horizonPolynomial, Polynomial.eval_comp]
  exact MachineComposition.natPolynomial_eval_mono p (paired_length_le q n witnessLength hw)

theorem horizon_monotone (p q : Polynomial ℕ) :
    Monotone (fun n => (horizonPolynomial p q).eval n) :=
  fun _ _ h => MachineComposition.natPolynomial_eval_mono _ h

theorem capacity_monotone (p q : Polynomial ℕ) (pushes : ℕ) :
    Monotone (fun n => (capacityPolynomial p q pushes).eval n) :=
  fun _ _ h => MachineComposition.natPolynomial_eval_mono _ h

theorem execution_stack_length_le_capacity (tm : Turing.FinTM2)
    (p q : Polynomial ℕ) (n : ℕ) (input : List (tm.Γ tm.k₀))
    (hi : input.length ≤ (pairLengthPolynomial q).eval n)
    (finish : tm.Cfg) (budget : ℕ)
    (ht : budget ≤ (horizonPolynomial p q).eval n)
    (run : StateTransition.EvalsToInTime tm.step (Turing.initList tm input)
      (some finish) budget) (k : tm.K) :
    (finish.stk k).length ≤ (capacityPolynomial p q (Runtime.programPushBound tm)).eval n := by
  have hs := Runtime.executionSizeBound tm.step (fun cfg => (cfg.stk k).length)
    (Runtime.programPushBound tm) (Runtime.stepStackLength tm k) run
  have hinit := (Runtime.initialStackLength tm input k).trans hi
  have hg := Nat.mul_le_mul_right (Runtime.programPushBound tm) ht
  calc
    (finish.stk k).length ≤ ((Turing.initList tm input).stk k).length +
        budget * Runtime.programPushBound tm := hs
    _ ≤ (pairLengthPolynomial q).eval n +
        (horizonPolynomial p q).eval n * Runtime.programPushBound tm :=
      Nat.add_le_add hinit hg
    _ = _ := by simp [capacityPolynomial, Nat.mul_comm]

theorem stackCapacity_le_polynomial (tm : Turing.FinTM2)
    (p q : Polynomial ℕ) (n : ℕ) (input : List (tm.Γ tm.k₀))
    (hi : input.length ≤ (pairLengthPolynomial q).eval n) :
    BoundedExecution.stackCapacity tm input ((horizonPolynomial p q).eval n) ≤
      (capacityPolynomial p q (Runtime.programPushBound tm)).eval n := by
  simpa only [BoundedExecution.stackCapacity, capacityPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Nat.mul_comm] using
    Nat.add_le_add_right hi ((horizonPolynomial p q).eval n * Runtime.programPushBound tm)

theorem run_stack_length_le_capacity (tm : Turing.FinTM2)
    (p q : Polynomial ℕ) (n : ℕ) (input : List (tm.Γ tm.k₀))
    (hi : input.length ≤ (pairLengthPolynomial q).eval n)
    (time : ℕ) (ht : time ≤ (horizonPolynomial p q).eval n) (k : tm.K) :
    ((BoundedExecution.run tm input time).stk k).length ≤
      (capacityPolynomial p q (Runtime.programPushBound tm)).eval n :=
  (BoundedExecution.run_stack_le tm input _ time ht k).trans
    (stackCapacity_le_polynomial tm p q n input hi)

theorem run_statement_budget_le_capacity (tm : Turing.FinTM2)
    (p q : Polynomial ℕ) (n : ℕ) (input : List (tm.Γ tm.k₀))
    (hi : input.length ≤ (pairLengthPolynomial q).eval n)
    (time : ℕ) (ht : time < (horizonPolynomial p q).eval n)
    (label : tm.Λ) (k : tm.K) :
    ((BoundedExecution.run tm input time).stk k).length +
        Runtime.statementPushBound (tm.m label) ≤
      (capacityPolynomial p q (Runtime.programPushBound tm)).eval n :=
  (BoundedExecution.statement_budget tm input _ time ht label k).trans
    (stackCapacity_le_polynomial tm p q n input hi)

noncomputable def configurationWidthPolynomial (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits : ℕ) : Polynomial ℕ :=
  C controlBits + capacityPolynomial p q pushes * C alphabetBits

noncomputable def transitionGatesPolynomial (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits expressionCost : ℕ) : Polynomial ℕ :=
  C expressionCost * configurationWidthPolynomial p q pushes controlBits alphabetBits

noncomputable def tableauGatesPolynomial (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits expressionCost : ℕ) : Polynomial ℕ :=
  horizonPolynomial p q *
    transitionGatesPolynomial p q pushes controlBits alphabetBits expressionCost

@[simp] theorem configurationWidthPolynomial_eval (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits n : ℕ) :
    (configurationWidthPolynomial p q pushes controlBits alphabetBits).eval n =
      controlBits + (capacityPolynomial p q pushes).eval n * alphabetBits := by
  simp [configurationWidthPolynomial]

@[simp] theorem transitionGatesPolynomial_eval (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits expressionCost n : ℕ) :
    (transitionGatesPolynomial p q pushes controlBits alphabetBits expressionCost).eval n =
      expressionCost * (controlBits + (capacityPolynomial p q pushes).eval n * alphabetBits) := by
  simp [transitionGatesPolynomial]

@[simp] theorem tableauGatesPolynomial_eval (p q : Polynomial ℕ)
    (pushes controlBits alphabetBits expressionCost n : ℕ) :
    (tableauGatesPolynomial p q pushes controlBits alphabetBits expressionCost).eval n =
      (horizonPolynomial p q).eval n * expressionCost *
        (controlBits + (capacityPolynomial p q pushes).eval n * alphabetBits) := by
  simp only [tableauGatesPolynomial, Polynomial.eval_mul, transitionGatesPolynomial_eval]
  exact (Nat.mul_assoc _ _ _).symm

noncomputable def formulaBitsPolynomial (varBound clauseBound : Polynomial ℕ) : Polynomial ℕ :=
  varBound + clauseBound + C 2 + clauseBound * (C 3 * (varBound + C 2))

@[simp] theorem formulaBitsPolynomial_eval (varBound clauseBound : Polynomial ℕ) (n : ℕ) :
    (formulaBitsPolynomial varBound clauseBound).eval n =
      varBound.eval n + clauseBound.eval n + 2 +
        clauseBound.eval n * (3 * (varBound.eval n + 2)) := by
  simp [formulaBitsPolynomial]

theorem formulaBits_length_le_polynomial (F : Target.Formula)
    (varBound clauseBound : Polynomial ℕ) (n : ℕ)
    (hv : F.variables ≤ varBound.eval n)
    (hc : F.clauses.length ≤ clauseBound.eval n) :
    (formulaBits F).length ≤ (formulaBitsPolynomial varBound clauseBound).eval n := by
  refine (formulaBits_length_le F).trans ?_
  rw [formulaBitsPolynomial_eval]
  exact Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add hv hc) 2)
    (Nat.mul_le_mul hc (Nat.mul_le_mul_left 3 (Nat.add_le_add_right hv 2)))

noncomputable def circuitVariablesPolynomial (inputs gates : Polynomial ℕ) : Polynomial ℕ :=
  inputs + gates

noncomputable def circuitClausesPolynomial (gates : Polynomial ℕ) : Polynomial ℕ :=
  C 3 * gates + 1

noncomputable def circuitBitsPolynomial (inputs gates : Polynomial ℕ) : Polynomial ℕ :=
  formulaBitsPolynomial (circuitVariablesPolynomial inputs gates)
    (circuitClausesPolynomial gates)

@[simp] theorem circuitVariablesPolynomial_eval (inputs gates : Polynomial ℕ) (n : ℕ) :
    (circuitVariablesPolynomial inputs gates).eval n = inputs.eval n + gates.eval n := by
  simp [circuitVariablesPolynomial]

@[simp] theorem circuitClausesPolynomial_eval (gates : Polynomial ℕ) (n : ℕ) :
    (circuitClausesPolynomial gates).eval n = 3 * gates.eval n + 1 := by
  simp [circuitClausesPolynomial]

@[simp] theorem circuitBitsPolynomial_eval (inputs gates : Polynomial ℕ) (n : ℕ) :
    (circuitBitsPolynomial inputs gates).eval n =
      (inputs.eval n + gates.eval n) + (3 * gates.eval n + 1) + 2 +
        (3 * gates.eval n + 1) * (3 * ((inputs.eval n + gates.eval n) + 2)) := by
  simp [circuitBitsPolynomial]

theorem circuit_formulaBits_length_le (F : Target.Formula) (inputCount gateCount : ℕ)
    (hv : F.variables ≤ inputCount + gateCount)
    (hc : F.clauses.length ≤ 3 * gateCount + 1) :
    (formulaBits F).length ≤
      (inputCount + gateCount) + (3 * gateCount + 1) + 2 +
        (3 * gateCount + 1) * (3 * ((inputCount + gateCount) + 2)) := by
  exact (formulaBits_length_le F).trans
    (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add hv hc) 2)
      (Nat.mul_le_mul hc (Nat.mul_le_mul_left 3 (Nat.add_le_add_right hv 2))))

theorem circuit_formulaBits_length_le_polynomial (F : Target.Formula)
    (inputCount gateCount : ℕ) (inputs gates : Polynomial ℕ) (n : ℕ)
    (hi : inputCount ≤ inputs.eval n) (hg : gateCount ≤ gates.eval n)
    (hv : F.variables ≤ inputCount + gateCount)
    (hc : F.clauses.length ≤ 3 * gateCount + 1) :
    (formulaBits F).length ≤ (circuitBitsPolynomial inputs gates).eval n := by
  apply formulaBits_length_le_polynomial
  · simpa using hv.trans (Nat.add_le_add hi hg)
  · simpa using hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hg) 1)

theorem toFormula_bits_length_le (circuit : Circuit) :
    (formulaBits circuit.toFormula).length ≤
      (circuit.inputs + circuit.gates.length) + (3 * circuit.gates.length + 1) + 2 +
        (3 * circuit.gates.length + 1) *
          (3 * ((circuit.inputs + circuit.gates.length) + 2)) :=
  circuit_formulaBits_length_le circuit.toFormula circuit.inputs circuit.gates.length
    (Circuit.toFormula_variables circuit).le (Circuit.toFormula_clause_count circuit).le

theorem toFormula_bits_length_le_polynomial (circuit : Circuit)
    (inputs gates : Polynomial ℕ) (n : ℕ)
    (hi : circuit.inputs ≤ inputs.eval n) (hg : circuit.gates.length ≤ gates.eval n) :
    (formulaBits circuit.toFormula).length ≤ (circuitBitsPolynomial inputs gates).eval n :=
  circuit_formulaBits_length_le_polynomial circuit.toFormula circuit.inputs circuit.gates.length
    inputs gates n hi hg
    (Circuit.toFormula_variables circuit).le (Circuit.toFormula_clause_count circuit).le

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.Bounds

end

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.CircuitProducerModel

open Turing
open UniqueGamesTheorem.Foundations.Hastad
open UniqueGamesTheorem.Reduction

def gateTemplate (tag : Fin 5) (position : Fin 9) : Fin 3 × Bool :=
  match tag.val with
  | 0 => (0, false)
  | 1 => (0, true)
  | 2 => [(0, true), (1, true), (1, true),
      (0, false), (1, false), (1, false),
      (0, true), (1, true), (1, true)].get position
  | 3 => [(0, false), (1, true), (1, true),
      (0, false), (2, true), (2, true),
      (0, true), (1, false), (2, false)].get position
  | _ => [(0, true), (1, false), (1, false),
      (0, true), (2, false), (2, false),
      (0, false), (1, true), (2, true)].get position

structure Record where
  tag : Fin 5
  output : Nat
  first : Nat
  second : Nat
  deriving DecidableEq

def Record.slot (r : Record) (j : Fin 3) : Nat :=
  match j.val with
  | 0 => r.output
  | 1 => r.first
  | _ => r.second

def Record.words (r : Record) : List Nat :=
  [r.tag.val, r.output, r.first, r.second]

def Record.bits (r : Record) : List Bool := encodeWords r.words

def Record.fieldValue (r : Record) (j : Fin 4) : Nat :=
  match j.val with
  | 0 => r.tag.val
  | 1 => r.output
  | 2 => r.first
  | _ => r.second

def templateWords (tag : Fin 5) (values : Fin 3 → Nat) : List Nat :=
  (List.finRange 9).flatMap fun j =>
    [values (gateTemplate tag j).1, if (gateTemplate tag j).2 then 1 else 0]

def Record.outputWords (r : Record) : List Nat := templateWords r.tag r.slot
def Record.outputBits (r : Record) : List Bool := encodeWords r.outputWords

def outputWords (selected : Nat) : List Nat :=
  [selected, 1, selected, 1, selected, 1]

inductive Tape where
  | input | header | counter | selected | field (slot : Fin 4)
  | scratch | reversed | output
  deriving DecidableEq, Fintype

inductive Context where
  | header (slot : Fin 2)
  | gate (tag : Fin 5) (position : Fin 9)
  | output (position : Fin 3)
  deriving DecidableEq, Fintype

abbrev State := (Unit × Context) × Option Bool
abbrev Alphabet (_ : Tape) := Bool

inductive Label where
  | headerStart (slot : Fin 3)
  | headerLoop (slot : Fin 3)
  | setup (context : Context)
  | scan (context : Context)
  | emit (context control : Context) (symbol : Bool)
  | restore (context : Context)
  | clearHeader | guard
  | fieldStart (slot : Fin 4)
  | fieldLoop (slot : Fin 4)
  | decodeTag
  | cleanup (slot : Fin 4)
  | finalCounter | clearSelected | finalReverse
  deriving DecidableEq, Fintype

def defaultControl : Context := .header 0
def initialState : State := (((), defaultControl), none)

def headerTape (slot : Fin 3) : Tape :=
  match slot.val with
  | 0 => .header
  | 1 => .counter
  | _ => .selected

def headerNext (slot : Fin 3) : Option Label :=
  if h : slot.val + 1 < 3 then some (.headerStart ⟨slot.val + 1, h⟩)
  else some (.setup (.header 0))

def contextSource : Context → Tape
  | .header j => if j.val = 0 then .header else .counter
  | .gate tag j => .field ⟨(gateTemplate tag j).1.val + 1, by
      have := (gateTemplate tag j).1.isLt
      omega⟩
  | .output _ => .selected

def affineEmit (scale offset : Nat) : Bool → List Bool
  | true => List.replicate scale true
  | false => encodeWord offset

def literalEmit (positive : Bool) : Bool → List Bool
  | true => [true]
  | false => [false] ++ encodeWord (if positive then 1 else 0)

def emission : Context → Bool → List Bool
  | .header j => if j.val = 0 then affineEmit 1 0 else affineEmit 3 1
  | .gate tag j => literalEmit (gateTemplate tag j).2
  | .output _ => literalEmit true

def contextNext : Context → Option Label
  | .header j => if j.val = 0 then some (.setup (.header 1)) else some .clearHeader
  | .gate tag j => if h : j.val + 1 < 9 then
      some (.setup (.gate tag ⟨j.val + 1, h⟩)) else some (.cleanup 0)
  | .output j => if h : j.val + 1 < 3 then
      some (.setup (.output ⟨j.val + 1, h⟩)) else some .finalCounter

def cleanupNext (j : Fin 4) : Label :=
  if h : j.val + 1 < 4 then .cleanup ⟨j.val + 1, h⟩ else .guard

def drain (tape : Tape) (again next : Label) : TM2.Stmt Alphabet Label State :=
  .pop tape (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun _ => again)
      (.load (fun state => (state.1, none)) (.goto fun _ => next)))

def resetGoto (next : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => initialState) (.goto fun _ => next)

def tagDecoder : Nat → Fin 5 → TM2.Stmt Alphabet Label State
  | 0, tag => .pop (.field 0) (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false) .halt
        (resetGoto (.setup (.gate tag 0))))
  | fuel + 1, tag => .pop (.field 0) (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (tagDecoder fuel ⟨min (tag.val + 1) 4, by omega⟩)
        (resetGoto (.setup (.gate tag 0))))

def program : Label → TM2.Stmt Alphabet Label State
  | .headerStart j => SourceMachine.fieldStart (headerTape j) (.headerLoop j)
  | .headerLoop j => SourceMachine.fieldLoop .input (headerTape j) (.headerLoop j)
      (headerNext j)
  | .setup c => .load (fun _ => (((), c), none)) (.goto fun _ => .scan c)
  | .scan c => MachineTransducerCopy.scanLoop (contextSource c) .scratch
      defaultControl (fun q b => .emit c q b) (.restore c)
  | .emit c q b => MachineTransducerCopy.emitter .reversed (fun q _ => q)
      emission (.scan c) q b
  | .restore c => MachineTransfer.loopAt .scratch (contextSource c) id false
      (.restore c) (contextNext c)
  | .clearHeader => drain .header .clearHeader .guard
  | .guard => MachineUnaryCounter.guard .counter (.fieldStart 0) (.setup (.output 0))
  | .fieldStart j => SourceMachine.fieldStart (.field j) (.fieldLoop j)
  | .fieldLoop j => SourceMachine.fieldLoop .input (.field j) (.fieldLoop j)
      (SourceMachine.fieldNext Label.fieldStart (some .decodeTag) j)
  | .decodeTag => tagDecoder 4 0
  | .cleanup j => drain (.field j) (.cleanup j) (cleanupNext j)
  | .finalCounter => .pop .counter (fun state _ => (state.1, none))
      (.goto fun _ => .clearSelected)
  | .clearSelected => drain .selected .clearSelected .finalReverse
  | .finalReverse => MachineTransfer.loopAt .reversed .output id false .finalReverse none

def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.CircuitProducerModel

end

end OAI
