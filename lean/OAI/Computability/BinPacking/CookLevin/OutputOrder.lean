import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Basic
import OAI.Computability.BinPacking.CookLevin.CircuitEncodingBridge
import OAI.Computability.BinPacking.CookLevin.MachineCircuit

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionTemplate

inductive Position where
  | current
  | zero
  | succ (p : Position)
  | pred (p : Position)
  deriving DecidableEq

def Position.eval (cursor : Nat) : Position → Nat
  | .current => cursor
  | .zero => 0
  | .succ p => p.eval cursor + 1
  | .pred p => p.eval cursor - 1

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionTemplate

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitBatch

open StatementCircuit

namespace Batch

variable {ι : Type*}

def cost (es : List (Expr ι)) : Nat := (es.map Expr.size).sum

def gates (wire : ι → Nat) (start : Nat) : List (Expr ι) → List Gate
  | [] => []
  | e :: es => e.gates wire start ++ gates wire (start + e.size) es

def roots (start : Nat) : List (Expr ι) → List Nat
  | [] => []
  | e :: es => e.root start :: roots (start + e.size) es

@[simp] theorem cost_nil : cost ([] : List (Expr ι)) = 0 := rfl

@[simp] theorem cost_cons (e : Expr ι) (es : List (Expr ι)) :
    cost (e :: es) = e.size + cost es := by simp [cost]

@[simp] theorem gates_length (wire : ι → Nat) (start : Nat) (es : List (Expr ι)) :
    (gates wire start es).length = cost es := by
  induction es generalizing start with
  | nil => rfl
  | cons e es ih => simp [gates, ih]

@[simp] theorem roots_length (start : Nat) (es : List (Expr ι)) :
    (roots start es).length = es.length := by
  induction es generalizing start <;> simp [roots, *]

theorem gates_ordered (wire : ι → Nat) (start : Nat) (es : List (Expr ι))
    (hw : ∀ i, wire i < start) : Ordered start (gates wire start es) := by
  induction es generalizing start with
  | nil => exact ordered_nil start
  | cons e es ih =>
    apply (e.gates_ordered wire start hw).append
    simpa only [Expr.gates_length] using
      ih (start + e.size) (fun i => lt_of_lt_of_le (hw i) (by omega))

theorem roots_bounds (start : Nat) (es : List (Expr ι)) (r : Nat)
    (hr : r ∈ roots start es) : start ≤ r ∧ r < start + cost es := by
  induction es generalizing start with
  | nil => simp [roots] at hr
  | cons e es ih =>
    simp only [roots, List.mem_cons] at hr
    rcases hr with rfl | hr
    · have hp := e.size_pos
      have hu := e.root_lt start
      simp only [cost_cons]
      constructor
      · unfold Expr.root; omega
      · omega
    · have ht := ih (start + e.size) hr
      simp only [cost_cons]
      omega

theorem eval_roots (wire : ι → Nat) (start : Nat) (es : List (Expr ι))
    (A : Nat → Bool) (hc : Consistent start (gates wire start es) A) :
    (roots start es).map A = es.map (fun e => e.eval (fun i => A (wire i))) := by
  induction es generalizing start with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨he, ht⟩ := (consistent_append start _ _ A).mp hc
    simp only [Expr.gates_length] at ht
    simp only [roots, List.map_cons, e.eval_of_consistent wire start A he,
      ih (start + e.size) ht]

def rootAt (start : Nat) (es : List (Expr ι)) (i : Fin es.length) : Nat :=
  (roots start es)[i.val]'(by simpa only [roots_length] using i.isLt)

theorem rootAt_lt (start : Nat) (es : List (Expr ι)) (i : Fin es.length) :
    rootAt start es i < start + cost es := by
  have hr : rootAt start es i ∈ roots start es :=
    List.mem_of_getElem (rfl :
      (roots start es)[i.val]'(by simpa only [roots_length] using i.isLt) = rootAt start es i)
  exact (roots_bounds start es _ hr).2

theorem eval_rootAt (wire : ι → Nat) (start : Nat) (es : List (Expr ι))
    (A : Nat → Bool) (hc : Consistent start (gates wire start es) A)
    (i : Fin es.length) :
    A (rootAt start es i) = es[i.val].eval (fun j => A (wire j)) := by
  have h := congrArg (fun xs : List Bool => xs[i.val]?) (eval_roots wire start es A hc)
  have hr : i.val < (roots start es).length := by simp
  simpa only [List.getElem?_map, List.getElem?_eq_getElem hr,
    List.getElem?_eq_getElem i.isLt, Option.map_some, Option.some.injEq, rootAt] using h

theorem cost_le (es : List (Expr ι)) (D : Nat)
    (h : ∀ e ∈ es, e.size ≤ D) : cost es ≤ es.length * D := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun f hf => h f (by simp [hf]))
    simp only [cost_cons, List.length_cons, Nat.succ_mul]
    omega

theorem cost_ofFn {n : Nat} (es : Fin n → Expr ι) :
    cost (List.ofFn es) = ∑ i, (es i).size := by
  simp [cost, List.map_ofFn, List.sum_ofFn]

theorem cost_ofFn_le {n : Nat} (es : Fin n → Expr ι) (D : Nat)
    (h : ∀ i, (es i).size ≤ D) : cost (List.ofFn es) ≤ n * D := by
  have hc := cost_le (List.ofFn es) D (by
    intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    exact h i)
  simpa only [List.length_ofFn] using hc

end Batch

structure Fragment (inputs : Nat) where
  gates : List Gate
  ordered : Ordered inputs gates

namespace Fragment

variable {inputs : Nat}

def empty (inputs : Nat) : Fragment inputs := ⟨[], ordered_nil inputs⟩

def evalWires (f : Fragment inputs) (input : Fin inputs → Bool) : Nat → Bool :=
  run inputs f.gates (inputEnv input)

theorem evalWires_input (f : Fragment inputs) (input : Fin inputs → Bool)
    (j : Fin inputs) : f.evalWires input j.val = input j := by
  rw [evalWires, run_eq_of_lt _ _ _ _ j.isLt]
  simp [inputEnv, j.isLt]

theorem evalWires_consistent (f : Fragment inputs) (input : Fin inputs → Bool) :
    Consistent inputs f.gates (f.evalWires input) :=
  run_consistent inputs f.gates (inputEnv input) f.ordered

def append (f : Fragment inputs) (gs : List Gate)
    (hg : Ordered (inputs + f.gates.length) gs) : Fragment inputs :=
  ⟨f.gates ++ gs, f.ordered.append hg⟩

theorem evalWires_append (f : Fragment inputs) (gs : List Gate)
    (hg : Ordered (inputs + f.gates.length) gs) (input : Fin inputs → Bool) :
    (f.append gs hg).evalWires input =
      run (inputs + f.gates.length) gs (f.evalWires input) :=
  run_append inputs f.gates gs (inputEnv input)

theorem evalWires_append_old (f : Fragment inputs) (gs : List Gate)
    (hg : Ordered (inputs + f.gates.length) gs) (input : Fin inputs → Bool)
    (j : Nat) (hj : j < inputs + f.gates.length) :
    (f.append gs hg).evalWires input j = f.evalWires input j := by
  rw [evalWires_append]
  exact run_eq_of_lt _ _ _ j hj

def toCircuit (f : Fragment inputs) (output : Fin (inputs + f.gates.length)) : Circuit :=
  ⟨inputs, f.gates, f.ordered, output⟩

@[simp] theorem toCircuit_eval (f : Fragment inputs)
    (output : Fin (inputs + f.gates.length)) (input : Fin inputs → Bool) :
    (f.toCircuit output).eval input = f.evalWires input output.val := rfl

end Fragment

structure Frame (inputs width : Nat) where
  fragment : Fragment inputs
  wires : Fin width → Fin (inputs + fragment.gates.length)

namespace Frame

variable {inputs width oldWidth newWidth : Nat}

def eval (f : Frame inputs width) (input : Fin inputs → Bool) : Fin width → Bool :=
  fun i => f.fragment.evalWires input (f.wires i).val

def initial (wire : Fin width → Fin inputs) : Frame inputs width where
  fragment := Fragment.empty inputs
  wires := wire

@[simp] theorem initial_eval (wire : Fin width → Fin inputs) (input : Fin inputs → Bool)
    (i : Fin width) : (initial wire).eval input i = input (wire i) :=
  (Fragment.empty inputs).evalWires_input input (wire i)

def step (f : Frame inputs oldWidth) (es : Fin newWidth → Expr (Fin oldWidth)) :
    Frame inputs newWidth where
  fragment := f.fragment.append
    (Batch.gates (fun i => (f.wires i).val) (inputs + f.fragment.gates.length) (List.ofFn es))
    (Batch.gates_ordered _ _ _ (fun i => (f.wires i).isLt))
  wires := fun i => ⟨Batch.rootAt (inputs + f.fragment.gates.length) (List.ofFn es)
      ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩, by
    have h := Batch.rootAt_lt (inputs + f.fragment.gates.length) (List.ofFn es)
      ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩
    simpa only [Fragment.append, List.length_append, Batch.gates_length, Nat.add_assoc] using h⟩

@[simp] theorem step_gate_count (f : Frame inputs oldWidth)
    (es : Fin newWidth → Expr (Fin oldWidth)) :
    (f.step es).fragment.gates.length =
      f.fragment.gates.length + Batch.cost (List.ofFn es) := by
  simp only [step, Fragment.append, List.length_append, Batch.gates_length]

theorem step_gate_count_sum (f : Frame inputs oldWidth)
    (es : Fin newWidth → Expr (Fin oldWidth)) :
    (f.step es).fragment.gates.length = f.fragment.gates.length + ∑ i, (es i).size := by
  rw [step_gate_count, Batch.cost_ofFn]

theorem step_gate_count_le (f : Frame inputs oldWidth)
    (es : Fin newWidth → Expr (Fin oldWidth)) (D : Nat) (h : ∀ i, (es i).size ≤ D) :
    (f.step es).fragment.gates.length ≤ f.fragment.gates.length + newWidth * D := by
  rw [step_gate_count]
  exact Nat.add_le_add_left (Batch.cost_ofFn_le es D h) _

theorem step_eval (f : Frame inputs oldWidth) (es : Fin newWidth → Expr (Fin oldWidth))
    (input : Fin inputs → Bool) (i : Fin newWidth) :
    (f.step es).eval input i = (es i).eval (f.eval input) := by
  let start := inputs + f.fragment.gates.length
  let wire := fun j : Fin oldWidth => (f.wires j).val
  let gs := Batch.gates wire start (List.ofFn es)
  have hc : Consistent start gs ((f.step es).fragment.evalWires input) :=
    ((consistent_append inputs f.fragment.gates gs _).mp
      ((f.step es).fragment.evalWires_consistent input)).2
  have he := Batch.eval_rootAt wire start (List.ofFn es)
    ((f.step es).fragment.evalWires input) hc
    ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩
  change (f.step es).eval input i = _ at he
  rw [he]
  simp only [List.getElem_ofFn]
  apply Expr.eval_congr
  intro j
  exact f.fragment.evalWires_append_old gs
    (Batch.gates_ordered wire start _ (fun j => (f.wires j).isLt))
    input (f.wires j).val (f.wires j).isLt

theorem step_eval_fun (f : Frame inputs oldWidth) (es : Fin newWidth → Expr (Fin oldWidth))
    (input : Fin inputs → Bool) :
    (f.step es).eval input = fun i => (es i).eval (f.eval input) := by
  funext i
  exact step_eval f es input i

def network (es : Fin width → Expr (Fin width)) (state : Fin width → Bool) :
    Fin width → Bool := fun i => (es i).eval state

def «repeat» (f : Frame inputs width) (es : Fin width → Expr (Fin width)) :
    Nat → Frame inputs width
  | 0 => f
  | t + 1 => («repeat» f es t).step es

theorem repeat_eval (f : Frame inputs width) (es : Fin width → Expr (Fin width))
    (input : Fin inputs → Bool) (T : Nat) :
    (f.repeat es T).eval input = (network es)^[T] (f.eval input) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [«repeat», step_eval_fun, Function.iterate_succ_apply', ← ih]
    rfl

theorem repeat_gate_count (f : Frame inputs width) (es : Fin width → Expr (Fin width))
    (T : Nat) :
    (f.repeat es T).fragment.gates.length =
      f.fragment.gates.length + T * Batch.cost (List.ofFn es) := by
  induction T with
  | zero => simp [«repeat»]
  | succ T ih =>
    rw [«repeat», step_gate_count, ih, Nat.succ_mul]
    omega

theorem repeat_gate_count_sum (f : Frame inputs width) (es : Fin width → Expr (Fin width))
    (T : Nat) :
    (f.repeat es T).fragment.gates.length = f.fragment.gates.length + T * ∑ i, (es i).size := by
  rw [repeat_gate_count, Batch.cost_ofFn]

theorem repeat_gate_count_le (f : Frame inputs width) (es : Fin width → Expr (Fin width))
    (T D : Nat) (h : ∀ i, (es i).size ≤ D) :
    (f.repeat es T).fragment.gates.length ≤ f.fragment.gates.length + T * (width * D) := by
  rw [repeat_gate_count]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left T (Batch.cost_ofFn_le es D h)) _

def toCircuit (f : Frame inputs width) (output : Fin width) : Circuit :=
  f.fragment.toCircuit (f.wires output)

@[simp] theorem toCircuit_eval (f : Frame inputs width) (output : Fin width)
    (input : Fin inputs → Bool) : (f.toCircuit output).eval input = f.eval input output := rfl

theorem repeat_toCircuit_eval (f : Frame inputs width) (es : Fin width → Expr (Fin width))
    (T : Nat) (output : Fin width) (input : Fin inputs → Bool) :
    ((f.repeat es T).toCircuit output).eval input =
      ((network es)^[T] (f.eval input)) output := by
  rw [toCircuit_eval, repeat_eval]

end Frame

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitBatch

namespace BinPackingGames.Foundations.Complexity.CookLevin.PositionMachine

open Turing MachineComposition TransitionTemplate

def usesCurrent : Position → Bool
  | .current => true
  | .zero => false
  | .succ p => usesCurrent p
  | .pred p => usesCurrent p

def initialValue (p : Position) (cursor : Nat) : Nat :=
  if usesCurrent p then cursor else 0

def transform : Position → Nat → Nat
  | .current, n => n
  | .zero, n => n
  | .succ p, n => transform p n + 1
  | .pred p, n => transform p n - 1

theorem transform_initialValue (p : Position) (cursor : Nat) :
    transform p (initialValue p cursor) = p.eval cursor := by
  induction p with
  | current => rfl
  | zero => rfl
  | succ p ih =>
    change transform p (initialValue p cursor) + 1 = p.eval cursor + 1
    exact congrArg (fun n : Nat => n + 1) ih
  | pred p ih =>
    change transform p (initialValue p cursor) - 1 = p.eval cursor - 1
    exact congrArg (fun n : Nat => n - 1) ih

section Statements

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := σ × Option Bool

def decrement (destination : K)
    (continuation : TM2.Stmt (Alphabet (K := K)) Λ (State σ)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .peek destination (fun s head => (s.1, head))
    (.branch (fun s => s.2.getD false)
      (.pop destination (fun s _ => (s.1, none)) continuation)
      (.load (fun s => (s.1, none)) continuation))

theorem stepAux_decrement (destination : K)
    (continuation : TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (decrement destination continuation) (ambient, register)
      (Function.update base destination (encodeWord n ++ suffix)) =
      TM2.stepAux continuation (ambient, none)
        (Function.update base destination (encodeWord (n - 1) ++ suffix)) := by
  cases n <;> simp [decrement, TM2.stepAux, encodeWord, List.replicate_succ]

def suffixStatement (destination : K) : Position →
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) →
      TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .current, continuation => .load (fun s => (s.1, none)) continuation
  | .zero, continuation => .load (fun s => (s.1, none)) continuation
  | .succ p, continuation =>
      suffixStatement destination p (.push destination (fun _ => true) continuation)
  | .pred p, continuation => suffixStatement destination p (decrement destination continuation)

theorem stepAux_suffixStatement (destination : K) (p : Position)
    (continuation : TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (suffixStatement destination p continuation) (ambient, register)
      (Function.update base destination (encodeWord n ++ suffix)) =
      TM2.stepAux continuation (ambient, none)
        (Function.update base destination (encodeWord (transform p n) ++ suffix)) := by
  induction p generalizing continuation with
  | current => rfl
  | zero => rfl
  | succ p ih =>
    rw [suffixStatement, ih]
    simp [TM2.stepAux, transform, encodeWord, List.replicate_succ]
  | pred p ih =>
    rw [suffixStatement, ih, stepAux_decrement]
    rfl

inductive Label where
  | start
  | scan
  | restore
  | finish
  deriving DecidableEq

instance : Fintype Label where
  elems := { .start, .scan, .restore, .finish }
  complete l := by cases l <;> simp

def statement (source scratch destination : K) (p : Position)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .start => if usesCurrent p then
      MachineUnaryAffineAt.seed destination 0 (labels .scan)
      else .push destination (fun _ => false) (.goto fun _ => labels .finish)
  | .scan => MachineUnaryAffineAt.scan source scratch destination 1
      (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt scratch source id false
      (labels .restore) (some (labels .finish))
  | .finish => suffixStatement destination p (Reduction.MachineTransfer.exitAt destination exit)

def seedSteps (p : Position) (cursor : Nat) : Nat :=
  if usesCurrent p then 2 * (cursor + 1) + 1 else 1

def steps (p : Position) (cursor : Nat) : Nat := seedSteps p cursor + 1

theorem seedTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (p : Position) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement source scratch destination p labels exit l)
    (base : K → List Bool) (cursor : Nat) (suffix : List Bool)
    (sourceWord : base source = encodeWord cursor ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[seedSteps p cursor]
      (some ⟨some (labels .start), (ambient, register), base⟩) =
      some ⟨some (labels .finish), (ambient, if usesCurrent p then none else register),
        Function.update base destination (encodeWord (initialValue p cursor) ++ base destination)⟩ := by
  cases hc : usesCurrent p with
  | false =>
    simp only [seedSteps, initialValue, hc, Bool.false_eq_true, ↓reduceIte,
      Function.iterate_one, advance_some]
    change some (TM2.stepAux (program (labels .start)) (ambient, register) base) = _
    rw [atLabels]
    simp [statement, hc, TM2.stepAux, encodeWord]
  | true =>
    have h := MachineUnaryAffineAt.seededAffineTrace source scratch destination hs hd hsd
      1 0 (labels .start) (labels .scan) (labels .restore) (some (labels .finish))
      program (by simpa [statement, hc] using atLabels .start)
      (atLabels .scan) (atLabels .restore) base cursor suffix sourceWord scratchEmpty
      ambient register
    simpa only [seedSteps, initialValue, hc, ↓reduceIte, one_mul, add_zero] using h

theorem finishTrace (source scratch destination : K)
    (p : Position) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atFinish : program (labels .finish) = statement source scratch destination p labels exit .finish)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[1]
      (some ⟨some (labels .finish), (ambient, register),
        Function.update base destination (encodeWord n ++ suffix)⟩) =
      some ⟨exit, (ambient, none),
        Function.update base destination (encodeWord (transform p n) ++ suffix)⟩ := by
  change some (TM2.stepAux (program (labels .finish)) _ _) = _
  rw [atFinish, statement, stepAux_suffixStatement]
  cases exit <;> rfl

theorem positionTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (p : Position) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement source scratch destination p labels exit l)
    (base : K → List Bool) (cursor : Nat) (suffix : List Bool)
    (sourceWord : base source = encodeWord cursor ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps p cursor]
      (some ⟨some (labels .start), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base destination (encodeWord (p.eval cursor) ++ base destination)⟩ := by
  rw [steps, Nat.add_comm (seedSteps p cursor) 1, Function.iterate_add_apply,
    seedTrace source scratch destination hs hd hsd p labels exit program atLabels
      base cursor suffix sourceWord scratchEmpty ambient register,
    finishTrace source scratch destination p labels exit program (atLabels .finish),
    transform_initialValue]

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 2 * Polynomial.X + Polynomial.C 4

theorem steps_le_time (p : Position) (cursor : Nat) :
    steps p cursor ≤ timePolynomial.eval cursor := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, steps, seedSteps]
  split <;> omega

def positionInPolynomialTime (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (p : Position) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement source scratch destination p labels exit l)
    (base : K → List Bool) (cursor : Nat) (suffix : List Bool)
    (sourceWord : base source = encodeWord cursor ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .start), (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        Function.update base destination (encodeWord (p.eval cursor) ++ base destination)⟩)
      (timePolynomial.eval cursor) where
  steps := steps p cursor
  evals_in_steps := positionTrace source scratch destination hs hd hsd p labels exit
    program atLabels base cursor suffix sourceWord scratchEmpty ambient register
  steps_le_m := steps_le_time p cursor

end Statements

abbrev machine (p : Position) : Turing.FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Label
  main := .start
  σ := State Unit
  initialState := ((), none)
  m := statement 0 1 2 p id none

def machineInPolynomialTime (p : Position) (base : Fin 3 → List Bool)
    (cursor : Nat) (suffix : List Bool)
    (sourceWord : base 0 = encodeWord cursor ++ suffix) (scratchEmpty : base 1 = []) :
    StateTransition.EvalsToInTime (machine p).step
      ⟨some .start, ((), none), base⟩
      (some ⟨none, ((), none), Function.update base 2 (encodeWord (p.eval cursor) ++ base 2)⟩)
      (timePolynomial.eval cursor) :=
  positionInPolynomialTime 0 1 2 (by decide) (by decide) (by decide) p id none
    (statement 0 1 2 p id none) (fun _ => rfl) base cursor suffix sourceWord scratchEmpty () none

end BinPackingGames.Foundations.Complexity.CookLevin.PositionMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.PostfixAlignment

open StatementCircuit CircuitBatch PostfixModel

variable {ι : Type*}

def exprTokens (wire : ι → Nat) : Expr ι → List Token
  | .input i => [.input (wire i)]
  | .const b => [.const b]
  | .not e => exprTokens wire e ++ [.not]
  | .and e f => exprTokens wire e ++ exprTokens wire f ++ [.and]
  | .or e f => exprTokens wire e ++ exprTokens wire f ++ [.or]

def forestTokens (wire : ι → Nat) (es : List (Expr ι)) : List Token :=
  es.flatMap (exprTokens wire)

@[simp] theorem exprTokens_length (wire : ι → Nat) (e : Expr ι) :
    (exprTokens wire e).length = e.size := by
  induction e <;> simp_all [exprTokens, Expr.size, Nat.add_assoc]

@[simp] theorem exprTokens_rename {κ : Type*} (f : ι → κ) (wire : κ → Nat) (e : Expr ι) :
    exprTokens wire (e.rename f) = exprTokens (fun i => wire (f i)) e := by
  induction e <;> simp_all [Expr.rename, exprTokens]

@[simp] theorem forestTokens_nil (wire : ι → Nat) :
    forestTokens wire ([] : List (Expr ι)) = [] := rfl

@[simp] theorem forestTokens_cons (wire : ι → Nat) (e : Expr ι) (es : List (Expr ι)) :
    forestTokens wire (e :: es) = exprTokens wire e ++ forestTokens wire es := rfl

@[simp] theorem forestTokens_length (wire : ι → Nat) (es : List (Expr ι)) :
    (forestTokens wire es).length = Batch.cost es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [forestTokens_cons, List.length_append, exprTokens_length,
      ih, Batch.cost_cons]

theorem compileTokens_append
    (start : Nat) (roots : List Nat) (first rest : List Token)
    (middle : Nat) (middleRoots : List Nat) (firstGates : List Gate)
    (finish : Nat) (finalRoots : List Nat) (lastGates : List Gate)
    (hfirst : compileTokens start roots first = some (middle, middleRoots, firstGates))
    (hrest : compileTokens middle middleRoots rest = some (finish, finalRoots, lastGates)) :
    compileTokens start roots (first ++ rest) =
      some (finish, finalRoots, firstGates ++ lastGates) := by
  induction first generalizing start roots middle middleRoots firstGates with
  | nil =>
    simp only [compileTokens, Option.some.injEq, Prod.mk.injEq] at hfirst
    rcases hfirst with ⟨rfl, rfl, rfl⟩
    simpa only [List.nil_append] using hrest
  | cons token tokens ih =>
    cases hg : token.takeGate roots with
    | none => simp [compileTokens, hg] at hfirst
    | some pair =>
      rcases pair with ⟨gate, remaining⟩
      cases ht : compileTokens (start + 1) (start :: remaining) tokens with
      | none => simp [compileTokens, hg, ht] at hfirst
      | some triple =>
        rcases triple with ⟨next, afterRoots, tailGates⟩
        simp [compileTokens, hg, ht] at hfirst
        rcases hfirst with ⟨rfl, rfl, rfl⟩
        have hi := ih (start + 1) (start :: remaining) next afterRoots tailGates ht hrest
        simp [List.cons_append, compileTokens, hg, hi]

theorem compile_exprTokens (wire : ι → Nat) (e : Expr ι)
    (start : Nat) (roots : List Nat) :
    compileTokens start roots (exprTokens wire e) =
      some (start + e.size, e.root start :: roots, e.gates wire start) := by
  induction e generalizing start roots with
  | input i => simp [exprTokens, compileTokens, Token.takeGate, Expr.root, Expr.size, Expr.gates]
  | const b => simp [exprTokens, compileTokens, Token.takeGate, Expr.root, Expr.size, Expr.gates]
  | not e ih =>
    have hop : compileTokens (start + e.size) (e.root start :: roots) [.not] =
        some (start + e.size + 1, (start + e.size) :: roots, [.not (e.root start)]) := rfl
    have he := compileTokens_append start roots (exprTokens wire e) [.not]
      _ _ _ _ _ _ (ih start roots) hop
    simpa only [exprTokens, Expr.gates, Expr.size, Expr.root_not, Nat.add_assoc] using he
  | and e f ihe ihf =>
    have hop : compileTokens (start + e.size + f.size)
        (f.root (start + e.size) :: e.root start :: roots) [.and] =
        some (start + e.size + f.size + 1, (start + e.size + f.size) :: roots,
          [.and (e.root start) (f.root (start + e.size))]) := rfl
    have hf := compileTokens_append (start + e.size) (e.root start :: roots)
      (exprTokens wire f) [.and] _ _ _ _ _ _ (ihf _ _) hop
    have he := compileTokens_append start roots (exprTokens wire e)
      (exprTokens wire f ++ [.and]) _ _ _ _ _ _ (ihe _ _) hf
    simpa only [exprTokens, Expr.gates, Expr.size, Expr.root_and, Nat.add_assoc,
      List.append_assoc] using he
  | or e f ihe ihf =>
    have hop : compileTokens (start + e.size + f.size)
        (f.root (start + e.size) :: e.root start :: roots) [.or] =
        some (start + e.size + f.size + 1, (start + e.size + f.size) :: roots,
          [.or (e.root start) (f.root (start + e.size))]) := rfl
    have hf := compileTokens_append (start + e.size) (e.root start :: roots)
      (exprTokens wire f) [.or] _ _ _ _ _ _ (ihf _ _) hop
    have he := compileTokens_append start roots (exprTokens wire e)
      (exprTokens wire f ++ [.or]) _ _ _ _ _ _ (ihe _ _) hf
    simpa only [exprTokens, Expr.gates, Expr.size, Expr.root_or, Nat.add_assoc,
      List.append_assoc] using he

theorem compile_forestTokens (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (roots : List Nat) :
    compileTokens start roots (forestTokens wire es) =
      some (start + Batch.cost es, (Batch.roots start es).reverse ++ roots,
        Batch.gates wire start es) := by
  induction es generalizing start roots with
  | nil => simp [forestTokens, compileTokens, Batch.cost, Batch.roots, Batch.gates]
  | cons e es ih =>
    have h := compileTokens_append start roots (exprTokens wire e) (forestTokens wire es)
      _ _ _ _ _ _ (compile_exprTokens wire e start roots)
      (ih (start + e.size) (e.root start :: roots))
    simpa only [forestTokens_cons, Batch.cost_cons, Batch.roots, Batch.gates,
      List.reverse_cons, List.append_assoc, List.singleton_append, Nat.add_assoc] using h

theorem exprTokens_lowered_ordered (wire : ι → Nat) (e : Expr ι) (start : Nat)
    (hw : ∀ i, wire i < start) : Ordered start (e.gates wire start) :=
  e.gates_ordered wire start hw

theorem forestTokens_lowered_ordered (wire : ι → Nat) (es : List (Expr ι)) (start : Nat)
    (hw : ∀ i, wire i < start) : Ordered start (Batch.gates wire start es) :=
  Batch.gates_ordered wire start es hw

theorem forestTokens_preserves_root_suffix (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (roots : List Nat) :
    ∃ fresh : List Nat,
      compileTokens start roots (forestTokens wire es) =
        some (start + Batch.cost es, fresh ++ roots, Batch.gates wire start es) ∧
      fresh.length = es.length ∧
      ∀ r ∈ fresh, start ≤ r ∧ r < start + Batch.cost es := by
  refine ⟨(Batch.roots start es).reverse, compile_forestTokens wire es start roots, ?_, ?_⟩
  · simp only [List.length_reverse, Batch.roots_length]
  · intro r hr
    exact Batch.roots_bounds start es r (List.mem_reverse.mp hr)

theorem expr_inputBits (wire : ι → Nat) (e : Expr ι) (start : Nat) :
    PostfixModel.inputBits start (exprTokens wire e) =
      encodeWords [start, e.size] ++ tokenBits (exprTokens wire e) := by
  simp only [PostfixModel.inputBits, exprTokens_length]

theorem forest_inputBits (wire : ι → Nat) (es : List (Expr ι)) (start : Nat) :
    PostfixModel.inputBits start (forestTokens wire es) =
      encodeWords [start, Batch.cost es] ++ tokenBits (forestTokens wire es) := by
  simp only [PostfixModel.inputBits, forestTokens_length]

theorem forest_gateRecords_alignment (wire : ι → Nat) (es : List (Expr ι))
    (start : Nat) (roots : List Nat) :
    (compileTokens start roots (forestTokens wire es)).map
      (fun result => gateRecords start result.2.2) =
      some (gateRecords start (Batch.gates wire start es)) := by
  rw [compile_forestTokens]
  rfl

theorem tokenWords_length_le (tokens : List Token) :
    (tokenWords tokens).length ≤ 2 * tokens.length := by
  induction tokens with
  | nil => simp [tokenWords]
  | cons t ts ih =>
    have ht : t.words.length ≤ 2 := by
      cases t with
      | const b => cases b <;> decide
      | not => decide
      | and => decide
      | or => decide
      | input w => simp [Token.words]
    simp only [tokenWords, List.flatMap_cons, List.length_append] at ih ⊢
    simp only [List.length_cons]
    omega

private theorem exprTokens_member (wire : ι → Nat) (e : Expr ι) (t : Token)
    (h : t ∈ exprTokens wire e) :
    (∃ b, t = .const b) ∨ t = .not ∨ t = .and ∨ t = .or ∨
      ∃ i, t = .input (wire i) := by
  induction e with
  | input i =>
    have ht : t = .input (wire i) := by simpa only [exprTokens, List.mem_singleton] using h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, ht⟩)))
  | const b =>
    have ht : t = .const b := by simpa only [exprTokens, List.mem_singleton] using h
    exact Or.inl ⟨b, ht⟩
  | not e ih =>
    simp only [exprTokens, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact ih h
    · exact Or.inr (Or.inl rfl)
  | and e f ihe ihf =>
    simp only [exprTokens, List.mem_append, List.mem_singleton, or_assoc] at h
    rcases h with h | h | rfl
    · exact ihe h
    · exact ihf h
    · exact Or.inr (Or.inr (Or.inl rfl))
  | or e f ihe ihf =>
    simp only [exprTokens, List.mem_append, List.mem_singleton, or_assoc] at h
    rcases h with h | h | rfl
    · exact ihe h
    · exact ihf h
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem expr_tokenWords_bounded (wire : ι → Nat) (e : Expr ι) (start : Nat)
    (hw : ∀ i, wire i < start) (word : Nat) (h : word ∈ tokenWords (exprTokens wire e)) :
    word ≤ max 5 start := by
  obtain ⟨t, ht, hword⟩ := List.mem_flatMap.mp h
  rcases exprTokens_member wire e t ht with ⟨b, rfl⟩ | rfl | rfl | rfl | ⟨i, rfl⟩
  · cases b <;> simp only [Token.words, List.mem_singleton] at hword <;> omega
  · simp only [Token.words, List.mem_singleton] at hword; omega
  · simp only [Token.words, List.mem_singleton] at hword; omega
  · simp only [Token.words, List.mem_singleton] at hword; omega
  · simp only [Token.words, List.mem_cons, List.not_mem_nil, or_false] at hword
    have hi := hw i
    rcases hword with rfl | rfl <;> omega

theorem forest_tokenWords_bounded (wire : ι → Nat) (es : List (Expr ι)) (start : Nat)
    (hw : ∀ i, wire i < start) (word : Nat) (h : word ∈ tokenWords (forestTokens wire es)) :
    word ≤ max 5 start := by
  obtain ⟨t, ht, hword⟩ := List.mem_flatMap.mp h
  obtain ⟨e, he, htoken⟩ := List.mem_flatMap.mp ht
  exact expr_tokenWords_bounded wire e start hw word
    (List.mem_flatMap.mpr ⟨t, htoken, hword⟩)

theorem forest_tokenBits_length_le (wire : ι → Nat) (es : List (Expr ι)) (start : Nat)
    (hw : ∀ i, wire i < start) :
    (tokenBits (forestTokens wire es)).length ≤
      2 * Batch.cost es * (max 5 start + 1) := by
  have hb := encodeWords_length_le (tokenWords (forestTokens wire es)) (max 5 start)
    (forest_tokenWords_bounded wire es start hw)
  have hc : (tokenWords (forestTokens wire es)).length ≤ 2 * Batch.cost es := by
    simpa only [forestTokens_length] using tokenWords_length_le (forestTokens wire es)
  exact hb.trans (Nat.mul_le_mul_right _ hc)

theorem forest_inputBits_length_le (wire : ι → Nat) (es : List (Expr ι)) (start : Nat)
    (hw : ∀ i, wire i < start) :
    (PostfixModel.inputBits start (forestTokens wire es)).length ≤
      start + Batch.cost es + 2 + 2 * Batch.cost es * (max 5 start + 1) := by
  rw [forest_inputBits, List.length_append]
  have hb := forest_tokenBits_length_le wire es start hw
  simp only [encodeWords, List.length_append, encodeWord_length, List.length_nil]
  omega

end BinPackingGames.Foundations.Complexity.CookLevin.PostfixAlignment

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionTemplate

open Turing StatementCircuit

variable {K : Type} (Γ : K → Type) (σ : Type)

inductive Term where
  | state (v : σ)
  | cell (k : K) (position : Position) (symbol : Option (Γ k))
  | const (value : Bool)
  | not (arg : Term)
  | and (left right : Term)
  | or (left right : Term)
  | atZero (position : Position) (yes no : Term)
  | within (position : Position) (yes no : Term)

variable {Γ σ} [∀ k, DecidableEq (Γ k)]

def Term.instantiate (S cursor : Nat) : Term Γ σ → Expr (InputBit Γ σ S)
  | .state v => .input (.inl v)
  | .cell k p a => if h : p.eval cursor < S then .input (.inr ⟨k, ⟨p.eval cursor, h⟩, a⟩)
      else .const (decide ((none : Option (Γ k)) = a))
  | .const b => .const b
  | .not e => .not (e.instantiate S cursor)
  | .and e f => .and (e.instantiate S cursor) (f.instantiate S cursor)
  | .or e f => .or (e.instantiate S cursor) (f.instantiate S cursor)
  | .atZero p yes no => if p.eval cursor = 0 then yes.instantiate S cursor
      else no.instantiate S cursor
  | .within p yes no => if p.eval cursor < S then yes.instantiate S cursor
      else no.instantiate S cursor

def Term.nodeCount : Term Γ σ → Nat
  | .state _ | .cell _ _ _ | .const _ => 1
  | .not e => e.nodeCount + 1
  | .and e f | .or e f | .atZero _ e f | .within _ e f =>
      e.nodeCount + f.nodeCount + 1

omit [∀ tape, DecidableEq (Γ tape)] in
theorem Term.instantiate_size_le (S cursor : Nat) (term : Term Γ σ) :
    (term.instantiate S cursor).size ≤ term.nodeCount := by
  induction term with
  | state v => simp [instantiate, nodeCount, Expr.size]
  | cell k p a =>
      by_cases h : p.eval cursor < S <;> simp [instantiate, nodeCount, h, Expr.size]
  | const b => simp [instantiate, nodeCount, Expr.size]
  | not e ih => simpa only [instantiate, nodeCount, Expr.size] using Nat.add_le_add_right ih 1
  | and e f ihe ihf | or e f ihe ihf =>
      simpa only [instantiate, nodeCount, Expr.size] using
        Nat.add_le_add_right (Nat.add_le_add ihe ihf) 1
  | atZero p e f ihe ihf =>
      by_cases h : p.eval cursor = 0 <;> simp only [instantiate, nodeCount, h, ite_true, ite_false] <;> omega
  | within p e f ihe ihf =>
      by_cases h : p.eval cursor < S <;> simp only [instantiate, nodeCount, h, ite_true, ite_false] <;> omega

def Term.disjoin : List (Term Γ σ) → Term Γ σ
  | [] => .const false
  | e :: rest => .or e (disjoin rest)

def Term.mux (condition yes no : Term Γ σ) : Term Γ σ :=
  .or (.and condition yes) (.and (.not condition) no)

omit [∀ tape, DecidableEq (Γ tape)] in
@[simp] theorem instantiate_disjoin (S cursor : Nat) (es : List (Term Γ σ)) :
    (Term.disjoin es).instantiate S cursor =
      Expr.disjoin (es.map (Term.instantiate S cursor)) := by
  induction es <;> simp_all [Term.disjoin, Term.instantiate, Expr.disjoin]

omit [∀ tape, DecidableEq (Γ tape)] in
@[simp] theorem instantiate_mux (S cursor : Nat) (c x y : Term Γ σ) :
    (Term.mux c x y).instantiate S cursor =
      Expr.mux (c.instantiate S cursor) (x.instantiate S cursor) (y.instantiate S cursor) := rfl

noncomputable def finiteTable {A B : Type} [Fintype A] [DecidableEq B]
    (f : A → B) (x : A → Term Γ σ) (b : B) : Term Γ σ :=
  Term.disjoin (Finset.univ.toList.map fun a => .and (x a) (.const (decide (f a = b))))

noncomputable def finiteTable₂ {A B C : Type} [Fintype A] [Fintype B] [DecidableEq C]
    (f : A → B → C) (x : A → Term Γ σ) (y : B → Term Γ σ) (c : C) : Term Γ σ :=
  finiteTable (fun p : A × B => f p.1 p.2) (fun p => .and (x p.1) (y p.2)) c

omit [∀ tape, DecidableEq (Γ tape)] in
@[simp] theorem instantiate_table {A B : Type} [Fintype A] [DecidableEq B]
    (S cursor : Nat) (f : A → B) (x : A → Term Γ σ) (b : B) :
    (finiteTable f x b).instantiate S cursor =
      table f (fun a => (x a).instantiate S cursor) b := by
  simp [finiteTable, table, List.map_map, Term.instantiate, Function.comp_def]

omit [∀ tape, DecidableEq (Γ tape)] in
@[simp] theorem instantiate_table₂ {A B C : Type} [Fintype A] [Fintype B] [DecidableEq C]
    (S cursor : Nat) (f : A → B → C) (x : A → Term Γ σ) (y : B → Term Γ σ) (c : C) :
    (finiteTable₂ f x y c).instantiate S cursor =
      table₂ f (fun a => (x a).instantiate S cursor)
        (fun b => (y b).instantiate S cursor) c := by
  simp [finiteTable₂, table₂, Term.instantiate]

structure Data where
  state : σ → Term Γ σ
  cells : ∀ k, Position → Option (Γ k) → Term Γ σ

structure Result (Λ : Type) extends Data (Γ := Γ) (σ := σ) where
  label : Option Λ → Term Γ σ

def Data.Matches (S cursor : Nat) (bits : Data (Γ := Γ) (σ := σ))
    (actual : DataBits (InputBit Γ σ S) Γ σ S) : Prop :=
  (∀ v, (bits.state v).instantiate S cursor = actual.state v) ∧
    ∀ k p a (h : p.eval cursor < S),
      (bits.cells k p a).instantiate S cursor = actual.cells k ⟨p.eval cursor, h⟩ a

def Result.Matches {Λ : Type} (S cursor : Nat) (bits : Result (Γ := Γ) (σ := σ) Λ)
    (actual : ResultBits (InputBit Γ σ S) Γ Λ σ S) : Prop :=
  bits.toData.Matches S cursor actual.toDataBits ∧
    ∀ label, (bits.label label).instantiate S cursor = actual.label label

def initial : Data (Γ := Γ) (σ := σ) where
  state := Term.state
  cells := Term.cell

omit [∀ tape, DecidableEq (Γ tape)] in
theorem initial_matches (S cursor : Nat) :
    (initial : Data (Γ := Γ) (σ := σ)).Matches S cursor (inputBits S) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro k p a hp
  simp [initial, Term.instantiate, hp, inputBits]

def read (bits : Data (Γ := Γ) (σ := σ)) (k : K) (p : Position) (a : Option (Γ k)) :
    Term Γ σ :=
  .within p (bits.cells k p a) (.const (decide ((none : Option (Γ k)) = a)))

theorem instantiate_read (S cursor : Nat) (bits : Data (Γ := Γ) (σ := σ))
    (actual : DataBits (InputBit Γ σ S) Γ σ S) (h : bits.Matches S cursor actual)
    (k : K) (p : Position) (a : Option (Γ k)) :
    (read bits k p a).instantiate S cursor = readBits (actual.cells k) (p.eval cursor) a := by
  by_cases hp : p.eval cursor < S
  · simpa [read, Term.instantiate, readBits, hp] using h.2 k p a hp
  · simp [read, Term.instantiate, readBits, hp]

variable {Λ : Type} [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [DecidableEq Λ]

noncomputable def push (bits : Data (Γ := Γ) (σ := σ)) (k : K) (f : σ → Γ k) :
    Data (Γ := Γ) (σ := σ) where
  state := bits.state
  cells := Function.update bits.cells k (fun p a =>
    .atZero p (finiteTable (fun v => some (f v)) bits.state a) (bits.cells k (.pred p) a))

noncomputable def peek (bits : Data (Γ := Γ) (σ := σ)) (k : K)
    (f : σ → Option (Γ k) → σ) : Data (Γ := Γ) (σ := σ) where
  state := finiteTable₂ f bits.state (read bits k .zero)
  cells := bits.cells

noncomputable def pop (bits : Data (Γ := Γ) (σ := σ)) (k : K)
    (f : σ → Option (Γ k) → σ) : Data (Γ := Γ) (σ := σ) where
  state := finiteTable₂ f bits.state (read bits k .zero)
  cells := Function.update bits.cells k (fun p a => read bits k (.succ p) a)

noncomputable def load (bits : Data (Γ := Γ) (σ := σ)) (f : σ → σ) :
    Data (Γ := Γ) (σ := σ) where
  state := finiteTable f bits.state
  cells := bits.cells

def mux (condition : Term Γ σ) (yes no : Result (Γ := Γ) (σ := σ) Λ) :
    Result (Γ := Γ) (σ := σ) Λ where
  state := fun v => .mux condition (yes.state v) (no.state v)
  cells := fun k p a => .mux condition (yes.cells k p a) (no.cells k p a)
  label := fun l => .mux condition (yes.label l) (no.label l)

omit [DecidableEq σ] [∀ tape, Fintype (Γ tape)] in
theorem push_matches (S cursor : Nat) (bits : Data (Γ := Γ) (σ := σ))
    (actual : DataBits (InputBit Γ σ S) Γ σ S) (h : bits.Matches S cursor actual)
    (k : K) (f : σ → Γ k) :
    (push bits k f).Matches S cursor (pushBits actual k f) := by
  refine ⟨h.1, ?_⟩
  intro j p a hp
  by_cases hj : j = k
  · subst j
    simp only [push, pushBits, Function.update_self]
    by_cases hz : p.eval cursor = 0
    · simp [Term.instantiate, hz, h.1]
    · have hpred : (Position.pred p).eval cursor < S := by
        simp only [Position.eval]
        omega
      simpa [Term.instantiate, Position.eval, hz] using h.2 k (.pred p) a hpred
  · simpa [push, pushBits, Function.update_of_ne hj] using h.2 j p a hp

omit [DecidableEq K] in
theorem peek_matches (S cursor : Nat) (bits : Data (Γ := Γ) (σ := σ))
    (actual : DataBits (InputBit Γ σ S) Γ σ S) (h : bits.Matches S cursor actual)
    (k : K) (f : σ → Option (Γ k) → σ) :
    (peek bits k f).Matches S cursor (peekBits actual k f) := by
  refine ⟨?_, h.2⟩
  intro v
  simp only [peek, peekBits, instantiate_table₂]
  have hs : (fun a => (bits.state a).instantiate S cursor) = actual.state := funext h.1
  have hc : (fun a => (read bits k .zero a).instantiate S cursor) =
      readBits (actual.cells k) 0 := by
    funext a
    exact instantiate_read S cursor bits actual h k .zero a
  rw [hs, hc]

theorem pop_matches (S cursor : Nat) (bits : Data (Γ := Γ) (σ := σ))
    (actual : DataBits (InputBit Γ σ S) Γ σ S) (h : bits.Matches S cursor actual)
    (k : K) (f : σ → Option (Γ k) → σ) :
    (pop bits k f).Matches S cursor (popBits actual k f) := by
  refine ⟨(peek_matches S cursor bits actual h k f).1, ?_⟩
  intro j p a hp
  by_cases hj : j = k
  · subst j
    simpa [pop, popBits, Position.eval] using instantiate_read S cursor bits actual h k (.succ p) a
  · simpa [pop, popBits, Function.update_of_ne hj] using h.2 j p a hp

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [∀ tape, Fintype (Γ tape)] in
theorem load_matches (S cursor : Nat) (bits : Data (Γ := Γ) (σ := σ))
    (actual : DataBits (InputBit Γ σ S) Γ σ S) (h : bits.Matches S cursor actual)
    (f : σ → σ) : (load bits f).Matches S cursor (loadBits actual f) := by
  refine ⟨?_, h.2⟩
  intro v
  simp [load, loadBits, h.1]

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] in
theorem mux_matches (S cursor : Nat) (condition : Term Γ σ)
    (yes no : Result (Γ := Γ) (σ := σ) Λ)
    (actualYes actualNo : ResultBits (InputBit Γ σ S) Γ Λ σ S)
    (hy : yes.Matches S cursor actualYes) (hn : no.Matches S cursor actualNo) :
    (mux condition yes no).Matches S cursor
      (muxResult (condition.instantiate S cursor) actualYes actualNo) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro v
    simp [mux, muxResult, hy.1.1, hn.1.1]
  · intro k p a hp
    simp [mux, muxResult, hy.1.2 k p a hp, hn.1.2 k p a hp]
  · intro l
    simp [mux, muxResult, hy.2, hn.2]

noncomputable def compile : TM2.Stmt Γ Λ σ → Data (Γ := Γ) (σ := σ) →
    Result (Γ := Γ) (σ := σ) Λ
  | .push k f next, bits => compile next (push bits k f)
  | .peek k f next, bits => compile next (peek bits k f)
  | .pop k f next, bits => compile next (pop bits k f)
  | .load f next, bits => compile next (load bits f)
  | .branch guard yes no, bits =>
      mux (finiteTable guard bits.state true) (compile yes bits) (compile no bits)
  | .goto label, bits =>
      { toData := bits, label := finiteTable (fun v => some (label v)) bits.state }
  | .halt, bits =>
      { toData := bits, label := fun l => .const (decide ((none : Option Λ) = l)) }

theorem compile_matches (S cursor : Nat) (stmt : TM2.Stmt Γ Λ σ)
    (bits : Data (Γ := Γ) (σ := σ)) (actual : DataBits (InputBit Γ σ S) Γ σ S)
    (h : bits.Matches S cursor actual) :
    (compile stmt bits).Matches S cursor (compileAux stmt actual) := by
  induction stmt generalizing bits actual with
  | push k f next ih =>
      exact ih (push bits k f) (pushBits actual k f) (push_matches S cursor bits actual h k f)
  | peek k f next ih =>
      exact ih (peek bits k f) (peekBits actual k f) (peek_matches S cursor bits actual h k f)
  | pop k f next ih =>
      exact ih (pop bits k f) (popBits actual k f) (pop_matches S cursor bits actual h k f)
  | load f next ih =>
      exact ih (load bits f) (loadBits actual f) (load_matches S cursor bits actual h f)
  | branch guard yes no ihy ihn =>
      have hm := mux_matches S cursor (finiteTable guard bits.state true)
        (compile yes bits) (compile no bits) (compileAux yes actual) (compileAux no actual)
        (ihy bits actual h) (ihn bits actual h)
      simpa [compile, compileAux, h.1] using hm
  | goto label =>
      refine ⟨h, ?_⟩
      intro l
      simp [compile, compileAux, h.1]
  | halt => exact ⟨h, fun _ => rfl⟩

abbrev OutputKind (Γ : K → Type) (Λ σ : Type) :=
  Option Λ ⊕ (σ ⊕ (Σ k, Option (Γ k)))

def bitKind {S : Nat} : ConfigBit Γ Λ σ S → OutputKind Γ Λ σ
  | .inl l => .inl l
  | .inr (.inl v) => .inr (.inl v)
  | .inr (.inr ⟨k, _, a⟩) => .inr (.inr ⟨k, a⟩)

def bitCursor {S : Nat} : ConfigBit Γ Λ σ S → Nat
  | .inl _ | .inr (.inl _) => 0
  | .inr (.inr ⟨_, i, _⟩) => i.val

def select (bits : Result (Γ := Γ) (σ := σ) Λ) : OutputKind Γ Λ σ → Term Γ σ
  | .inl l => bits.label l
  | .inr (.inl v) => bits.state v
  | .inr (.inr ⟨k, a⟩) => bits.cells k .current a

noncomputable def transition (stmt : TM2.Stmt Γ Λ σ) (kind : OutputKind Γ Λ σ) : Term Γ σ :=
  select (compile stmt initial) kind

theorem transition_instantiate (S : Nat) (stmt : TM2.Stmt Γ Λ σ)
    (bit : ConfigBit Γ Λ σ S) :
    (transition stmt (bitKind bit)).instantiate S (bitCursor bit) = transitionExpr S stmt bit := by
  have h := compile_matches S (bitCursor bit) stmt initial (inputBits S)
    (initial_matches S (bitCursor bit))
  rcases bit with l | (v | ⟨k, i, a⟩)
  · exact h.2 l
  · exact h.1.1 v
  · exact h.1.2 k .current a i.isLt

inductive Global where
  | label (value : Option Λ)
  | data (term : Term Γ σ)
  | const (value : Bool)
  | and (left right : Global)
  | or (left right : Global)

def Global.instantiate (S cursor : Nat) : Global (Γ := Γ) (Λ := Λ) (σ := σ) →
    Expr (ConfigBit Γ Λ σ S)
  | .label l => .input (.inl l)
  | .data e => (e.instantiate S cursor).rename Sum.inr
  | .const b => .const b
  | .and e f => .and (e.instantiate S cursor) (f.instantiate S cursor)
  | .or e f => .or (e.instantiate S cursor) (f.instantiate S cursor)

def Global.nodeCount : Global (Γ := Γ) (Λ := Λ) (σ := σ) → Nat
  | .label _ | .const _ => 1
  | .data e => e.nodeCount
  | .and e f | .or e f => e.nodeCount + f.nodeCount + 1

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] in
theorem Global.instantiate_size_le (S cursor : Nat)
    (term : Global (Γ := Γ) (Λ := Λ) (σ := σ)) :
    (term.instantiate S cursor).size ≤ term.nodeCount := by
  induction term with
  | label l => simp [instantiate, nodeCount, Expr.size]
  | data e => simpa only [instantiate, nodeCount, Expr.size_rename] using e.instantiate_size_le S cursor
  | const b => simp [instantiate, nodeCount, Expr.size]
  | and e f ihe ihf | or e f ihe ihf =>
      simpa only [instantiate, nodeCount, Expr.size] using
        Nat.add_le_add_right (Nat.add_le_add ihe ihf) 1

def Global.disjoin : List (Global (Γ := Γ) (Λ := Λ) (σ := σ)) →
    Global (Γ := Γ) (Λ := Λ) (σ := σ)
  | [] => .const false
  | e :: es => .or e (disjoin es)

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] in
@[simp] theorem instantiate_global_disjoin (S cursor : Nat)
    (es : List (Global (Γ := Γ) (Λ := Λ) (σ := σ))) :
    (Global.disjoin es).instantiate S cursor =
      Expr.disjoin (es.map (Global.instantiate S cursor)) := by
  induction es <;> simp_all [Global.disjoin, Global.instantiate, Expr.disjoin]

def self : OutputKind Γ Λ σ → Global (Γ := Γ) (Λ := Λ) (σ := σ)
  | .inl l => .label l
  | .inr (.inl v) => .data (.state v)
  | .inr (.inr ⟨k, a⟩) => .data (.cell k .current a)

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] in
theorem self_instantiate (S : Nat) (bit : ConfigBit Γ Λ σ S) :
    (self (bitKind bit)).instantiate S (bitCursor bit) = .input bit := by
  rcases bit with l | (v | ⟨k, i, a⟩)
  · rfl
  · rfl
  · simp [self, bitKind, bitCursor, Global.instantiate, Term.instantiate,
      Position.eval, i.isLt, Expr.rename]

variable [Fintype Λ]

noncomputable def sticky (program : Λ → TM2.Stmt Γ Λ σ) (kind : OutputKind Γ Λ σ) :
    Global (Γ := Γ) (Λ := Λ) (σ := σ) :=
  .or (.and (.label none) (self kind))
    (Global.disjoin (Finset.univ.toList.map fun l =>
      .and (.label (some l)) (.data (transition (program l) kind))))

theorem sticky_instantiate (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ)
    (bit : ConfigBit Γ Λ σ S) :
    (sticky program (bitKind bit)).instantiate S (bitCursor bit) =
      MachineCircuit.stickyExpr S program bit := by
  simp only [sticky, Global.instantiate, instantiate_global_disjoin, List.map_map,
    Function.comp_def, self_instantiate, transition_instantiate,
    MachineCircuit.stickyExpr]
  rfl

def kindIndexEquiv (indexing : ConfigIndex.Indexing Γ Λ σ) :
    OutputKind Γ Λ σ ≃
      Fin (indexing.labelCount + indexing.stateCount + indexing.symbolCount) :=
  (Equiv.sumCongr indexing.labels (Equiv.sumCongr indexing.states indexing.symbols)).trans
    ((Equiv.sumAssoc (Fin indexing.labelCount) (Fin indexing.stateCount)
      (Fin indexing.symbolCount)).symm.trans
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin indexing.symbolCount))).trans
        finSumFinEquiv))

noncomputable def templateBank (indexing : ConfigIndex.Indexing Γ Λ σ)
    (program : Λ → TM2.Stmt Γ Λ σ)
    (i : Fin (indexing.labelCount + indexing.stateCount + indexing.symbolCount)) :
    Global (Γ := Γ) (Λ := Λ) (σ := σ) :=
  sticky program ((kindIndexEquiv indexing).symm i)

@[simp] theorem templateBank_select (indexing : ConfigIndex.Indexing Γ Λ σ)
    (program : Λ → TM2.Stmt Γ Λ σ) (kind : OutputKind Γ Λ σ) :
    templateBank indexing program (kindIndexEquiv indexing kind) = sticky program kind := by
  simp [templateBank]

def rootLookup (roots : List Nat) (address : Nat) : Nat := roots[address]?.getD 0

def configWire (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat) (S : Nat)
    (bit : ConfigBit Γ Λ σ S) : Nat :=
  rootLookup roots (indexing.configIndexEquiv S bit).val

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem labelAddress_lt_width (indexing : ConfigIndex.Indexing Γ Λ σ)
    (S : Nat) (label : Option Λ) :
    (indexing.labels label).val < indexing.width S := by
  simpa only [ConfigIndex.Indexing.configIndex_label] using
    (indexing.configIndexEquiv S (.inl label)).isLt

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem stateAddress_lt_width (indexing : ConfigIndex.Indexing Γ Λ σ)
    (S : Nat) (state : σ) :
    indexing.labelCount + (indexing.states state).val < indexing.width S := by
  simpa only [ConfigIndex.Indexing.configIndex_state] using
    (indexing.configIndexEquiv S (.inr (.inl state))).isLt

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem cellAddress_lt_width (indexing : ConfigIndex.Indexing Γ Λ σ)
    (S : Nat) (k : K) (position : Nat) (symbol : Option (Γ k)) (hp : position < S) :
    indexing.labelCount + indexing.stateCount + position * indexing.symbolCount +
      (indexing.symbols ⟨k, symbol⟩).val < indexing.width S := by
  simpa only [ConfigIndex.Indexing.configIndex_cell] using
    (indexing.configIndexEquiv S (.inr (.inr ⟨k, ⟨position, hp⟩, symbol⟩))).isLt

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem rootLookup_present (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat)
    (S : Nat) (hroots : indexing.width S ≤ roots.length)
    (address : Nat) (haddress : address < indexing.width S) :
    roots[address]? = some (rootLookup roots address) := by
  have h : address < roots.length := haddress.trans_le hroots
  simp only [rootLookup, List.getElem?_eq_getElem h, Option.getD_some]

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem configWire_present (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat)
    (S : Nat) (hroots : indexing.width S ≤ roots.length) (bit : ConfigBit Γ Λ σ S) :
    roots[(indexing.configIndexEquiv S bit).val]? = some (configWire indexing roots S bit) :=
  rootLookup_present indexing roots S hroots _ (indexing.configIndexEquiv S bit).isLt

def Term.tokens (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat)
    (S cursor : Nat) : Term Γ σ → List PostfixModel.Token
  | .state v => [.input (rootLookup roots
      (indexing.labelCount + (indexing.states v).val))]
  | .cell k p a => if p.eval cursor < S then
      [.input (rootLookup roots (indexing.labelCount + indexing.stateCount +
        p.eval cursor * indexing.symbolCount + (indexing.symbols ⟨k, a⟩).val))]
      else [.const (decide ((none : Option (Γ k)) = a))]
  | .const b => [.const b]
  | .not e => e.tokens indexing roots S cursor ++ [.not]
  | .and e f => e.tokens indexing roots S cursor ++ f.tokens indexing roots S cursor ++ [.and]
  | .or e f => e.tokens indexing roots S cursor ++ f.tokens indexing roots S cursor ++ [.or]
  | .atZero p yes no => if p.eval cursor = 0 then yes.tokens indexing roots S cursor
      else no.tokens indexing roots S cursor
  | .within p yes no => if p.eval cursor < S then yes.tokens indexing roots S cursor
      else no.tokens indexing roots S cursor

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem Term.tokens_eq (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat)
    (S cursor : Nat) (term : Term Γ σ) :
    term.tokens indexing roots S cursor =
      PostfixAlignment.exprTokens (fun bit => configWire indexing roots S (.inr bit))
        (term.instantiate S cursor) := by
  induction term with
  | state v => simp [tokens, instantiate, PostfixAlignment.exprTokens, configWire]
  | cell k p a =>
      by_cases h : p.eval cursor < S <;>
        simp [tokens, instantiate, h, PostfixAlignment.exprTokens, configWire]
  | const b => rfl
  | not e ih => simp only [tokens, instantiate, PostfixAlignment.exprTokens, ih]
  | and e f ihe ihf => simp only [tokens, instantiate, PostfixAlignment.exprTokens, ihe, ihf]
  | or e f ihe ihf => simp only [tokens, instantiate, PostfixAlignment.exprTokens, ihe, ihf]
  | atZero p e f ihe ihf =>
      by_cases h : p.eval cursor = 0 <;> simp [tokens, instantiate, h, ihe, ihf]
  | within p e f ihe ihf =>
      by_cases h : p.eval cursor < S <;> simp [tokens, instantiate, h, ihe, ihf]

def Global.tokens (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat)
    (S cursor : Nat) : Global (Γ := Γ) (Λ := Λ) (σ := σ) → List PostfixModel.Token
  | .label l => [.input (rootLookup roots (indexing.labels l).val)]
  | .data e => e.tokens indexing roots S cursor
  | .const b => [.const b]
  | .and e f => e.tokens indexing roots S cursor ++ f.tokens indexing roots S cursor ++ [.and]
  | .or e f => e.tokens indexing roots S cursor ++ f.tokens indexing roots S cursor ++ [.or]

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem Global.tokens_eq (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat)
    (S cursor : Nat) (term : Global (Γ := Γ) (Λ := Λ) (σ := σ)) :
    term.tokens indexing roots S cursor =
      PostfixAlignment.exprTokens (configWire indexing roots S) (term.instantiate S cursor) := by
  induction term with
  | label l => simp [tokens, instantiate, PostfixAlignment.exprTokens, configWire]
  | data e =>
      simp only [tokens, instantiate, PostfixAlignment.exprTokens_rename]
      exact e.tokens_eq indexing roots S cursor
  | const b => rfl
  | and e f ihe ihf => simp only [tokens, instantiate, PostfixAlignment.exprTokens, ihe, ihf]
  | or e f ihe ihf => simp only [tokens, instantiate, PostfixAlignment.exprTokens, ihe, ihf]

theorem sticky_tokens_eq (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat)
    (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ) (bit : ConfigBit Γ Λ σ S) :
    (sticky program (bitKind bit)).tokens indexing roots S (bitCursor bit) =
      PostfixAlignment.exprTokens (configWire indexing roots S)
        (MachineCircuit.stickyExpr S program bit) := by
  rw [Global.tokens_eq, sticky_instantiate]

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem Global.tokens_length_le (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat)
    (S cursor : Nat) (term : Global (Γ := Γ) (Λ := Λ) (σ := σ)) :
    (term.tokens indexing roots S cursor).length ≤ term.nodeCount := by
  rw [term.tokens_eq, PostfixAlignment.exprTokens_length]
  exact term.instantiate_size_le S cursor

theorem sticky_tokens_length_le (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat)
    (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ) (bit : ConfigBit Γ Λ σ S) :
    ((sticky program (bitKind bit)).tokens indexing roots S (bitCursor bit)).length ≤
      MachineCircuit.expressionCost program := by
  rw [sticky_tokens_eq, PostfixAlignment.exprTokens_length]
  exact MachineCircuit.stickyExpr_size_le S program bit

def outputOrder (indexing : ConfigIndex.Indexing Γ Λ σ) (S : Nat) :
    List (ConfigBit Γ Λ σ S) :=
  (List.finRange (indexing.width S)).map (indexing.configIndexEquiv S).symm

noncomputable def forestTokens (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat)
    (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ) : List PostfixModel.Token :=
  (outputOrder indexing S).flatMap fun bit =>
    (sticky program (bitKind bit)).tokens indexing roots S (bitCursor bit)

theorem forestTokens_eq (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat)
    (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ) :
    forestTokens indexing roots S program =
      PostfixAlignment.forestTokens (configWire indexing roots S)
        ((outputOrder indexing S).map (MachineCircuit.stickyExpr S program)) := by
  simp only [forestTokens, PostfixAlignment.forestTokens, List.flatMap_map]
  apply List.flatMap_congr
  intro bit _
  exact sticky_tokens_eq indexing roots S program bit

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
@[simp] theorem outputOrder_length (indexing : ConfigIndex.Indexing Γ Λ σ) (S : Nat) :
    (outputOrder indexing S).length = indexing.width S := by
  simp [outputOrder]

theorem forestTokens_length_le (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat)
    (S : Nat) (program : Λ → TM2.Stmt Γ Λ σ) :
    (forestTokens indexing roots S program).length ≤
      indexing.width S * MachineCircuit.expressionCost program := by
  have h (bits : List (ConfigBit Γ Λ σ S)) :
      (bits.flatMap fun bit =>
        (sticky program (bitKind bit)).tokens indexing roots S (bitCursor bit)).length ≤
        bits.length * MachineCircuit.expressionCost program := by
    induction bits with
    | nil => simp
    | cons bit bits ih =>
        have hb := sticky_tokens_length_le indexing roots S program bit
        simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
        omega
  simpa only [forestTokens, outputOrder_length] using h (outputOrder indexing S)

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionTemplate

namespace BinPackingGames.Foundations.Complexity.CookLevin.OutputOrder

open StatementCircuit

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

private theorem unindex_label (indexing : ConfigIndex.Indexing Γ Λ σ) (S : Nat)
    (label : Fin indexing.labelCount) (j : Fin (indexing.width S))
    (hj : j.val = label.val) :
    (indexing.configIndexEquiv S).symm j =
      (Sum.inl (indexing.labels.symm label) : ConfigBit Γ Λ σ S) := by
  apply (indexing.configIndexEquiv S).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  simpa only [ConfigIndex.Indexing.configIndex_label, Equiv.apply_symm_apply] using hj

private theorem unindex_state (indexing : ConfigIndex.Indexing Γ Λ σ) (S : Nat)
    (state : Fin indexing.stateCount) (j : Fin (indexing.width S))
    (hj : j.val = indexing.labelCount + state.val) :
    (indexing.configIndexEquiv S).symm j =
      (Sum.inr (Sum.inl (indexing.states.symm state)) : ConfigBit Γ Λ σ S) := by
  apply (indexing.configIndexEquiv S).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  simpa only [ConfigIndex.Indexing.configIndex_state, Equiv.apply_symm_apply] using hj

private theorem unindex_cell (indexing : ConfigIndex.Indexing Γ Λ σ) (S : Nat)
    (cursor : Fin S) (symbol : Fin indexing.symbolCount) (j : Fin (indexing.width S))
    (hj : j.val = indexing.labelCount + indexing.stateCount +
      cursor.val * indexing.symbolCount + symbol.val) :
    (indexing.configIndexEquiv S).symm j =
      (let a := indexing.symbols.symm symbol
       Sum.inr (Sum.inr ⟨a.1, cursor, a.2⟩) : ConfigBit Γ Λ σ S) := by
  dsimp only
  apply (indexing.configIndexEquiv S).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  rw [ConfigIndex.Indexing.configIndex_cell]
  simpa only [Sigma.eta, Equiv.apply_symm_apply] using hj

theorem outputOrder_eq_blocks (indexing : ConfigIndex.Indexing Γ Λ σ) (S : Nat) :
    TransitionTemplate.outputOrder indexing S =
      ((List.finRange indexing.labelCount).map fun i =>
        (Sum.inl (indexing.labels.symm i) : ConfigBit Γ Λ σ S)) ++
      ((List.finRange indexing.stateCount).map fun i =>
        (Sum.inr (Sum.inl (indexing.states.symm i)) : ConfigBit Γ Λ σ S)) ++
      ((List.finRange S).flatMap fun cursor =>
        (List.finRange indexing.symbolCount).map fun j =>
          let a := indexing.symbols.symm j
          (Sum.inr (Sum.inr ⟨a.1, cursor, a.2⟩) : ConfigBit Γ Λ σ S)) := by
  simp only [TransitionTemplate.outputOrder, List.flatMap_def, ← List.ofFn_eq_map]
  change List.ofFn (fun j : Fin (indexing.labelCount + indexing.stateCount +
      S * indexing.symbolCount) => (indexing.configIndexEquiv S).symm j) = _
  rw [List.ofFn_add (n := indexing.labelCount + indexing.stateCount)
    (m := S * indexing.symbolCount)]
  rw [List.ofFn_add (n := indexing.labelCount) (m := indexing.stateCount)]
  rw [List.ofFn_mul (m := S) (n := indexing.symbolCount)]
  congr 1
  · congr 1
    · apply congrArg List.ofFn
      funext i
      exact unindex_label indexing S i _ rfl
    · apply congrArg List.ofFn
      funext i
      exact unindex_state indexing S i _ rfl
  · apply congrArg List.flatten
    apply congrArg List.ofFn
    funext cursor
    apply congrArg List.ofFn
    funext symbol
    apply unindex_cell indexing S cursor symbol
    simp only [Fin.val_natAdd]
    omega

end BinPackingGames.Foundations.Complexity.CookLevin.OutputOrder

end OAI
