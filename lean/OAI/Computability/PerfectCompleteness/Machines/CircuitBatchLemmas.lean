import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import OAI.Computability.PerfectCompleteness.Machines.StatementCircuit

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.CircuitBatch

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

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.CircuitBatch

end

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.ConfigIndex

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

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.ConfigIndex

end

end OAI
