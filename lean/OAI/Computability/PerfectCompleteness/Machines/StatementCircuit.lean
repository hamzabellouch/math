import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import OAI.Computability.PerfectCompleteness.Machines.BoundedExecution
import OAI.Computability.PerfectCompleteness.Machines.CircuitLemmas
import OAI.Computability.PerfectCompleteness.Machines.ProducerBootstrapLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.StatementCircuit

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

omit [(k : K) → Fintype (Γ k)] in
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

omit [DecidableEq K] [(k : K) → Fintype (Γ k)] in
theorem realizes_loadBits {S : Nat} (bits : DataBits ι Γ σ S) (input : ι → Bool)
    (v : σ) (tapes : ∀ k, List (Γ k)) (h : bits.Realizes input v tapes)
    (f : σ → σ) : (loadBits bits f).Realizes input (f v) tapes := by
  exact ⟨fun w => eval_table input f bits.state v h.1 w, h.2⟩

omit [DecidableEq K] [Fintype σ] [(k : K) → Fintype (Γ k)] in
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

omit [DecidableEq K] [Fintype σ] [(k : K) → Fintype (Γ k)] in
theorem inputBits_realizes (S : Nat) (v : σ) (tapes : ∀ k, List (Γ k)) :
    (inputBits S).Realizes (inputEncoding S v tapes) v tapes := by
  exact ⟨fun _ => rfl, fun _ _ _ => rfl⟩

omit [DecidableEq K] [Fintype σ] [(k : K) → Fintype (Γ k)] in
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

section Size

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

omit [DecidableEq σ] [(k : K) → Fintype (Γ k)] in
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

omit [DecidableEq K] [(k : K) → Fintype (Γ k)] [(k : K) → DecidableEq (Γ k)] in
theorem loadBits_bounded {S : Nat} (bits : DataBits ι Γ σ S) (C : Nat)
    (h : bits.Bounded C) (f : σ → σ) :
    (loadBits bits f).Bounded (max C (unaryCost σ C)) := by
  exact ⟨fun v => (size_table_le f bits.state v C h.1).trans (Nat.le_max_right _ _),
    fun k i a => (h.2 k i a).trans (Nat.le_max_left _ _)⟩

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(k : K) → Fintype (Γ k)]
  [(k : K) → DecidableEq (Γ k)] [DecidableEq Λ] in
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

end Size

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.StatementCircuit

end

end OAI
