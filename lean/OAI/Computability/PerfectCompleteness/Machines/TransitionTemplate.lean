import OAI.Computability.PerfectCompleteness.Machines.CircuitBatchLemmas
import OAI.Computability.PerfectCompleteness.Machines.MachineCircuit
import OAI.Computability.PerfectCompleteness.Machines.PositionLemmas
import OAI.Computability.PerfectCompleteness.Machines.PostfixAlignment

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionTemplate

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

omit [∀ k, DecidableEq (Γ k)] in
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

omit [∀ k, DecidableEq (Γ k)] in
@[simp] theorem instantiate_disjoin (S cursor : Nat) (es : List (Term Γ σ)) :
    (Term.disjoin es).instantiate S cursor =
      Expr.disjoin (es.map (Term.instantiate S cursor)) := by
  induction es <;> simp_all [Term.disjoin, Term.instantiate, Expr.disjoin]

omit [∀ k, DecidableEq (Γ k)] in
@[simp] theorem instantiate_mux (S cursor : Nat) (c x y : Term Γ σ) :
    (Term.mux c x y).instantiate S cursor =
      Expr.mux (c.instantiate S cursor) (x.instantiate S cursor) (y.instantiate S cursor) := rfl

noncomputable def finiteTable {A B : Type} [Fintype A] [DecidableEq B]
    (f : A → B) (x : A → Term Γ σ) (b : B) : Term Γ σ :=
  Term.disjoin (Finset.univ.toList.map fun a => .and (x a) (.const (decide (f a = b))))

noncomputable def finiteTable₂ {A B C : Type} [Fintype A] [Fintype B] [DecidableEq C]
    (f : A → B → C) (x : A → Term Γ σ) (y : B → Term Γ σ) (c : C) : Term Γ σ :=
  finiteTable (fun p : A × B => f p.1 p.2) (fun p => .and (x p.1) (y p.2)) c

omit [∀ k, DecidableEq (Γ k)] in
@[simp] theorem instantiate_table {A B : Type} [Fintype A] [DecidableEq B]
    (S cursor : Nat) (f : A → B) (x : A → Term Γ σ) (b : B) :
    (finiteTable f x b).instantiate S cursor =
      table f (fun a => (x a).instantiate S cursor) b := by
  simp [finiteTable, table, List.map_map, Term.instantiate, Function.comp_def]

omit [∀ k, DecidableEq (Γ k)] in
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

omit [∀ k, DecidableEq (Γ k)] in
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

omit [DecidableEq σ] [∀ k, Fintype (Γ k)] in
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

omit [∀ k, DecidableEq (Γ k)] [DecidableEq K] [∀ k, Fintype (Γ k)] in
theorem load_matches (S cursor : Nat) (bits : Data (Γ := Γ) (σ := σ))
    (actual : DataBits (InputBit Γ σ S) Γ σ S) (h : bits.Matches S cursor actual)
    (f : σ → σ) : (load bits f).Matches S cursor (loadBits actual f) := by
  refine ⟨?_, h.2⟩
  intro v
  simp [load, loadBits, h.1]

omit [∀ k, DecidableEq (Γ k)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ k, Fintype (Γ k)] [DecidableEq Λ] in
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

omit [∀ k, DecidableEq (Γ k)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ k, Fintype (Γ k)] [DecidableEq Λ] in
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

omit [∀ k, DecidableEq (Γ k)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ k, Fintype (Γ k)] [DecidableEq Λ] in
@[simp] theorem instantiate_global_disjoin (S cursor : Nat)
    (es : List (Global (Γ := Γ) (Λ := Λ) (σ := σ))) :
    (Global.disjoin es).instantiate S cursor =
      Expr.disjoin (es.map (Global.instantiate S cursor)) := by
  induction es <;> simp_all [Global.disjoin, Global.instantiate, Expr.disjoin]

def self : OutputKind Γ Λ σ → Global (Γ := Γ) (Λ := Λ) (σ := σ)
  | .inl l => .label l
  | .inr (.inl v) => .data (.state v)
  | .inr (.inr ⟨k, a⟩) => .data (.cell k .current a)

omit [∀ k, DecidableEq (Γ k)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ k, Fintype (Γ k)] [DecidableEq Λ] in
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

omit [∀ k, DecidableEq (Γ k)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ] in
theorem labelAddress_lt_width (indexing : ConfigIndex.Indexing Γ Λ σ)
    (S : Nat) (label : Option Λ) :
    (indexing.labels label).val < indexing.width S := by
  simpa only [ConfigIndex.Indexing.configIndex_label] using
    (indexing.configIndexEquiv S (.inl label)).isLt

omit [∀ k, DecidableEq (Γ k)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ] in
theorem stateAddress_lt_width (indexing : ConfigIndex.Indexing Γ Λ σ)
    (S : Nat) (state : σ) :
    indexing.labelCount + (indexing.states state).val < indexing.width S := by
  simpa only [ConfigIndex.Indexing.configIndex_state] using
    (indexing.configIndexEquiv S (.inr (.inl state))).isLt

omit [∀ k, DecidableEq (Γ k)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ] in
theorem cellAddress_lt_width (indexing : ConfigIndex.Indexing Γ Λ σ)
    (S : Nat) (k : K) (position : Nat) (symbol : Option (Γ k)) (hp : position < S) :
    indexing.labelCount + indexing.stateCount + position * indexing.symbolCount +
      (indexing.symbols ⟨k, symbol⟩).val < indexing.width S := by
  simpa only [ConfigIndex.Indexing.configIndex_cell] using
    (indexing.configIndexEquiv S (.inr (.inr ⟨k, ⟨position, hp⟩, symbol⟩))).isLt

omit [∀ k, DecidableEq (Γ k)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ] in
theorem rootLookup_present (indexing : ConfigIndex.Indexing Γ Λ σ) (roots : List Nat)
    (S : Nat) (hroots : indexing.width S ≤ roots.length)
    (address : Nat) (haddress : address < indexing.width S) :
    roots[address]? = some (rootLookup roots address) := by
  have h : address < roots.length := haddress.trans_le hroots
  simp only [rootLookup, List.getElem?_eq_getElem h, Option.getD_some]

omit [∀ k, DecidableEq (Γ k)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ] in
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

omit [∀ k, DecidableEq (Γ k)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ] in
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

omit [∀ k, DecidableEq (Γ k)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ] in
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

omit [∀ k, DecidableEq (Γ k)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ] in
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

omit [∀ k, DecidableEq (Γ k)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ] in
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

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.TransitionTemplate

end

end OAI
