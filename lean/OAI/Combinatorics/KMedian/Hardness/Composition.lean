import Mathlib
import OAI.Combinatorics.KMedian.Hardness.Model
import OAI.Combinatorics.KMedian.Main

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Complexity.FiniteComposition
open Turing Function Finset Polynomial
open Binary (Trace)

structure Machine where
  K : Type
  [decK : DecidableEq K]
  [finK : Fintype K]
  Γ : K → Type
  [finΓ : ∀ k, Fintype (Γ k)]
  input : K
  output : K
  inputAlphabet : Γ input ≃ Bool
  outputAlphabet : Γ output ≃ Bool
  Label : Type
  [finLabel : Fintype Label]
  main : Label
  State : Type
  [finState : Fintype State]
  initial : State
  code : Label → TM2.Stmt Γ Label State

attribute [instance] Machine.decK Machine.finK Machine.finΓ Machine.finLabel Machine.finState

theorem cfg_ext {K L S : Type} {Γ : K → Type} {a b : TM2.Cfg Γ L S}
    (hl : a.l = b.l) (hv : a.var = b.var) (hs : a.stk = b.stk) : a = b := by
  cases a
  cases b
  cases hl
  cases hv
  cases hs
  rfl

namespace Machine

def tm (M : Machine) : FinTM2 where
  K := M.K
  k₀ := M.input
  k₁ := M.output
  Γ := M.Γ
  Λ := M.Label
  main := M.main
  σ := M.State
  initialState := M.initial
  m := M.code

abbrev Cfg (M : Machine) := TM2.Cfg M.Γ M.Label M.State
abbrev step (M : Machine) : M.Cfg → Option M.Cfg := TM2.step M.code

def single {K : Type} [DecidableEq K] {Γ : K → Type}
    (k : K) (xs : List (Γ k)) : ∀ j, List (Γ j) := update (fun _ => []) k xs

def initialCfg (M : Machine) (xs : List Bool) : M.Cfg :=
  ⟨some M.main, M.initial, single M.input (xs.map M.inputAlphabet.symm)⟩

def finalCfg (M : Machine) (xs : List Bool) : M.Cfg :=
  ⟨none, M.initial, single M.output (xs.map M.outputAlphabet.symm)⟩

@[simp] theorem init_eq (M : Machine) (xs : List Bool) :
    initList M.tm (xs.map M.inputAlphabet.symm) = M.initialCfg xs := by
  dsimp only [tm]
  apply cfg_ext <;> try rfl
  funext k
  by_cases h : k = M.input
  · subst k; simp [initList, initialCfg, single]
  · change (dite (k = M.input) _ _) = update (fun _ => []) M.input _ k
    simp [h]

@[simp] theorem halt_eq (M : Machine) (xs : List Bool) :
    haltList M.tm (xs.map M.outputAlphabet.symm) = M.finalCfg xs := by
  dsimp only [tm]
  apply cfg_ext <;> try rfl
  funext k
  by_cases h : k = M.output
  · subst k; simp [haltList, finalCfg, single]
  · change (dite (k = M.output) _ _) = update (fun _ => []) M.output _ k
    simp [h]

end Machine

structure Embedding {K K' : Type} [DecidableEq K] [DecidableEq K']
    (Γ : K → Type) (L S : Type) (Γ' : K' → Type) (L' S' : Type) where
  key : K → K'
  symbol : ∀ k, Γ k ≃ Γ' (key k)
  read : S' → S
  write : S' → S → S'
  state : S → S'
  read_state : ∀ v, read (state v) = v
  write_state : ∀ v w, write (state v) w = state w
  stack : (∀ k, List (Γ k)) → ∀ k, List (Γ' k)
  stack_key : ∀ s k, stack s (key k) = (s k).map (symbol k)
  stack_update : ∀ s k x,
    stack (update s k x) = update (stack s) (key k) (x.map (symbol k))
  label : L → L'
  halted : Option L'
  stop : TM2.Stmt Γ' L' S'
  stop_spec : ∀ v s, TM2.stepAux stop (state v) (stack s) = ⟨halted, state v, stack s⟩

namespace Embedding
variable {K K' L S L' S' : Type} [DecidableEq K] [DecidableEq K']
  {Γ : K → Type} {Γ' : K' → Type}
variable (E : Embedding Γ L S Γ' L' S')

def stmt : TM2.Stmt Γ L S → TM2.Stmt Γ' L' S'
  | .push k f q => .push (E.key k) (fun v => E.symbol k (f (E.read v))) (stmt q)
  | .peek k f q => .peek (E.key k)
      (fun v x => E.write v (f (E.read v) (x.map (E.symbol k).symm))) (stmt q)
  | .pop k f q => .pop (E.key k)
      (fun v x => E.write v (f (E.read v) (x.map (E.symbol k).symm))) (stmt q)
  | .load f q => .load (fun v => E.write v (f (E.read v))) (stmt q)
  | .branch f q r => .branch (fun v => f (E.read v)) (stmt q) (stmt r)
  | .goto f => .goto (fun v => E.label (f (E.read v)))
  | .halt => E.stop

def cfg (a : TM2.Cfg Γ L S) : TM2.Cfg Γ' L' S' :=
  ⟨a.l.elim E.halted (fun l => some (E.label l)), E.state a.var, E.stack a.stk⟩

theorem head_map_inverse {α β : Type} (e : α ≃ β) (xs : List α) :
    ((xs.map e).head?).map e.symm = xs.head? := by cases xs <;> simp

theorem stepAux_stmt (q : TM2.Stmt Γ L S) (v : S) (s : ∀ k, List (Γ k)) :
    TM2.stepAux (E.stmt q) (E.state v) (E.stack s) = E.cfg (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih =>
      simp only [stmt, TM2.stepAux, E.read_state, E.stack_key, ← List.map_cons,
        ← E.stack_update]
      exact ih _ _
  | peek k f q ih =>
      simp only [stmt, TM2.stepAux, E.read_state, E.stack_key, head_map_inverse, E.write_state]
      exact ih _ _
  | pop k f q ih =>
      simp only [stmt, TM2.stepAux, E.read_state, E.stack_key, head_map_inverse,
        E.write_state, ← List.map_tail, ← E.stack_update]
      exact ih _ _
  | load f q ih =>
      simp only [stmt, TM2.stepAux, E.read_state, E.write_state]
      exact ih _ _
  | branch f q r ihq ihr =>
      cases h : f v <;> simp only [stmt, TM2.stepAux, E.read_state, h, Bool.cond_false,
        Bool.cond_true]
      · exact ihr _ _
      · exact ihq _ _
  | goto f => simp only [stmt, TM2.stepAux, E.read_state, cfg, Option.elim_some]
  | halt => exact E.stop_spec v s

theorem step_cfg (m : L → TM2.Stmt Γ L S) (m' : L' → TM2.Stmt Γ' L' S')
    (hm : ∀ l, m' (E.label l) = E.stmt (m l))
    (a b : TM2.Cfg Γ L S) (h : TM2.step m a = some b) :
    TM2.step m' (E.cfg a) = some (E.cfg b) := by
  rcases a with ⟨l, v, s⟩
  cases l with
  | none => cases h
  | some l =>
      have hb : b = TM2.stepAux (m l) v s := (Option.some.inj h).symm
      subst b
      simp only [cfg, Option.elim_some, TM2.step, hm]
      exact congrArg some (E.stepAux_stmt (m l) v s)

theorem trace (m : L → TM2.Stmt Γ L S) (m' : L' → TM2.Stmt Γ' L' S')
    (hm : ∀ l, m' (E.label l) = E.stmt (m l))
    {n : ℕ} {a b : TM2.Cfg Γ L S} (h : Trace (TM2.step m) n a b) :
    Trace (TM2.step m') n (E.cfg a) (E.cfg b) :=
  h.map E.cfg (E.step_cfg m m' hm)
end Embedding
namespace Compose
variable (M N : Machine)

abbrev Key := M.K ⊕ (Unit ⊕ N.K)
abbrev Label := M.Label ⊕ (Bool ⊕ N.Label)
abbrev State := M.State × N.State × Option Bool

def Alphabet : Key M N → Type
  | .inl k => M.Γ k
  | .inr (.inl _) => Bool
  | .inr (.inr k) => N.Γ k

instance alphabetFinite (k : Key M N) : Fintype (Alphabet M N k) := by
  rcases k with k | (_ | k)
  · exact M.finΓ k
  · exact inferInstanceAs (Fintype Bool)
  · exact N.finΓ k

abbrev phaseLabel (b : Bool) : Label M N := .inr (.inl b)
abbrev auxiliary : Key M N := .inr (.inl ())

def left : Embedding M.Γ M.Label M.State (Alphabet M N) (Label M N) (State M N) where
  key := Sum.inl
  symbol k := Equiv.refl (M.Γ k)
  read := Prod.fst
  write v x := (x, v.2)
  state v := (v, N.initial, none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s k := match k with
    | .inl j => s j
    | .inr _ => []
  stack_key s k := by exact (List.map_id (s k)).symm
  stack_update s k x := by
    funext j
    rcases j with j | j
    · by_cases h : j = k
      · subst j
        simp only [Function.update_self]
        exact (List.map_id x).symm
      · simp [Function.update_of_ne h, Function.update_of_ne (mt Sum.inl.inj h)]
        rfl
    · simp
  label := Sum.inl
  halted := some (phaseLabel M N false)
  stop := .goto (fun _ => phaseLabel M N false)
  stop_spec _ _ := rfl

def right : Embedding N.Γ N.Label N.State (Alphabet M N) (Label M N) (State M N) where
  key k := .inr (.inr k)
  symbol k := Equiv.refl (N.Γ k)
  read v := v.2.1
  write v x := (v.1, x, v.2.2)
  state v := (M.initial, v, none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s k := match k with
    | .inl _ => []
    | .inr (.inl _) => []
    | .inr (.inr j) => s j
  stack_key s k := by exact (List.map_id (s k)).symm
  stack_update s k x := by
    funext j
    rcases j with j | (j | j)
    · simp
    · simp
    · by_cases h : j = k
      · subst j
        simp only [Function.update_self]
        exact (List.map_id x).symm
      · simp [Function.update_of_ne h,
          Function.update_of_ne (mt (fun e => Sum.inr.inj (Sum.inr.inj e)) h)]
        rfl
  label l := .inr (.inr l)
  halted := none
  stop := .halt
  stop_spec _ _ := rfl

def source (b : Bool) : Key M N := if b then auxiliary M N else .inl M.output
def target (b : Bool) : Key M N := if b then .inr (.inr N.input) else auxiliary M N

theorem source_ne_target (b : Bool) : source M N b ≠ target M N b := by
  cases b <;> simp [source, target, auxiliary]

def sourceAlphabet : (b : Bool) → Alphabet M N (source M N b) ≃ Bool
  | false => M.outputAlphabet
  | true => Equiv.refl Bool

def targetAlphabet : (b : Bool) → Alphabet M N (target M N b) ≃ Bool
  | false => Equiv.refl Bool
  | true => N.inputAlphabet

def following (b : Bool) : Label M N :=
  if b then .inr (.inr N.main) else phaseLabel M N true

def clean (v : State M N) : State M N := (v.1, v.2.1, none)

def transfer (b : Bool) : TM2.Stmt (Alphabet M N) (Label M N) (State M N) :=
  .pop (source M N b) (fun v c => (v.1, v.2.1, c.map (sourceAlphabet M N b)))
    (.branch (fun v => v.2.2.isSome)
      (.push (target M N b) (fun v => (targetAlphabet M N b).symm (v.2.2.getD false))
        (.load (clean M N) (.goto (fun _ => phaseLabel M N b))))
      (.load (clean M N) (.goto (fun _ => following M N b))))

def code : Label M N → TM2.Stmt (Alphabet M N) (Label M N) (State M N)
  | .inl l => (left M N).stmt (M.code l)
  | .inr (.inl b) => transfer M N b
  | .inr (.inr l) => (right M N).stmt (N.code l)

abbrev machine : Machine where
  K := Key M N
  Γ := Alphabet M N
  input := .inl M.input
  output := .inr (.inr N.output)
  inputAlphabet := M.inputAlphabet
  outputAlphabet := N.outputAlphabet
  Label := Label M N
  main := .inl M.main
  State := State M N
  initial := (M.initial, N.initial, none)
  code := code M N

theorem code_left (l : M.Label) : (machine M N).code ((left M N).label l) =
    (left M N).stmt (M.code l) := rfl

theorem code_right (l : N.Label) : (machine M N).code ((right M N).label l) =
    (right M N).stmt (N.code l) := rfl

theorem initial_left (s : List Bool) : (left M N).cfg (M.initialCfg s) =
    (machine M N).initialCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · by_cases h : k = M.input
    · subst k; simp [Embedding.cfg, left, Machine.initialCfg, Machine.single, machine]; try rfl
    · simp [Embedding.cfg, left, Machine.initialCfg, Machine.single, machine,
        Function.update_of_ne h, Function.update_of_ne (mt Sum.inl.inj h)]; try rfl
  · simp [Embedding.cfg, left, Machine.initialCfg, Machine.single, machine]

theorem final_right (s : List Bool) : (right M N).cfg (N.finalCfg s) =
    (machine M N).finalCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | (k | k)
  · simp [Embedding.cfg, right, Machine.finalCfg, Machine.single, machine]
  · simp [Embedding.cfg, right, Machine.finalCfg, Machine.single, machine]
  · by_cases h : k = N.output
    · subst k; simp [Embedding.cfg, right, Machine.finalCfg, Machine.single, machine]; try rfl
    · simp [Embedding.cfg, right, Machine.finalCfg, Machine.single, machine,
        Function.update_of_ne h,
        Function.update_of_ne (mt (fun e => Sum.inr.inj (Sum.inr.inj e)) h)]; try rfl

end Compose

def twoStacks {K : Type} [DecidableEq K] {Γ : K → Type}
    (a b : K) (xs : List (Γ a)) (ys : List (Γ b)) : ∀ k, List (Γ k) :=
  update (Machine.single a xs) b ys

theorem twoStacks_source {K : Type} [DecidableEq K] {Γ : K → Type}
    {a b : K} (h : a ≠ b) (xs : List (Γ a)) (ys : List (Γ b)) :
    twoStacks a b xs ys a = xs := by
  simp [twoStacks, Machine.single, Function.update_of_ne h]

theorem twoStacks_target {K : Type} [DecidableEq K] {Γ : K → Type}
    (a b : K) (xs : List (Γ a)) (ys : List (Γ b)) :
    twoStacks a b xs ys b = ys := by simp [twoStacks]

theorem twoStacks_move {K : Type} [DecidableEq K] {Γ : K → Type}
    {a b : K} (h : a ≠ b) (x : Γ a) (y : Γ b) (xs : List (Γ a)) (ys : List (Γ b)) :
    update (update (twoStacks a b (x :: xs) ys) a xs) b (y :: ys) =
      twoStacks a b xs (y :: ys) := by
  funext k
  by_cases ha : k = a
  · subst k; simp [twoStacks, Machine.single, Function.update_of_ne h]
  · by_cases hb : k = b
    · subst k; simp [twoStacks, Machine.single]
    · simp [twoStacks, Machine.single, Function.update_of_ne ha, Function.update_of_ne hb]

theorem twoStacks_pop_empty {K : Type} [DecidableEq K] {Γ : K → Type}
    {a b : K} (h : a ≠ b) (ys : List (Γ b)) :
    update (twoStacks a b [] ys) a [] = twoStacks a b [] ys := by
  funext k
  by_cases ha : k = a
  · subst k; simp [twoStacks, Machine.single, Function.update_of_ne h]
  · simp [Function.update_of_ne ha]

namespace Compose
variable (M N : Machine)

def transferCfg (b : Bool) (xs ys : List Bool) : (machine M N).Cfg :=
  ⟨some (phaseLabel M N b), (M.initial, N.initial, none),
    twoStacks (source M N b) (target M N b)
      (xs.map (sourceAlphabet M N b).symm) (ys.map (targetAlphabet M N b).symm)⟩

def boundaryCfg (b : Bool) (ys : List Bool) : (machine M N).Cfg :=
  ⟨some (following M N b), (M.initial, N.initial, none),
    twoStacks (source M N b) (target M N b) [] (ys.map (targetAlphabet M N b).symm)⟩

theorem transfer_cons (b x : Bool) (xs ys : List Bool) :
    (machine M N).step (transferCfg M N b (x :: xs) ys) =
      some (transferCfg M N b xs (x :: ys)) := by
  change some (TM2.stepAux (transfer M N b) (M.initial, N.initial, none)
    (twoStacks (source M N b) (target M N b)
      ((x :: xs).map (sourceAlphabet M N b).symm)
      (ys.map (targetAlphabet M N b).symm))) = _
  simp only [transfer, TM2.stepAux, List.map_cons]
  rw [twoStacks_source (source_ne_target M N b)]
  simp only [List.head?_cons, List.tail_cons, Option.map_some, Equiv.apply_symm_apply,
    Option.isSome_some, Bool.cond_true, Option.getD_some, clean]
  rw [Function.update_of_ne (Ne.symm (source_ne_target M N b)), twoStacks_target]
  rw [twoStacks_move (source_ne_target M N b)]
  rfl

theorem transfer_run (b : Bool) (xs ys : List Bool) :
    Trace (machine M N).step xs.length (transferCfg M N b xs ys)
      (transferCfg M N b [] (xs.reverse ++ ys)) := by
  induction xs generalizing ys with
  | nil => exact Trace.refl _
  | cons x xs ih =>
      have h := Trace.cons (transfer_cons M N b x xs ys) (ih (x :: ys))
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
        using h

theorem transfer_empty (b : Bool) (ys : List Bool) :
    (machine M N).step (transferCfg M N b [] ys) = some (boundaryCfg M N b ys) := by
  change some (TM2.stepAux (transfer M N b) (M.initial, N.initial, none)
    (twoStacks (source M N b) (target M N b) []
      (ys.map (targetAlphabet M N b).symm))) = _
  simp only [transfer, TM2.stepAux]
  rw [twoStacks_source (source_ne_target M N b)]
  simp only [List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none,
    Bool.cond_false, clean]
  rw [twoStacks_pop_empty (source_ne_target M N b)]
  rfl

theorem left_final (ys : List Bool) :
    (left M N).cfg (M.finalCfg ys) = transferCfg M N false ys [] := by
  apply cfg_ext <;> try rfl
  funext j
  rcases j with j | (j | j)
  · by_cases h : j = M.output
    · subst j
      simp [Embedding.cfg, left, Machine.finalCfg, Machine.single, transferCfg,
        twoStacks, source, target, sourceAlphabet, targetAlphabet, auxiliary]; try rfl
    · simp [Embedding.cfg, left, Machine.finalCfg, Machine.single, transferCfg,
        twoStacks, source, target, sourceAlphabet, targetAlphabet, auxiliary,
        Function.update_of_ne h, Function.update_of_ne (mt Sum.inl.inj h)]; rfl
  · simp [Embedding.cfg, left, Machine.finalCfg, Machine.single, transferCfg,
      twoStacks, source, target, sourceAlphabet, targetAlphabet, auxiliary]
  · simp [Embedding.cfg, left, Machine.finalCfg, Machine.single, transferCfg,
      twoStacks, source, target, sourceAlphabet, targetAlphabet, auxiliary]

theorem boundary_false (ys : List Bool) :
    boundaryCfg M N false ys = transferCfg M N true ys [] := by
  apply cfg_ext <;> try rfl
  funext j
  rcases j with j | (j | j)
  · by_cases h : j = M.output
    · subst j
      simp [boundaryCfg, transferCfg, twoStacks, Machine.single, source, target,
        sourceAlphabet, targetAlphabet, auxiliary]
    · simp [boundaryCfg, transferCfg, twoStacks, Machine.single, source, target,
        sourceAlphabet, targetAlphabet, auxiliary]
  · cases j
    simp [boundaryCfg, transferCfg, twoStacks, Machine.single, source, target,
      sourceAlphabet, targetAlphabet, auxiliary]; try rfl
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  · by_cases h : j = N.input
    · subst j
      simp [boundaryCfg, transferCfg, twoStacks, Machine.single, source, target,
        sourceAlphabet, targetAlphabet, auxiliary]
    · simp [boundaryCfg, transferCfg, twoStacks, Machine.single, source, target,
        sourceAlphabet, targetAlphabet, auxiliary,
        Function.update_of_ne (mt (fun e => Sum.inr.inj (Sum.inr.inj e)) h)]

theorem boundary_true (ys : List Bool) :
    boundaryCfg M N true ys = (right M N).cfg (N.initialCfg ys) := by
  apply cfg_ext <;> try rfl
  funext j
  rcases j with j | (j | j)
  · simp [boundaryCfg, twoStacks, Machine.single, source, target, targetAlphabet,
      auxiliary, Embedding.cfg, right, Machine.initialCfg]
  · cases j
    simp [boundaryCfg, twoStacks, Machine.single, source, target, targetAlphabet,
      auxiliary, Embedding.cfg, right, Machine.initialCfg]
  · by_cases h : j = N.input
    · subst j
      simp [boundaryCfg, twoStacks, Machine.single, source, target, targetAlphabet,
        auxiliary, Embedding.cfg, right, Machine.initialCfg]; try rfl
    · simp [boundaryCfg, twoStacks, Machine.single, source, target, targetAlphabet,
        auxiliary, Embedding.cfg, right, Machine.initialCfg, Function.update_of_ne h,
        Function.update_of_ne (mt (fun e => Sum.inr.inj (Sum.inr.inj e)) h)]; rfl

theorem transfer_all (ys : List Bool) :
    Trace (machine M N).step (2 * ys.length + 2)
      ((left M N).cfg (M.finalCfg ys)) ((right M N).cfg (N.initialCfg ys)) := by
  have h₀ := transfer_run M N false ys []
  have h₁ := Trace.cons (transfer_empty M N false ys.reverse) (Trace.refl _)
  have h₂ := transfer_run M N true ys.reverse []
  have h₃ := Trace.cons (transfer_empty M N true ys) (Trace.refl _)
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at h₀ h₂
  rw [boundary_false] at h₁
  rw [boundary_true] at h₃
  have hh := ((h₀.trans h₁).trans h₂).trans h₃
  rw [left_final]
  convert hh using 1; omega

theorem run {t u : ℕ} {xs ys zs : List Bool}
    (hM : Trace M.step t (M.initialCfg xs) (M.finalCfg ys))
    (hN : Trace N.step u (N.initialCfg ys) (N.finalCfg zs)) :
    Trace (machine M N).step (t + 2 * ys.length + 2 + u)
      ((machine M N).initialCfg xs) ((machine M N).finalCfg zs) := by
  have hL := (left M N).trace M.code (machine M N).code (code_left M N) hM
  have hR := (right M N).trace N.code (machine M N).code (code_right M N) hN
  have h := (hL.trans (transfer_all M N ys)).trans hR
  rw [initial_left, final_right] at h
  convert h using 1

end Compose

namespace Machine
variable {K L S : Type} {Γ : K → Type} [DecidableEq K]

def pushes : TM2.Stmt Γ L S → ℕ
  | .push _ _ q => 1+pushes q
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ => 0
  | .halt => 0

def volume [Fintype K] (s : ∀ k, List (Γ k)) : ℕ := ∑ k, (s k).length

variable [Fintype K]

theorem volume_update (s : ∀ k, List (Γ k)) (k : K) (v : List (Γ k)) :
    volume (update s k v)+(s k).length=volume s+v.length := by
  classical
  unfold volume
  have he : (fun j => (update s k v j).length)=update (fun j => (s j).length) k v.length := by
    funext j
    by_cases h : j = k
    · subst j; simp
    · simp [Function.update_of_ne h]
  rw [he,Finset.sum_update_of_mem (mem_univ k)]
  have hh := Finset.sum_erase_add (univ : Finset K) (fun j => (s j).length) (mem_univ k)
  simp only [Finset.sdiff_singleton_eq_erase]
  omega

theorem stepAux_volume (q : TM2.Stmt Γ L S)
    (v : S) (s : ∀ k, List (Γ k)) :
    volume (TM2.stepAux q v s).stk ≤ volume s+pushes q := by
  induction q generalizing v s with
  | push k g q ih =>
      have h := ih v (update s k (g v::s k))
      have hv := volume_update s k (g v::s k)
      simp only [List.length_cons] at hv
      simpa only [TM2.stepAux,pushes,Nat.add_assoc] using (by omega :
        volume (TM2.stepAux q v (update s k (g v::s k))).stk≤volume s+(1+pushes q))
  | peek k g q ih => exact ih _ _
  | pop k g q ih =>
      have h := ih (g v (s k).head?) (update s k (s k).tail)
      have hv := volume_update s k (s k).tail
      have hl := List.length_tail (l := s k)
      simp only [TM2.stepAux,pushes]
      omega
  | load g q ih => exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simpa only [TM2.stepAux,hg,Bool.false_eq_true,Bool.cond_false,pushes] using
          (ihr v s).trans (Nat.add_le_add_left (le_max_right (pushes q) _) _)
      · simpa only [TM2.stepAux,hg,Bool.cond_true,pushes] using
          (ihq v s).trans (Nat.add_le_add_left (le_max_left _ (pushes r)) _)
  | goto g => simp only [TM2.stepAux,pushes,Nat.add_zero,le_refl]
  | halt => simp only [TM2.stepAux,pushes,Nat.add_zero,le_refl]

def growth (M : Machine) : ℕ := ∑ l, pushes (M.code l)

theorem step_volume (M : Machine) (a b : M.Cfg) (h : M.step a=some b) :
    volume b.stk ≤ volume a.stk+M.growth := by
  rcases a with ⟨l,v,s⟩
  cases l with
  | none => cases h
  | some l =>
      have hb : b=TM2.stepAux (M.code l) v s := (Option.some.inj h).symm
      rw [hb]
      exact (stepAux_volume _ _ _).trans (Nat.add_le_add_left
        (show pushes (M.code l) ≤ M.growth from
          single_le_sum (f:=fun x => pushes (M.code x)) (fun _ _ => Nat.zero_le _) (mem_univ l)) _)

theorem trace_volume (M : Machine) {n : ℕ} {a b : M.Cfg}
    (h : Trace M.step n a b) : volume b.stk ≤ volume a.stk+n*M.growth := by
  induction h with
  | refl => simp
  | @cons n a b c hab hbc ih =>
      have hs := M.step_volume a b hab
      calc
        _ ≤ volume b.stk+n*M.growth := ih
        _ ≤ volume a.stk+(n+1)*M.growth := by rw [Nat.add_mul]; omega

theorem volume_single (k : K) (xs : List (Γ k)) :
    volume (single k xs) = xs.length := by
  have h := volume_update (fun k : K => ([] : List (Γ k))) k xs
  simpa [volume, single] using h

@[simp] theorem initial_volume (M : Machine) (s : List Bool) :
    volume (M.initialCfg s).stk = s.length := by
  simp only [initialCfg, volume_single, List.length_map]

@[simp] theorem final_volume (M : Machine) (s : List Bool) :
    volume (M.finalCfg s).stk = s.length := by
  simp only [finalCfg, volume_single, List.length_map]

 theorem output_length (M : Machine) {s t : List Bool} {n : ℕ}
    (h : Trace M.step n (M.initialCfg s) (M.finalCfg t)) :
    t.length ≤ s.length+n*M.growth := by
  simpa only [initial_volume, final_volume] using M.trace_volume h

end Machine

structure PolyProgram {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) where
  machine : Machine
  time : Polynomial ℕ
  outputs : ∀ a, ∃ n, n ≤ time.eval (ea a).length ∧
    Trace machine.step n (machine.initialCfg (ea a)) (machine.finalCfg (eb (f a)))

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
variable {f : α → β} {g : β → γ}

noncomputable def stock (P : PolyProgram ea eb f) : TM2ComputableInPolyTime ea eb f where
  tm := P.machine.tm
  inputAlphabet := P.machine.inputAlphabet
  outputAlphabet := P.machine.outputAlphabet
  time := P.time
  outputsFun a := by
    let n := Classical.choose (P.outputs a)
    have hn := (Classical.choose_spec (P.outputs a)).1
    have ht := (Classical.choose_spec (P.outputs a)).2
    refine ⟨⟨n, ?_⟩, hn⟩
    change (flip Bind.bind P.machine.step)^[n]
      (some (initList P.machine.tm ((ea a).map P.machine.inputAlphabet.symm))) =
      some (haltList P.machine.tm ((eb (f a)).map P.machine.outputAlphabet.symm))
    rw [Machine.init_eq, Machine.halt_eq]
    exact ht.iterate_eq

 theorem finite_work (P : PolyProgram ea eb f) (k : P.stock.tm.K) : Finite (P.stock.tm.Γ k) :=
  @Finite.of_fintype (P.machine.Γ k) (P.machine.finΓ k)

noncomputable def stockMachine (p : TM2ComputableInPolyTime ea eb f)
    (h : ∀ k : p.tm.K, Finite (p.tm.Γ k)) : Machine := {
    K := p.tm.K
    finK := p.tm.kFin
    decK := p.tm.kDecidableEq
    Γ := p.tm.Γ
    finΓ := fun k => @Fintype.ofFinite (p.tm.Γ k) (h k)
    input := p.tm.k₀
    output := p.tm.k₁
    inputAlphabet := p.inputAlphabet
    outputAlphabet := p.outputAlphabet
    Label := p.tm.Λ
    finLabel := p.tm.ΛFin
    main := p.tm.main
    State := p.tm.σ
    finState := p.tm.σFin
    initial := p.tm.initialState
    code := p.tm.m }

noncomputable def ofStock (p : TM2ComputableInPolyTime ea eb f)
    (h : ∀ k : p.tm.K, Finite (p.tm.Γ k)) : PolyProgram ea eb f where
  machine := stockMachine p h
  time := p.time
  outputs a := by
    let ht := p.outputsFun a
    refine ⟨ht.steps, ht.steps_le_m, ?_⟩
    rw [← Machine.init_eq, ← Machine.halt_eq]
    exact Trace.of_iterate ht.evals_in_steps

noncomputable def sizeBound (P : PolyProgram ea eb f) : Polynomial ℕ :=
  X + P.time * C P.machine.growth

 theorem length_bound (P : PolyProgram ea eb f) (a : α) :
    (eb (f a)).length ≤ P.sizeBound.eval (ea a).length := by
  obtain ⟨n, hn, ht⟩ := P.outputs a
  have hl := P.machine.output_length ht
  simp only [sizeBound, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C]
  exact hl.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hn) _)

noncomputable def compTime (P : PolyProgram ea eb f) (Q : PolyProgram eb ec g) : Polynomial ℕ :=
  P.time + 2 * P.sizeBound + 2 + Q.time.comp P.sizeBound

noncomputable def comp (P : PolyProgram ea eb f) (Q : PolyProgram eb ec g) :
    PolyProgram ea ec (g ∘ f) where
  machine := Compose.machine P.machine Q.machine
  time := P.compTime Q
  outputs a := by
    obtain ⟨n, hn, ht⟩ := P.outputs a
    obtain ⟨m, hm, hu⟩ := Q.outputs (f a)
    refine ⟨n + (2 * (eb (f a)).length + 2) + m, ?_, Compose.run _ _ ht hu⟩
    have hl := P.length_bound a
    have hq := hm.trans (Binary.polynomial_eval_mono Q.time hl)
    simp only [compTime, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_comp]
    omega

 def congr (P : PolyProgram ea eb f) (f' : α → β) (h : ∀ a, f a = f' a) :
    PolyProgram ea eb f' where
  machine := P.machine
  time := P.time
  outputs a := by rw [← h a]; exact P.outputs a

end PolyProgram

end MetricKMedian.Complexity.FiniteComposition

namespace MetricKMedian.Complexity

theorem FinitePolyTime.comp {α β γ : Type}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    {f : α → β} {g : β → γ}
    (hf : FinitePolyTime ea eb f) (hg : FinitePolyTime eb ec g) :
    FinitePolyTime ea ec (g ∘ f) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  let r := (FiniteComposition.PolyProgram.ofStock p hp).comp
    (FiniteComposition.PolyProgram.ofStock q hq)
  exact ⟨r.stock, r.finite_work⟩

end MetricKMedian.Complexity

end Inline_PCPInherited

end OAI
