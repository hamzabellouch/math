import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ExecutionState

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition

structure Program where
  K : Type
  [kDecidableEq : DecidableEq K]
  [kFinite : Fintype K]
  input : K
  output : K
  Label : Type
  [labelFinite : Fintype Label]
  main : Label
  State : Type
  [stateFinite : Fintype State]
  initial : State
  code : Label → TM2.Stmt (fun _ : K => Bool) Label State

attribute [instance] Program.kDecidableEq Program.kFinite Program.labelFinite Program.stateFinite

abbrev Program.machine (p : Program) : FinTM2 where
  K := p.K
  k₀ := p.input
  k₁ := p.output
  Γ _ := Bool
  Λ := p.Label
  main := p.main
  σ := p.State
  initialState := p.initial
  m := p.code

abbrev Stacks (K : Type) := K → List Bool

noncomputable def embedStacks {K L : Type} (e : K ↪ L) (s : Stacks K) : Stacks L := by
  classical
  exact fun l => if h : ∃ k, e k = l then s h.choose else []

lemma embedStacks_apply {K L : Type} (e : K ↪ L) (s : Stacks K) (k : K) :
    embedStacks e s (e k) = s k := by
  classical
  simp only [embedStacks,dite_eq_left (show ∃ j, e j = e k from ⟨k,rfl⟩)]
  congr 1
  exact e.injective (Classical.choose_spec (show ∃ j, e j = e k from ⟨k,rfl⟩))

lemma embedStacks_not_image {K L : Type} (e : K ↪ L) (s : Stacks K) (l : L)
    (h : ¬∃ k, e k = l) : embedStacks e s l = [] := by
  classical
  simp only [embedStacks,dite_eq_right h]

lemma embedStacks_update {K L : Type} [DecidableEq K] [DecidableEq L]
    (e : K ↪ L) (s : Stacks K) (k : K) (v : List Bool) :
    embedStacks e (Function.update s k v) = Function.update (embedStacks e s) (e k) v := by
  classical
  funext l
  by_cases h : ∃ j, e j = l
  · obtain ⟨j,rfl⟩ := h
    simp only [embedStacks_apply,Function.update_apply,e.injective.eq_iff]
  · rw [embedStacks_not_image e _ l h,Function.update_of_ne (by intro he; exact h ⟨k,he.symm⟩),
      embedStacks_not_image e s l h]

section Rename
variable {K L A B S T : Type} [DecidableEq K] [DecidableEq L]

def renameStmt (ek : K ↪ L) (el : A → B) (es : S → T) (rs : T → S)
    (ret : Option B) : TM2.Stmt (fun _ : K => Bool) A S → TM2.Stmt (fun _ : L => Bool) B T
  | .push k f q => .push (ek k) (fun t => f (rs t)) (renameStmt ek el es rs ret q)
  | .peek k f q => .peek (ek k) (fun t b => es (f (rs t) b)) (renameStmt ek el es rs ret q)
  | .pop k f q => .pop (ek k) (fun t b => es (f (rs t) b)) (renameStmt ek el es rs ret q)
  | .load f q => .load (fun t => es (f (rs t))) (renameStmt ek el es rs ret q)
  | .branch f q r => .branch (fun t => f (rs t))
      (renameStmt ek el es rs ret q) (renameStmt ek el es rs ret r)
  | .goto f => .goto (fun t => el (f (rs t)))
  | .halt => match ret with | none => .halt | some b => .goto (fun _ => b)

noncomputable def renameCfg (ek : K ↪ L) (el : A → B) (es : S → T)
    (ret : Option B) (c : TM2.Cfg (fun _ : K => Bool) A S) : TM2.Cfg (fun _ : L => Bool) B T :=
  ⟨c.l.elim ret (fun a => some (el a)), es c.var, embedStacks ek c.stk⟩

lemma stepAux_rename (ek : K ↪ L) (el : A → B) (es : S → T) (rs : T → S)
    (h : ∀ s, rs (es s) = s) (ret : Option B)
    (q : TM2.Stmt (fun _ : K => Bool) A S) (s : S) (stk : Stacks K) :
    TM2.stepAux (renameStmt ek el es rs ret q) (es s) (embedStacks ek stk) =
      renameCfg ek el es ret (TM2.stepAux q s stk) := by
  induction q generalizing s stk with
  | push k f q ih =>
    simp only [renameStmt,TM2.stepAux,h,embedStacks_apply,←embedStacks_update]
    exact ih _ _
  | peek k f q ih =>
    simp only [renameStmt,TM2.stepAux,h,embedStacks_apply]
    exact ih _ _
  | pop k f q ih =>
    simp only [renameStmt,TM2.stepAux,h,embedStacks_apply,←embedStacks_update]
    exact ih _ _
  | load f q ih =>
    simp only [renameStmt,TM2.stepAux,h]
    exact ih _ _
  | branch f q r ihq ihr =>
    simp only [renameStmt,TM2.stepAux,h]
    cases f s <;> simp only [Bool.cond_false,Bool.cond_true]
    · exact ihr _ _
    · exact ihq _ _
  | goto f => simp only [renameStmt,TM2.stepAux,h,renameCfg,Option.elim_some]
  | halt => cases ret <;> rfl

end Rename

lemma iterate_transfer {S T : Type} (f : S → Option S) (g : T → Option T) (e : S → T)
    (h : ∀ s s', f s = some s' → g (e s) = some (e s')) (n : ℕ) (s s' : S)
    (he : (fun x : Option S => x.bind f)^[n] (some s) = some s') :
    (fun x : Option T => x.bind g)^[n] (some (e s)) = some (e s') := by
  induction n generalizing s with
  | zero => simpa only [Function.iterate_zero_apply,Option.some.injEq] using congrArg e (Option.some.inj he)
  | succ n ih =>
    rw [Function.iterate_succ_apply] at he ⊢
    change (fun x : Option S => x.bind f)^[n] (f s) = some s' at he
    change (fun x : Option T => x.bind g)^[n] (g (e s)) = some (e s')
    cases hf : f s with
    | none =>
      rw [hf] at he
      have hn : (fun x : Option S => x.bind f)^[n] none = none :=
        Function.iterate_fixed rfl n
      rw [hn] at he
      contradiction
    | some t =>
      rw [h s t hf]
      exact ih t (by simpa only [hf] using he)

end MetricKMedianRecovery.BitMachine

end OAI
