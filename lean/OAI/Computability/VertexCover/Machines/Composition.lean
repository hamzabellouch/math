import Mathlib
import OAI.Computability.VertexCover.PCP.ConstraintGraph
import OAI.Computability.VertexCover.Encoding.Runtime
import OAI.Computability.VertexCover.Encoding.MachineComposition
import OAI.Computability.VertexCover.Reduction.GridBudget

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                            
section

namespace VertexCover.Machine
open Turing
open Turing.TM2
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace Compose

variable (A B : FinTM2)

abbrev K := A.K ⊕ (B.K ⊕ Unit)
abbrev Γ : K A B → Type
  | .inl k => A.Γ k
  | .inr (.inl k) => B.Γ k
  | .inr (.inr _) => Bool
abbrev Λ := A.Λ ⊕ (B.Λ ⊕ Bool)
abbrev State := A.σ × B.σ × Option Bool

instance : Fintype (State A B) := inferInstanceAs (Fintype (A.σ × B.σ × Option Bool))

abbrev Cfg := Turing.TM2.Cfg (Γ A B) (Λ A B) (State A B)
abbrev Stmt := Turing.TM2.Stmt (Γ A B) (Λ A B) (State A B)

abbrev first (k : A.K) : K A B := .inl k
abbrev second (k : B.K) : K A B := .inr (.inl k)
abbrev temporary : K A B := .inr (.inr ())
abbrev transfer (b : Bool) : Λ A B := .inr (.inr b)

def firstStatement : A.Stmt → Stmt A B
  | .push k f p => .push (first A B k) (fun s => f s.1) (firstStatement p)
  | .peek k f p => .peek (first A B k) (fun s x => (f s.1 x, s.2)) (firstStatement p)
  | .pop k f p => .pop (first A B k) (fun s x => (f s.1 x, s.2)) (firstStatement p)
  | .load f p => .load (fun s => (f s.1, s.2)) (firstStatement p)
  | .branch f p q => .branch (fun s => f s.1) (firstStatement p) (firstStatement q)
  | .goto f => .goto (fun s => .inl (f s.1))
  | .halt => .goto (fun _ => transfer A B false)

def secondStatement : B.Stmt → Stmt A B
  | .push k f p => .push (second A B k) (fun s => f s.2.1) (secondStatement p)
  | .peek k f p => .peek (second A B k)
      (fun s x => (s.1, f s.2.1 x, s.2.2)) (secondStatement p)
  | .pop k f p => .pop (second A B k)
      (fun s x => (s.1, f s.2.1 x, s.2.2)) (secondStatement p)
  | .load f p => .load (fun s => (s.1, f s.2.1, s.2.2)) (secondStatement p)
  | .branch f p q => .branch (fun s => f s.2.1) (secondStatement p) (secondStatement q)
  | .goto f => .goto (fun s => .inr (.inl (f s.2.1)))
  | .halt => .halt

variable (outA : A.Γ A.k₁ ≃ Bool) (inB : B.Γ B.k₀ ≃ Bool)

def program : Λ A B → Stmt A B
  | .inl l => firstStatement A B (A.m l)
  | .inr (.inl l) => secondStatement A B (B.m l)
  | .inr (.inr false) =>
      .pop (first A B A.k₁) (fun s x => (s.1, s.2.1, x.map outA))
        (.branch (fun s => s.2.2.isSome)
          (.push (temporary A B) (fun s => s.2.2.getD false)
            (.goto (fun _ => transfer A B false)))
          (.goto (fun _ => transfer A B true)))
  | .inr (.inr true) =>
      .pop (temporary A B) (fun s x => (s.1, s.2.1, x))
        (.branch (fun s => s.2.2.isSome)
          (.push (second A B B.k₀) (fun s => inB.symm (s.2.2.getD false))
            (.goto (fun _ => transfer A B true)))
          (.goto (fun _ => .inr (.inl B.main))))

abbrev machine : FinTM2 where
  K := K A B
  k₀ := first A B A.k₀
  k₁ := second A B B.k₁
  Γ := Γ A B
  Λ := Λ A B
  main := .inl A.main
  σ := State A B
  initialState := (A.initialState, B.initialState, none)
  m := program A B outA inB
  Γk₀Fin := A.Γk₀Fin

def tapes (ta : ∀ k, List (A.Γ k)) (tb : ∀ k, List (B.Γ k)) (temp : List Bool) :
    ∀ k, List (Γ A B k)
  | .inl k => ta k
  | .inr (.inl k) => tb k
  | .inr (.inr _) => temp

@[simp] theorem tapes_first (ta : ∀ k, List (A.Γ k)) (tb : ∀ k, List (B.Γ k))
    (t : List Bool) (k : A.K) : tapes A B ta tb t (first A B k) = ta k := rfl
@[simp] theorem tapes_second (ta : ∀ k, List (A.Γ k)) (tb : ∀ k, List (B.Γ k))
    (t : List Bool) (k : B.K) : tapes A B ta tb t (second A B k) = tb k := rfl
@[simp] theorem tapes_temporary (ta : ∀ k, List (A.Γ k)) (tb : ∀ k, List (B.Γ k))
    (t : List Bool) : tapes A B ta tb t (temporary A B) = t := rfl

theorem tapes_update_first (ta : ∀ k, List (A.Γ k)) (tb : ∀ k, List (B.Γ k))
    (t : List Bool) (k : A.K) (v : List (A.Γ k)) :
    tapes A B (Function.update ta k v) tb t =
      Function.update (tapes A B ta tb t) (first A B k) v := by
  funext j
  rcases j with j | (j | j)
  · by_cases h : j = k
    · subst j; simp [tapes, first]
    · simp [tapes, first, Function.update, h]
  · simp [tapes, first, Function.update]
  · simp [tapes, first, Function.update]

theorem tapes_update_second (ta : ∀ k, List (A.Γ k)) (tb : ∀ k, List (B.Γ k))
    (t : List Bool) (k : B.K) (v : List (B.Γ k)) :
    tapes A B ta (Function.update tb k v) t =
      Function.update (tapes A B ta tb t) (second A B k) v := by
  funext j
  rcases j with j | (j | j)
  · simp [tapes, second, Function.update]
  · by_cases h : j = k
    · subst j; simp [tapes, second]
    · simp [tapes, second, Function.update, h]
  · simp [tapes, second, Function.update]

theorem tapes_update_temporary (ta : ∀ k, List (A.Γ k)) (tb : ∀ k, List (B.Γ k))
    (t v : List Bool) :
    tapes A B ta tb v = Function.update (tapes A B ta tb t) (temporary A B) v := by
  funext j
  rcases j with j | (j | j)
  · simp [tapes, temporary, Function.update]
  · simp [tapes, temporary, Function.update]
  · cases j; simp [tapes, temporary]

def firstCfg (state : B.σ) (flag : Option Bool)
    (tb : ∀ k, List (B.Γ k)) (temp : List Bool) (c : A.Cfg) : Cfg A B where
  l := some (c.l.elim (transfer A B false) Sum.inl)
  var := (c.var, state, flag)
  stk := tapes A B c.stk tb temp

def secondCfg (state : A.σ) (flag : Option Bool)
    (ta : ∀ k, List (A.Γ k)) (temp : List Bool) (c : B.Cfg) : Cfg A B where
  l := c.l.map (fun l => .inr (.inl l))
  var := (state, c.var, flag)
  stk := tapes A B ta c.stk temp

theorem first_stepAux (b : B.σ) (flag : Option Bool)
    (tb : ∀ k, List (B.Γ k)) (temp : List Bool)
    (q : A.Stmt) (s : A.σ) (ta : ∀ k, List (A.Γ k)) :
    stepAux (firstStatement A B q) (s, b, flag) (tapes A B ta tb temp) =
      firstCfg A B b flag tb temp (stepAux q s ta) := by
  induction q generalizing s ta with
  | push k f p ih =>
    simp only [firstStatement, stepAux, tapes_first]
    rw [← tapes_update_first]
    exact ih s _
  | peek k f p ih =>
    simpa only [firstStatement, stepAux, tapes_first] using ih (f s (ta k).head?) ta
  | pop k f p ih =>
    simp only [firstStatement, stepAux, tapes_first]
    rw [← tapes_update_first]
    exact ih (f s (ta k).head?) _
  | load f p ih => simpa only [firstStatement, stepAux] using ih (f s) ta
  | branch f p q ihp ihq =>
    cases h : f s with
    | false => simpa only [firstStatement, stepAux, h, Bool.cond_false] using ihq s ta
    | true => simpa only [firstStatement, stepAux, h, Bool.cond_true] using ihp s ta
  | goto f => rfl
  | halt => rfl

theorem second_stepAux (a : A.σ) (flag : Option Bool)
    (ta : ∀ k, List (A.Γ k)) (temp : List Bool)
    (q : B.Stmt) (s : B.σ) (tb : ∀ k, List (B.Γ k)) :
    stepAux (secondStatement A B q) (a, s, flag) (tapes A B ta tb temp) =
      secondCfg A B a flag ta temp (stepAux q s tb) := by
  induction q generalizing s tb with
  | push k f p ih =>
    simp only [secondStatement, stepAux, tapes_second]
    rw [← tapes_update_second]
    exact ih s _
  | peek k f p ih =>
    simpa only [secondStatement, stepAux, tapes_second] using ih (f s (tb k).head?) tb
  | pop k f p ih =>
    simp only [secondStatement, stepAux, tapes_second]
    rw [← tapes_update_second]
    exact ih (f s (tb k).head?) _
  | load f p ih => simpa only [secondStatement, stepAux] using ih (f s) tb
  | branch f p q ihp ihq =>
    cases h : f s with
    | false => simpa only [secondStatement, stepAux, h, Bool.cond_false] using ihq s tb
    | true => simpa only [secondStatement, stepAux, h, Bool.cond_true] using ihp s tb
  | goto f => rfl
  | halt => rfl

theorem first_step (b : B.σ) (flag : Option Bool)
    (tb : ∀ k, List (B.Γ k)) (temp : List Bool) (c c' : A.Cfg)
    (h : A.step c = some c') :
    (machine A B outA inB).step (firstCfg A B b flag tb temp c) =
      some (firstCfg A B b flag tb temp c') := by
  rcases c with ⟨l,s,ta⟩
  cases l with
  | none => simp [FinTM2.step, step] at h
  | some l =>
    have hc : stepAux (A.m l) s ta = c' := Option.some.inj h
    rw [← hc]
    change some (stepAux (firstStatement A B (A.m l)) (s,b,flag) (tapes A B ta tb temp)) = _
    exact congrArg some (first_stepAux A B b flag tb temp (A.m l) s ta)

theorem second_step (a : A.σ) (flag : Option Bool)
    (ta : ∀ k, List (A.Γ k)) (temp : List Bool) (c c' : B.Cfg)
    (h : B.step c = some c') :
    (machine A B outA inB).step (secondCfg A B a flag ta temp c) =
      some (secondCfg A B a flag ta temp c') := by
  rcases c with ⟨l,s,tb⟩
  cases l with
  | none => simp [FinTM2.step, step] at h
  | some l =>
    have hc : stepAux (B.m l) s tb = c' := Option.some.inj h
    rw [← hc]
    change some (stepAux (secondStatement A B (B.m l)) (a,s,flag) (tapes A B ta tb temp)) = _
    exact congrArg some (second_stepAux A B a flag ta temp (B.m l) s tb)

def tapeOnly {K : Type} {Γ : K → Type} [DecidableEq K] (k : K) (s : List (Γ k)) :
    ∀ j, List (Γ j) := Function.update (fun _ => []) k s

@[simp] theorem tapeOnly_self {K : Type} {Γ : K → Type} [DecidableEq K]
    (k : K) (s : List (Γ k)) : tapeOnly k s k = s := Function.update_self _ _ _

@[simp] theorem tapeOnly_nil {K : Type} {Γ : K → Type} [DecidableEq K]
    (k : K) : tapeOnly (Γ := Γ) k [] = fun _ => [] := Function.update_eq_self _ _

@[simp] theorem tapeOnly_update {K : Type} {Γ : K → Type} [DecidableEq K]
    (k : K) (s t : List (Γ k)) : Function.update (tapeOnly k s) k t = tapeOnly k t :=
  Function.update_idem _ _ _

def bridgeOne (s : List (A.Γ A.k₁)) (temp : List Bool) (flag : Option Bool) : Cfg A B where
  l := some (transfer A B false)
  var := (A.initialState, B.initialState, flag)
  stk := tapes A B (tapeOnly A.k₁ s) (fun _ => []) temp

def bridgeTwo (temp : List Bool) (s : List (B.Γ B.k₀)) (flag : Option Bool) : Cfg A B where
  l := some (transfer A B true)
  var := (A.initialState, B.initialState, flag)
  stk := tapes A B (fun _ => []) (tapeOnly B.k₀ s) temp

theorem bridgeOne_cons (x : A.Γ A.k₁) (xs : List (A.Γ A.k₁)) (temp : List Bool)
    (flag : Option Bool) :
    (machine A B outA inB).step (bridgeOne A B (x::xs) temp flag) =
      some (bridgeOne A B xs (outA x::temp) (some (outA x))) := by
  change step (program A B outA inB) _ = _
  simp only [bridgeOne, step, program, stepAux, tapes_first,
    tapeOnly_self, List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some,
    Bool.cond_true, Option.getD_some]
  rw [← tapes_update_first, tapeOnly_update]
  simp only [tapes_temporary]
  rw [← tapes_update_temporary]

theorem bridgeOne_nil (temp : List Bool) (flag : Option Bool) :
    (machine A B outA inB).step (bridgeOne A B [] temp flag) =
      some (bridgeTwo A B temp [] none) := by
  change step (program A B outA inB) _ = _
  simp only [bridgeOne, step, program, stepAux, tapes_first,
    tapeOnly_self, List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none,
    Bool.cond_false]
  rw [← tapes_update_first, tapeOnly_update]
  simp only [tapeOnly_nil, bridgeTwo]

theorem bridgeTwo_cons (x : Bool) (xs : List Bool) (s : List (B.Γ B.k₀))
    (flag : Option Bool) :
    (machine A B outA inB).step (bridgeTwo A B (x::xs) s flag) =
      some (bridgeTwo A B xs (inB.symm x::s) (some x)) := by
  change step (program A B outA inB) _ = _
  simp only [bridgeTwo, step, program, stepAux, tapes_temporary,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [← tapes_update_temporary]
  simp only [tapes_second, tapeOnly_self]
  rw [← tapes_update_second, tapeOnly_update]

theorem init_tapes (M : FinTM2) (s : List (M.Γ M.k₀)) :
    (initList M s).stk = tapeOnly M.k₀ s := by
  funext k
  by_cases h : k = M.k₀
  · subst k; simp [initList, tapeOnly]
  · simp [initList, tapeOnly, Function.update, h]

theorem halt_tapes (M : FinTM2) (s : List (M.Γ M.k₁)) :
    (haltList M s).stk = tapeOnly M.k₁ s := by
  funext k
  by_cases h : k = M.k₁
  · subst k; simp [haltList, tapeOnly]
  · simp [haltList, tapeOnly, Function.update, h]

theorem bridgeTwo_nil (s : List (B.Γ B.k₀)) (flag : Option Bool) :
    (machine A B outA inB).step (bridgeTwo A B [] s flag) =
      some (secondCfg A B A.initialState none (fun _ => []) [] (Turing.initList B s)) := by
  change step (program A B outA inB) _ = _
  simp only [bridgeTwo, step, program, stepAux, tapes_temporary,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [← tapes_update_temporary]
  simp only [secondCfg, init_tapes]
  rfl

private def oneStep {S : Type} (step : S → Option S) (a b : S) (h : step a = some b) :
    StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := h
  steps_le_m := le_rfl

def bridgeOne_run (s : List (A.Γ A.k₁)) (temp : List Bool) (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A B) (machine A B outA inB).step
      (bridgeOne A B s temp flag)
      (some (bridgeTwo A B ((s.map outA).reverse ++ temp) [] none)) (s.length + 1) := by
  induction s generalizing temp flag with
  | nil =>
    exact oneStep _ _ _ (bridgeOne_nil A B outA inB temp flag)
  | cons x xs ih =>
    have e₁ := oneStep _ _ _ (bridgeOne_cons A B outA inB x xs temp flag)
    have e₂ := ih (outA x :: temp) (some (outA x))
    have both := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.length_cons] using both

def bridgeTwo_run (temp : List Bool) (s : List (B.Γ B.k₀)) (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A B) (machine A B outA inB).step
      (bridgeTwo A B temp s flag)
      (some (secondCfg A B A.initialState none (fun _ => []) []
        (Turing.initList B ((temp.map inB.symm).reverse ++ s)))) (temp.length + 1) := by
  induction temp generalizing s flag with
  | nil => exact oneStep _ _ _ (bridgeTwo_nil A B outA inB s flag)
  | cons x xs ih =>
    have e₁ := oneStep _ _ _ (bridgeTwo_cons A B outA inB x xs s flag)
    have e₂ := ih (inB.symm x :: s) (some x)
    have both := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.length_cons] using both

theorem cfg_ext {c c' : Cfg A B} (hl : c.l = c'.l)
    (hs : c.var = c'.var) (ht : c.stk = c'.stk) : c = c' := by
  rcases c with ⟨l,s,t⟩
  rcases c' with ⟨l',s',t'⟩
  cases hl; cases hs; cases ht
  rfl

theorem first_initial (s : List (A.Γ A.k₀)) :
    firstCfg A B B.initialState none (fun _ => []) [] (Turing.initList A s) =
      Turing.initList (machine A B outA inB) s := by
  apply cfg_ext A B
  · rfl
  · rfl
  · rw [init_tapes]
    change tapes A B (initList A s).stk (fun _ => []) [] = _
    rw [init_tapes]
    funext k
    rcases k with k | (k | k)
    · by_cases h : k = A.k₀
      · subst k; simp [machine, tapes, tapeOnly, first]
      · simp [machine, tapes, tapeOnly, first, Function.update, h]
    · simp [machine, tapes, tapeOnly, first, Function.update]
    · simp [machine, tapes, tapeOnly, first, Function.update]

theorem first_halted (s : List (A.Γ A.k₁)) :
    firstCfg A B B.initialState none (fun _ => []) [] (Turing.haltList A s) =
      bridgeOne A B s [] none := by
  simp only [firstCfg, halt_tapes, bridgeOne]
  rfl

theorem second_halted (s : List (B.Γ B.k₁)) :
    secondCfg A B A.initialState none (fun _ => []) [] (Turing.haltList B s) =
      Turing.haltList (machine A B outA inB) s := by
  apply cfg_ext A B
  · rfl
  · rfl
  · rw [halt_tapes]
    change tapes A B (fun _ => []) (haltList B s).stk [] = _
    rw [halt_tapes]
    funext k
    rcases k with k | (k | k)
    · simp [machine, tapes, tapeOnly, second, Function.update]
    · by_cases h : k = B.k₁
      · subst k; simp [machine, tapes, tapeOnly, second]
      · simp [machine, tapes, tapeOnly, second, Function.update, h]
    · simp [machine, tapes, tapeOnly, second, Function.update]

open UniqueGames.Foundations.Complexity.MachineComposition

def outputs (input : List (A.Γ A.k₀)) (middle : List Bool) (output : List (B.Γ B.k₁))
    (n₁ n₂ : ℕ)
    (h₁ : Turing.TM2OutputsInTime A input (some (middle.map outA.symm)) n₁)
    (h₂ : Turing.TM2OutputsInTime B (middle.map inB.symm) (some output) n₂) :
    Turing.TM2OutputsInTime (machine A B outA inB) input (some output)
      (n₁ + 2 * (middle.length + 1) + n₂) := by
  have e₁ := liftExecutionInTime A.step (machine A B outA inB).step
    (firstCfg A B B.initialState none (fun _ => []) [])
    (first_step A B outA inB B.initialState none (fun _ => []) []) h₁
  rw [first_initial, first_halted] at e₁
  have e₂ : @StateTransition.EvalsToInTime (Cfg A B) (machine A B outA inB).step
      (bridgeOne A B (middle.map outA.symm) [] none)
      (some (bridgeTwo A B middle.reverse [] none)) (middle.length+1) := by
    simpa only [List.map_map, Equiv.apply_symm_apply, Function.comp_def,
      List.map_id_fun, List.map_id, List.map_id', List.append_nil, List.length_map] using
      bridgeOne_run A B outA inB (middle.map outA.symm) [] none
  have e₃ : @StateTransition.EvalsToInTime (Cfg A B) (machine A B outA inB).step
      (bridgeTwo A B middle.reverse [] none)
      (some (secondCfg A B A.initialState none (fun _ => []) []
        (initList B (middle.map inB.symm)))) (middle.length+1) := by
    simpa only [List.map_reverse, List.reverse_reverse, List.append_nil, List.length_reverse] using
      bridgeTwo_run A B outA inB middle.reverse [] none
  have e₄ := liftExecutionInTime B.step (machine A B outA inB).step
    (secondCfg A B A.initialState none (fun _ => []) [])
    (second_step A B outA inB A.initialState none (fun _ => []) []) h₂
  rw [second_halted] at e₄
  have e₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂
  have e₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁₂ e₃
  have all := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁₂₃ e₄
  exact { all with steps_le_m := by have hh := all.steps_le_m; omega }

theorem finiteAlphabet (hA : ∀ k, Finite (A.Γ k)) (hB : ∀ k, Finite (B.Γ k)) :
    ∀ k, Finite ((machine A B outA inB).Γ k) := by
  rintro (k | (k | k))
  · exact hA k
  · exact hB k
  · exact inferInstanceAs (Finite Bool)

end Compose

open UniqueGames.Foundations.Complexity

noncomputable def compose {α β γ : Type}
    {eα : α → List Bool} {eβ : β → List Bool} {eγ : γ → List Bool}
    {f : α → β} {g : β → γ}
    (c₁ : Turing.TM2ComputableInPolyTime eα eβ f)
    (c₂ : Turing.TM2ComputableInPolyTime eβ eγ g) :
    Turing.TM2ComputableInPolyTime eα eγ (g ∘ f) where
  tm := Compose.machine c₁.tm c₂.tm c₁.outputAlphabet c₂.inputAlphabet
  inputAlphabet := c₁.inputAlphabet
  outputAlphabet := c₂.outputAlphabet
  time := MachineComposition.compositionPolynomial c₁.time c₂.time
    (Polynomial.X + Polynomial.C (Runtime.programPushBound c₁.tm)*c₁.time)
  outputsFun a := by
    have run := Compose.outputs c₁.tm c₂.tm c₁.outputAlphabet c₂.inputAlphabet
      ((eα a).map c₁.inputAlphabet.symm) (eβ (f a)) ((eγ (g (f a))).map c₂.outputAlphabet.symm)
      (c₁.time.eval (eα a).length) (c₂.time.eval (eβ (f a)).length)
      (c₁.outputsFun a) (c₂.outputsFun (f a))
    refine { run with steps_le_m := ?_ }
    exact run.steps_le_m.trans
      (MachineComposition.compositionBudget_le _ _ _ _ _ (Runtime.encodedOutputLength c₁ a))

theorem compose_finite {α β γ : Type}
    {eα : α → List Bool} {eβ : β → List Bool} {eγ : γ → List Bool}
    {f : α → β} {g : β → γ}
    (c₁ : Turing.TM2ComputableInPolyTime eα eβ f)
    (c₂ : Turing.TM2ComputableInPolyTime eβ eγ g)
    (h₁ : ∀ k, Finite (c₁.tm.Γ k)) (h₂ : ∀ k, Finite (c₂.tm.Γ k)) :
    ∀ k, Finite ((compose c₁ c₂).tm.Γ k) :=
  Compose.finiteAlphabet c₁.tm c₂.tm c₁.outputAlphabet c₂.inputAlphabet h₁ h₂

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
