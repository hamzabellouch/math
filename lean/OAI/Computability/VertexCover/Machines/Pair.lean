import Mathlib
import OAI.Computability.VertexCover.Analysis.Restriction
import OAI.Computability.VertexCover.Machines.Composition

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
open Turing Turing.TM2
open UniqueGames.Foundations.Complexity.MachineComposition (liftExecutionInTime)
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

def frame : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: frame bs

def pairBits (a b : List Bool) : List Bool := frame a ++ b

theorem frame_length (a : List Bool) : (frame a).length = 2 * a.length + 1 := by
  induction a with
  | nil => rfl
  | cons b bs ih => simp [frame, ih]; omega

namespace Pair
open Compose (K Γ State tapes first second temporary tapes_first tapes_second
  tapes_temporary tapes_update_first tapes_update_second tapes_update_temporary
  tapeOnly init_tapes halt_tapes tapeOnly_self tapeOnly_nil tapeOnly_update)
variable (A B : FinTM2)
abbrev Λ := A.Λ ⊕ (B.Λ ⊕ Fin 4)
abbrev phase (i : Fin 4) : Λ A B := .inr (.inr i)
abbrev Cfg := Turing.TM2.Cfg (Γ A B) (Λ A B) (State A B)
abbrev Stmt := Turing.TM2.Stmt (Γ A B) (Λ A B) (State A B)
def firstStatement : A.Stmt → Stmt A B
  | .push k f p => .push (first A B k) (fun s => f s.1) (firstStatement p)
  | .peek k f p => .peek (first A B k) (fun s x => (f s.1 x, s.2)) (firstStatement p)
  | .pop k f p => .pop (first A B k) (fun s x => (f s.1 x, s.2)) (firstStatement p)
  | .load f p => .load (fun s => (f s.1, s.2)) (firstStatement p)
  | .branch f p q => .branch (fun s => f s.1) (firstStatement p) (firstStatement q)
  | .goto f => .goto (fun s => .inl (f s.1))
  | .halt => .goto (fun _ => .inr (.inl B.main))

def secondStatement : B.Stmt → Stmt A B
  | .push k f p => .push (second A B k) (fun s => f s.2.1) (secondStatement p)
  | .peek k f p => .peek (second A B k)
      (fun s x => (s.1, f s.2.1 x, s.2.2)) (secondStatement p)
  | .pop k f p => .pop (second A B k)
      (fun s x => (s.1, f s.2.1 x, s.2.2)) (secondStatement p)
  | .load f p => .load (fun s => (s.1, f s.2.1, s.2.2)) (secondStatement p)
  | .branch f p q => .branch (fun s => f s.2.1) (secondStatement p) (secondStatement q)
  | .goto f => .goto (fun s => .inr (.inl (f s.2.1)))
  | .halt => .goto (fun _ => phase A B 2)

variable (inA : A.Γ A.k₀ ≃ Bool) (inB : B.Γ B.k₀ ≃ Bool)
  (outA : A.Γ A.k₁ ≃ Bool) (outB : B.Γ B.k₁ ≃ Bool)

def program : Λ A B → Stmt A B
  | .inl l => firstStatement A B (A.m l)
  | .inr (.inl l) => secondStatement A B (B.m l)
  | .inr (.inr i) =>
    if i = 0 then
      .pop (first A B A.k₀) (fun s x => (s.1, s.2.1, x.map inA))
        (.branch (fun s => s.2.2.isSome)
          (.push (temporary A B) (fun s => s.2.2.getD false)
            (.goto (fun _ => phase A B 0)))
          (.goto (fun _ => phase A B 1)))
    else if i = 1 then
      .pop (temporary A B) (fun s x => (s.1, s.2.1, x))
        (.branch (fun s => s.2.2.isSome)
          (.push (first A B A.k₀) (fun s => inA.symm (s.2.2.getD false))
            (.push (second A B B.k₀) (fun s => inB.symm (s.2.2.getD false))
              (.goto (fun _ => phase A B 1))))
          (.goto (fun _ => .inl A.main)))
    else if i = 2 then
      .pop (first A B A.k₁) (fun s x => (s.1, s.2.1, x.map outA))
        (.branch (fun s => s.2.2.isSome)
          (.push (temporary A B) (fun s => s.2.2.getD false)
            (.goto (fun _ => phase A B 2)))
          (.push (second A B B.k₁) (fun _ => outB.symm false)
            (.goto (fun _ => phase A B 3))))
    else
      .pop (temporary A B) (fun s x => (s.1, s.2.1, x))
        (.branch (fun s => s.2.2.isSome)
          (.push (second A B B.k₁) (fun s => outB.symm (s.2.2.getD false))
            (.push (second A B B.k₁) (fun _ => outB.symm true)
              (.goto (fun _ => phase A B 3))))
          (.load (fun _ => (A.initialState, B.initialState, none)) .halt))

abbrev machine : FinTM2 where
  K := K A B
  k₀ := first A B A.k₀
  k₁ := second A B B.k₁
  Γ := Γ A B
  Λ := Λ A B
  σ := State A B
  initialState := (A.initialState, B.initialState, none)
  main := phase A B 0
  m := program A B inA inB outA outB
  Γk₀Fin := A.Γk₀Fin

def firstCfg (state : B.σ) (flag : Option Bool)
    (tb : ∀ k, List (B.Γ k)) (temp : List Bool) (c : A.Cfg) : Cfg A B where
  l := some (c.l.elim ((.inr (.inl B.main))) Sum.inl)
  var := (c.var, state, flag)
  stk := tapes A B c.stk tb temp

def secondCfg (state : A.σ) (flag : Option Bool)
    (ta : ∀ k, List (A.Γ k)) (temp : List Bool) (c : B.Cfg) : Cfg A B where
  l := some (c.l.elim (phase A B 2) (fun l => .inr (.inl l)))
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
    (machine A B inA inB outA outB).step (firstCfg A B b flag tb temp c) =
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
    (machine A B inA inB outA outB).step (secondCfg A B a flag ta temp c) =
      some (secondCfg A B a flag ta temp c') := by
  rcases c with ⟨l,s,tb⟩
  cases l with
  | none => simp [FinTM2.step, step] at h
  | some l =>
    have hc : stepAux (B.m l) s tb = c' := Option.some.inj h
    rw [← hc]
    change some (stepAux (secondStatement A B (B.m l)) (a,s,flag) (tapes A B ta tb temp)) = _
    exact congrArg some (second_stepAux A B a flag ta temp (B.m l) s tb)

theorem cfg_ext {c c' : Cfg A B} (hl : c.l = c'.l)
    (hs : c.var = c'.var) (ht : c.stk = c'.stk) : c = c' := by
  rcases c with ⟨l,s,t⟩
  rcases c' with ⟨l',s',t'⟩
  cases hl; cases hs; cases ht
  rfl

def oneStep {S : Type} (step : S → Option S) (a b : S) (h : step a = some b) :
    StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := h
  steps_le_m := le_rfl

def cfg0 (s : List (A.Γ A.k₀)) (temp : List Bool) (flag : Option Bool) : Cfg A B where
  l := some (phase A B 0)
  var := (A.initialState, B.initialState, flag)
  stk := tapes A B (tapeOnly A.k₀ s) (fun _ => []) temp

def cfg1 (s : List (A.Γ A.k₀)) (t : List (B.Γ B.k₀)) (temp : List Bool)
    (flag : Option Bool) : Cfg A B where
  l := some (phase A B 1)
  var := (A.initialState, B.initialState, flag)
  stk := tapes A B (tapeOnly A.k₀ s) (tapeOnly B.k₀ t) temp

def cfg2 (s : List (A.Γ A.k₁)) (t : List (B.Γ B.k₁)) (temp : List Bool)
    (flag : Option Bool) : Cfg A B where
  l := some (phase A B 2)
  var := (A.initialState, B.initialState, flag)
  stk := tapes A B (tapeOnly A.k₁ s) (tapeOnly B.k₁ t) temp

def cfg3 (t : List (B.Γ B.k₁)) (temp : List Bool) (flag : Option Bool) : Cfg A B where
  l := some (phase A B 3)
  var := (A.initialState, B.initialState, flag)
  stk := tapes A B (fun _ => []) (tapeOnly B.k₁ t) temp

theorem cfg0_cons (x : A.Γ A.k₀) (xs : List (A.Γ A.k₀)) (temp : List Bool)
    (flag : Option Bool) :
    (machine A B inA inB outA outB).step (cfg0 A B (x::xs) temp flag) =
      some (cfg0 A B xs (inA x::temp) (some (inA x))) := by
  change step (program A B inA inB outA outB) _ = _
  simp only [cfg0, step, program, phase, ↓reduceIte, stepAux, tapes_first,
    tapeOnly_self, List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some,
    Bool.cond_true, Option.getD_some]
  rw [← tapes_update_first, tapeOnly_update]
  simp only [tapes_temporary]
  rw [← tapes_update_temporary]

theorem cfg0_nil (temp : List Bool) (flag : Option Bool) :
    (machine A B inA inB outA outB).step (cfg0 A B [] temp flag) =
      some (cfg1 A B [] [] temp none) := by
  change step (program A B inA inB outA outB) _ = _
  simp only [cfg0, step, program, phase, ↓reduceIte, stepAux, tapes_first,
    tapeOnly_self, List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none,
    Bool.cond_false]
  rw [← tapes_update_first, tapeOnly_update]
  simp only [tapeOnly_nil, cfg1]

theorem cfg1_cons (x : Bool) (xs : List Bool) (s : List (A.Γ A.k₀))
    (t : List (B.Γ B.k₀)) (flag : Option Bool) :
    (machine A B inA inB outA outB).step (cfg1 A B s t (x::xs) flag) =
      some (cfg1 A B (inA.symm x::s) (inB.symm x::t) xs (some x)) := by
  change step (program A B inA inB outA outB) _ = _
  simp only [cfg1, step, program, phase, Fin.reduceEq, ↓reduceIte, stepAux, tapes_temporary,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [← tapes_update_temporary]
  simp only [tapes_first, tapeOnly_self]
  rw [← tapes_update_first, tapeOnly_update]
  simp only [tapes_second, tapeOnly_self]
  rw [← tapes_update_second, tapeOnly_update]

theorem cfg1_nil (s : List (A.Γ A.k₀)) (t : List (B.Γ B.k₀)) (flag : Option Bool) :
    (machine A B inA inB outA outB).step (cfg1 A B s t [] flag) =
      some (firstCfg A B B.initialState none (tapeOnly B.k₀ t) [] (initList A s)) := by
  change step (program A B inA inB outA outB) _ = _
  simp only [cfg1, step, program, phase, Fin.reduceEq, ↓reduceIte, stepAux, tapes_temporary,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [← tapes_update_temporary]
  simp only [firstCfg, init_tapes]
  rfl

theorem cfg2_cons (x : A.Γ A.k₁) (xs : List (A.Γ A.k₁)) (t : List (B.Γ B.k₁))
    (temp : List Bool) (flag : Option Bool) :
    (machine A B inA inB outA outB).step (cfg2 A B (x::xs) t temp flag) =
      some (cfg2 A B xs t (outA x::temp) (some (outA x))) := by
  change step (program A B inA inB outA outB) _ = _
  simp only [cfg2, step, program, phase, Fin.reduceEq, ↓reduceIte, stepAux, tapes_first,
    tapeOnly_self, List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some,
    Bool.cond_true, Option.getD_some]
  rw [← tapes_update_first, tapeOnly_update]
  simp only [tapes_temporary]
  rw [← tapes_update_temporary]

theorem cfg2_nil (t : List (B.Γ B.k₁)) (temp : List Bool) (flag : Option Bool) :
    (machine A B inA inB outA outB).step (cfg2 A B [] t temp flag) =
      some (cfg3 A B (outB.symm false :: t) temp none) := by
  change step (program A B inA inB outA outB) _ = _
  simp only [cfg2, step, program, phase, Fin.reduceEq, ↓reduceIte, stepAux, tapes_first,
    tapeOnly_self, List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none,
    Bool.cond_false]
  rw [← tapes_update_first, tapeOnly_update]
  simp only [tapeOnly_nil, tapes_second, tapeOnly_self]
  rw [← tapes_update_second, tapeOnly_update]
  rfl

theorem cfg3_cons (x : Bool) (xs : List Bool) (t : List (B.Γ B.k₁)) (flag : Option Bool) :
    (machine A B inA inB outA outB).step (cfg3 A B t (x::xs) flag) =
      some (cfg3 A B (outB.symm true::outB.symm x::t) xs (some x)) := by
  change step (program A B inA inB outA outB) _ = _
  simp only [cfg3, step, program, phase, Fin.reduceEq, ↓reduceIte, stepAux, tapes_temporary,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [← tapes_update_temporary]
  simp only [tapes_second, tapeOnly_self]
  rw [← tapes_update_second, tapeOnly_update]
  simp only [tapes_second, tapeOnly_self]
  rw [← tapes_update_second, tapeOnly_update]

theorem cfg3_nil (t : List (B.Γ B.k₁)) (flag : Option Bool) :
    (machine A B inA inB outA outB).step (cfg3 A B t [] flag) =
      some (haltList (machine A B inA inB outA outB) t) := by
  change step (program A B inA inB outA outB) _ = _
  simp only [cfg3, step, program, phase, Fin.reduceEq, ↓reduceIte, stepAux, tapes_temporary,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [← tapes_update_temporary]
  congr 1
  apply cfg_ext A B
  · rfl
  · rfl
  · rw [halt_tapes]
    funext k
    rcases k with k | (k | k)
    · simp [tapes, tapeOnly, second, Function.update]
    · by_cases h : k = B.k₁
      · subst k; simp [tapes, tapeOnly, second]
      · simp [tapes, tapeOnly, second, Function.update, h]
    · simp [tapes, tapeOnly, second, Function.update]
def cfg0_run (s : List (A.Γ A.k₀)) (temp : List Bool) (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A B) (machine A B inA inB outA outB).step
      (cfg0 A B s temp flag)
      (some (cfg1 A B [] [] ((s.map inA).reverse ++ temp) none)) (s.length+1) := by
  induction s generalizing temp flag with
  | nil => exact oneStep _ _ _ (cfg0_nil A B inA inB outA outB temp flag)
  | cons x xs ih =>
    have e₁ := oneStep _ _ _ (cfg0_cons A B inA inB outA outB x xs temp flag)
    have e₂ := ih (inA x::temp) (some (inA x))
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.length_cons] using
      StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂

def cfg1_run (temp : List Bool) (s : List (A.Γ A.k₀)) (t : List (B.Γ B.k₀))
    (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A B) (machine A B inA inB outA outB).step
      (cfg1 A B s t temp flag)
      (some (firstCfg A B B.initialState none
        (tapeOnly B.k₀ ((temp.map inB.symm).reverse ++ t)) []
        (initList A ((temp.map inA.symm).reverse ++ s)))) (temp.length+1) := by
  induction temp generalizing s t flag with
  | nil => exact oneStep _ _ _ (cfg1_nil A B inA inB outA outB s t flag)
  | cons x xs ih =>
    have e₁ := oneStep _ _ _ (cfg1_cons A B inA inB outA outB x xs s t flag)
    have e₂ := ih (inA.symm x::s) (inB.symm x::t) (some x)
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.length_cons] using
      StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂

def cfg2_run (s : List (A.Γ A.k₁)) (t : List (B.Γ B.k₁)) (temp : List Bool)
    (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A B) (machine A B inA inB outA outB).step
      (cfg2 A B s t temp flag)
      (some (cfg3 A B (outB.symm false::t) ((s.map outA).reverse ++ temp) none))
      (s.length+1) := by
  induction s generalizing temp flag with
  | nil => exact oneStep _ _ _ (cfg2_nil A B inA inB outA outB t temp flag)
  | cons x xs ih =>
    have e₁ := oneStep _ _ _ (cfg2_cons A B inA inB outA outB x xs t temp flag)
    have e₂ := ih (outA x::temp) (some (outA x))
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.length_cons] using
      StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂

def cfg3_run (temp : List Bool) (t : List (B.Γ B.k₁)) (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A B) (machine A B inA inB outA outB).step
      (cfg3 A B t temp flag)
      (some (haltList (machine A B inA inB outA outB)
        ((temp.reverse.flatMap (fun b => [outB.symm true, outB.symm b])) ++ t)))
      (temp.length+1) := by
  induction temp generalizing t flag with
  | nil => exact oneStep _ _ _ (cfg3_nil A B inA inB outA outB t flag)
  | cons x xs ih =>
    have e₁ := oneStep _ _ _ (cfg3_cons A B inA inB outA outB x xs t flag)
    have e₂ := ih (outB.symm true::outB.symm x::t) (some x)
    simpa only [List.reverse_cons, List.flatMap_append, List.flatMap_singleton,
      List.append_assoc, List.cons_append, List.nil_append, List.length_cons] using
      StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂

theorem initial_eq (s : List (A.Γ A.k₀)) :
    cfg0 A B s [] none = initList (machine A B inA inB outA outB) s := by
  apply cfg_ext A B
  · rfl
  · rfl
  · rw [init_tapes]
    funext k
    rcases k with k | (k | k)
    · by_cases h : k = A.k₀
      · subst k; simp [cfg0, tapes, tapeOnly, first]
      · simp [cfg0, tapes, tapeOnly, first, Function.update, h]
    · simp [cfg0, tapes, tapeOnly, first, Function.update]
    · simp [cfg0, tapes, tapeOnly, first, Function.update]

theorem first_halted (s : List (A.Γ A.k₁)) (t : List (B.Γ B.k₀)) :
    firstCfg A B B.initialState none (tapeOnly B.k₀ t) [] (haltList A s) =
      secondCfg A B A.initialState none (tapeOnly A.k₁ s) [] (initList B t) := by
  simp only [firstCfg, secondCfg, init_tapes, halt_tapes]
  rfl

theorem second_halted (s : List (A.Γ A.k₁)) (t : List (B.Γ B.k₁)) :
    secondCfg A B A.initialState none (tapeOnly A.k₁ s) [] (haltList B t) =
      cfg2 A B s t [] none := by
  simp only [secondCfg, halt_tapes, cfg2]
  rfl

theorem frame_eq (s t : List Bool) :
    s.flatMap (fun b => [true,b]) ++ false::t = pairBits s t := by
  induction s with
  | nil => rfl
  | cons x xs ih => simpa only [List.flatMap_cons, List.cons_append, List.nil_append,
        List.append_assoc, pairBits, frame] using congrArg (fun l => true::x::l) ih

def outputs (input left right : List Bool) (n₁ n₂ : ℕ)
    (h₁ : TM2OutputsInTime A (input.map inA.symm) (some (left.map outA.symm)) n₁)
    (h₂ : TM2OutputsInTime B (input.map inB.symm) (some (right.map outB.symm)) n₂) :
    TM2OutputsInTime (machine A B inA inB outA outB) (input.map inA.symm)
      (some ((pairBits left right).map outB.symm))
      (2*(input.length+1) + n₁ + n₂ + 2*(left.length+1)) := by
  have e₀ : @StateTransition.EvalsToInTime (Cfg A B) (machine A B inA inB outA outB).step
      (initList (machine A B inA inB outA outB) (input.map inA.symm))
      (some (cfg1 A B [] [] input.reverse none)) (input.length+1) := by
    have e := cfg0_run A B inA inB outA outB (input.map inA.symm) [] none
    rw [initial_eq] at e
    simpa only [List.map_map, Function.comp_def, Equiv.apply_symm_apply, List.map_id',
      List.append_nil, List.length_map] using e
  have e₁ : @StateTransition.EvalsToInTime (Cfg A B) (machine A B inA inB outA outB).step
      (cfg1 A B [] [] input.reverse none)
      (some (firstCfg A B B.initialState none (tapeOnly B.k₀ (input.map inB.symm)) []
        (initList A (input.map inA.symm)))) (input.length+1) := by
    simpa only [List.map_reverse, List.reverse_reverse, List.append_nil, List.length_reverse] using
      cfg1_run A B inA inB outA outB input.reverse [] [] none
  have e₂ := liftExecutionInTime A.step (machine A B inA inB outA outB).step
    (firstCfg A B B.initialState none (tapeOnly B.k₀ (input.map inB.symm)) [])
    (first_step A B inA inB outA outB B.initialState none (tapeOnly B.k₀ (input.map inB.symm)) []) h₁
  rw [first_halted] at e₂
  have e₃ := liftExecutionInTime B.step (machine A B inA inB outA outB).step
    (secondCfg A B A.initialState none (tapeOnly A.k₁ (left.map outA.symm)) [])
    (second_step A B inA inB outA outB A.initialState none (tapeOnly A.k₁ (left.map outA.symm)) []) h₂
  rw [second_halted] at e₃
  have e₄ : @StateTransition.EvalsToInTime (Cfg A B) (machine A B inA inB outA outB).step
      (cfg2 A B (left.map outA.symm) (right.map outB.symm) [] none)
      (some (cfg3 A B (outB.symm false::right.map outB.symm) left.reverse none))
      (left.length+1) := by
    simpa only [List.map_map, Function.comp_def, Equiv.apply_symm_apply, List.map_id',
      List.append_nil, List.length_map] using
      cfg2_run A B inA inB outA outB (left.map outA.symm) (right.map outB.symm) [] none
  have e₅ : @StateTransition.EvalsToInTime (Cfg A B) (machine A B inA inB outA outB).step
      (cfg3 A B (outB.symm false::right.map outB.symm) left.reverse none)
      (some (haltList (machine A B inA inB outA outB) ((pairBits left right).map outB.symm)))
      (left.length+1) := by
    have e := cfg3_run A B inA inB outA outB left.reverse (outB.symm false::right.map outB.symm) none
    have hword : left.flatMap (fun b => [outB.symm true, outB.symm b]) ++
        outB.symm false::right.map outB.symm = (pairBits left right).map outB.symm := by
      rw [← frame_eq, List.map_append, List.map_flatMap]
      rfl
    simpa only [List.reverse_reverse, hword, List.length_reverse] using e
  have e₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₀ e₁
  have e₀₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₀₁ e₂
  have e₀₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₀₂ e₃
  have e₀₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₀₃ e₄
  have all := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₀₄ e₅
  exact { all with steps_le_m := by have h := all.steps_le_m; omega }

theorem finiteAlphabet (hA : ∀ k, Finite (A.Γ k)) (hB : ∀ k, Finite (B.Γ k)) :
    ∀ k, Finite ((machine A B inA inB outA outB).Γ k) := by
  rintro (k | (k | k))
  · exact hA k
  · exact hB k
  · exact inferInstanceAs (Finite Bool)

end Pair
open UniqueGames.Foundations.Complexity

noncomputable def pair {α β γ : Type}
    {eα : α → List Bool} {eβ : β → List Bool} {eγ : γ → List Bool}
    {f : α → β} {g : α → γ}
    (c₁ : TM2ComputableInPolyTime eα eβ f) (c₂ : TM2ComputableInPolyTime eα eγ g) :
    TM2ComputableInPolyTime eα (fun p : β × γ => pairBits (eβ p.1) (eγ p.2))
      (fun a => (f a,g a)) where
  tm := Pair.machine c₁.tm c₂.tm c₁.inputAlphabet c₂.inputAlphabet
    c₁.outputAlphabet c₂.outputAlphabet
  inputAlphabet := c₁.inputAlphabet
  outputAlphabet := c₂.outputAlphabet
  time := Polynomial.C 2 * (Polynomial.X + 1) + c₁.time + c₂.time +
    Polynomial.C 2 * (Polynomial.X + Polynomial.C (Runtime.programPushBound c₁.tm) * c₁.time + 1)
  outputsFun a := by
    have run := Pair.outputs c₁.tm c₂.tm c₁.inputAlphabet c₂.inputAlphabet
      c₁.outputAlphabet c₂.outputAlphabet (eα a) (eβ (f a)) (eγ (g a))
      (c₁.time.eval (eα a).length) (c₂.time.eval (eα a).length)
      (c₁.outputsFun a) (c₂.outputsFun a)
    refine { run with steps_le_m := ?_ }
    apply run.steps_le_m.trans
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one]
    have bound := Runtime.encodedOutputLength c₁ a
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at bound
    omega

theorem pair_finite {α β γ : Type}
    {eα : α → List Bool} {eβ : β → List Bool} {eγ : γ → List Bool}
    {f : α → β} {g : α → γ}
    (c₁ : TM2ComputableInPolyTime eα eβ f) (c₂ : TM2ComputableInPolyTime eα eγ g)
    (h₁ : ∀ k, Finite (c₁.tm.Γ k)) (h₂ : ∀ k, Finite (c₂.tm.Γ k)) :
    ∀ k, Finite ((pair c₁ c₂).tm.Γ k) :=
  Pair.finiteAlphabet c₁.tm c₂.tm c₁.inputAlphabet c₂.inputAlphabet
    c₁.outputAlphabet c₂.outputAlphabet h₁ h₂

structure Poly {α β : Type} (eα : α → List Bool) (eβ : β → List Bool) (f : α → β) where
  computation : TM2ComputableInPolyTime eα eβ f
  finiteAlphabet : ∀ k, Finite (computation.tm.Γ k)

noncomputable def Poly.comp {α β γ : Type}
    {eα : α → List Bool} {eβ : β → List Bool} {eγ : γ → List Bool}
    {f : α → β} {g : β → γ} (c₁ : Poly eα eβ f) (c₂ : Poly eβ eγ g) :
    Poly eα eγ (g ∘ f) :=
  ⟨compose c₁.computation c₂.computation,
    compose_finite c₁.computation c₂.computation c₁.finiteAlphabet c₂.finiteAlphabet⟩

noncomputable def Poly.pair {α β γ : Type}
    {eα : α → List Bool} {eβ : β → List Bool} {eγ : γ → List Bool}
    {f : α → β} {g : α → γ} (c₁ : Poly eα eβ f) (c₂ : Poly eα eγ g) :
    Poly eα (fun p : β × γ => pairBits (eβ p.1) (eγ p.2)) (fun a => (f a,g a)) :=
  ⟨VertexCover.Machine.pair c₁.computation c₂.computation,
    pair_finite c₁.computation c₂.computation c₁.finiteAlphabet c₂.finiteAlphabet⟩

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
