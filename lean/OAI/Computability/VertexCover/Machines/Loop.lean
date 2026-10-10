import Mathlib
import OAI.Computability.VertexCover.Machines.Pair

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
open UniqueGames.Foundations.Complexity
attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

namespace Loop
variable (A : FinTM2)
abbrev K := A.K ⊕ Bool
abbrev Γ := MachineEmbedding.Alphabet A.Γ (fun _ : Bool => Bool)
abbrev Λ := A.Λ ⊕ Fin 3
abbrev State := A.σ × Bool × Option Bool
abbrev Cfg := Turing.TM2.Cfg (Γ A) (Λ A) (State A)
abbrev Stmt := Turing.TM2.Stmt (Γ A) (Λ A) (State A)
abbrev temporary : K A := .inr false
abbrev output : K A := .inr true
abbrev phase (i : Fin 3) : Λ A := .inr i
abbrev haltTarget : Option (Λ A) := some (phase A 0)
abbrev tapes := @MachineEmbedding.tapes A.K Bool A.Γ (fun _ => Bool)

variable (inA : A.Γ A.k₀ ≃ Bool) (outA : A.Γ A.k₁ ≃ Bool)

def extra : Fin 3 → Stmt A
  | i => if i = 0 then
      .pop (.inl A.k₁) (fun s x => (s.1, (x.map outA).getD false, none))
        (.goto (fun _ => phase A 1))
    else if i = 1 then
      .pop (.inl A.k₁) (fun s x => (s.1, s.2.1, x.map outA))
        (.branch (fun s => s.2.2.isSome)
          (.push (temporary A) (fun s => s.2.2.getD false)
            (.goto (fun _ => phase A 1)))
          (.goto (fun _ => phase A 2)))
    else
      .pop (temporary A) (fun s x => (s.1, s.2.1, x))
        (.branch (fun s => s.2.2.isSome)
          (.branch (fun s => s.2.1)
            (.push (.inl A.k₀) (fun s => inA.symm (s.2.2.getD false))
              (.goto (fun _ => phase A 2)))
            (.push (output A) (fun s => s.2.2.getD false)
              (.goto (fun _ => phase A 2))))
          (.branch (fun s => s.2.1)
            (.load (fun _ => (A.initialState,false,none)) (.goto (fun _ => .inl A.main)))
            (.load (fun _ => (A.initialState,false,none)) .halt)))

abbrev program := MachineEmbedding.program (haltTarget A) A.m (extra A inA outA)

abbrev machine : FinTM2 where
  K := K A
  Γ := Γ A
  k₀ := .inl A.k₀
  k₁ := output A
  Λ := Λ A
  σ := State A
  main := .inl A.main
  initialState := (A.initialState,false,none)
  m := program A inA outA
  Γk₀Fin := A.Γk₀Fin

open Compose (tapeOnly tapeOnly_nil tapeOnly_self tapeOnly_update init_tapes halt_tapes)

def extraTapes (temp out : List Bool) : Bool → List Bool
  | false => temp
  | true => out

@[simp] theorem extraTapes_false (temp out : List Bool) : extraTapes temp out false = temp := rfl
@[simp] theorem extraTapes_true (temp out : List Bool) : extraTapes temp out true = out := rfl

theorem tapes_update_extra (ta : ∀ k, List (A.Γ k)) (tb : Bool → List Bool)
    (j : Bool) (s : List Bool) :
    tapes A ta (Function.update tb j s) = Function.update (tapes A ta tb) (.inr j) s := by
  funext k
  rcases k with k | k
  · simp [tapes, MachineEmbedding.tapes, Function.update]
  · by_cases h : k = j
    · subst k; simp [tapes, MachineEmbedding.tapes]
    · simp [tapes, MachineEmbedding.tapes, Function.update, h]

theorem update_extra_false (a b c : List Bool) :
    Function.update (extraTapes a b) false c = extraTapes c b := by
  funext k; cases k <;> simp [extraTapes]

theorem update_extra_true (a b c : List Bool) :
    Function.update (extraTapes a b) true c = extraTapes a c := by
  funext k; cases k <;> simp [extraTapes]

abbrev embedded (c : A.Cfg) : Cfg A :=
  MachineEmbedding.configuration (haltTarget A) (false,none) (extraTapes [] []) c

def cfg1 (mode : Bool) (s : List (A.Γ A.k₁)) (temp : List Bool)
    (flag : Option Bool) : Cfg A where
  l := some (phase A 1)
  var := (A.initialState,mode,flag)
  stk := tapes A (tapeOnly A.k₁ s) (extraTapes temp [])

def cfg2true (s : List (A.Γ A.k₀)) (temp : List Bool) (flag : Option Bool) : Cfg A where
  l := some (phase A 2)
  var := (A.initialState,true,flag)
  stk := tapes A (tapeOnly A.k₀ s) (extraTapes temp [])

def cfg2false (s temp : List Bool) (flag : Option Bool) : Cfg A where
  l := some (phase A 2)
  var := (A.initialState,false,flag)
  stk := tapes A (fun _ => []) (extraTapes temp s)

theorem cfg_ext {c c' : Cfg A} (hl : c.l = c'.l)
    (hs : c.var = c'.var) (ht : c.stk = c'.stk) : c = c' := by
  rcases c with ⟨l,s,t⟩
  rcases c' with ⟨l',s',t'⟩
  cases hl; cases hs; cases ht
  rfl

theorem halt_label (s : List (A.Γ A.k₁)) : (haltList A s).l = none := rfl

theorem halt_var (s : List (A.Γ A.k₁)) : (haltList A s).var = A.initialState := rfl

theorem cfg0_step (mode : Bool) (s : List Bool) :
    (machine A inA outA).step (embedded A (haltList A ((mode::s).map outA.symm))) =
      some (cfg1 A mode (s.map outA.symm) [] none) := by
  change step (program A inA outA) _ = _
  simp only [embedded, MachineEmbedding.configuration, halt_tapes, halt_label, halt_var,
    MachineEmbedding.label, haltTarget, phase, step, program, MachineEmbedding.program,
    extra, ↓reduceIte, stepAux, MachineEmbedding.tapes_inl, List.map_cons, tapeOnly_self,
    List.head?_cons, List.tail_cons, Option.map_some, Equiv.apply_symm_apply, Option.getD_some]
  rw [← MachineEmbedding.tapes_update, tapeOnly_update]
  rfl

theorem cfg1_cons (mode : Bool) (x : A.Γ A.k₁) (xs : List (A.Γ A.k₁))
    (temp : List Bool) (flag : Option Bool) :
    (machine A inA outA).step (cfg1 A mode (x::xs) temp flag) =
      some (cfg1 A mode xs (outA x::temp) (some (outA x))) := by
  change step (program A inA outA) _ = _
  simp only [cfg1, step, program, MachineEmbedding.program, phase, extra, Fin.reduceEq,
    ↓reduceIte, stepAux, MachineEmbedding.tapes_inl, tapeOnly_self,
    List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some,
    Bool.cond_true, Option.getD_some]
  rw [← MachineEmbedding.tapes_update, tapeOnly_update]
  simp only [temporary, MachineEmbedding.tapes_inr, extraTapes_false]
  rw [← tapes_update_extra, update_extra_false]

theorem cfg1_nil_true (temp : List Bool) (flag : Option Bool) :
    (machine A inA outA).step (cfg1 A true [] temp flag) =
      some (cfg2true A [] temp none) := by
  change step (program A inA outA) _ = _
  simp only [cfg1, step, program, MachineEmbedding.program, phase, extra, Fin.reduceEq,
    ↓reduceIte, stepAux, MachineEmbedding.tapes_inl, tapeOnly_self,
    List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, Bool.cond_false]
  rw [← MachineEmbedding.tapes_update, tapeOnly_update]
  simp only [tapeOnly_nil, cfg2true]

theorem cfg1_nil_false (temp : List Bool) (flag : Option Bool) :
    (machine A inA outA).step (cfg1 A false [] temp flag) =
      some (cfg2false A [] temp none) := by
  change step (program A inA outA) _ = _
  simp only [cfg1, step, program, MachineEmbedding.program, phase, extra, Fin.reduceEq,
    ↓reduceIte, stepAux, MachineEmbedding.tapes_inl, tapeOnly_self,
    List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, Bool.cond_false]
  rw [← MachineEmbedding.tapes_update, tapeOnly_update]
  simp only [tapeOnly_nil, cfg2false]

theorem cfg2true_cons (x : Bool) (xs : List Bool) (s : List (A.Γ A.k₀)) (flag : Option Bool) :
    (machine A inA outA).step (cfg2true A s (x::xs) flag) =
      some (cfg2true A (inA.symm x::s) xs (some x)) := by
  change step (program A inA outA) _ = _
  simp only [cfg2true, step, program, MachineEmbedding.program, phase, extra, Fin.reduceEq,
    ↓reduceIte, stepAux, temporary, MachineEmbedding.tapes_inr, extraTapes_false,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.getD_some]
  rw [← tapes_update_extra, update_extra_false]
  simp only [MachineEmbedding.tapes_inl, tapeOnly_self]
  rw [← MachineEmbedding.tapes_update, tapeOnly_update]

theorem cfg2false_cons (x : Bool) (xs s : List Bool) (flag : Option Bool) :
    (machine A inA outA).step (cfg2false A s (x::xs) flag) =
      some (cfg2false A (x::s) xs (some x)) := by
  change step (program A inA outA) _ = _
  simp only [cfg2false, step, program, MachineEmbedding.program, phase, extra, Fin.reduceEq,
    ↓reduceIte, stepAux, temporary, MachineEmbedding.tapes_inr, extraTapes_false,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Bool.cond_false,
    Option.getD_some]
  rw [← tapes_update_extra, update_extra_false]
  simp only [output, MachineEmbedding.tapes_inr, extraTapes_true]
  rw [← tapes_update_extra, update_extra_true]

theorem initial_eq (s : List (A.Γ A.k₀)) :
    embedded A (initList A s) = initList (machine A inA outA) s := by
  apply cfg_ext A
  · rfl
  · rfl
  · rw [init_tapes]
    change tapes A (initList A s).stk (extraTapes [] []) = _
    rw [init_tapes]
    funext k
    rcases k with k | k
    · by_cases h : k = A.k₀
      · subst k; simp [tapes, MachineEmbedding.tapes, tapeOnly]
      · simp [tapes, MachineEmbedding.tapes, tapeOnly, Function.update, h]
    · cases k <;> simp [tapes, MachineEmbedding.tapes, tapeOnly, Function.update, extraTapes]

theorem cfg2true_nil (s : List (A.Γ A.k₀)) (flag : Option Bool) :
    (machine A inA outA).step (cfg2true A s [] flag) =
      some (initList (machine A inA outA) s) := by
  rw [← initial_eq]
  change step (program A inA outA) _ = _
  simp only [cfg2true, step, program, MachineEmbedding.program, phase, extra, Fin.reduceEq,
    ↓reduceIte, stepAux, temporary, MachineEmbedding.tapes_inr, extraTapes_false,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_true, Bool.cond_false]
  rw [← tapes_update_extra, update_extra_false]
  simp only [embedded, MachineEmbedding.configuration, init_tapes]
  rfl

theorem cfg2false_nil (s : List Bool) (flag : Option Bool) :
    (machine A inA outA).step (cfg2false A s [] flag) =
      some (haltList (machine A inA outA) s) := by
  change step (program A inA outA) _ = _
  simp only [cfg2false, step, program, MachineEmbedding.program, phase, extra, Fin.reduceEq,
    ↓reduceIte, stepAux, temporary, MachineEmbedding.tapes_inr, extraTapes_false,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  rw [← tapes_update_extra, update_extra_false]
  congr 1
  apply cfg_ext A
  · rfl
  · rfl
  · rw [halt_tapes]
    funext k
    rcases k with k | k
    · simp [tapes, MachineEmbedding.tapes, tapeOnly, output, Function.update]
    · cases k <;> simp [tapes, MachineEmbedding.tapes, tapeOnly, output, Function.update, extraTapes]
def cfg1_run_true (s : List (A.Γ A.k₁)) (temp : List Bool) (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (cfg1 A true s temp flag)
      (some (cfg2true A [] ((s.map outA).reverse ++ temp) none)) (s.length+1) := by
  induction s generalizing temp flag with
  | nil => exact Pair.oneStep _ _ _ (cfg1_nil_true A inA outA temp flag)
  | cons x xs ih =>
    have e₁ := Pair.oneStep _ _ _ (cfg1_cons A inA outA true x xs temp flag)
    have e₂ := ih (outA x::temp) (some (outA x))
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.length_cons] using
      StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂

def cfg1_run_false (s : List (A.Γ A.k₁)) (temp : List Bool) (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (cfg1 A false s temp flag)
      (some (cfg2false A [] ((s.map outA).reverse ++ temp) none)) (s.length+1) := by
  induction s generalizing temp flag with
  | nil => exact Pair.oneStep _ _ _ (cfg1_nil_false A inA outA temp flag)
  | cons x xs ih =>
    have e₁ := Pair.oneStep _ _ _ (cfg1_cons A inA outA false x xs temp flag)
    have e₂ := ih (outA x::temp) (some (outA x))
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.length_cons] using
      StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂

def cfg2true_run (temp : List Bool) (s : List (A.Γ A.k₀)) (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (cfg2true A s temp flag)
      (some (initList (machine A inA outA) ((temp.map inA.symm).reverse ++ s)))
      (temp.length+1) := by
  induction temp generalizing s flag with
  | nil => exact Pair.oneStep _ _ _ (cfg2true_nil A inA outA s flag)
  | cons x xs ih =>
    have e₁ := Pair.oneStep _ _ _ (cfg2true_cons A inA outA x xs s flag)
    have e₂ := ih (inA.symm x::s) (some x)
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append, List.length_cons] using
      StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂

def cfg2false_run (temp s : List Bool) (flag : Option Bool) :
    @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (cfg2false A s temp flag)
      (some (haltList (machine A inA outA) (temp.reverse ++ s))) (temp.length+1) := by
  induction temp generalizing s flag with
  | nil => exact Pair.oneStep _ _ _ (cfg2false_nil A inA outA s flag)
  | cons x xs ih =>
    have e₁ := Pair.oneStep _ _ _ (cfg2false_cons A inA outA x xs s flag)
    have e₂ := ih (x::s) (some x)
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons] using
      StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₁ e₂

open MachineComposition (embeddedExecution)

def bodyRun (mode : Bool) (input next : List Bool) (n : ℕ)
    (h : TM2OutputsInTime A (input.map inA.symm) (some ((mode::next).map outA.symm)) n) :
    @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (initList (machine A inA outA) (input.map inA.symm))
      (some (cfg1 A mode (next.map outA.symm) [] none)) (n+1) := by
  have e := embeddedExecution (haltTarget A) (false,none) (extraTapes [] []) A.m
    (extra A inA outA) h
  change @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
    (embedded A (initList A (input.map inA.symm)))
    (some (embedded A (haltList A ((mode::next).map outA.symm)))) n at e
  rw [initial_eq] at e
  have all := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e
    (Pair.oneStep _ _ _ (cfg0_step A inA outA mode next))
  exact { all with steps_le_m := by have hh := all.steps_le_m; omega }

def restart (input next : List Bool) (n : ℕ)
    (h : TM2OutputsInTime A (input.map inA.symm) (some ((true::next).map outA.symm)) n) :
    @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (initList (machine A inA outA) (input.map inA.symm))
      (some (initList (machine A inA outA) (next.map inA.symm)))
      (n+1+2*(next.length+1)) := by
  have e₀ := bodyRun A inA outA true input next n h
  have e₁ : @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (cfg1 A true (next.map outA.symm) [] none)
      (some (cfg2true A [] next.reverse none)) (next.length+1) := by
    simpa only [List.map_map, Function.comp_def, Equiv.apply_symm_apply, List.map_id',
      List.append_nil, List.length_map] using
      cfg1_run_true A inA outA (next.map outA.symm) [] none
  have e₂ : @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (cfg2true A [] next.reverse none)
      (some (initList (machine A inA outA) (next.map inA.symm))) (next.length+1) := by
    simpa only [List.map_reverse, List.reverse_reverse, List.append_nil, List.length_reverse] using
      cfg2true_run A inA outA next.reverse [] none
  have all := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₀ e₁) e₂
  exact { all with steps_le_m := by have hh := all.steps_le_m; omega }

def finish (input next : List Bool) (n : ℕ)
    (h : TM2OutputsInTime A (input.map inA.symm) (some ((false::next).map outA.symm)) n) :
    TM2OutputsInTime (machine A inA outA) (input.map inA.symm) (some next)
      (n+1+2*(next.length+1)) := by
  have e₀ := bodyRun A inA outA false input next n h
  have e₁ : @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (cfg1 A false (next.map outA.symm) [] none)
      (some (cfg2false A [] next.reverse none)) (next.length+1) := by
    simpa only [List.map_map, Function.comp_def, Equiv.apply_symm_apply, List.map_id',
      List.append_nil, List.length_map] using
      cfg1_run_false A inA outA (next.map outA.symm) [] none
  have e₂ : @StateTransition.EvalsToInTime (Cfg A) (machine A inA outA).step
      (cfg2false A [] next.reverse none)
      (some (haltList (machine A inA outA) next)) (next.length+1) := by
    simpa only [List.reverse_reverse, List.append_nil, List.length_reverse] using
      cfg2false_run A inA outA next.reverse [] none
  have all := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ e₀ e₁) e₂
  exact { all with steps_le_m := by have hh := all.steps_le_m; omega }

theorem finiteAlphabet (hA : ∀ k, Finite (A.Γ k)) :
    ∀ k, Finite ((machine A inA outA).Γ k) := by
  rintro (k | k)
  · exact hA k
  · exact inferInstanceAs (Finite Bool)

end Loop

inductive BoundedRun {α : Type} (e : α → List Bool) (body : α → Bool × α) (bound : ℕ) :
    α → α → ℕ → Prop
  | stop (a : α) (size : (e a).length ≤ bound) (done : (body a).1 = false) :
      BoundedRun e body bound a (body a).2 1
  | next (a z : α) (n : ℕ) (size : (e a).length ≤ bound) (more : (body a).1 = true)
      (tail : BoundedRun e body bound (body a).2 z n) :
      BoundedRun e body bound a z (n+1)

noncomputable def loopCost {α : Type} {e : α → List Bool} {body : α → Bool × α}
    (c : TM2ComputableInPolyTime e (fun p : Bool × α => p.1 :: e p.2) body) : Polynomial ℕ :=
  c.time + 1 + Polynomial.C 2 *
    (Polynomial.X + Polynomial.C (Runtime.programPushBound c.tm) * c.time + 1)

theorem loopCost_bound {α : Type} {e : α → List Bool} {body : α → Bool × α}
    (c : TM2ComputableInPolyTime e (fun p : Bool × α => p.1 :: e p.2) body)
    (a : α) (B : ℕ) (ha : (e a).length ≤ B) :
    c.time.eval (e a).length + 1 + 2*((e (body a).2).length + 1) ≤ (loopCost c).eval B := by
  have ho := Runtime.encodedOutputLength c a
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    List.length_cons] at ho
  have ht := MachineComposition.natPolynomial_eval_mono c.time ha
  have hp := Nat.mul_le_mul_left (Runtime.programPushBound c.tm) ht
  simp only [loopCost, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one]
  omega

theorem boundedRun_execution {α : Type} {e : α → List Bool} {body : α → Bool × α}
    (c : TM2ComputableInPolyTime e (fun p : Bool × α => p.1 :: e p.2) body)
    {B : ℕ} {a z : α} {n : ℕ} (h : BoundedRun e body B a z n) :
    Nonempty (TM2OutputsInTime (Loop.machine c.tm c.inputAlphabet c.outputAlphabet)
      ((e a).map c.inputAlphabet.symm) (some (e z)) (n*(loopCost c).eval B)) := by
  induction h with
  | stop a ha stop =>
    have ho := c.outputsFun a
    simp only [stop] at ho
    have run := Loop.finish c.tm c.inputAlphabet c.outputAlphabet (e a) (e (body a).2)
      (c.time.eval (e a).length) ho
    refine ⟨{ run with steps_le_m := ?_ }⟩
    simpa only [one_mul] using run.steps_le_m.trans (loopCost_bound c a B ha)
  | next a z n ha more tail ih =>
    obtain ⟨ih⟩ := ih
    have ho := c.outputsFun a
    simp only [more] at ho
    have run := Loop.restart c.tm c.inputAlphabet c.outputAlphabet (e a) (e (body a).2)
      (c.time.eval (e a).length) ho
    have all := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run ih
    refine ⟨{ all with steps_le_m := ?_ }⟩
    have h := all.steps_le_m
    have hb := loopCost_bound c a B ha
    rw [Nat.add_mul]
    omega

noncomputable def Poly.loop {α : Type} {e : α → List Bool} {body : α → Bool × α}
    (c : Poly e (fun p : Bool × α => p.1 :: e p.2) body)
    (result : α → α) (size count : Polynomial ℕ)
    (spec : ∀ a, ∃ n, n ≤ count.eval (e a).length ∧
      BoundedRun e body (size.eval (e a).length) a (result a) n) : Poly e e result where
  computation := {
    tm := Loop.machine c.computation.tm c.computation.inputAlphabet c.computation.outputAlphabet
    inputAlphabet := c.computation.inputAlphabet
    outputAlphabet := Equiv.refl Bool
    time := count * (loopCost c.computation).comp size
    outputsFun := fun a => Classical.choice (by
      simp only [show (Equiv.refl Bool).invFun = id from rfl, List.map_id]
      obtain ⟨n, hn, run⟩ := spec a
      obtain ⟨execution⟩ := boundedRun_execution c.computation run
      refine ⟨{ execution with steps_le_m := ?_ }⟩
      simp only [Polynomial.eval_mul, Polynomial.eval_comp]
      exact execution.steps_le_m.trans (Nat.mul_le_mul_right _ hn)) }
  finiteAlphabet := Loop.finiteAlphabet _ _ _ c.finiteAlphabet

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
