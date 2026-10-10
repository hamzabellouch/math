import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.ValuePolynomial
import OAI.Combinatorics.IndependentSets.Machines.Restrict

namespace OAI

namespace IndependentSetsCut.CounterMachine
open Turing Polynomial Command

def printer (len bit : Expr) : Command ℕ := .seq (print len bit) eraseInput

noncomputable def printerTime (len bit : Expr) : Polynomial ℕ :=
  len.timePolynomial+len.valuePolynomial*
    (bit.timePolynomial.comp (X+len.valuePolynomial)+
      2*bit.valuePolynomial.comp (X+len.valuePolynomial)+4)+1+7*X+8

 theorem printer_evaluates (len bit : Expr) (input : List Bool) :
    Within (printer len bit) (initial input)
      ⟨fun _ => 0, [], [], table len bit input⟩ ((printerTime len bit).eval input.length-1) := by
  have hp := print_evaluates len bit input
  have he := eraseInput_evaluates {initial input with output := table len bit input}
    (by intro r hr; rfl) rfl
  have h := hp.seq he
  apply h.mono
  simp only [printerTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_comp, Expr.timePolynomial_eval, Expr.valuePolynomial_eval]

  simp only [initial] at *
  omega

 theorem halted_eq {R : Type} [DecidableEq R] [Fintype R] (c : Command R) (out : List Bool) :
    embed (⟨⟨fun _ => 0, [], [], out⟩, none⟩ : Configuration R c.FinalLabel) =
      haltList c.finiteMachine out := by
  unfold embed haltList
  congr 1
  funext k
  cases k <;> simp [tapes, finiteMachine, machine]
  rfl

noncomputable def tableComputer (len bit : Expr) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) id (table len bit) where
  tm := (printer len bit).finite.finiteMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := printerTime len bit
  outputsFun input := by
    let h := printer_evaluates len bit input
    let n := Classical.choose h
    have hn := Classical.choose_spec h
    have he := Command.finite_evaluates hn.2
    change Evaluates _ (initial input) ⟨fun _ => 0, [], [], table len bit input⟩ n at he
    have run := machine_run he
    have hout := halted_eq (printer len bit).finite (table len bit input)
    have run' : StateTransition.EvalsToInTime (printer len bit).finite.finiteMachine.step
        (initList (printer len bit).finite.finiteMachine input)
        (some (haltList (printer len bit).finite.finiteMachine (table len bit input))) (n+1) := by
      convert run using 1
      congr 1
      unfold haltList embed
      congr 1
      funext k
      cases k <;> simp [tapes, finiteMachine, machine]
      rfl
    let run := run'
    refine ⟨⟨run.steps, ?_⟩, ?_⟩
    · change (flip Option.bind (printer len bit).finite.finiteMachine.step)^[run.steps]
        (some (initList (printer len bit).finite.finiteMachine (input.map (id : Bool → Bool)))) =
        some (haltList (printer len bit).finite.finiteMachine ((table len bit input).map (id : Bool → Bool)))
      erw [List.map_id, List.map_id]
      exact run.evals_in_steps
    · have hs := run.steps_le_m
      have hb := hn.1
      have hp : 0 < (printerTime len bit).eval input.length := by
        simp only [printerTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
          Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_comp, Expr.timePolynomial_eval, Expr.valuePolynomial_eval]
        omega
      change run.steps ≤ (printerTime len bit).eval input.length
      omega

 theorem tableComputer_finiteAlphabet (len bit : Expr) (k : (tableComputer len bit).tm.K) :
    Finite ((tableComputer len bit).tm.Γ k) := inferInstanceAs (Finite Bool)

end IndependentSetsCut.CounterMachine

namespace IndependentSetsCut.CounterMachine.Expr
open scoped BigOperators
open Finset

def rename (ρ : ℕ → ℕ) : Expr → Expr
  | .const n => .const n
  | .arg i => .arg (ρ i)
  | .length => .length
  | .bit e => .bit (rename ρ e)
  | .add a b => .add (rename ρ a) (rename ρ b)
  | .sub a b => .sub (rename ρ a) (rename ρ b)
  | .mul a b => .mul (rename ρ a) (rename ρ b)
  | .zero a => .zero (rename ρ a)
  | .sum b f => .sum (rename ρ b) (rename (bind (fun i => ρ i+1) 0) f)

@[simp] theorem rename_eval (e : Expr) (ρ : ℕ → ℕ) (input : List Bool) (args : ℕ → ℕ) :
    (e.rename ρ).eval input args = e.eval input (fun i => args (ρ i)) := by
  induction e generalizing ρ args <;> simp only [rename, eval] at *
  all_goals try simp_all
  case sum b f ib iF =>
    apply sum_congr rfl
    intro i hi
    congr 1
    funext j
    cases j <;> rfl

def bindExpr (σ : ℕ → Expr) (e : Expr) : ℕ → Expr
  | 0 => e
  | i+1 => σ i

def subst (σ : ℕ → Expr) : Expr → Expr
  | .const n => .const n
  | .arg i => σ i
  | .length => .length
  | .bit e => .bit (subst σ e)
  | .add a b => .add (subst σ a) (subst σ b)
  | .sub a b => .sub (subst σ a) (subst σ b)
  | .mul a b => .mul (subst σ a) (subst σ b)
  | .zero a => .zero (subst σ a)
  | .sum b f => .sum (subst σ b) (subst (bindExpr (fun i => (σ i).rename Nat.succ) (.arg 0)) f)

@[simp] theorem subst_eval (e : Expr) (σ : ℕ → Expr) (input : List Bool) (args : ℕ → ℕ) :
    (e.subst σ).eval input args = e.eval input (fun i => (σ i).eval input args) := by
  induction e generalizing σ args <;> simp only [subst, eval] at *
  all_goals try simp_all
  case sum b f ib iF =>
    apply sum_congr rfl
    intro i hi
    congr 1
    funext j
    cases j with
    | zero => rfl
    | succ j => simp [bindExpr, bind]

def positive (a : Expr) : Expr := .zero (.zero a)
def equal (a b : Expr) : Expr := .zero (.add (.sub a b) (.sub b a))
def le (a b : Expr) : Expr := .zero (.sub a b)
def lt (a b : Expr) : Expr := le (.add a (.const 1)) b

@[simp] theorem positive_eval (a : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (positive a).eval input args = if a.eval input args ≠ 0 then 1 else 0 := by
  simp [positive, eval]

@[simp] theorem equal_eval (a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (equal a b).eval input args = if a.eval input args = b.eval input args then 1 else 0 := by
  by_cases h : a.eval input args = b.eval input args
  · simp only [equal, eval, h, Nat.sub_self, Nat.zero_add, ↓reduceIte]
  · have hn : a.eval input args-b.eval input args+(b.eval input args-a.eval input args) ≠ 0 := by omega
    simp only [equal, eval, h, hn, ↓reduceIte]

@[simp] theorem le_eval (a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (le a b).eval input args = if a.eval input args ≤ b.eval input args then 1 else 0 := by
  simp [le, eval, Nat.sub_eq_zero_iff_le]

@[simp] theorem lt_eval (a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (lt a b).eval input args = if a.eval input args < b.eval input args then 1 else 0 := by
  simp [lt, eval]

def cond (c a b : Expr) : Expr := .add (.mul (positive c) a) (.mul (.zero c) b)
@[simp] theorem cond_eval (c a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (cond c a b).eval input args = if c.eval input args ≠ 0 then a.eval input args else b.eval input args := by
  simp only [cond, eval, positive_eval]; split_ifs <;> simp_all

def quotient (a b : Expr) : Expr :=
  .mul (positive b) (.sum a (le (.mul (.add (.arg 0) (.const 1)) (b.rename Nat.succ)) (a.rename Nat.succ)))

 theorem quotient_sum (a b : ℕ) (hb : 0 < b) :
    (∑ i ∈ range a, if (i+1)*b ≤ a then (1:ℕ) else 0) = a/b := by
  have hcond (i : ℕ) : (i+1)*b ≤ a ↔ i < a/b := by
    rw [← Nat.le_div_iff_mul_le hb, Nat.add_one_le_iff]
  simp_rw [hcond]
  rw [sum_boole]
  have hs : {i ∈ range a | i < a/b} = range (a/b) := by
    ext i; simp only [mem_filter, mem_range]
    exact and_iff_right_of_imp (fun hi => hi.trans_le (Nat.div_le_self _ _))
  simp only [hs, card_range, Nat.cast_id]

@[simp] theorem quotient_eval (a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (quotient a b).eval input args = a.eval input args / b.eval input args := by
  simp only [quotient, eval, positive_eval, le_eval, rename_eval, bind]
  by_cases hb : b.eval input args = 0
  · simp [hb]
  · simp only [hb, ne_eq, not_false_eq_true, ↓reduceIte, one_mul]
    simpa using quotient_sum (a.eval input args) (b.eval input args) (by omega)

def remainder (a b : Expr) : Expr := .sub a (.mul (quotient a b) b)
@[simp] theorem remainder_eval (a b : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (remainder a b).eval input args = a.eval input args % b.eval input args := by
  simp only [remainder, eval, quotient_eval]
  exact Nat.mod_eq_sub_div_mul.symm

def power (a : Expr) : ℕ → Expr
  | 0 => .const 1
  | n+1 => .mul (power a n) a
@[simp] theorem power_eval (a : Expr) (n : ℕ) (input : List Bool) (args : ℕ → ℕ) :
    (power a n).eval input args = (a.eval input args)^n := by
  induction n <;> simp [power, eval, pow_succ, *]

end IndependentSetsCut.CounterMachine.Expr

end OAI
