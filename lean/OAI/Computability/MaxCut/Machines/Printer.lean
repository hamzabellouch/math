import Mathlib
import OAI.Computability.MaxCut.Gadgets.ValuePolynomial
import OAI.Computability.MaxCut.Estimates.CorrectSum

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine
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

/-- A genuine polynomial-time finite Boolean-tape Turing machine for any closed
bounded-arithmetic bit table. This is an operational theorem, not a closure
axiom or a unit-cost machine convention. -/
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

end OptimalMaxCut.CounterMachine

end

end OAI
