import OAI.Computability.PerfectCompleteness.Machines.ClashMachineFull
import OAI.Computability.PerfectCompleteness.Machines.ValidityMachine

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.ValidityMachine.Full

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean emitted)


variable {K Λ σ : Type} [DecidableEq K]

def nonemptyMap : Fin 7 ↪ Fin 10 := ⟨![0, 1, 3, 5, 9, 7, 8], by decide⟩

inductive Label where
  | nonempty (l : Nonempty.Label)
  | clash (l : ClashMachine.Full.Label)
  | finish
  deriving DecidableEq, Fintype

def statement (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (ValidityMachine.Alphabet (K := K)) Λ (State σ)
  | .nonempty l => Nonempty.statement (nonemptyMap.trans slots)
      (fun l => labels (.nonempty l)) (some (labels (.clash .start))) l
  | .clash l => ClashMachine.Full.statement slots (fun l => labels (.clash l))
      (some (labels .finish)) l
  | .finish => ClashMachine.literal (slots 7) (slots 8) [.not, .and]
      (Reduction.MachineTransfer.exitAt (slots 7) exit)

def steps (q : Nat) : Nat := Nonempty.steps q + ClashMachine.Full.steps q + 1

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 20 * (Polynomial.X + Polynomial.C 2) ^ 2 +
    ClashMachine.Full.timePolynomial + Polynomial.C 1

theorem timePolynomial_eval (q : Nat) :
    timePolynomial.eval q = 20 * (q + 2) ^ 2 + ClashMachine.Full.timePolynomial.eval q + 1 := by
  simp [timePolynomial]

theorem steps_le_time (q : Nat) : steps q ≤ timePolynomial.eval q := by
  rw [timePolynomial_eval]
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nonempty.steps_le q) (ClashMachine.Full.steps_le_time q)) 1

private theorem chain {A : Type*} {f : A → A} {x y z : A} {n m : Nat}
    (first : f^[n] x = y) (second : f^[m] y = z) : f^[n + m] x = z := by
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

theorem trace (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (ValidityMachine.Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (q : Nat) (ready : ClashMachine.Full.Ready slots base q) (ambient : σ) :
    (advance (TM2.step program))^[steps q]
      (some ⟨some (labels (.nonempty .initialize)), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 7) (slots 8) base (validityTokens q)⟩ := by
  have nr : Nonempty.Ready (nonemptyMap.trans slots) base q := {
    boundWord := ready.source
    remainingEmpty := ready.empty 1 (by decide) (by decide) (by decide)
    currentEmpty := ready.empty 3 (by decide) (by decide) (by decide)
    scratchEmpty := ready.empty 5 (by decide) (by decide) (by decide)
    closureEmpty := ready.empty 9 (by decide) (by decide) (by decide) }
  have hn := Nonempty.trace (nonemptyMap.trans slots) (fun l => labels (.nonempty l))
    (some (labels (.clash .start))) program (fun _ => atLabels _) base q nr ambient
  let afterNonempty := emitted (slots 7) (slots 8) base (nonemptyTokens q)
  change (advance (TM2.step program))^[Nonempty.steps q]
    (some ⟨some (labels (.nonempty .initialize)), clean ambient, base⟩) =
    some ⟨some (labels (.clash .start)), clean ambient, afterNonempty⟩ at hn
  have hc := ClashMachine.Full.trace slots (fun l => labels (.clash l))
    (some (labels .finish)) program (fun _ => atLabels _)
    afterNonempty q (ready.emitted (nonemptyTokens q)) ambient
  let afterClash := emitted (slots 7) (slots 8) afterNonempty (clashTokens q)
  have hf : (advance (TM2.step program))^[1]
      (some ⟨some (labels .finish), clean ambient, afterClash⟩) =
      some ⟨exit, clean ambient, emitted (slots 7) (slots 8) afterClash [.not, .and]⟩ := by
    change some (TM2.stepAux (program (labels .finish)) _ _) = _
    rw [atLabels, statement, ClashMachine.stepAux_literal (slots 7) (slots 8)
      (slots.injective.ne (by decide : (7 : Fin 10) ≠ 8))]
    cases exit <;> rfl
  have h := chain (chain hn hc) hf
  simpa only [steps, afterClash, afterNonempty,
    ClashMachine.emitted_append (slots 7) (slots 8)
      (slots.injective.ne (by decide : (7 : Fin 10) ≠ 8)), validityTokens] using h

def inTime (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (ValidityMachine.Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (q : Nat) (ready : ClashMachine.Full.Ready slots base q) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.nonempty .initialize)), clean ambient, base⟩
      (some ⟨exit, clean ambient, emitted (slots 7) (slots 8) base (validityTokens q)⟩)
      (timePolynomial.eval q) where
  steps := steps q
  evals_in_steps := by
    change (advance (TM2.step program))^[steps q] _ = _
    exact trace slots labels exit program atLabels base q ready ambient
  steps_le_m := steps_le_time q

section FiniteMachine

variable [Fintype K] [Fintype σ]

def machine (slots : Fin 10 ↪ K) (ambient : σ) : FinTM2 where
  K := K
  k₀ := slots 0
  k₁ := slots 7
  Γ := ValidityMachine.Alphabet
  Λ := Label
  main := .nonempty .initialize
  σ := State σ
  initialState := clean ambient
  Γk₀Fin := inferInstance
  m := statement slots id none

theorem machineTrace (slots : Fin 10 ↪ K) (base : K → List Bool) (q : Nat)
    (ready : ClashMachine.Full.Ready slots base q) (ambient : σ) :
    (advance (machine slots ambient).step)^[steps q]
      (some ⟨some (.nonempty .initialize), clean ambient, base⟩) =
      some ⟨none, clean ambient, emitted (slots 7) (slots 8) base (validityTokens q)⟩ := by
  exact trace slots id none (machine slots ambient).m (fun _ => rfl) base q ready ambient

def machineInTime (slots : Fin 10 ↪ K) (base : K → List Bool) (q : Nat)
    (ready : ClashMachine.Full.Ready slots base q) (ambient : σ) :
    StateTransition.EvalsToInTime (machine slots ambient).step
      ⟨some (.nonempty .initialize), clean ambient, base⟩
      (some ⟨none, clean ambient, emitted (slots 7) (slots 8) base (validityTokens q)⟩)
      (timePolynomial.eval q) :=
  inTime slots id none (machine slots ambient).m (fun _ => rfl) base q ready ambient

end FiniteMachine

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.ValidityMachine.Full

end OAI
