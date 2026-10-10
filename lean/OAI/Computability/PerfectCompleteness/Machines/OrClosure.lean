import OAI.Computability.PerfectCompleteness.Machines.PositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Reduction.MachineSubstitution
import OAI.Computability.UniqueGames.Reduction.MachineTransfer

namespace OAI


namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure

open Turing PostfixModel InitializationTemplate
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)


variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

structure Ports (K : Type) where
  remaining : K
  reversed : K
  count : K
  remaining_ne_reversed : remaining ≠ reversed
  remaining_ne_count : remaining ≠ count
  reversed_ne_count : reversed ≠ count

def frame (ports : Ports K) (base : K → List Bool)
    (remaining reversed count : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base ports.remaining remaining)
    ports.reversed reversed) ports.count count

@[simp] theorem frame_remaining (p : Ports K) (base : K → List Bool)
    (remaining reversed count : List Bool) :
    frame p base remaining reversed count p.remaining = remaining := by
  simp [frame, p.remaining_ne_count, p.remaining_ne_reversed]

@[simp] theorem frame_reversed (p : Ports K) (base : K → List Bool)
    (remaining reversed count : List Bool) :
    frame p base remaining reversed count p.reversed = reversed := by
  simp [frame, p.reversed_ne_count]

@[simp] theorem frame_count (p : Ports K) (base : K → List Bool)
    (remaining reversed count : List Bool) :
    frame p base remaining reversed count p.count = count := by
  simp [frame]

theorem frame_other (p : Ports K) (base : K → List Bool)
    (remaining reversed count : List Bool) (k : K)
    (hr : k ≠ p.remaining) (ho : k ≠ p.reversed) (hc : k ≠ p.count) :
    frame p base remaining reversed count k = base k := by
  simp [frame, hr, ho, hc]

@[simp] theorem frame_self (p : Ports K) (base : K → List Bool) :
    frame p base (base p.remaining) (base p.reversed) (base p.count) = base := by
  simp [frame]

@[simp] theorem update_remaining (p : Ports K) (base : K → List Bool)
    (remaining reversed count replacement : List Bool) :
    Function.update (frame p base remaining reversed count) p.remaining replacement =
      frame p base replacement reversed count := by
  funext k
  by_cases hr : k = p.remaining <;> by_cases ho : k = p.reversed <;>
    by_cases hc : k = p.count <;>
    simp_all [frame, p.remaining_ne_reversed, p.remaining_ne_count, p.reversed_ne_count,
      Ne.symm p.remaining_ne_reversed, Ne.symm p.remaining_ne_count, Ne.symm p.reversed_ne_count]

@[simp] theorem update_reversed (p : Ports K) (base : K → List Bool)
    (remaining reversed count replacement : List Bool) :
    Function.update (frame p base remaining reversed count) p.reversed replacement =
      frame p base remaining replacement count := by
  funext k
  by_cases hr : k = p.remaining <;> by_cases ho : k = p.reversed <;>
    by_cases hc : k = p.count <;>
    simp_all [frame, p.remaining_ne_reversed, p.remaining_ne_count, p.reversed_ne_count,
      Ne.symm p.remaining_ne_reversed, Ne.symm p.remaining_ne_count, Ne.symm p.reversed_ne_count]

@[simp] theorem update_count (p : Ports K) (base : K → List Bool)
    (remaining reversed count replacement : List Bool) :
    Function.update (frame p base remaining reversed count) p.count replacement =
      frame p base remaining reversed replacement := by
  simp [frame]

def seed (p : Ports K) (again : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .push p.reversed (fun _ => false)
    (.push p.count (fun _ => true)
      (.load (fun state => (state.1, none)) (.goto fun _ => again)))

def loop (p : Ports K) (again : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop p.remaining (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (pushWord p.reversed (encodeWord 4)
        (.push p.count (fun _ => true)
          (.load (fun state => (state.1, none)) (.goto fun _ => again))))
      (.push p.remaining (fun _ => false)
        (.load (fun state => (state.1, none))
          (Reduction.MachineTransfer.exitAt p.remaining exit))))

omit [DecidableEq K] in
theorem seedPushBound (p : Ports K) (again : Λ) :
    Runtime.statementPushBound (seed (σ := σ) p again) = 2 := rfl

omit [DecidableEq K] in
theorem loopPushBound (p : Ports K) (again : Λ) (exit : Option Λ) :
    Runtime.statementPushBound (loop (σ := σ) p again exit) = 6 := by
  cases exit <;> rfl

theorem seedStep (p : Ports K) (again : Λ) (base : K → List Bool)
    (remaining output count : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (seed p again) (ambient, register)
      (frame p base remaining output count) =
      ⟨some again, (ambient, none),
        frame p base remaining (false :: output) (true :: count)⟩ := by
  simp [seed, TM2.stepAux]

theorem loopStep_zero (p : Ports K) (again : Λ) (exit : Option Λ)
    (base : K → List Bool) (suffix output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop p again exit) (ambient, register)
      (frame p base (encodeWord 0 ++ suffix) output count) =
      ⟨exit, (ambient, none), frame p base (encodeWord 0 ++ suffix) output count⟩ := by
  cases exit <;>
    simp [loop, TM2.stepAux, encodeWord, Reduction.MachineTransfer.exitAt]

theorem loopStep_succ (p : Ports K) (again : Λ) (exit : Option Λ)
    (base : K → List Bool) (n : Nat) (suffix output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop p again exit) (ambient, register)
      (frame p base (encodeWord (n + 1) ++ suffix) output count) =
      ⟨some again, (ambient, none),
        frame p base (encodeWord n ++ suffix)
          ((encodeWord 4).reverse ++ output) (true :: count)⟩ := by
  simp [loop, TM2.stepAux, stepAux_pushWord, encodeWord, List.replicate_succ]

theorem tokenBits_append (first second : List Token) :
    tokenBits (first ++ second) = tokenBits first ++ tokenBits second := by
  simp [tokenBits, tokenWords, encodeWords_append]

@[simp] theorem tokenBits_or : tokenBits [Token.or] = encodeWord 4 := rfl

@[simp] theorem tokenBits_false : tokenBits [Token.const false] = [false] := rfl

theorem tokenBits_closeOr (n : Nat) :
    tokenBits (closeOr n) = [false] ++ tokenBits (List.replicate n Token.or) := by
  unfold closeOr
  rw [tokenBits_append, tokenBits_false]

theorem tokenBits_replicate_succ (n : Nat) :
    tokenBits (List.replicate (n + 1) Token.or) =
      encodeWord 4 ++ tokenBits (List.replicate n Token.or) := by
  rw [List.replicate_succ]
  change tokenBits ([Token.or] ++ List.replicate n Token.or) = _
  rw [tokenBits_append, tokenBits_or]

private theorem replicate_push (n : Nat) (count : List Bool) :
    List.replicate n true ++ true :: count =
      List.replicate (n + 1) true ++ count := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [List.replicate_succ, List.cons_append] using (congrArg (List.cons true) ih)

theorem loopTrace (p : Ports K) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program again = loop p again exit)
    (base : K → List Bool) (n : Nat) (suffix output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (ambient, register),
        frame p base (encodeWord n ++ suffix) output count⟩) =
      some ⟨exit, (ambient, none),
        frame p base (encodeWord 0 ++ suffix)
          ((tokenBits (List.replicate n Token.or)).reverse ++ output)
          (List.replicate n true ++ count)⟩ := by
  induction n generalizing output count register with
  | zero =>
      change some (TM2.stepAux (program again) (ambient, register)
        (frame p base (encodeWord 0 ++ suffix) output count)) = _
      rw [atLoop, loopStep_zero]
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[n + 1]
        (some (TM2.stepAux (program again) (ambient, register)
          (frame p base (encodeWord (n + 1) ++ suffix) output count))) = _
      rw [atLoop, loopStep_succ, ih]
      simp only [tokenBits_replicate_succ, List.reverse_append, List.append_assoc]
      rw [replicate_push]

theorem closureTrace (p : Ports K) (entry again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atSeed : program entry = seed p again)
    (atLoop : program again = loop p again exit)
    (base : K → List Bool) (n : Nat) (suffix output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some entry, (ambient, register),
        frame p base (encodeWord n ++ suffix) output count⟩) =
      some ⟨exit, (ambient, none),
        frame p base (encodeWord 0 ++ suffix)
          ((tokenBits (closeOr n)).reverse ++ output)
          (List.replicate (n + 1) true ++ count)⟩ := by
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step program))^[n + 1]
    (some (TM2.stepAux (program entry) (ambient, register)
      (frame p base (encodeWord n ++ suffix) output count))) = _
  rw [atSeed, seedStep, loopTrace p again exit program atLoop]
  simp only [tokenBits_closeOr, List.singleton_append, List.reverse_cons, List.append_assoc]
  rw [replicate_push]

def closureInTime (p : Ports K) (entry again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atSeed : program entry = seed p again)
    (atLoop : program again = loop p again exit)
    (base : K → List Bool) (n : Nat) (suffix output count : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some entry, (ambient, register), frame p base (encodeWord n ++ suffix) output count⟩
      (some ⟨exit, (ambient, none),
        frame p base (encodeWord 0 ++ suffix)
          ((tokenBits (closeOr n)).reverse ++ output)
          (List.replicate (n + 1) true ++ count)⟩) (n + 2) where
  steps := n + 2
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[n + 2] _ = _
    exact closureTrace p entry again exit program atSeed atLoop
      base n suffix output count ambient register
  steps_le_m := Nat.le_refl _

theorem increment_count (n c : Nat) (suffix : List Bool) :
    List.replicate (n + 1) true ++ (encodeWord c ++ suffix) =
      encodeWord (c + n + 1) ++ suffix := by
  simp only [encodeWord, ← List.append_assoc, List.replicate_append_replicate]
  rw [show n + 1 + c = c + n + 1 by omega]

section FiniteMachine

variable [Fintype K] [Fintype σ]

def machine (p : Ports K) (ambient : σ) : FinTM2 where
  K := K
  k₀ := p.remaining
  k₁ := p.reversed
  Γ := Alphabet
  Λ := Bool
  main := false
  σ := σ × Option Bool
  initialState := (ambient, none)
  Γk₀Fin := inferInstance
  m label := if label then loop p true none else seed p true

theorem machineTrace (p : Ports K) (base : K → List Bool) (n : Nat)
    (suffix output count : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (machine p ambient).step)^[n + 2]
      (some ⟨some false, (ambient, register),
        frame p base (encodeWord n ++ suffix) output count⟩) =
      some ⟨none, (ambient, none),
        frame p base (encodeWord 0 ++ suffix)
          ((tokenBits (closeOr n)).reverse ++ output)
          (List.replicate (n + 1) true ++ count)⟩ := by
  exact closureTrace p false true none (machine p ambient).m rfl rfl
    base n suffix output count ambient register

end FiniteMachine

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.OrClosure

end OAI
