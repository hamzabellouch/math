import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.RawInitialMachineBudget
import OAI.Combinatorics.IndependentSets.Machines.MachineComposition

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineUnaryCounter

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def guard (counter : K) (bodyLabel exitLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .peek counter (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.pop counter (fun state _ => (state.1, none)) (.goto fun _ => bodyLabel))
      (.load (fun state => (state.1, none)) (.goto fun _ => exitLabel)))

def counterTapes (counter : K) (base : K → List Bool) (n : Nat)
    (suffix : List Bool) : K → List Bool :=
  Function.update base counter (encodeWord n ++ suffix)

@[simp] theorem counterTapes_counter (counter : K) (base : K → List Bool)
    (n : Nat) (suffix : List Bool) :
    counterTapes counter base n suffix counter = encodeWord n ++ suffix := by
  simp [counterTapes]

theorem counterTapes_other (counter other : K) (hne : other ≠ counter)
    (base : K → List Bool) (n : Nat) (suffix : List Bool) :
    counterTapes counter base n suffix other = base other := by
  simp [counterTapes, hne]

omit [DecidableEq K] in
theorem guardPushBound (counter : K) (bodyLabel exitLabel : Λ) :
    Runtime.statementPushBound (guard (σ := σ) counter bodyLabel exitLabel) = 0 := by
  rfl

theorem stepAux_succ (counter : K) (bodyLabel exitLabel : Λ)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (guard counter bodyLabel exitLabel) (ambient, register)
      (counterTapes counter base (n + 1) suffix) =
      ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩ := by
  simp [guard, TM2.stepAux, counterTapes, encodeWord, List.replicate_succ]

theorem stepAux_zero (counter : K) (bodyLabel exitLabel : Λ)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (guard counter bodyLabel exitLabel) (ambient, register)
      (counterTapes counter base 0 suffix) =
      ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩ := by
  simp [guard, TM2.stepAux, counterTapes, encodeWord]

theorem guardStep_succ (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some guardLabel, (ambient, register), counterTapes counter base (n + 1) suffix⟩ =
      some ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩ := by
  change some (TM2.stepAux (program guardLabel) (ambient, register)
    (counterTapes counter base (n + 1) suffix)) = _
  rw [atGuard, stepAux_succ]

theorem guardStep_zero (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program
      ⟨some guardLabel, (ambient, register), counterTapes counter base 0 suffix⟩ =
      some ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩ := by
  change some (TM2.stepAux (program guardLabel) (ambient, register)
    (counterTapes counter base 0 suffix)) = _
  rw [atGuard, stepAux_zero]

theorem guardTrace_succ (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some guardLabel, (ambient, register),
        counterTapes counter base (n + 1) suffix⟩) =
      some ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩ := by
  simpa only [Function.iterate_one, MachineComposition.advance_some] using
    guardStep_succ counter guardLabel bodyLabel exitLabel program atGuard
      base n suffix ambient register

theorem guardTrace_zero (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some guardLabel, (ambient, register), counterTapes counter base 0 suffix⟩) =
      some ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩ := by
  simpa only [Function.iterate_one, MachineComposition.advance_some] using
    guardStep_zero counter guardLabel bodyLabel exitLabel program atGuard
      base suffix ambient register

def guardInTime_succ (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, (ambient, register), counterTapes counter base (n + 1) suffix⟩
      (some ⟨some bodyLabel, (ambient, none), counterTapes counter base n suffix⟩) 1 where
  steps := 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[1] _ = _
    exact guardTrace_succ counter guardLabel bodyLabel exitLabel program atGuard
      base n suffix ambient register
  steps_le_m := Nat.le_refl _

def guardInTime_zero (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, (ambient, register), counterTapes counter base 0 suffix⟩
      (some ⟨some exitLabel, (ambient, none), counterTapes counter base 0 suffix⟩) 1 where
  steps := 1
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[1] _ = _
    exact guardTrace_zero counter guardLabel bodyLabel exitLabel program atGuard
      base suffix ambient register
  steps_le_m := Nat.le_refl _

end IndependentSetsGames.Foundations.Complexity.MachineUnaryCounter

end OAI
