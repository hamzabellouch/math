import Mathlib
import OAI.Computability.MinUncut.Machines.MachineFiniteSequence

namespace OAI

namespace MinUncutGames.Foundations.Hastad.SourceRuntimeFinish

open Turing Complexity

variable {K Λ σ : Type} [DecidableEq K]

abbrev Label (clearKeys : List K) := MachineDrainMany.Label clearKeys ⊕ Bool
abbrev Tapes (K : Type) := K → List Bool

def entry (clearKeys : List K) (labels : Label clearKeys → Λ) : Option Λ :=
  MachineDrainMany.entry clearKeys (fun l => labels (.inl l)) (some (labels (.inr false)))

def statement (clearKeys : List K) (accumulator output : K) (canonical : σ)
    (labels : Label clearKeys → Λ) (exit : Option Λ) :
    Label clearKeys → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .inl label => MachineDrainMany.instruction clearKeys (fun l => labels (.inl l))
      (some (labels (.inr false))) label
  | .inr false => Reduction.MachineTransfer.loopAt accumulator output id false
      (labels (.inr false)) (some (labels (.inr true)))
  | .inr true => .load (fun _ => (canonical, none)) (Reduction.MachineTransfer.exitAt output exit)

def canonicalTapes (output : K) (word : List Bool) : Tapes K :=
  Function.update (fun _ => []) output word

def finishCost (clearKeys : List K) (accumulator : K) (base : Tapes K) : Nat :=
  MachineDrainMany.steps clearKeys base + (base accumulator).length + 2

theorem cleared_frame (clearKeys : List K) (base : Tapes K) (tape : K)
    (h : tape ∉ clearKeys) : MachineDrainMany.finalTapes clearKeys base tape = base tape :=
  MachineDrainMany.finalTapes_not_mem clearKeys base tape h

theorem reversed_tapes (clearKeys : List K) (accumulator output : K)
    (distinct : accumulator ≠ output)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : Tapes K) :
    Reduction.MachineTransfer.tapesAt accumulator output
      (MachineDrainMany.finalTapes clearKeys base) [] (base accumulator).reverse =
      canonicalTapes output (base accumulator).reverse := by
  funext k
  by_cases hout : k = output
  · subst k
    simp [Reduction.MachineTransfer.tapesAt, canonicalTapes]
  · by_cases hacc : k = accumulator
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, canonicalTapes, distinct]
    · have hclear := MachineDrainMany.finalTapes_mem clearKeys base k (covers k hacc hout)
      simp [Reduction.MachineTransfer.tapesAt, canonicalTapes, hout, hacc, hclear]

def finishInTime (clearKeys : List K) (accumulator output : K)
    (distinct : accumulator ≠ output)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (canonical : σ) (labels : Label clearKeys → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ label,
      program (labels label) = statement clearKeys accumulator output canonical labels exit label)
    (base : Tapes K) (outputEmpty : base output = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry clearKeys labels, (ambient, register), base⟩
      (some ⟨exit, (canonical, none), canonicalTapes output (base accumulator).reverse⟩)
      (finishCost clearKeys accumulator base) := by
  let cleared := MachineDrainMany.finalTapes clearKeys base
  let afterRegister := MachineDrainMany.finalRegister clearKeys register
  let drain : StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry clearKeys labels, (ambient, register), base⟩
      (some ⟨some (labels (.inr false)), (ambient, afterRegister), cleared⟩)
      (MachineDrainMany.steps clearKeys base) := {
    steps := MachineDrainMany.steps clearKeys base
    evals_in_steps := MachineDrainMany.trace clearKeys (fun l => labels (.inl l))
      (some (labels (.inr false))) program (fun l => atLabels (.inl l)) base ambient register
    steps_le_m := Nat.le_refl _ }
  have acc : cleared accumulator = base accumulator := cleared_frame _ _ _ keepAccumulator
  have out : cleared output = [] := (cleared_frame _ _ _ keepOutput).trans outputEmpty
  let reverse : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inr false)), (ambient, afterRegister), cleared⟩
      (some ⟨some (labels (.inr true)), (ambient, none),
        canonicalTapes output (base accumulator).reverse⟩) ((base accumulator).length + 1) := {
    steps := (base accumulator).length + 1
    evals_in_steps := by
      change (Reduction.MachineTransfer.nextAt output program)^[(base accumulator).length + 1]
        (some ⟨some (labels (.inr false)), (ambient, afterRegister), cleared⟩) = _
      have run := Reduction.MachineTransfer.transferAt_fromTapes (Γ := fun _ : K => Bool)
        accumulator output distinct id false (labels (.inr false))
        (some (labels (.inr true))) program
        (by simpa only [statement] using atLabels (.inr false)) cleared ambient afterRegister
      simpa only [acc, out, List.map_id, List.append_nil,
        cleared, reversed_tapes clearKeys accumulator output distinct covers base] using run
    steps_le_m := Nat.le_refl _ }
  let reset : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inr true)), (ambient, none), canonicalTapes output (base accumulator).reverse⟩
      (some ⟨exit, (canonical, none), canonicalTapes output (base accumulator).reverse⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change some (TM2.stepAux (program (labels (.inr true))) _ _) = _
      rw [atLabels]
      cases exit <;> rfl
    steps_le_m := Nat.le_refl _ }
  let first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ drain reverse
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first reset
  have hsteps : run.steps = finishCost clearKeys accumulator base := by
    change 1 + ((base accumulator).length + 1 + MachineDrainMany.steps clearKeys base) = _
    unfold finishCost
    omega
  exact {
    steps := finishCost clearKeys accumulator base
    evals_in_steps := by simpa only [hsteps] using run.evals_in_steps
    steps_le_m := Nat.le_refl _ }

theorem finishCost_le_list (clearKeys : List K) (accumulator : K) (base : Tapes K) :
    finishCost clearKeys accumulator base ≤ MachineDrainMany.lengthSum clearKeys base +
      clearKeys.length + (base accumulator).length + 2 := by
  have h := MachineDrainMany.steps_le clearKeys base
  unfold finishCost
  omega

variable [Fintype K]
open scoped BigOperators

def totalLength (base : Tapes K) : Nat := ∑ k, (base k).length

theorem totalLength_erase (base : Tapes K) (source : K) :
    totalLength (Function.update base source []) + (base source).length = totalLength base := by
  calc
    _ = ∑ k, (((Function.update base source []) k).length +
        if k = source then (base source).length else 0) := by
      simp [totalLength, Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : k = source
      · subst k
        simp
      · simp [h]

theorem drain_conservation (clearKeys : List K) (base : Tapes K) :
    MachineDrainMany.steps clearKeys base +
      totalLength (MachineDrainMany.finalTapes clearKeys base) =
        totalLength base + clearKeys.length := by
  induction clearKeys generalizing base with
  | nil => simp [MachineDrainMany.steps, MachineDrainMany.finalTapes]
  | cons source rest ih =>
      have h := ih (Function.update base source [])
      have erase := totalLength_erase base source
      simp only [MachineDrainMany.steps, MachineDrainMany.finalTapes, List.length_cons]
      omega

theorem cleared_totalLength (clearKeys : List K) (accumulator output : K)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : Tapes K) (outputEmpty : base output = []) :
    totalLength (MachineDrainMany.finalTapes clearKeys base) = (base accumulator).length := by
  have point (k : K) : (MachineDrainMany.finalTapes clearKeys base k).length =
      if k = accumulator then (base accumulator).length else 0 := by
    by_cases ha : k = accumulator
    · subst k
      simp [cleared_frame clearKeys base accumulator keepAccumulator]
    · by_cases ho : k = output
      · subst k
        simp [ha, cleared_frame clearKeys base output keepOutput, outputEmpty]
      · rw [MachineDrainMany.finalTapes_mem clearKeys base k (covers k ha ho)]
        simp [ha]
  simp only [totalLength, point]
  simp

theorem finishCost_eq_totalLength (clearKeys : List K) (accumulator output : K)
    (keepAccumulator : accumulator ∉ clearKeys) (keepOutput : output ∉ clearKeys)
    (covers : ∀ k, k ≠ accumulator → k ≠ output → k ∈ clearKeys)
    (base : Tapes K) (outputEmpty : base output = []) :
    finishCost clearKeys accumulator base = totalLength base + clearKeys.length + 2 := by
  have h := drain_conservation clearKeys base
  rw [cleared_totalLength clearKeys accumulator output keepAccumulator keepOutput covers
    base outputEmpty] at h
  unfold finishCost
  omega

end MinUncutGames.Foundations.Hastad.SourceRuntimeFinish

end OAI
