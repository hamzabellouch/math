import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineSubstitution
import OAI.Computability.DirectedFeedback.Machines.MachineTransducer
import OAI.Computability.DirectedFeedback.Games.Target

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceRuntimeFinish

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


end DFVSGames.Foundations.Hastad.SourceRuntimeFinish


namespace DFVSGames.Foundations.Complexity.MachineUnaryAffineAt

open Turing
open MachineComposition
open Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (restoreLabel : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun s => (s.1,none)) (.goto (fun _ => restoreLabel))

def scan (source scratch destination : K) (coefficient : Nat) (scanLabel restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun s head => (s.1,head))
    (.branch (fun s => s.2.getD false)
      (.push scratch (fun _ => true)
        (pushWord destination (List.replicate coefficient true) (.goto (fun _ => scanLabel))))
      (.branch (fun s => s.2.isSome)
        (.push source (fun _ => false) (finish restoreLabel))
        (finish restoreLabel)))

def seed (destination : K) (offset : Nat) (scanLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  pushWord destination (encodeWord offset).reverse (.goto (fun _ => scanLabel))

def tapes (source scratch destination : K) (base : K → List Bool)
    (input saved output : List Bool) : K → List Bool :=
  MachineCopy.forkTapes source scratch destination base input saved output

@[simp] theorem tapes_source (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output source = input :=
  MachineCopy.forkTapes_source source scratch destination hs hd base input saved output

@[simp] theorem tapes_scratch (source scratch destination : K) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output scratch = saved :=
  MachineCopy.forkTapes_left source scratch destination hsd base input saved output

@[simp] theorem tapes_destination (source scratch destination : K)
    (base : K → List Bool) (input saved output : List Bool) :
    tapes source scratch destination base input saved output destination = output :=
  MachineCopy.forkTapes_right source scratch destination base input saved output

private theorem update_source_inline_MachineUnaryAffineAt (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) source replacement =
      tapes source scratch destination base replacement saved output := by
  funext k
  by_cases h₀ : k = source
  · subst k; simp [tapes, MachineCopy.forkTapes, hs, hd]
  · by_cases h₁ : k = scratch
    · subst k; simp [tapes, MachineCopy.forkTapes, h₀, hsd]
    · by_cases h₂ : k = destination
      · subst k; simp [tapes, MachineCopy.forkTapes, h₀]
      · simp [tapes, MachineCopy.forkTapes, h₀, h₁, h₂]

private theorem update_scratch_inline_MachineUnaryAffineAt (source scratch destination : K) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) scratch replacement =
      tapes source scratch destination base input replacement output := by
  funext k
  by_cases h : k = scratch
  · subst k; simp [tapes, MachineCopy.forkTapes, hsd]
  · by_cases h' : k = destination
    · subst k; simp [tapes, MachineCopy.forkTapes, h]
    · simp [tapes, MachineCopy.forkTapes, h, h']

private theorem update_destination_inline_MachineUnaryAffineAt (source scratch destination : K)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) destination replacement =
      tapes source scratch destination base input saved replacement := by
  simp [tapes, MachineCopy.forkTapes]

theorem prepend_replicate_word (c b : Nat) (suffix : List Bool) :
    List.replicate c true ++ (encodeWord b ++ suffix) =
      encodeWord (c + b) ++ suffix := by
  simp only [encodeWord, List.replicate_add, List.append_assoc]

theorem scan_step_succ (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (suffix saved output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, (ambient,register), tapes source scratch destination base
      (encodeWord (a + 1) ++ suffix) saved (encodeWord b ++ output)⟩ =
      some ⟨some scanLabel, (ambient,some true), tapes source scratch destination base
        (encodeWord a ++ suffix) (true :: saved) (encodeWord (coefficient + b) ++ output)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  rw [show encodeWord (a + 1) ++ suffix = true :: (encodeWord a ++ suffix) by
    simp [encodeWord, List.replicate_succ]]
  simp [scan, TM2.stepAux, tapes_source _ _ _ hs hd,
    update_source_inline_MachineUnaryAffineAt source scratch destination hs hd hsd, tapes_scratch _ _ _ hsd,
    update_scratch_inline_MachineUnaryAffineAt _ _ _ hsd, stepAux_pushWord, tapes_destination,
    prepend_replicate_word, update_destination_inline_MachineUnaryAffineAt]

theorem scan_step_zero (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (base : K → List Bool) (b : Nat) (suffix saved output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, (ambient,register), tapes source scratch destination base
      (encodeWord 0 ++ suffix) saved (encodeWord b ++ output)⟩ =
      some ⟨some restoreLabel, (ambient,none), tapes source scratch destination base
        (encodeWord 0 ++ suffix) saved (encodeWord b ++ output)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  rw [show encodeWord 0 ++ suffix = false :: suffix from rfl]
  simp [scan, finish, TM2.stepAux, tapes_source _ _ _ hs hd,
    update_source_inline_MachineUnaryAffineAt source scratch destination hs hd hsd]

theorem scanTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (suffix saved output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[a + 1]
      (some ⟨some scanLabel, (ambient,register), tapes source scratch destination base
        (encodeWord a ++ suffix) saved (encodeWord b ++ output)⟩) =
      some ⟨some restoreLabel, (ambient,none), tapes source scratch destination base
        (encodeWord 0 ++ suffix) (List.replicate a true ++ saved)
        (encodeWord (coefficient * a + b) ++ output)⟩ := by
  induction a generalizing b saved register with
  | zero =>
      simpa using scan_step_zero source scratch destination hs hd hsd coefficient scanLabel
        restoreLabel program atScan base b suffix saved output ambient register
  | succ a ih =>
      rw [Function.iterate_succ_apply]
      simp only [advance_some]
      rw [scan_step_succ source scratch destination hs hd hsd coefficient scanLabel restoreLabel
        program atScan]
      rw [ih]
      have hval : coefficient * a + (coefficient + b) = coefficient * (a + 1) + b := by
        rw [Nat.mul_succ]; omega
      rw [hval]
      have hsave : List.replicate a true ++ true :: saved = List.replicate (a + 1) true ++ saved := by
        simp only [List.replicate_add, List.replicate_one, List.append_assoc, List.singleton_append]
      rw [hsave]

theorem restoreTapes (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (base : K → List Bool) (a value : Nat) (suffix output : List Bool) :
    Reduction.MachineTransfer.tapesAt scratch source
      (tapes source scratch destination base (encodeWord 0 ++ suffix)
        (List.replicate a true) (encodeWord value ++ output))
      [] (encodeWord a ++ suffix) =
      tapes source scratch destination base (encodeWord a ++ suffix) [] (encodeWord value ++ output) := by
  funext k
  by_cases h₀ : k = source
  · subst k; simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, hs, hd]
  · by_cases h₁ : k = scratch
    · subst k
      simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, Ne.symm hs, hsd]
    · by_cases h₂ : k = destination
      · subst k
        simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, Ne.symm hd, Ne.symm hsd]
      · simp [tapes, MachineCopy.forkTapes, Reduction.MachineTransfer.tapesAt, h₀, h₁, h₂]

theorem affineTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (atRestore : program restoreLabel = Reduction.MachineTransfer.loopAt
      scratch source id false restoreLabel exit)
    (base : K → List Bool) (a b : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (a + 1)]
      (some ⟨some scanLabel, (ambient,register), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord b ++ output)⟩) =
      some ⟨exit, (ambient,none), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord (coefficient * a + b) ++ output)⟩ := by
  have hscan := scanTrace source scratch destination hs hd hsd coefficient scanLabel restoreLabel
    program atScan base a b suffix [] output ambient register
  simp only [List.append_nil] at hscan
  let mid := tapes source scratch destination base (encodeWord 0 ++ suffix)
    (List.replicate a true) (encodeWord (coefficient * a + b) ++ output)
  have hrestore := Reduction.MachineTransfer.transferAt_fromTapes scratch source (Ne.symm hs)
    id false restoreLabel exit program atRestore mid ambient none
  change (advance (TM2.step program))^[(mid scratch).length + 1]
    (some ⟨some restoreLabel,(ambient,none),mid⟩) = _ at hrestore
  have hsaved : mid scratch = List.replicate a true := by
    simp [mid, tapes, hsd]
  have hsource : mid source = encodeWord 0 ++ suffix := by
    simp [mid, tapes, hs, hd]
  rw [hsaved, hsource] at hrestore
  simp only [List.length_replicate, List.reverse_replicate, List.map_id] at hrestore
  have hword : List.replicate a true ++ (encodeWord 0 ++ suffix) = encodeWord a ++ suffix := by
    simp [encodeWord, List.append_assoc]
  rw [hword] at hrestore
  simp only [mid, restoreTapes source scratch destination hs hd hsd] at hrestore
  rw [show 2 * (a + 1) = (a + 1) + (a + 1) by omega, Function.iterate_add_apply, hscan]
  exact hrestore

def affineInTime (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient : Nat) (scanLabel restoreLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (atRestore : program restoreLabel = Reduction.MachineTransfer.loopAt
      scratch source id false restoreLabel exit)
    (base : K → List Bool) (a b : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some scanLabel, (ambient,register), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord b ++ output)⟩
      (some ⟨exit, (ambient,none), tapes source scratch destination base
        (encodeWord a ++ suffix) [] (encodeWord (coefficient * a + b) ++ output)⟩)
      (2 * (a + 1)) where
  steps := 2 * (a + 1)
  evals_in_steps := affineTrace source scratch destination hs hd hsd coefficient scanLabel
    restoreLabel exit program atScan atRestore base a b suffix output ambient register
  steps_le_m := Nat.le_refl _

theorem seededAffineTrace (source scratch destination : K)
    (hs : source ≠ scratch) (hd : source ≠ destination) (hsd : scratch ≠ destination)
    (coefficient offset : Nat) (seedLabel scanLabel restoreLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atSeed : program seedLabel = seed destination offset scanLabel)
    (atScan : program scanLabel = scan source scratch destination coefficient scanLabel restoreLabel)
    (atRestore : program restoreLabel = Reduction.MachineTransfer.loopAt
      scratch source id false restoreLabel exit)
    (base : K → List Bool) (a : Nat) (suffix : List Bool)
    (sourceWord : base source = encodeWord a ++ suffix) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * (a + 1) + 1]
      (some ⟨some seedLabel, (ambient,register), base⟩) =
      some ⟨exit, (ambient,none),
        Function.update base destination (encodeWord (coefficient * a + offset) ++ base destination)⟩ := by
  have hseed : TM2.step program ⟨some seedLabel,(ambient,register),base⟩ =
      some ⟨some scanLabel,(ambient,register),
        Function.update base destination (encodeWord offset ++ base destination)⟩ := by
    change some (TM2.stepAux (program seedLabel) _ _) = _
    rw [atSeed, seed, stepAux_pushWord]
    simp only [List.reverse_reverse, TM2.stepAux]
  have hrun := affineTrace source scratch destination hs hd hsd coefficient scanLabel restoreLabel
    exit program atScan atRestore base a offset suffix (base destination) ambient register
  have hframe (word : List Bool) :
      tapes source scratch destination base (encodeWord a ++ suffix) [] word =
        Function.update base destination word := by
    rw [← sourceWord, ← scratchEmpty]
    simp only [tapes, MachineCopy.forkTapes, Function.update_eq_self]
  rw [hframe, hframe] at hrun
  rw [Function.iterate_succ_apply]
  simp only [advance_some]
  rw [hseed]
  exact hrun

inductive Label
  | seed | scan | restore
  deriving DecidableEq

instance instFintypeLabel : Fintype Label :=
  Fintype.ofList [.seed, .scan, .restore] (by
    intro label
    cases label <;> simp)

def program (source scratch destination : K) (coefficient offset : Nat) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool)
  | .seed => seed destination offset .scan
  | .scan => scan source scratch destination coefficient .scan .restore
  | .restore => Reduction.MachineTransfer.loopAt scratch source id false .restore none

def machine (coefficient offset : Nat) : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Label
  main := .seed
  σ := Unit × Option Bool
  initialState := ((),none)
  m := program 0 1 2 coefficient offset

end DFVSGames.Foundations.Complexity.MachineUnaryAffineAt


namespace DFVSGames.Explicit.MachineUniformProgram

open Turing DFVSGames.Reduction
open DFVSGames.Foundations.Complexity DFVSGames.Foundations.Hastad

inductive Tape
  | input | vertices | alphabet | occurrences | newOccurrences
  | affineScratch | copyScratch | accumulator | output
  deriving DecidableEq

instance instFintypeTape : Fintype Tape :=
  Fintype.ofList [.input, .vertices, .alphabet, .occurrences, .newOccurrences,
    .affineScratch, .copyScratch, .accumulator, .output] (by
    intro tape
    cases tape <;> simp)

abbrev State := MachineFieldTemplate.State Unit

def initialState : State := (((), ()), none)

def headerField : Fin 3 → Tape
  | 0 => .vertices
  | 1 => .alphabet
  | 2 => .occurrences

def emitField : Fin 4 → Tape
  | 0 => .vertices
  | 1 => .alphabet
  | 2 => .newOccurrences
  | 3 => .input

def tokens (C : Nat) : List (MachineFieldTemplate.Token 4) :=
  [.copy 0, .copy 1, .copy 2] ++ List.replicate C (.copy 3)

def clearKeys : List Tape :=
  [.input, .vertices, .alphabet, .occurrences, .newOccurrences,
    .affineScratch, .copyScratch]

inductive Label (C : Nat)
  | headerStart (i : Fin 3)
  | headerRead (i : Fin 3)
  | scale (phase : Fin 3)
  | emit (label : MachineFieldTemplate.Label (tokens C).length)
  | finishStart
  | finish (label : SourceRuntimeFinish.Label clearKeys)
  deriving DecidableEq, Fintype

def headerNext {C : Nat} (i : Fin 3) : Label C :=
  if h : i.val + 1 < 3 then .headerStart ⟨i.val + 1, h⟩ else .scale 0

def emitEntry (C : Nat) : Label C :=
  .emit (MachineFieldTemplate.startAt (tokens C).length 0)

def program (C : Nat) : Label C → TM2.Stmt (fun _ : Tape => Bool) (Label C) State
  | .headerStart i => SourceMachine.fieldStart (headerField i) (.headerRead i)
  | .headerRead i => SourceMachine.fieldLoop .input (headerField i)
      (.headerRead i) (some (headerNext i))
  | .scale 0 => MachineUnaryAffineAt.seed .newOccurrences 0 (.scale 1)
  | .scale 1 => MachineUnaryAffineAt.scan .occurrences .affineScratch
      .newOccurrences C (.scale 1) (.scale 2)
  | .scale 2 => MachineTransfer.loopAt .affineScratch .occurrences id false
      (.scale 2) (some (emitEntry C))
  | .emit label => MachineFieldTemplate.instruction (tokens C) emitField
      .copyScratch .accumulator Label.emit (some .finishStart) label
  | .finishStart => .load (fun _ => initialState)
      (MachineTransfer.exitAt .output (SourceRuntimeFinish.entry clearKeys Label.finish))
  | .finish label => SourceRuntimeFinish.statement clearKeys .accumulator .output
      ((), ()) Label.finish none label

def machine (C : Nat) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label C
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program C

theorem covers (k : Tape) (ha : k ≠ .accumulator) (ho : k ≠ .output) :
    k ∈ clearKeys := by
  cases k <;> simp_all [clearKeys]

theorem accumulator_not_mem_clearKeys : Tape.accumulator ∉ clearKeys := by decide
theorem output_not_mem_clearKeys : Tape.output ∉ clearKeys := by decide

end DFVSGames.Explicit.MachineUniformProgram


namespace DFVSGames.Explicit.MachineUniformHeaders

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineUniformProgram

def inputTapes (bits : List Bool) : Tape → List Bool :=
  fun k => if k = .input then bits else []

def afterVertices (n : Nat) (rest : List Bool) : Tape → List Bool :=
  fun k => if k = .input then rest else if k = .vertices then encodeWord n else []

def afterAlphabet (n q : Nat) (rest : List Bool) : Tape → List Bool :=
  fun k => if k = .input then rest else if k = .vertices then encodeWord n
    else if k = .alphabet then encodeWord q else []

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  fun k => if k = .input then body else if k = .vertices then encodeWord n
    else if k = .alphabet then encodeWord q
    else if k = .occurrences then encodeWord Q else []

theorem initList_eq (C : Nat) (bits : List Bool) :
    initList (machine C) bits =
      ⟨some (.headerStart 0), initialState, inputTapes bits⟩ := by
  unfold initList
  congr 1

theorem first_result (n : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes Tape.input .vertices
      (inputTapes (encodeWord n ++ rest)) rest
      (encodeWord n ++ inputTapes (encodeWord n ++ rest) .vertices) =
      afterVertices n rest := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, inputTapes, afterVertices]

theorem second_result (n q : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes Tape.input .alphabet
      (afterVertices n (encodeWord q ++ rest)) rest
      (encodeWord q ++ afterVertices n (encodeWord q ++ rest) .alphabet) =
      afterAlphabet n q rest := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, afterVertices, afterAlphabet]

theorem third_result (n q Q : Nat) (body : List Bool) :
    SourceMachine.fieldTapes Tape.input .occurrences
      (afterAlphabet n q (encodeWord Q ++ body)) body
      (encodeWord Q ++ afterAlphabet n q (encodeWord Q ++ body) .occurrences) =
      resultTapes n q Q body := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, afterAlphabet, resultTapes]

def headersInTime (C q n Q : Nat) (body : List Bool) :
    StateTransition.EvalsToInTime (machine C).step
      (initList (machine C) (encodeWords [n, q, Q] ++ body))
      (some ⟨some (.scale 0), initialState, resultTapes n q Q body⟩)
      (n + q + Q + 6) := by
  have first := SourceMachine.fieldInTime Tape.input .vertices (by decide)
    (.headerStart 0 : Label C) (.headerRead 0) (some (.headerStart 1))
    (program C) rfl rfl
    (inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))) n
    (encodeWord q ++ (encodeWord Q ++ body)) rfl ((), ()) none
  rw [first_result] at first
  have second := SourceMachine.fieldInTime Tape.input .alphabet (by decide)
    (.headerStart 1 : Label C) (.headerRead 1) (some (.headerStart 2))
    (program C) rfl rfl (afterVertices n (encodeWord q ++ (encodeWord Q ++ body))) q
    (encodeWord Q ++ body) rfl ((), ()) none
  rw [second_result] at second
  have third := SourceMachine.fieldInTime Tape.input .occurrences (by decide)
    (.headerStart 2 : Label C) (.headerRead 2) (some (.scale 0))
    (program C) rfl rfl (afterAlphabet n q (encodeWord Q ++ body)) Q body rfl ((), ()) none
  rw [third_result] at third
  have firstSecond := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstSecond third
  rw [initList_eq]
  change StateTransition.EvalsToInTime (TM2.step (program C))
    ⟨some (.headerStart 0), initialState, inputTapes (encodeWords [n, q, Q] ++ body)⟩
    (some ⟨some (.scale 0), initialState, resultTapes n q Q body⟩) (n + q + Q + 6)
  simpa only [encodeWords, List.nil_append, List.append_assoc]
    using ({
      toEvalsTo := whole.toEvalsTo
      steps_le_m := by
        have bound := whole.steps_le_m
        omega } : StateTransition.EvalsToInTime (TM2.step (program C))
        ⟨some (.headerStart 0), initialState,
          inputTapes (encodeWord n ++ (encodeWord q ++ (encodeWord Q ++ body)))⟩
        (some ⟨some (.scale 0), initialState, resultTapes n q Q body⟩)
        (n + q + Q + 6))

theorem headers_budget (q n Q : Nat) (body : List Bool) :
    n + q + Q + 6 ≤ (encodeWords [n, q, Q] ++ body).length + 3 := by
  simp only [List.length_append, encodeWords_length, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil]
  omega

end DFVSGames.Explicit.MachineUniformHeaders


namespace DFVSGames.Integration.GapSemantics

open DFVSGames.Foundations.Target

def errorValue (e : RationalError) : ℚ := (e.numerator : ℚ) / e.denominator

def satisfactionRate {q : Nat} (g : Instance q) (labeling : Fin g.vertices → Fin q) : ℚ :=
  (countSatisfied labeling g.constraints : ℚ) / g.constraints.length

theorem countSatisfied_eq_sum {n q : Nat} (labeling : Fin n → Fin q)
    (constraints : List (Constraint n q)) :
    countSatisfied labeling constraints =
      (constraints.map (fun c => if c.satisfied labeling then (1 : Nat) else 0)).sum := by
  induction constraints with
  | nil => rfl
  | cons c cs ih => simp [countSatisfied, ih]

theorem countSatisfied_ofFn {m n q : Nat} (labeling : Fin n → Fin q)
    (constraints : Fin m → Constraint n q) :
    countSatisfied labeling (List.ofFn constraints) =
      ∑ i, if (constraints i).satisfied labeling then (1 : Nat) else 0 := by
  rw [countSatisfied_eq_sum, List.map_ofFn, List.sum_ofFn]
  rfl

def uniformConstraintAcceptance {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) : ℚ :=
  Finset.univ.expect (fun i : Fin g.constraints.length =>
    if g.constraints[i.val].satisfied labeling then (1 : ℚ) else 0)

theorem uniformConstraintAcceptance_eq_rate {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) :
    uniformConstraintAcceptance g labeling = satisfactionRate g labeling := by
  have hcount := countSatisfied_ofFn labeling
    (fun i : Fin g.constraints.length => g.constraints[i.val])
  rw [List.ofFn_getElem] at hcount
  unfold uniformConstraintAcceptance satisfactionRate
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin, hcount]
  congr 1
  simp

theorem errorValue_pos (e : RationalError) : 0 < errorValue e := by
  apply div_pos
  · exact_mod_cast e.numeratorPositive
  · exact_mod_cast e.denominatorPositive

theorem errorValue_lt_half (e : RationalError) : errorValue e < 1 / 2 := by
  have hd : (0 : ℚ) < e.denominator := by exact_mod_cast e.denominatorPositive
  have hn : (2 : ℚ) * e.numerator < e.denominator := by exact_mod_cast e.belowHalf
  unfold errorValue
  apply (div_lt_iff₀ hd).2
  linarith

theorem satisfactionRate_nonneg {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) : 0 ≤ satisfactionRate g labeling := by
  apply div_nonneg <;> exact Nat.cast_nonneg _

theorem satisfactionRate_le_one {q : Nat} (g : Instance q)
    (labeling : Fin g.vertices → Fin q) : satisfactionRate g labeling ≤ 1 := by
  have hm : (0 : ℚ) < g.constraints.length := by
    exact_mod_cast g.constraintCount_positive
  unfold satisfactionRate
  rw [div_le_iff₀ hm, one_mul]
  exact_mod_cast countSatisfied_le_length labeling g.constraints

theorem completeAt_iff {q : Nat} (e : RationalError) (g : Instance q) :
    CompleteAt e g ↔ ∃ labeling, 1 - errorValue e ≤ satisfactionRate g labeling := by
  unfold CompleteAt
  apply exists_congr
  intro labeling
  have hd : (0 : ℚ) < e.denominator := by exact_mod_cast e.denominatorPositive
  have hm : (0 : ℚ) < g.constraints.length := by
    exact_mod_cast g.constraintCount_positive
  have hsub : (1 : ℚ) - (e.numerator : ℚ) / e.denominator =
      ((e.denominator : ℚ) - e.numerator) / e.denominator := by
    rw [sub_div, div_self (ne_of_gt hd)]
  unfold errorValue satisfactionRate
  rw [hsub, div_le_div_iff₀ hd hm]
  constructor
  · intro h
    have hq : (e.denominator : ℚ) * g.constraints.length ≤
        (e.denominator : ℚ) * countSatisfied labeling g.constraints +
          (e.numerator : ℚ) * g.constraints.length := by exact_mod_cast h
    nlinarith
  · intro h
    have hq : (e.denominator : ℚ) * g.constraints.length ≤
        (e.denominator : ℚ) * countSatisfied labeling g.constraints +
          (e.numerator : ℚ) * g.constraints.length := by nlinarith
    exact_mod_cast hq

theorem soundAt_iff {q : Nat} (e : RationalError) (g : Instance q) :
    SoundAt e g ↔ ∀ labeling, satisfactionRate g labeling ≤ errorValue e := by
  unfold SoundAt
  apply forall_congr'
  intro labeling
  have hd : (0 : ℚ) < e.denominator := by exact_mod_cast e.denominatorPositive
  have hm : (0 : ℚ) < g.constraints.length := by
    exact_mod_cast g.constraintCount_positive
  unfold errorValue satisfactionRate
  rw [div_le_div_iff₀ hm hd]
  constructor
  · intro h
    have hq : (e.denominator : ℚ) * countSatisfied labeling g.constraints ≤
        (e.numerator : ℚ) * g.constraints.length := by exact_mod_cast h
    nlinarith
  · intro h
    have hq : (e.denominator : ℚ) * countSatisfied labeling g.constraints ≤
        (e.numerator : ℚ) * g.constraints.length := by nlinarith
    exact_mod_cast hq

theorem completeAt_mono {q : Nat} {e e' : RationalError} {g : Instance q}
    (hee : errorValue e ≤ errorValue e') (hg : CompleteAt e g) : CompleteAt e' g := by
  obtain ⟨labeling, hl⟩ := (completeAt_iff e g).1 hg
  apply (completeAt_iff e' g).2
  exact ⟨labeling, le_trans (sub_le_sub_left hee 1) hl⟩

theorem soundAt_mono {q : Nat} {e e' : RationalError} {g : Instance q}
    (hee : errorValue e ≤ errorValue e') (hg : SoundAt e g) : SoundAt e' g := by
  apply (soundAt_iff e' g).2
  intro labeling
  exact le_trans ((soundAt_iff e g).1 hg labeling) hee

theorem completeAt_iff_real {q : Nat} (e : RationalError) (g : Instance q) :
    CompleteAt e g ↔ ∃ labeling,
      1 - (errorValue e : ℝ) ≤
        (countSatisfied labeling g.constraints : ℝ) / g.constraints.length := by
  rw [completeAt_iff]
  apply exists_congr
  intro labeling
  simpa [satisfactionRate] using
    (Rat.cast_le (K := ℝ) (p := 1 - errorValue e)
      (q := satisfactionRate g labeling)).symm

theorem soundAt_iff_real {q : Nat} (e : RationalError) (g : Instance q) :
    SoundAt e g ↔ ∀ labeling,
      (countSatisfied labeling g.constraints : ℝ) / g.constraints.length ≤
        (errorValue e : ℝ) := by
  rw [soundAt_iff]
  apply forall_congr'
  intro labeling
  simpa [satisfactionRate] using
    (Rat.cast_le (K := ℝ) (p := satisfactionRate g labeling) (q := errorValue e)).symm

end DFVSGames.Integration.GapSemantics

end OAI
