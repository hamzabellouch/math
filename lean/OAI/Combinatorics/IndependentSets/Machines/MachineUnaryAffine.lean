import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineCopy
import OAI.Combinatorics.IndependentSets.Machines.PushWord

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineUnaryAffineAt

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

theorem update_source (source scratch destination : K)
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

theorem update_scratch (source scratch destination : K) (hsd : scratch ≠ destination)
    (base : K → List Bool) (input saved output replacement : List Bool) :
    Function.update (tapes source scratch destination base input saved output) scratch replacement =
      tapes source scratch destination base input replacement output := by
  funext k
  by_cases h : k = scratch
  · subst k; simp [tapes, MachineCopy.forkTapes, hsd]
  · by_cases h' : k = destination
    · subst k; simp [tapes, MachineCopy.forkTapes, h]
    · simp [tapes, MachineCopy.forkTapes, h, h']

theorem update_destination (source scratch destination : K)
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
    update_source source scratch destination hs hd hsd, tapes_scratch _ _ _ hsd,
    update_scratch _ _ _ hsd, stepAux_pushWord, tapes_destination,
    prepend_replicate_word, update_destination]

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
    update_source source scratch destination hs hd hsd]

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

instance : Fintype Label where
  elems := {.seed, .scan, .restore}
  complete value := by cases value <;> simp

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

end IndependentSetsGames.Foundations.Complexity.MachineUnaryAffineAt

end OAI
