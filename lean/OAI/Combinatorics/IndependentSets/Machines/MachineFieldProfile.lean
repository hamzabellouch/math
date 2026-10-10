import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineCopy
import OAI.Combinatorics.IndependentSets.Machines.MachineControl

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineFieldProfile

open Turing

abbrev Profile (q : Nat) := Fin q → Fin q → Bool

def equalityProfile {q : Nat} (words : Fin q → List Bool) : Profile q :=
  fun i j => decide (words i = words j)

theorem equalityProfile_encodeWord {q : Nat} (names : Fin q → Nat) (i j : Fin q) :
    equalityProfile (fun k => encodeWord (names k)) i j = decide (names i = names j) := by
  have h : encodeWord (names i) = encodeWord (names j) ↔ names i = names j := by
    constructor
    · intro heq
      have hh := congrArg List.length heq
      simpa only [encodeWord_length, Nat.add_right_cancel_iff] using hh
    · rintro heq
      rw [heq]
  simp only [equalityProfile, h]

section Transport
variable {K Λ σ τ : Type} [DecidableEq K]

omit [DecidableEq K] in
theorem statement_roundtrip (e : σ ≃ τ)
    (q : TM2.Stmt (fun _ : K => Bool) Λ τ) :
    MachineControl.statement id e (MachineControl.statement id e.symm q) = q := by
  induction q <;> simp_all [MachineControl.statement]

def copyStateEquiv (σ : Type) :
    ((σ × Bool × Option Bool) × Option Bool) ≃ MachineCompare.State σ where
  toFun s := (s.1.1, s.1.2.1, s.1.2.2, s.2)
  invFun s := ((s.1, s.2.1, s.2.2.1), s.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def normalState (ambient : σ) : MachineCompare.State σ := (ambient, false, none, none)

def copyStatement (q : TM2.Stmt (fun _ : K => Bool) Λ
    ((σ × Bool × Option Bool) × Option Bool)) :
    TM2.Stmt (fun _ : K => Bool) Λ (MachineCompare.State σ) :=
  MachineControl.statement id (copyStateEquiv σ) q

def copyInCompareState (source destination scratch : K)
    (hSD : source ≠ destination) (hST : source ≠ scratch) (hDT : destination ≠ scratch)
    (firstLabel secondLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineCompare.State σ))
    (atFirst : program firstLabel = copyStatement
      (Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel)))
    (atSecond : program secondLabel = copyStatement
      (MachineCopy.forkLoop scratch source destination false secondLabel exit))
    (base : K → List Bool) (hScratch : base scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some firstLabel, normalState ambient, base⟩
      (some ⟨exit, normalState ambient,
        Function.update base destination (base source ++ base destination)⟩)
      (2 * ((base source).length + 1)) := by
  let e := copyStateEquiv σ
  let view := MachineControl.program (Equiv.refl Λ) e.symm program
  have hfirst : view firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id false firstLabel (some secondLabel) := by
    dsimp [view, MachineControl.program]
    rw [atFirst]
    exact statement_roundtrip e.symm _
  have hsecond : view secondLabel =
      MachineCopy.forkLoop scratch source destination false secondLabel exit := by
    dsimp [view, MachineControl.program]
    rw [atSecond]
    exact statement_roundtrip e.symm _
  let run := MachineCopy.copyInTime source destination scratch hSD hST hDT false
    firstLabel secondLabel exit view hfirst hsecond base hScratch (ambient, false, none) none
  have hprogram : MachineControl.program (Equiv.refl Λ) e view = program := by
    funext label
    exact statement_roundtrip e (program label)
  have hsim (a b : TM2.Cfg (fun _ : K => Bool) Λ ((σ × Bool × Option Bool) × Option Bool))
      (hab : TM2.step view a = some b) :
      TM2.step program (MachineControl.configuration id e a) =
        some (MachineControl.configuration id e b) := by
    have hh := MachineControl.step_simulation (Equiv.refl Λ) e view a
    rw [hprogram, hab] at hh
    exact hh
  have lifted := MachineComposition.liftExecutionInTime (TM2.step view) (TM2.step program)
    (MachineControl.configuration id e) hsim run
  simpa [MachineControl.configuration, copyStateEquiv, normalState, e] using lifted

end Transport

variable {K Λ σ : Type} [DecidableEq K]

def nonDestructiveCompareInTime (left right workLeft workRight scratch : K)
    (hleft : left ≠ workLeft ∧ left ≠ workRight ∧ left ≠ scratch)
    (hright : right ≠ workLeft ∧ right ≠ workRight ∧ right ≠ scratch)
    (hwork : workLeft ≠ workRight ∧ workLeft ≠ scratch ∧ workRight ≠ scratch)
    (leftFirst leftSecond rightFirst rightSecond compareLabel : Λ)
    (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineCompare.State σ))
    (atLeftFirst : program leftFirst = copyStatement
      (Reduction.MachineTransfer.loopAt left scratch id false leftFirst (some leftSecond)))
    (atLeftSecond : program leftSecond = copyStatement
      (MachineCopy.forkLoop scratch left workLeft false leftSecond (some rightFirst)))
    (atRightFirst : program rightFirst = copyStatement
      (Reduction.MachineTransfer.loopAt right scratch id false rightFirst (some rightSecond)))
    (atRightSecond : program rightSecond = copyStatement
      (MachineCopy.forkLoop scratch right workRight false rightSecond (some compareLabel)))
    (atCompare : program compareLabel =
      MachineCompare.loop workLeft workRight compareLabel equalExit differentExit)
    (base : K → List Bool) (hWL : base workLeft = []) (hWR : base workRight = [])
    (hScratch : base scratch = []) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some leftFirst, normalState ambient, base⟩
      (some ⟨if base left = base right then equalExit else differentExit,
        normalState ambient, base⟩)
      (2 * ((base left).length + 1) + 2 * ((base right).length + 1) +
        max (base left).length (base right).length + 1) := by
  let t₁ := Function.update base workLeft (base left)
  let t₂ := Function.update t₁ workRight (base right)
  have h₁ := copyInCompareState left workLeft scratch hleft.1 hleft.2.2 hwork.2.1
    leftFirst leftSecond (some rightFirst) program atLeftFirst atLeftSecond base hScratch ambient
  simp only [hWL, List.append_nil] at h₁
  have hSR : t₁ right = base right := by simp [t₁, hright.1]
  have hDR : t₁ workRight = [] := by simp [t₁, Ne.symm hwork.1, hWR]
  have hTR : t₁ scratch = [] := by simp [t₁, Ne.symm hwork.2.1, hScratch]
  have h₂ := copyInCompareState right workRight scratch hright.2.1 hright.2.2 hwork.2.2
    rightFirst rightSecond (some compareLabel) program atRightFirst atRightSecond t₁ hTR ambient
  rw [hSR, hDR] at h₂
  simp only [List.append_nil] at h₂
  have hL : t₂ workLeft = base left := by simp [t₂, t₁, hwork.1]
  have hR : t₂ workRight = base right := by simp [t₂]
  have hrestore : Reduction.MachineTransfer.tapesAt workLeft workRight t₂ [] [] = base := by
    funext p
    by_cases hl : p = workLeft
    · subst p
      simp [Reduction.MachineTransfer.tapesAt, hwork.1, hWL]
    · by_cases hr : p = workRight
      · subst p
        simp [Reduction.MachineTransfer.tapesAt, hWR]
      · simp [Reduction.MachineTransfer.tapesAt, t₂, t₁, hl, hr]
  have h₃ := MachineCompare.compareInTime workLeft workRight hwork.1 compareLabel
    equalExit differentExit program atCompare t₂ ambient none none
  rw [hL, hR, hrestore] at h₃
  let h₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ h₁ h₂
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ h₁₂ h₃
  exact { toEvalsTo := run.toEvalsTo, steps_le_m := by have h := run.steps_le_m; omega }

end IndependentSetsGames.Foundations.Complexity.MachineFieldProfile

end OAI
