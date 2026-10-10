import Mathlib
import OAI.Computability.MinUncut.PCP.AddressArithmetic
import OAI.Computability.MinUncut.Machines.MachineRegisterEmit

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceEquationEmit

open Turing Complexity
open SourceAddressDescriptors
open MinUncutGames.Reduction.CloneGap
open MinUncutGames.Reduction.MachineSubstitution

inductive Label
  | seed | thirdDrain | thirdFork | thirdEmit
  | secondDrain | secondFork | secondEmit | firstDrain | firstFork | firstEmit
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.seed, .thirdDrain, .thirdFork, .thirdEmit,
  .secondDrain, .secondFork, .secondEmit, .firstDrain, .firstFork, .firstEmit]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (σ : Type) := σ × Option Bool

def rhsBit (e : Equation Descriptor) : Nat := if e.rhs then 1 else 0

def steps (values : Fin 3 → Nat) (e : Equation Descriptor) : Nat :=
  2 * (values e.first.1 + values e.second.1 + values e.third.1) + 16

variable {K Λ σ : Type} [DecidableEq K]

def statement (sources : Fin 3 → K) (destination scratch : K)
    (e : Equation Descriptor) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .seed => pushWord destination (encodeWord (rhsBit e)).reverse
      (.goto fun _ => labels .thirdDrain)
  | .thirdDrain => Reduction.MachineTransfer.loopAt (sources e.third.1) scratch id false
      (labels .thirdDrain) (some (labels .thirdFork))
  | .thirdFork => MachineCopy.forkLoop scratch (sources e.third.1) destination false
      (labels .thirdFork) (some (labels .thirdEmit))
  | .thirdEmit => MachineRegisterEmit.emitStatement destination e.third.2
      (some (labels .secondDrain))
  | .secondDrain => Reduction.MachineTransfer.loopAt (sources e.second.1) scratch id false
      (labels .secondDrain) (some (labels .secondFork))
  | .secondFork => MachineCopy.forkLoop scratch (sources e.second.1) destination false
      (labels .secondFork) (some (labels .secondEmit))
  | .secondEmit => MachineRegisterEmit.emitStatement destination e.second.2
      (some (labels .firstDrain))
  | .firstDrain => Reduction.MachineTransfer.loopAt (sources e.first.1) scratch id false
      (labels .firstDrain) (some (labels .firstFork))
  | .firstFork => MachineCopy.forkLoop scratch (sources e.first.1) destination false
      (labels .firstFork) (some (labels .firstEmit))
  | .firstEmit => MachineRegisterEmit.emitStatement destination e.first.2 exit

def program (sources : Fin 3 → K) (destination scratch : K) (e : Equation Descriptor) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (State σ) :=
  statement sources destination scratch e id none

def prefixTapes (destination : K) (base : K → List Bool) (written : List Nat) :
    K → List Bool := Function.update base destination (encodeWords written ++ base destination)

theorem prefixTapes_other (destination : K) (base : K → List Bool) (written : List Nat)
    (k : K) (hk : k ≠ destination) : prefixTapes destination base written k = base k := by
  simp [prefixTapes, hk]

theorem equationTrace (sources : Fin 3 → K) (destination scratch : K)
    (sourceDestination : ∀ side, sources side ≠ destination)
    (sourceScratch : ∀ side, sources side ≠ scratch)
    (destinationScratch : destination ≠ scratch) (e : Equation Descriptor)
    (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement sources destination scratch e labels exit label)
    (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (sources side) = encodeWord (values side))
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps values e]
      (some ⟨some (labels .seed), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), prefixTapes destination base (words values e)⟩ := by
  have hw (written : List Nat) (side : Fin 3) :
      prefixTapes destination base written (sources side) = encodeWord (values side) := by
    rw [prefixTapes_other _ _ _ _ (sourceDestination side), sourceWords side]
  have hs (written : List Nat) : prefixTapes destination base written scratch = [] := by
    rw [prefixTapes_other _ _ _ _ (Ne.symm destinationScratch), scratchEmpty]
  have hseed : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .seed), (ambient, register), base⟩) =
      some ⟨some (labels .thirdDrain), (ambient, register),
        prefixTapes destination base [rhsBit e]⟩ := by
    change some (TM2.stepAux (p (labels .seed)) (ambient, register) base) = _
    rw [atLabels .seed]
    simp only [statement, stepAux_pushWord, List.reverse_reverse, TM2.stepAux,
      prefixTapes, encodeWords, List.append_nil]
  have hthird : (MachineComposition.advance (TM2.step p))^[2 * values e.third.1 + 5]
      (some ⟨some (labels .thirdDrain), (ambient, register),
        prefixTapes destination base [rhsBit e]⟩) =
      some ⟨some (labels .secondDrain), (ambient, none),
        prefixTapes destination base [realize values e.third, rhsBit e]⟩ := by
    have h := MachineRegisterEmit.registerEmitTrace (sources e.third.1) destination scratch
      (sourceDestination _) (sourceScratch _) destinationScratch e.third.2
      (labels .thirdDrain) (labels .thirdFork) (labels .thirdEmit) (some (labels .secondDrain))
      p (atLabels .thirdDrain) (atLabels .thirdFork) (atLabels .thirdEmit)
      (prefixTapes destination base [rhsBit e]) (values e.third.1)
      (hw _ _) (hs _) ambient register
    simpa only [prefixTapes, Function.update_self, Function.update_idem, realize,
      encodeWords, List.append_nil, List.append_assoc] using h
  have hsecond : (MachineComposition.advance (TM2.step p))^[2 * values e.second.1 + 5]
      (some ⟨some (labels .secondDrain), (ambient, none),
        prefixTapes destination base [realize values e.third, rhsBit e]⟩) =
      some ⟨some (labels .firstDrain), (ambient, none),
        prefixTapes destination base [realize values e.second, realize values e.third, rhsBit e]⟩ := by
    have h := MachineRegisterEmit.registerEmitTrace (sources e.second.1) destination scratch
      (sourceDestination _) (sourceScratch _) destinationScratch e.second.2
      (labels .secondDrain) (labels .secondFork) (labels .secondEmit) (some (labels .firstDrain))
      p (atLabels .secondDrain) (atLabels .secondFork) (atLabels .secondEmit)
      (prefixTapes destination base [realize values e.third, rhsBit e]) (values e.second.1)
      (hw _ _) (hs _) ambient none
    simpa only [prefixTapes, Function.update_self, Function.update_idem, realize,
      encodeWords, List.append_nil, List.append_assoc] using h
  have hfirst : (MachineComposition.advance (TM2.step p))^[2 * values e.first.1 + 5]
      (some ⟨some (labels .firstDrain), (ambient, none),
        prefixTapes destination base [realize values e.second, realize values e.third, rhsBit e]⟩) =
      some ⟨exit, (ambient, none), prefixTapes destination base (words values e)⟩ := by
    have h := MachineRegisterEmit.registerEmitTrace (sources e.first.1) destination scratch
      (sourceDestination _) (sourceScratch _) destinationScratch e.first.2
      (labels .firstDrain) (labels .firstFork) (labels .firstEmit) exit
      p (atLabels .firstDrain) (atLabels .firstFork) (atLabels .firstEmit)
      (prefixTapes destination base [realize values e.second, realize values e.third, rhsBit e])
      (values e.first.1) (hw _ _) (hs _) ambient none
    simpa only [prefixTapes, Function.update_self, Function.update_idem, words, rhsBit, realize,
      encodeWords, List.append_nil, List.append_assoc] using h
  rw [show steps values e = (2 * values e.first.1 + 5) +
      ((2 * values e.second.1 + 5) + ((2 * values e.third.1 + 5) + 1)) by
        unfold steps; omega]
  rw [Function.iterate_add_apply _ (2 * values e.first.1 + 5),
    Function.iterate_add_apply _ (2 * values e.second.1 + 5),
    Function.iterate_add_apply _ (2 * values e.third.1 + 5), hseed, hthird, hsecond, hfirst]

def equationInTime (sources : Fin 3 → K) (destination scratch : K)
    (sourceDestination : ∀ side, sources side ≠ destination)
    (sourceScratch : ∀ side, sources side ≠ scratch)
    (destinationScratch : destination ≠ scratch) (e : Equation Descriptor)
    (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement sources destination scratch e labels exit label)
    (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (sources side) = encodeWord (values side))
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .seed), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), prefixTapes destination base (words values e)⟩)
      (steps values e) where
  steps := steps values e
  evals_in_steps := equationTrace sources destination scratch sourceDestination sourceScratch
    destinationScratch e labels exit p atLabels base values sourceWords scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

def programInTime (sources : Fin 3 → K) (destination scratch : K)
    (sourceDestination : ∀ side, sources side ≠ destination)
    (sourceScratch : ∀ side, sources side ≠ scratch)
    (destinationScratch : destination ≠ scratch) (e : Equation Descriptor)
    (base : K → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (sources side) = encodeWord (values side))
    (scratchEmpty : base scratch = []) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program (σ := σ) sources destination scratch e))
      ⟨some .seed, (ambient, register), base⟩
      (some ⟨none, (ambient, none), prefixTapes destination base (words values e)⟩)
      (steps values e) :=
  equationInTime sources destination scratch sourceDestination sourceScratch destinationScratch
    e id none (program sources destination scratch e) (fun _ => rfl)
    base values sourceWords scratchEmpty ambient register

abbrev Tape := Fin 3 ⊕ Bool

def machine (e : Equation Descriptor) : FinTM2 where
  K := Tape
  k₀ := .inl 0
  k₁ := .inr false
  Γ _ := Bool
  Λ := Label
  main := .seed
  σ := State Unit
  initialState := ((), none)
  m := program Sum.inl (.inr false) (.inr true) e

def machineInTime (e : Equation Descriptor) (base : Tape → List Bool) (values : Fin 3 → Nat)
    (sourceWords : ∀ side, base (.inl side) = encodeWord (values side))
    (scratchEmpty : base (.inr true) = []) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine e).step
      ⟨some Label.seed, ((), register), base⟩
      (some ⟨none, ((), none), prefixTapes (.inr false : Tape) base (words values e)⟩)
      (steps values e) :=
  programInTime Sum.inl (.inr false : Tape) (.inr true)
    (fun _ => Sum.inl_ne_inr) (fun _ => Sum.inl_ne_inr) (by decide)
    e base values sourceWords scratchEmpty () register

end MinUncutGames.Foundations.Hastad.SourceEquationEmit

end

end OAI
