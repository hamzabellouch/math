import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.ExpanderTableWords
import OAI.Combinatorics.IndependentSets.Machines.MachineExpanderRowProgram

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineComposition

def lookupPhaseLabel {d : Nat} (second : Bool)
    (l : MachinePreservingLookupClean.Label) : Label d :=
  if second then .secondLookup l else .firstLookup l

def scanPhaseLabel {d : Nat} (second : Bool) : Label d :=
  if second then .secondScan else .firstScan

def reversePhaseLabel {d : Nat} (second : Bool) : Label d :=
  if second then .secondReverse else .firstReverse

def lookupPhasePort {d : Nat} (second : Bool) (control : Control d) : Fin (degree d) :=
  if second then secondOffset control else firstOffset control

def lookupPhaseAddress {d : Nat} (second : Bool) (vertex : Nat) (control : Control d) : Nat :=
  if second then secondAddress vertex control else firstAddress vertex control

theorem lookupPhaseAddress_eq_rowIndex {v d : Nat} (second : Bool)
    (vertex : Fin v) (control : Control d) :
    lookupPhaseAddress second vertex.val control =
      (rowIndex v (degree d) (vertex, lookupPhasePort second control)).val := by
  cases second
  · exact firstAddress_eq_rowIndex vertex control
  · exact secondAddress_eq_rowIndex vertex control

theorem lookupTape_injective : Function.Injective lookupTape := by decide

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

def lookupResultTapes (ports : Tape → K) (base : K → List Bool)
    (value : Nat) (indexSuffix : List Bool) : K → List Bool :=
  MachinePreservingLookup.initialTapes (ports ∘ lookupTape) base 0 indexSuffix []
    (encodeWord value ++ base (ports .lookupOutput))

theorem lookupResultTapes_index (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) (value : Nat) (indexSuffix : List Bool) :
    lookupResultTapes ports base value indexSuffix (ports .queryIndex) =
      encodeWord 0 ++ indexSuffix := by
  apply MachineLookup.tapes_index
  · exact fun h => (by decide : Tape.queryIndex ≠ .lookupWork) (distinct h)
  · exact fun h => (by decide : Tape.queryIndex ≠ .lookupOutput) (distinct h)

theorem lookupResultTapes_work (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) (value : Nat) (indexSuffix : List Bool) :
    lookupResultTapes ports base value indexSuffix (ports .lookupWork) = [] := by
  apply MachineLookup.tapes_source
  exact fun h => (by decide : Tape.lookupWork ≠ .lookupOutput) (distinct h)

theorem lookupResultTapes_output (ports : Tape → K)
    (base : K → List Bool) (value : Nat) (indexSuffix : List Bool) :
    lookupResultTapes ports base value indexSuffix (ports .lookupOutput) =
      encodeWord value ++ base (ports .lookupOutput) := by
  apply MachineLookup.tapes_destination

theorem lookupResultTapes_other (ports : Tape → K) (base : K → List Bool)
    (value : Nat) (indexSuffix : List Bool) (p : K)
    (hi : p ≠ ports .queryIndex) (hw : p ≠ ports .lookupWork)
    (ho : p ≠ ports .lookupOutput) :
    lookupResultTapes ports base value indexSuffix p = base p := by
  exact MachineLookup.tapes_other _ _ _ p hi hw ho _ _ _ _

theorem lookupResultTapes_table (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) (value : Nat) (indexSuffix : List Bool) :
    lookupResultTapes ports base value indexSuffix (ports .table) = base (ports .table) := by
  apply lookupResultTapes_other
  all_goals intro h; have := distinct h; cases this

theorem lookupResultTapes_restore (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) (value : Nat) (indexSuffix : List Bool) :
    lookupResultTapes ports base value indexSuffix (ports .lookupRestore) =
      base (ports .lookupRestore) := by
  apply lookupResultTapes_other
  all_goals intro h; have := distinct h; cases this

variable {v d : Nat} (second : Bool) (positive : 0 < d)
    (H : Table (cloudSize d) d) (ports : Tape → K)
    (distinct : Function.Injective ports) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (base : K → List Bool) (G : Table v (degree d))
    (tableWord : base (ports .table) = encodeWords (rotationWords G))
    (scratchEmpty : base (ports .lookupRestore) = [])
    (x : Fin v × Fin (degree d)) (indexSuffix : List Bool)
    (counterWord : base (ports .queryIndex) =
      encodeWord (rowIndex v (degree d) x).val ++ indexSuffix)
    (workEmpty : base (ports .lookupWork) = [])
    (ambient : (Ambient ρ d × Fin (degree d)) × Unit) (register : Option Bool)

include positive H distinct exit code tableWord scratchEmpty counterWord workEmpty

theorem lookupPhaseTrace :
    (advance (TM2.step target))^[MachinePreservingLookupClean.steps
        (rotationWords G) (rowIndex v (degree d) x).val]
      (some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))),
        (ambient, register), base⟩) =
      some ⟨some (labels (scanPhaseLabel second)), (ambient, none),
        lookupResultTapes ports base (reverseIndex G (rowIndex v (degree d) x)).val
          indexSuffix⟩ := by
  apply MachinePreservingLookupClean.traceAt_fromTapes (ports ∘ lookupTape)
    (distinct.comp lookupTape_injective)
    (fun l => labels (lookupPhaseLabel second l)) (some (labels (scanPhaseLabel second)))
    target
  · intro l
    cases second
    · exact code (.firstLookup l)
    · exact code (.secondLookup l)
  · exact tableWord
  · exact scratchEmpty
  · exact rotationWords_getElem? G (rowIndex v (degree d) x)
  · exact counterWord
  · exact workEmpty

def lookupPhaseInTime :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))),
        (ambient, register), base⟩
      (some ⟨some (labels (scanPhaseLabel second)), (ambient, none),
        lookupResultTapes ports base (reverseIndex G (rowIndex v (degree d) x)).val
          indexSuffix⟩)
      (6 * (encodeWords (rotationWords G)).length + 4) where
  steps := MachinePreservingLookupClean.steps (rotationWords G) (rowIndex v (degree d) x).val
  evals_in_steps := lookupPhaseTrace second positive H ports distinct labels exit target code
    base G tableWord scratchEmpty x indexSuffix counterWord workEmpty ambient register
  steps_le_m := MachinePreservingLookupClean.steps_le (rotationWords G) _ _
    (rotationWords_getElem? G (rowIndex v (degree d) x))

end IndependentSetsGames.Foundations.Complexity.MachineExpanderRow

end OAI
