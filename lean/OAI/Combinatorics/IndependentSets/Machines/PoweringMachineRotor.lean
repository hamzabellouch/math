import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineAffineLookup
import OAI.Combinatorics.IndependentSets.Expansion.PortTableLookup

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineRotor

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

abbrev Alphabet (_ : K) := Bool

def reverseRole (i : Fin 5) : Fin 7 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 4 else 6

def endpointRole (i : Fin 5) : Fin 7 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else if i = 3 then 5 else 6

theorem reverseRole_injective : Function.Injective reverseRole := by decide
theorem endpointRole_injective : Function.Injective endpointRole := by decide
theorem source_outside_reverse : ∀ i, (1 : Fin 7) ≠ reverseRole i := by decide
theorem reverse_outside_endpoint : ∀ i, (4 : Fin 7) ≠ endpointRole i := by decide

def reverseTapes (tape : Fin 7 → K) : Fin 5 → K := tape ∘ reverseRole
def endpointTapes (tape : Fin 7 → K) : Fin 5 → K := tape ∘ endpointRole

inductive Label
  | reverse (l : MachineAffineLookup.Label)
  | endpoint (l : MachineAffineLookup.Label)
  deriving DecidableEq, Fintype

def instruction (tape : Fin 7 → K) (degree port : Nat)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .reverse l => MachineAffineLookup.instruction (tape 1) (reverseTapes tape)
      (4098 * degree) (4098 * port + 3) (fun q => labels (.reverse q))
      (some (labels (.endpoint .seed))) l
  | .endpoint l => MachineAffineLookup.instruction (tape 4) (endpointTapes tape)
      4098 2 (fun q => labels (.endpoint q)) exit l

def reverseId (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) : Nat :=
  table.reverseIndex[PortTables.rowIndex n d (vertex, port)].val

def reverseAddress (vertex : Fin n) (port : Fin d) : Nat :=
  (4098 * d) * vertex.val + (4098 * port.val + 3)

def endpointAddress (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) : Nat :=
  4098 * reverseId table vertex port + 2

theorem reverse_selected (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) :
    (PortTables.tableWords table)[reverseAddress vertex port]? =
      some (reverseId table vertex port) := by
  have h := PortTableLookup.reverse_word table (PortTables.rowIndex n d (vertex, port))
  have hindex : reverseAddress vertex port = 3 + 4098 * (PortTables.rowIndex n d (vertex, port)).val := by
    simp only [reverseAddress, PortTables.rowIndex_val, Nat.mul_add, Nat.mul_assoc]
    omega
  rw [hindex]
  exact h

theorem endpoint_selected (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) :
    (PortTables.tableWords table)[endpointAddress table vertex port]? =
      some ((PortTables.rotation table (vertex, port)).1.val) := by
  have h := PortTableLookup.rotation_head_word table (vertex, port)
  simpa only [endpointAddress, reverseId, Nat.add_comm] using h

def afterReverse (tape : Fin 7 → K) (table : PortTables.Table n d)
    (vertex : Fin n) (port : Fin d) (base : K → List Bool) : K → List Bool :=
  MachineAffineLookup.finalTapes (reverseTapes tape) base (PortTables.tableWords table)
    (reverseAddress vertex port) (reverseId table vertex port)

def finalTapes (tape : Fin 7 → K) (table : PortTables.Table n d)
    (vertex : Fin n) (port : Fin d) (base : K → List Bool) : K → List Bool :=
  MachineAffineLookup.finalTapes (endpointTapes tape)
    (afterReverse tape table vertex port base) (PortTables.tableWords table)
    (endpointAddress table vertex port) ((PortTables.rotation table (vertex, port)).1.val)

def steps (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) : Nat :=
  MachineAffineLookup.steps (PortTables.tableWords table) vertex.val (4098 * d) (4098 * port.val + 3) +
    MachineAffineLookup.steps (PortTables.tableWords table) (reverseId table vertex port) 4098 2

theorem rotorTrace (tape : Fin 7 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (port : Fin d)
    (atLabels : ∀ l, program (labels l) = instruction tape d port.val labels exit l)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (tableWord : base (tape 0) = PortTables.tableBits table)
    (scratchEmpty : base (tape 6) = []) (suffix : List Bool)
    (sourceWord : base (tape 1) = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps table vertex port]
      (some ⟨some (labels (.reverse .seed)), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), finalTapes tape table vertex port base⟩ := by
  have hd (i j : Fin 7) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have hrDistinct : Function.Injective (reverseTapes tape) := distinct.comp reverseRole_injective
  have heDistinct : Function.Injective (endpointTapes tape) := distinct.comp endpointRole_injective
  have hrOutside : ∀ i, tape 1 ≠ reverseTapes tape i := fun i =>
    hd 1 (reverseRole i) (source_outside_reverse i)
  have heOutside : ∀ i, tape 4 ≠ endpointTapes tape i := fun i =>
    hd 4 (endpointRole i) (reverse_outside_endpoint i)
  have hreverse := MachineAffineLookup.affineLookupTrace (tape 1) (reverseTapes tape)
    hrDistinct hrOutside (4098 * d) (4098 * port.val + 3)
    (fun q => labels (.reverse q)) (some (labels (.endpoint .seed)))
    program (fun q => atLabels (.reverse q)) base (PortTables.tableWords table)
    tableWord scratchEmpty vertex.val suffix sourceWord (reverseId table vertex port)
    (reverse_selected table vertex port) ambient register
  let mid := afterReverse tape table vertex port base
  have hmidTable : mid (tape 0) = PortTables.tableBits table := by
    calc
      mid (tape 0) = base (tape 0) :=
        MachineAffineLookup.finalTapes_other _ _ _ _ _ _
          (hd 0 2 (by decide)) (hd 0 3 (by decide)) (hd 0 4 (by decide))
      _ = _ := tableWord
  have hmidScratch : mid (tape 6) = [] := by
    calc
      mid (tape 6) = base (tape 6) :=
        MachineAffineLookup.finalTapes_other _ _ _ _ _ _
          (hd 6 2 (by decide)) (hd 6 3 (by decide)) (hd 6 4 (by decide))
      _ = _ := scratchEmpty
  have hmidSource : mid (tape 4) = encodeWord (reverseId table vertex port) ++ base (tape 4) :=
    MachineAffineLookup.finalTapes_output _ _ _ _ _
  have hendpoint := MachineAffineLookup.affineLookupTrace (tape 4) (endpointTapes tape)
    heDistinct heOutside 4098 2 (fun q => labels (.endpoint q)) exit
    program (fun q => atLabels (.endpoint q)) mid (PortTables.tableWords table)
    hmidTable hmidScratch (reverseId table vertex port) (base (tape 4)) hmidSource
    ((PortTables.rotation table (vertex, port)).1.val)
    (endpoint_selected table vertex port) ambient none
  rw [steps, Nat.add_comm, Function.iterate_add_apply, hreverse]
  exact hendpoint

theorem finalTapes_endpoint (tape : Fin 7 → K) (distinct : Function.Injective tape)
    (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) (base : K → List Bool) :
    finalTapes tape table vertex port base (tape 5) =
      encodeWord ((PortTables.rotation table (vertex, port)).1.val) ++ base (tape 5) := by
  have hd (i j : Fin 7) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  change MachineAffineLookup.finalTapes (endpointTapes tape) _ _ _ _ (endpointTapes tape 3) = _
  rw [MachineAffineLookup.finalTapes_output]
  congr 1
  exact MachineAffineLookup.finalTapes_other _ _ _ _ _ _
    (hd 5 2 (by decide)) (hd 5 3 (by decide)) (hd 5 4 (by decide))

theorem finalTapes_other (tape : Fin 7 → K) (table : PortTables.Table n d)
    (vertex : Fin n) (port : Fin d) (base : K → List Bool) (k : K)
    (h₂ : k ≠ tape 2) (h₃ : k ≠ tape 3) (h₄ : k ≠ tape 4) (h₅ : k ≠ tape 5) :
    finalTapes tape table vertex port base k = base k := by
  calc
    finalTapes tape table vertex port base k = afterReverse tape table vertex port base k :=
      MachineAffineLookup.finalTapes_other _ _ _ _ _ _ h₂ h₃ h₅
    _ = base k := MachineAffineLookup.finalTapes_other _ _ _ _ _ _ h₂ h₃ h₄

theorem steps_le (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) :
    steps table vertex port ≤ 14 * (PortTables.tableBits table).length + 12 := by
  have hvertex : vertex.val ≤ (encodeWords (PortTables.tableWords table)).length :=
    Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length table)
  have hreverse := MachineLookupSpec.output_length_le (PortTables.tableWords table)
    (reverseAddress vertex port) (reverseId table vertex port) (reverse_selected table vertex port)
  rw [encodeWord_length] at hreverse
  have hr := MachineAffineLookup.steps_le_table (PortTables.tableWords table)
    vertex.val (4098 * d) (4098 * port.val + 3) (reverseId table vertex port)
    (reverse_selected table vertex port) hvertex
  have he := MachineAffineLookup.steps_le_table (PortTables.tableWords table)
    (reverseId table vertex port) 4098 2 ((PortTables.rotation table (vertex, port)).1.val)
    (endpoint_selected table vertex port) (by omega)
  change _ ≤ 14 * (encodeWords (PortTables.tableWords table)).length + 12
  unfold steps
  omega

def machine (degree port : Nat) : FinTM2 where
  K := Fin 7
  k₀ := 0
  k₁ := 5
  Γ _ := Bool
  Λ := Label
  main := .reverse .seed
  σ := Unit × Option Bool
  initialState := ((),none)
  m := instruction id degree port id none

end IndependentSetsGames.Foundations.Complexity.PoweringMachineRotor

end OAI
