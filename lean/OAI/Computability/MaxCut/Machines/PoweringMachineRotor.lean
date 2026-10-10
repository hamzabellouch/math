import Mathlib
import OAI.Computability.MaxCut.Games.PoweringMasterState
import OAI.Computability.MaxCut.PCP.PortTableLookup

namespace OAI

/-! A rotor step on the live unary port-table encoding. First read the reverse
dart identifier; then read that dart's tail vertex. This uses no division or
runtime graph data in finite control. Both positional selections are proved
from the actual serialization. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRotor

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

/-- Its finite description depends on the fixed degree and selected port;
the vertex count and graph table are runtime tape data. -/
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

end MaxCutGames.Foundations.Complexity.PoweringMachineRotor

/-! Fixed port words are executed by a finite chain of actual rotor programs.
The six shared tapes hold table, query, scan, reverse identifier, scratch and
output. Each walk position has a separate physical vertex tape. The final
unary copy also handles the empty word and preserves the starting vertex. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineWord

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

abbrev Alphabet (_ : K) := Bool
abbrev Tape (t : Nat) := Fin 6 ⊕ Fin (t + 1)

def first (t : Nat) : Fin (t + 1) := ⟨0, by omega⟩

def shift (t : Nat) : Tape t → Tape (t + 1) := Sum.map id Fin.succ

theorem shift_injective (t : Nat) : Function.Injective (shift t) := by
  intro a b h
  cases a <;> cases b <;> simp_all [shift]

def rotorRole (t : Nat) (i : Fin 7) : Tape (t + 1) :=
  if i = 0 then .inl 0 else if i = 1 then .inr (first (t + 1)) else
  if i = 2 then .inl 1 else if i = 3 then .inl 2 else
  if i = 4 then .inl 3 else if i = 5 then .inr (first t).succ else .inl 4

theorem rotorRole_injective (t : Nat) : Function.Injective (rotorRole t) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [rotorRole, first, Fin.ext_iff]

def Label : Nat → Type
  | 0 => MachineUnaryAffineAt.Label
  | t + 1 => PoweringMachineRotor.Label ⊕ Label t

instance labelFintype (t : Nat) : Fintype (Label t) := by
  induction t with
  | zero => exact inferInstanceAs (Fintype MachineUnaryAffineAt.Label)
  | succ t ih =>
      letI := ih
      exact inferInstanceAs (Fintype (PoweringMachineRotor.Label ⊕ Label t))

instance labelDecidableEq (t : Nat) : DecidableEq (Label t) := by
  induction t with
  | zero => exact inferInstanceAs (DecidableEq MachineUnaryAffineAt.Label)
  | succ t ih =>
      letI := ih
      exact inferInstanceAs (DecidableEq (PoweringMachineRotor.Label ⊕ Label t))

def entry : (t : Nat) → Label t
  | 0 => .seed
  | _ + 1 => .inl (.reverse .seed)

def copyInstruction (source scratch output : K)
    (labels : MachineUnaryAffineAt.Label → Λ) (exit : Option Λ) :
    MachineUnaryAffineAt.Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .seed => MachineUnaryAffineAt.seed output 0 (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source scratch output 1 (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt scratch source id false (labels .restore) exit

def instruction : (t : Nat) → (Tape t → K) → (Fin t → Fin d) →
    (Label t → Λ) → Option Λ → Label t →
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | 0, placement, _, labels, exit =>
      copyInstruction (placement (.inr (first 0))) (placement (.inl 4))
        (placement (.inl 5)) labels exit
  | t + 1, placement, ports, labels, exit => fun l =>
      match l with
      | .inl q => PoweringMachineRotor.instruction (placement ∘ rotorRole t) d (ports 0).val
          (fun z => labels (.inl z)) (some (labels (.inr (entry t)))) q
      | .inr q => instruction t (placement ∘ shift t) (fun j => ports j.succ)
          (fun z => labels (.inr z)) exit q

def steps (table : PortTables.Table n d) :
    (t : Nat) → Fin n → (Fin t → Fin d) → Nat
  | 0, vertex, _ => 2 * (vertex.val + 1) + 1
  | t + 1, vertex, ports => PoweringMachineRotor.steps table vertex (ports 0) +
      steps table t (PortTables.rotation table (vertex, ports 0)).1 (fun j => ports j.succ)

def finalTapes (table : PortTables.Table n d) :
    (t : Nat) → (Tape t → K) → Fin n → (Fin t → Fin d) → (K → List Bool) → K → List Bool
  | 0, placement, vertex, _, base =>
      Function.update base (placement (.inl 5)) (encodeWord vertex.val ++ base (placement (.inl 5)))
  | t + 1, placement, vertex, ports, base =>
      finalTapes table t (placement ∘ shift t) (PortTables.rotation table (vertex, ports 0)).1
        (fun j => ports j.succ)
        (PoweringMachineRotor.finalTapes (placement ∘ rotorRole t) table vertex (ports 0) base)

theorem finalTapes_other (table : PortTables.Table n d) (t : Nat)
    (placement : Tape t → K) (vertex : Fin n) (ports : Fin t → Fin d)
    (base : K → List Bool) (k : K)
    (hquery : k ≠ placement (.inl 1)) (hscan : k ≠ placement (.inl 2))
    (hreverse : k ≠ placement (.inl 3)) (houtput : k ≠ placement (.inl 5))
    (hpositions : ∀ i : Fin t, k ≠ placement (.inr i.succ)) :
    finalTapes table t placement vertex ports base k = base k := by
  induction t generalizing vertex base with
  | zero => simp only [finalTapes, Function.update_of_ne houtput]
  | succ t ih =>
      let mid := PoweringMachineRotor.finalTapes (placement ∘ rotorRole t) table vertex (ports 0) base
      calc
        finalTapes table (t + 1) placement vertex ports base k = mid k :=
          ih (placement ∘ shift t) (PortTables.rotation table (vertex, ports 0)).1
            (fun j => ports j.succ) mid hquery hscan hreverse houtput
            (fun i => hpositions i.succ)
        _ = base k := PoweringMachineRotor.finalTapes_other _ _ _ _ _ k
          hquery hscan hreverse (hpositions (first t))

/-- Actual execution together with its endpoint word. No trace or running-time
hypothesis is needed: the recursive proof composes the concrete instructions. -/
theorem wordTrace (table : PortTables.Table n d) (t : Nat)
    (placement : Tape t → K) (distinct : Function.Injective placement)
    (vertex : Fin n) (ports : Fin t → Fin d)
    (labels : Label t → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction t placement ports labels exit l)
    (base : K → List Bool) (tableWord : base (placement (.inl 0)) = PortTables.tableBits table)
    (scratchEmpty : base (placement (.inl 4)) = []) (suffix : List Bool)
    (sourceWord : base (placement (.inr (first t))) = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps table t vertex ports]
      (some ⟨some (labels (entry t)), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), finalTapes table t placement vertex ports base⟩ ∧
    finalTapes table t placement vertex ports base (placement (.inl 5)) =
      encodeWord (PoweringWalks.wordEnd (PortTables.portGraph table) t vertex ports).val ++
        base (placement (.inl 5)) := by
  induction t generalizing vertex base suffix register with
  | zero =>
      have hd (i j : Tape 0) (hne : i ≠ j) : placement i ≠ placement j := fun h => hne (distinct h)
      have hrun := MachineUnaryAffineAt.seededAffineTrace
        (placement (.inr (first 0))) (placement (.inl 4)) (placement (.inl 5))
        (hd _ _ (by simp [first])) (hd _ _ (by simp [first])) (hd _ _ (by simp []))
        1 0 (labels .seed) (labels .scan) (labels .restore) exit program
        (atLabels .seed) (atLabels .scan) (atLabels .restore)
        base vertex.val suffix sourceWord scratchEmpty ambient register
      constructor
      · simpa only [steps, entry, finalTapes, Nat.one_mul, Nat.add_zero] using hrun
      · simp only [finalTapes, Function.update_self, PoweringWalks.wordEnd]
  | succ t ih =>
      have hd (i j : Tape (t + 1)) (hne : i ≠ j) : placement i ≠ placement j :=
        fun h => hne (distinct h)
      have hrotor := PoweringMachineRotor.rotorTrace (placement ∘ rotorRole t)
        (distinct.comp (rotorRole_injective t)) (fun q => labels (.inl q))
        (some (labels (.inr (entry t)))) program (ports 0) (fun q => atLabels (.inl q))
        table vertex base tableWord scratchEmpty suffix sourceWord ambient register
      let mid := PoweringMachineRotor.finalTapes (placement ∘ rotorRole t) table vertex (ports 0) base
      have hmidTable : mid (placement (.inl 0)) = PortTables.tableBits table := by
        calc
          mid (placement (.inl 0)) = base (placement (.inl 0)) :=
            PoweringMachineRotor.finalTapes_other _ _ _ _ _ _
              (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole]))
              (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole, first]))
          _ = _ := tableWord
      have hmidScratch : mid (placement (.inl 4)) = [] := by
        calc
          mid (placement (.inl 4)) = base (placement (.inl 4)) :=
            PoweringMachineRotor.finalTapes_other _ _ _ _ _ _
              (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole]))
              (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole, first]))
          _ = _ := scratchEmpty
      have hmidOutput : mid (placement (.inl 5)) = base (placement (.inl 5)) :=
        PoweringMachineRotor.finalTapes_other _ _ _ _ _ _
          (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole]))
          (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole, first]))
      have hmidSource : mid (placement (.inr (first t).succ)) =
          encodeWord (PortTables.rotation table (vertex, ports 0)).1.val ++
            base (placement (.inr (first t).succ)) :=
        PoweringMachineRotor.finalTapes_endpoint _ (distinct.comp (rotorRole_injective t)) _ _ _ _
      have htail := ih (placement ∘ shift t) (distinct.comp (shift_injective t))
        (PortTables.rotation table (vertex, ports 0)).1 (fun j => ports j.succ)
        (fun q => labels (.inr q)) (fun q => atLabels (.inr q)) mid hmidTable hmidScratch
        (base (placement (.inr (first t).succ))) hmidSource none
      constructor
      · rw [steps, Nat.add_comm, Function.iterate_add_apply]
        simp only [entry]
        rw [hrotor]
        exact htail.1
      · change finalTapes table t (placement ∘ shift t)
          (PortTables.rotation table (vertex, ports 0)).1 (fun j => ports j.succ) mid
          ((placement ∘ shift t) (.inl 5)) = _
        rw [htail.2]
        change _ ++ mid (placement (.inl 5)) = _
        rw [hmidOutput]
        rfl

theorem steps_le (table : PortTables.Table n d) (t : Nat)
    (vertex : Fin n) (ports : Fin t → Fin d) :
    steps table t vertex ports ≤ (14 * t + 2) * (PortTables.tableBits table).length + 12 * t + 3 := by
  induction t generalizing vertex with
  | zero =>
      have h := Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length table)
      simp only [steps, Nat.mul_zero, Nat.zero_add]
      omega
  | succ t ih =>
      have hr := PoweringMachineRotor.steps_le table vertex (ports 0)
      have ht := ih (PortTables.rotation table (vertex, ports 0)).1 (fun j => ports j.succ)
      simp only [steps, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc] at ht ⊢
      omega

def machine (degree t : Nat) (ports : Fin t → Fin degree) : FinTM2 where
  K := Tape t
  k₀ := .inl 0
  k₁ := .inl 5
  Γ _ := Bool
  Λ := Label t
  main := entry t
  σ := Unit × Option Bool
  initialState := ((),none)
  m := instruction t id ports id none

end MaxCutGames.Foundations.Complexity.PoweringMachineWord

/-! A fixed shared tape layout for the actual powering field subroutines.
The vertex identifiers live on physical tapes. The trajectory capacity is
fixed by `max`; each bounded word uses its first `t` trajectory tapes. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineTapes

abbrev Tape (max : Nat) := Fin 11 ⊕ Fin max

def table (max : Nat) : Tape max := .inl 0
def start (max : Nat) : Tape max := .inl 1
def query (max : Nat) : Tape max := .inl 2
def scan (max : Nat) : Tape max := .inl 3
def reverse (max : Nat) : Tape max := .inl 4
def scratch (max : Nat) : Tape max := .inl 5
def leftEndpoint (max : Nat) : Tape max := .inl 6
def rightEndpoint (max : Nat) : Tape max := .inl 7
def leftCopy (max : Nat) : Tape max := .inl 8
def rightCopy (max : Nat) : Tape max := .inl 9
def rowOutput (max : Nat) : Tape max := .inl 10

def endpoint (max : Nat) (target : Bool) : Tape max :=
  if target then rightEndpoint max else leftEndpoint max

@[simp] theorem endpoint_false (max : Nat) : endpoint max false = leftEndpoint max := rfl
@[simp] theorem endpoint_true (max : Nat) : endpoint max true = rightEndpoint max := rfl

/-- Table, query, scan, reverse identifier, scratch, selected endpoint. -/
def wordSharedRole (target : Bool) (i : Fin 6) : Fin 11 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else
  if i = 3 then 4 else if i = 4 then 5 else if target then 7 else 6

/-- Position zero is the caller's starting vertex; later positions are the
separate physical trajectory tapes. -/
def trajectoryPlacement {t max : Nat} (h : t ≤ max) : Fin (t + 1) → Tape max :=
  Fin.cases (start max) (fun i => .inr (Fin.castLE h i))

def wordPlacement {t max : Nat} (h : t ≤ max) (target : Bool) :
    PoweringMachineWord.Tape t → Tape max
  | .inl i => .inl (wordSharedRole target i)
  | .inr i => trajectoryPlacement h i

@[simp] theorem wordPlacement_inl_zero {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 0) = table max := rfl
@[simp] theorem wordPlacement_inl_one {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 1) = query max := rfl
@[simp] theorem wordPlacement_inl_two {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 2) = scan max := rfl
@[simp] theorem wordPlacement_inl_three {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 3) = reverse max := rfl
@[simp] theorem wordPlacement_inl_four {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 4) = scratch max := rfl
@[simp] theorem wordPlacement_inl_five {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inl 5) = endpoint max target := by cases target <;> rfl
@[simp] theorem wordPlacement_first {t max : Nat} (h : t ≤ max) (target : Bool) :
    wordPlacement h target (.inr (PoweringMachineWord.first t)) = start max := rfl
@[simp] theorem wordPlacement_succ {t max : Nat} (h : t ≤ max) (target : Bool) (i : Fin t) :
    wordPlacement h target (.inr i.succ) = .inr (Fin.castLE h i) := rfl

def relationPlacement (max : Nat) (i : Fin 6) : Tape max :=
  .inl (if i = 0 then 6 else if i = 1 then 0 else if i = 2 then 2 else
    if i = 3 then 3 else if i = 4 then 10 else 5)

@[simp] theorem relationPlacement_zero (max : Nat) : relationPlacement max 0 = leftEndpoint max := rfl
@[simp] theorem relationPlacement_one (max : Nat) : relationPlacement max 1 = table max := rfl
@[simp] theorem relationPlacement_two (max : Nat) : relationPlacement max 2 = query max := rfl
@[simp] theorem relationPlacement_three (max : Nat) : relationPlacement max 3 = scan max := rfl
@[simp] theorem relationPlacement_four (max : Nat) : relationPlacement max 4 = rowOutput max := rfl
@[simp] theorem relationPlacement_five (max : Nat) : relationPlacement max 5 = scratch max := rfl

def equalityPlacement (max : Nat) (i : Fin 6) : Tape max :=
  .inl (if i = 0 then 6 else if i = 1 then 7 else if i = 2 then 8 else
    if i = 3 then 9 else if i = 4 then 5 else 10)

@[simp] theorem equalityPlacement_zero (max : Nat) : equalityPlacement max 0 = leftEndpoint max := rfl
@[simp] theorem equalityPlacement_one (max : Nat) : equalityPlacement max 1 = rightEndpoint max := rfl
@[simp] theorem equalityPlacement_two (max : Nat) : equalityPlacement max 2 = leftCopy max := rfl
@[simp] theorem equalityPlacement_three (max : Nat) : equalityPlacement max 3 = rightCopy max := rfl
@[simp] theorem equalityPlacement_four (max : Nat) : equalityPlacement max 4 = scratch max := rfl
@[simp] theorem equalityPlacement_five (max : Nat) : equalityPlacement max 5 = rowOutput max := rfl

theorem wordSharedRole_injective (target : Bool) : Function.Injective (wordSharedRole target) := by
  cases target <;> decide

theorem wordSharedRole_ne_start (target : Bool) :
    ∀ i : Fin 6, wordSharedRole target i ≠ 1 := by
  cases target <;> decide

theorem wordSharedRole_ne_rowOutput (target : Bool) :
    ∀ i : Fin 6, wordSharedRole target i ≠ 10 := by
  cases target <;> decide

theorem trajectoryPlacement_injective {t max : Nat} (ht : t ≤ max) :
    Function.Injective (trajectoryPlacement ht) := by
  intro a b
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases ?_ (fun j => ?_) b
    · intro _
      rfl
    · intro h
      change (Sum.inl (1 : Fin 11) : Tape max) = .inr (Fin.castLE ht j) at h
      cases h
  · refine Fin.cases ?_ (fun j => ?_) b
    · intro h
      change (Sum.inr (Fin.castLE ht i) : Tape max) = .inl (1 : Fin 11) at h
      cases h
    · intro h
      change (Sum.inr (Fin.castLE ht i) : Tape max) = .inr (Fin.castLE ht j) at h
      have hc : Fin.castLE ht i = Fin.castLE ht j := Sum.inr.inj h
      have hv : i.val = j.val := congrArg (fun x : Fin max => x.val) hc
      have hij : i = j := Fin.ext hv
      exact congrArg Fin.succ hij

theorem wordShared_ne_trajectory {t max : Nat} (ht : t ≤ max) (target : Bool)
    (i : Fin 6) :
    ∀ j : Fin (t + 1),
      (Sum.inl (wordSharedRole target i) : Tape max) ≠ trajectoryPlacement ht j := by
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · intro h
    change (Sum.inl (wordSharedRole target i) : Tape max) = .inl (1 : Fin 11) at h
    exact wordSharedRole_ne_start target i (Sum.inl.inj h)
  · intro h
    change (Sum.inl (wordSharedRole target i) : Tape max) = .inr (Fin.castLE ht k) at h
    cases h

/-- Every tape used by a bounded word is placed on its own physical tape. -/
theorem wordPlacement_injective {t max : Nat} (ht : t ≤ max) (target : Bool) :
    Function.Injective (wordPlacement ht target) := by
  intro a b h
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          exact congrArg Sum.inl (wordSharedRole_injective target (Sum.inl.inj h))
      | inr j =>
          exact False.elim (wordShared_ne_trajectory ht target i j h)
  | inr i =>
      cases b with
      | inl j =>
          exact False.elim (wordShared_ne_trajectory ht target j i h.symm)
      | inr j =>
          exact congrArg Sum.inr (trajectoryPlacement_injective ht h)

theorem relationPlacement_injective (max : Nat) : Function.Injective (relationPlacement max) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [relationPlacement]

theorem equalityPlacement_injective (max : Nat) : Function.Injective (equalityPlacement max) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [equalityPlacement]

/-- Word subroutines cannot use the row-output tape, even temporarily. -/
theorem wordPlacement_ne_rowOutput {t max : Nat} (ht : t ≤ max) (target : Bool)
    (i : PoweringMachineWord.Tape t) : wordPlacement ht target i ≠ rowOutput max := by
  cases i with
  | inl i =>
      intro h
      exact wordSharedRole_ne_rowOutput target i (Sum.inl.inj h)
  | inr j =>
      refine Fin.cases ?_ (fun i => ?_) j
      · intro h
        change (Sum.inl (1 : Fin 11) : Tape max) = .inl (10 : Fin 11) at h
        have hne : (1 : Fin 11) ≠ 10 := by decide
        exact hne (Sum.inl.inj h)
      · intro h
        change (Sum.inr (Fin.castLE ht i) : Tape max) = .inl (10 : Fin 11) at h
        cases h

/-- A shared role is disjoint from every trajectory tape. This supplies the
position-frame premise of `PoweringMachineWord.finalTapes_other`. -/
theorem shared_ne_wordPlacement_succ {t max : Nat} (ht : t ≤ max) (target : Bool)
    (role : Fin 11) (i : Fin t) :
    (Sum.inl role : Tape max) ≠ wordPlacement ht target (.inr i.succ) := by
  intro h
  change (Sum.inl role : Tape max) = .inr (Fin.castLE ht i) at h
  cases h

end MaxCutGames.Foundations.Complexity.PoweringMachineTapes

/-! Actual powering initialization on the common finite tape set. The first
unary input field is copied by the affine machine and consumed by the checked
header program. The original input and every unrelated tape are preserved.
No runtime graph or vertex count is captured by the finite program. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineInitialize

open Turing
open PoweringMachineLoop PoweringMasterState

abbrev ExtraTape (max : Nat) := PoweringMachineTapes.Tape max ⊕ Unit
abbrev GlobalTape (max : Nat) := HeaderTape ⊕ ExtraTape max
abbrev Label := HeaderLabel ⊕ MachineUnaryAffineAt.Label

def finalOutput (max : Nat) : GlobalTape max := .inr (.inr ())

/-- The unary start vertex and outer counter occupy the same physical tape. -/
def commonPlacement (max : Nat) (tape : PoweringMachineTapes.Tape max) : GlobalTape max :=
  if tape = PoweringMachineTapes.start max then .inl .counter else .inr (.inl tape)

theorem commonPlacement_injective (max : Nat) : Function.Injective (commonPlacement max) := by
  intro a b h
  by_cases ha : a = PoweringMachineTapes.start max <;>
    by_cases hb : b = PoweringMachineTapes.start max <;>
      simp_all [commonPlacement]

@[simp] theorem commonPlacement_start (max : Nat) :
    commonPlacement max (PoweringMachineTapes.start max) = .inl .counter := by
  simp [commonPlacement]

@[simp] theorem commonPlacement_table (max : Nat) :
    commonPlacement max (PoweringMachineTapes.table max) =
      .inr (.inl (PoweringMachineTapes.table max)) := by
  simp [commonPlacement, PoweringMachineTapes.table, PoweringMachineTapes.start]

@[simp] theorem commonPlacement_scratch (max : Nat) :
    commonPlacement max (PoweringMachineTapes.scratch max) =
      .inr (.inl (PoweringMachineTapes.scratch max)) := by
  simp [commonPlacement, PoweringMachineTapes.scratch, PoweringMachineTapes.start]

@[simp] theorem commonPlacement_rowOutput (max : Nat) :
    commonPlacement max (PoweringMachineTapes.rowOutput max) =
      .inr (.inl (PoweringMachineTapes.rowOutput max)) := by
  simp [commonPlacement, PoweringMachineTapes.rowOutput, PoweringMachineTapes.start]

theorem commonPlacement_ne_finalOutput (max : Nat) (tape : PoweringMachineTapes.Tape max) :
    commonPlacement max tape ≠ finalOutput max := by
  by_cases h : tape = PoweringMachineTapes.start max <;>
    simp [commonPlacement, finalOutput, h]

theorem commonPlacement_ne_header (max : Nat) (tape : PoweringMachineTapes.Tape max)
    (field : HeaderTape) (hne : field ≠ .counter) :
    commonPlacement max tape ≠ .inl field := by
  by_cases h : tape = PoweringMachineTapes.start max <;>
    simp [commonPlacement, h, Ne.symm hne]

/-- Header writers use the common work tapes but emit on the final output.
The relation producer continues to use `commonPlacement rowOutput`. -/
def headerPlacement (max : Nat) (tape : PoweringMachineTapes.Tape max) : GlobalTape max :=
  if tape = PoweringMachineTapes.rowOutput max then finalOutput max
  else commonPlacement max tape

theorem headerPlacement_injective (max : Nat) : Function.Injective (headerPlacement max) := by
  intro a b h
  by_cases ha : a = PoweringMachineTapes.rowOutput max
  · subst a
    by_cases hb : b = PoweringMachineTapes.rowOutput max
    · exact hb.symm
    · simp only [headerPlacement, ite_eq_right hb] at h
      exact False.elim (commonPlacement_ne_finalOutput max b h.symm)
  · by_cases hb : b = PoweringMachineTapes.rowOutput max
    · subst b
      simp only [headerPlacement, ite_eq_right ha] at h
      exact False.elim (commonPlacement_ne_finalOutput max a h)
    · simp only [headerPlacement, ite_eq_right ha, ite_eq_right hb] at h
      exact commonPlacement_injective max h

@[simp] theorem headerPlacement_rowOutput (max : Nat) :
    headerPlacement max (PoweringMachineTapes.rowOutput max) = finalOutput max := by
  simp [headerPlacement]

theorem headerPlacement_eq_common (max : Nat) (tape : PoweringMachineTapes.Tape max)
    (hne : tape ≠ PoweringMachineTapes.rowOutput max) :
    headerPlacement max tape = commonPlacement max tape := by simp [headerPlacement, hne]

theorem headerPlacement_ne_data (max : Nat) (tape : PoweringMachineTapes.Tape max) :
    headerPlacement max tape ≠ commonPlacement max (PoweringMachineTapes.rowOutput max) := by
  by_cases h : tape = PoweringMachineTapes.rowOutput max
  · simp only [headerPlacement, ite_eq_left h]
    exact Ne.symm (commonPlacement_ne_finalOutput max _)
  · rw [headerPlacement_eq_common max tape h]
    exact fun heq => h (commonPlacement_injective max heq)

theorem headerPlacement_ne_header (max : Nat) (tape : PoweringMachineTapes.Tape max)
    (field : HeaderTape) (hne : field ≠ .counter) :
    headerPlacement max tape ≠ .inl field := by
  by_cases h : tape = PoweringMachineTapes.rowOutput max
  · simp [headerPlacement, h, finalOutput]
  · rw [headerPlacement_eq_common max tape h]
    exact commonPlacement_ne_header max tape field hne

/- Alphabet equality transport makes the existing dependent disjoint-tape
embedding usable with the homogeneous Boolean primitives. These are equality
transports, not a second implementation of the header machine. -/

private def castTapes_inline_PoweringMachineInitialize {K : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (tapes : ∀ k, List (Γ k)) : ∀ k, List (Δ k) := h ▸ tapes

private def castStatement_inline_PoweringMachineInitialize {K Λ σ : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (q : TM2.Stmt Γ Λ σ) : TM2.Stmt Δ Λ σ := h ▸ q

private def castConfiguration_inline_PoweringMachineInitialize {K Λ σ : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Δ Λ σ := h ▸ c

private theorem castTapes_apply_inline_PoweringMachineInitialize {K : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (tapes : ∀ k, List (Γ k)) (k : K) :
    castTapes_inline_PoweringMachineInitialize h tapes k = cast (congrArg (fun alphabet => List (alphabet k)) h) (tapes k) := by
  cases h
  rfl

private theorem castConfiguration_mk_inline_PoweringMachineInitialize {K Λ σ : Type} {Γ Δ : K → Type} (h : Γ = Δ)
    (label : Option Λ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    castConfiguration_inline_PoweringMachineInitialize h ⟨label, state, tapes⟩ = ⟨label, state, castTapes_inline_PoweringMachineInitialize h tapes⟩ := by
  cases h
  rfl

private theorem stepAux_cast_inline_PoweringMachineInitialize {K Λ σ : Type} [DecidableEq K]
    {Γ Δ : K → Type} (h : Γ = Δ) (q : TM2.Stmt Γ Λ σ)
    (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (castStatement_inline_PoweringMachineInitialize h q) state (castTapes_inline_PoweringMachineInitialize h tapes) =
      castConfiguration_inline_PoweringMachineInitialize h (TM2.stepAux q state tapes) := by
  cases h
  rfl

private theorem boolAlphabet_eq_inline_PoweringMachineInitialize (max : Nat) :
    MachineEmbedding.Alphabet HeaderAlphabet (fun _ : ExtraTape max => Bool) =
      (fun _ : GlobalTape max => Bool) := by
  funext tape
  cases tape <;> rfl

def mergeTapes {max : Nat} (header : HeaderTape → List Bool)
    (extra : ExtraTape max → List Bool) : GlobalTape max → List Bool
  | .inl k => header k
  | .inr e => extra e

private theorem castTapes_embedding_inline_PoweringMachineInitialize {max : Nat} (header : HeaderTape → List Bool)
    (extra : ExtraTape max → List Bool) :
    castTapes_inline_PoweringMachineInitialize (boolAlphabet_eq_inline_PoweringMachineInitialize max) (MachineEmbedding.tapes header extra) =
      mergeTapes header extra := by
  funext tape
  rw [castTapes_apply_inline_PoweringMachineInitialize]
  cases tape <;> rfl

private def dropUnit_inline_PoweringMachineInitialize (N : Nat) : (Master N × Unit) ≃ Master N where
  toFun := Prod.fst
  invFun state := (state, ())
  left_inv := by rintro ⟨state, ⟨⟩⟩; rfl
  right_inv := by intro state; rfl

/-- The native checked header statement is embedded and its inert extra
register removed. All four native header tapes keep their identities. -/
def headerStatement (max N B : Nat) (label : HeaderLabel) :
    TM2.Stmt (fun _ : GlobalTape max => Bool) Label (Master N) :=
  MachineStateEquiv.statement (dropUnit_inline_PoweringMachineInitialize N)
    (castStatement_inline_PoweringMachineInitialize (boolAlphabet_eq_inline_PoweringMachineInitialize max)
      (MachineEmbedding.statement (Λextra := MachineUnaryAffineAt.Label)
        (τ := Unit) none (headerProgram (σ := OtherRegisters N) B label)))

def headerConfiguration {max N : Nat} (extra : ExtraTape max → List Bool)
    (c : TM2.Cfg HeaderAlphabet HeaderLabel (Master N)) :
    TM2.Cfg (fun _ : GlobalTape max => Bool) Label (Master N) :=
  ⟨c.l.map Sum.inl, c.var, mergeTapes c.stk extra⟩

private theorem headerConfiguration_eq_inline_PoweringMachineInitialize {max N : Nat} (extra : ExtraTape max → List Bool)
    (c : TM2.Cfg HeaderAlphabet HeaderLabel (Master N)) :
    headerConfiguration extra c =
      MachineStateEquiv.configuration (dropUnit_inline_PoweringMachineInitialize N)
        (castConfiguration_inline_PoweringMachineInitialize (boolAlphabet_eq_inline_PoweringMachineInitialize max)
          (MachineEmbedding.configuration (Λextra := MachineUnaryAffineAt.Label)
            none () extra c)) := by
  cases c with
  | mk label state tapes =>
    simp only [MachineEmbedding.configuration, castConfiguration_mk_inline_PoweringMachineInitialize,
      MachineStateEquiv.configuration, castTapes_embedding_inline_PoweringMachineInitialize, dropUnit_inline_PoweringMachineInitialize,
      Equiv.coe_fn_mk, headerConfiguration]
    cases label <;> rfl

theorem stepAux_headerStatement (max N B : Nat) (label : HeaderLabel)
    (state : Master N) (header : HeaderTape → List Bool)
    (extra : ExtraTape max → List Bool) :
    TM2.stepAux (headerStatement max N B label) state (mergeTapes header extra) =
      headerConfiguration extra (TM2.stepAux (headerProgram B label) state header) := by
  rw [headerStatement, MachineStateEquiv.stepAux_transport_symm]
  change MachineStateEquiv.configuration (dropUnit_inline_PoweringMachineInitialize N)
    (TM2.stepAux (castStatement_inline_PoweringMachineInitialize (boolAlphabet_eq_inline_PoweringMachineInitialize max)
      (MachineEmbedding.statement none (headerProgram B label))) (state, ())
      (mergeTapes header extra)) = _
  rw [← castTapes_embedding_inline_PoweringMachineInitialize, stepAux_cast_inline_PoweringMachineInitialize, MachineEmbedding.stepAux_simulation]
  exact (headerConfiguration_eq_inline_PoweringMachineInitialize extra _).symm

def program (max N B : Nat) : Label →
    TM2.Stmt (fun _ : GlobalTape max => Bool) Label (Master N)
  | .inl label => headerStatement max N B label
  | .inr .seed => MachineUnaryAffineAt.seed (.inl .source) 0 (.inr .scan)
  | .inr .scan => MachineUnaryAffineAt.scan
      (commonPlacement max (PoweringMachineTapes.table max))
      (commonPlacement max (PoweringMachineTapes.scratch max))
      (.inl .source) 1 (.inr .scan) (.inr .restore)
  | .inr .restore => Reduction.MachineTransfer.loopAt
      (commonPlacement max (PoweringMachineTapes.scratch max))
      (commonPlacement max (PoweringMachineTapes.table max))
      id false (.inr .restore) (some (.inl .initialize))

theorem headerStep (max N B : Nat) (extra : ExtraTape max → List Bool)
    (a b : TM2.Cfg HeaderAlphabet HeaderLabel (Master N))
    (run : TM2.step (headerProgram B) a = some b) :
    TM2.step (program max N B) (headerConfiguration extra a) =
      some (headerConfiguration extra b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => simp [TM2.step] at run
    | some label =>
      have hb : TM2.stepAux (headerProgram B label) state tapes = b := Option.some.inj run
      rw [← hb]
      change some (TM2.stepAux (headerStatement max N B label) state
        (mergeTapes tapes extra)) = _
      rw [stepAux_headerStatement]

theorem headerTrace (max N B vertices : Nat) (extra : ExtraTape max → List Bool)
    (state : Master N) :
    (MachineComposition.advance (TM2.step (program max N B)))^[vertices + 2]
      (some ⟨some (.inl .initialize), state,
        mergeTapes (initialTapes vertices []) extra⟩) =
      some ⟨none, (state.1, none), mergeTapes (finalTapes B vertices []) extra⟩ := by
  exact MachineComposition.liftSuccessfulTrace (TM2.step (headerProgram B))
    (TM2.step (program max N B)) (headerConfiguration extra)
    (headerStep max N B extra) (vertices + 2) _ _
    (PoweringMachineLoop.headerTrace B vertices [] state.1 state.2)

def initialGlobalTapes {max : Nat} (extra : ExtraTape max → List Bool) :
    GlobalTape max → List Bool := mergeTapes (fun _ => []) extra

theorem copyFirstTrace (max N B vertices : Nat) (extra : ExtraTape max → List Bool)
    (suffix : List Bool)
    (input : extra (.inl (PoweringMachineTapes.table max)) = encodeWord vertices ++ suffix)
    (scratch : extra (.inl (PoweringMachineTapes.scratch max)) = [])
    (state : Master N) :
    (MachineComposition.advance (TM2.step (program max N B)))^[2 * (vertices + 1) + 1]
      (some ⟨some (.inr .seed), state, initialGlobalTapes extra⟩) =
      some ⟨some (.inl .initialize), (state.1, none),
        mergeTapes (initialTapes vertices []) extra⟩ := by
  have copied := MachineUnaryAffineAt.seededAffineTrace
    (commonPlacement max (PoweringMachineTapes.table max))
    (commonPlacement max (PoweringMachineTapes.scratch max)) (.inl HeaderTape.source)
    (by
      intro heq
      have hroles := commonPlacement_injective max heq
      simp [PoweringMachineTapes.table, PoweringMachineTapes.scratch] at hroles)
    (by simp) (by simp) 1 0 (.inr .seed) (.inr .scan) (.inr .restore)
    (some (.inl .initialize)) (program max N B) rfl rfl rfl
    (initialGlobalTapes extra) vertices suffix
    (by simpa [initialGlobalTapes, mergeTapes] using input)
    (by simpa [initialGlobalTapes, mergeTapes] using scratch) state.1 state.2
  have handoff : Function.update (initialGlobalTapes extra) (.inl HeaderTape.source)
      (encodeWord (1 * vertices + 0) ++ initialGlobalTapes extra (.inl .source)) =
      mergeTapes (initialTapes vertices []) extra := by
    funext tape
    cases tape with
    | inl field => cases field <;> simp [initialGlobalTapes, mergeTapes, initialTapes]
    | inr field => simp [initialGlobalTapes, mergeTapes]
  rw [handoff] at copied
  exact copied

/-- A concrete successful trace: copy the live input count, then execute the
existing header machine on that copy. Runtime is exactly `3*vertices+5`. -/
theorem initializeTrace (max N B vertices : Nat) (extra : ExtraTape max → List Bool)
    (suffix : List Bool)
    (input : extra (.inl (PoweringMachineTapes.table max)) = encodeWord vertices ++ suffix)
    (scratch : extra (.inl (PoweringMachineTapes.scratch max)) = [])
    (state : Master N) :
    (MachineComposition.advance (TM2.step (program max N B)))^[3 * vertices + 5]
      (some ⟨some (.inr .seed), state, initialGlobalTapes extra⟩) =
      some ⟨none, (state.1, none), mergeTapes (finalTapes B vertices []) extra⟩ := by
  rw [show 3 * vertices + 5 = (vertices + 2) + (2 * (vertices + 1) + 1) by omega,
    Function.iterate_add_apply, copyFirstTrace max N B vertices extra suffix input scratch state]
  exact headerTrace max N B vertices extra (state.1, none)

def initializeInTime (max N B vertices : Nat) (extra : ExtraTape max → List Bool)
    (suffix : List Bool)
    (input : extra (.inl (PoweringMachineTapes.table max)) = encodeWord vertices ++ suffix)
    (scratch : extra (.inl (PoweringMachineTapes.scratch max)) = [])
    (state : Master N) :
    StateTransition.EvalsToInTime (TM2.step (program max N B))
      ⟨some (.inr .seed), state, initialGlobalTapes extra⟩
      (some ⟨none, (state.1, none), mergeTapes (finalTapes B vertices []) extra⟩)
      (3 * vertices + 5) where
  steps := 3 * vertices + 5
  evals_in_steps := initializeTrace max N B vertices extra suffix input scratch state
  steps_le_m := Nat.le_refl _

/-- The five finite initialization labels can be placed in a caller's program.
The native halt becomes its chosen continuation in the very same transition. -/
def instruction {Λ : Type} (max N B : Nat) (labels : Label → Λ) (exit : Option Λ)
    (label : Label) : TM2.Stmt (fun _ : GlobalTape max => Bool) Λ (Master N) :=
  MachineSubroutine.statement labels exit (program max N B label)

def initializeAtInTime {Λ : Type} (max N B vertices : Nat)
    (labels : Label → Λ) (exit : Option Λ)
    (caller : Λ → TM2.Stmt (fun _ : GlobalTape max => Bool) Λ (Master N))
    (atLabels : ∀ label, caller (labels label) = instruction max N B labels exit label)
    (extra : ExtraTape max → List Bool) (suffix : List Bool)
    (input : extra (.inl (PoweringMachineTapes.table max)) = encodeWord vertices ++ suffix)
    (scratch : extra (.inl (PoweringMachineTapes.scratch max)) = [])
    (state : Master N) :
    StateTransition.EvalsToInTime (TM2.step caller)
      ⟨some (labels (.inr .seed)), state, initialGlobalTapes extra⟩
      (some ⟨exit, (state.1, none), mergeTapes (finalTapes B vertices []) extra⟩)
      (3 * vertices + 5) :=
  MachineSubroutine.execution labels exit (program max N B) caller atLabels
    (initializeInTime max N B vertices extra suffix input scratch state)

@[simp] theorem final_counter (max B vertices : Nat) (extra : ExtraTape max → List Bool) :
    mergeTapes (finalTapes B vertices []) extra
      (commonPlacement max (PoweringMachineTapes.start max)) = encodeWord vertices := by
  simp [mergeTapes, finalTapes]

@[simp] theorem final_vertices (max B vertices : Nat) (extra : ExtraTape max → List Bool) :
    mergeTapes (finalTapes B vertices []) extra (.inl .vertices) = encodeWord vertices := rfl

@[simp] theorem final_darts (max B vertices : Nat) (extra : ExtraTape max → List Bool) :
    mergeTapes (finalTapes B vertices []) extra (.inl .darts) = encodeWord (B * vertices) := rfl

@[simp] theorem final_extra (max B vertices : Nat) (extra : ExtraTape max → List Bool)
    (tape : ExtraTape max) :
    mergeTapes (finalTapes B vertices []) extra (.inr tape) = extra tape := rfl

end MaxCutGames.Foundations.Complexity.PoweringMachineInitialize

end OAI
