import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.PoweringPlanBudget
import OAI.Combinatorics.IndependentSets.Machines.PoweringMachineTapes

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.PoweringMachineRowHeaders

open Turing MachineComposition
open PCP PoweringRowHeaderSemantics
open PoweringMachineTapes

variable {K Λ σ : Type} [DecidableEq K]
variable {vertices d max : Nat}

def headerPlacement {t max : Nat} (h : t ≤ max) : PoweringMachineWord.Tape t → Tape max :=
  (Equiv.swap (leftEndpoint max) (rowOutput max)) ∘ wordPlacement h false

theorem headerPlacement_injective {t max : Nat} (h : t ≤ max) :
    Function.Injective (headerPlacement h) :=
  (Equiv.swap (leftEndpoint max) (rowOutput max)).injective.comp (wordPlacement_injective h false)

@[simp] theorem headerPlacement_table {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 0) = table max := by
  simp [headerPlacement, table, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_query {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 1) = query max := by
  simp [headerPlacement, query, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_scan {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 2) = scan max := by
  simp [headerPlacement, scan, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_reverse {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 3) = reverse max := by
  simp [headerPlacement, reverse, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_scratch {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 4) = scratch max := by
  simp [headerPlacement, scratch, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_output {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inl 5) = rowOutput max := by
  simp [headerPlacement]

@[simp] theorem headerPlacement_start {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inr (PoweringMachineWord.first t)) = start max := by
  simp [headerPlacement, start, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_succ {t max : Nat} (h : t ≤ max) (i : Fin t) :
    headerPlacement h (.inr i.succ) = .inr (Fin.castLE h i) := by
  simp [headerPlacement, leftEndpoint, rowOutput, Equiv.swap_apply_def]

abbrev Label (n : Nat) := MachineUnaryAffineAt.Label ⊕
  (MachineUnaryAffineAt.Label ⊕ PoweringMachineWord.Label (n + 1))

def entry (n : Nat) : Label n := .inl .seed

def tailEntry (n : Nat) (direction : Bool) : Label n :=
  if direction then .inr (.inr (PoweringMachineWord.entry (n + 1))) else .inr (.inl .seed)

def affineInstruction (source work output : K) (coefficient offset : Nat)
    (labels : MachineUnaryAffineAt.Label → Λ) (exit : Option Λ) :
    MachineUnaryAffineAt.Label → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .seed => MachineUnaryAffineAt.seed output offset (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source work output coefficient (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt work source id false (labels .restore) exit

def instruction (n : Nat) (h : n + 1 ≤ max) (placement : Tape max → K)
    (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n → Λ) (exit : Option Λ) :
    Label n → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .inl q => affineInstruction (placement (start max)) (placement (scratch max))
      (placement (rowOutput max)) (blockSize d n) (reverseOffset d n ports direction)
      (fun z => labels (.inl z)) (some (labels (tailEntry n direction))) q
  | .inr (.inl q) => PoweringMachineWord.copyInstruction
      (placement (start max)) (placement (scratch max)) (placement (rowOutput max))
      (fun z => labels (.inr (.inl z))) exit q
  | .inr (.inr q) => PoweringMachineWord.instruction (n + 1)
      (placement ∘ headerPlacement h) ports (fun z => labels (.inr (.inr z))) exit q

def afterReverse (n : Nat) (placement : Tape max → K) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) : K → List Bool :=
  Function.update base (placement (rowOutput max))
    (encodeWord (reverseValue d n vertex ports direction) ++ base (placement (rowOutput max)))

def finalTapes (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (base : K → List Bool) : K → List Bool :=
  let mid := afterReverse n placement vertex ports direction base
  if direction then
    PoweringMachineWord.finalTapes input (n + 1) (placement ∘ headerPlacement h) vertex ports mid
  else Function.update mid (placement (rowOutput max))
    (encodeWord vertex.val ++ mid (placement (rowOutput max)))

def steps (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : Nat :=
  (2 * (vertex.val + 1) + 1) +
    if direction then PoweringMachineWord.steps input (n + 1) vertex ports
    else 2 * (vertex.val + 1) + 1

theorem headerTrace (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction n h placement ports direction labels exit l)
    (base : K → List Bool) (tableWord : base (placement (table max)) = PortTables.tableBits input)
    (scratchEmpty : base (placement (scratch max)) = []) (suffix : List Bool)
    (sourceWord : base (placement (start max)) = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps input n vertex ports direction]
      (some ⟨some (labels (entry n)), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), finalTapes input n h placement vertex ports direction base⟩ ∧
    finalTapes input n h placement vertex ports direction base (placement (rowOutput max)) =
      encodeWords (headerWords input n vertex ports direction) ++ base (placement (rowOutput max)) := by
  have hd (i j : Tape max) (hne : i ≠ j) : placement i ≠ placement j :=
    fun eq => hne (distinct eq)
  have hsourceOut : placement (start max) ≠ placement (rowOutput max) :=
    hd _ _ (by simp [start, rowOutput])
  have hscratchOut : placement (scratch max) ≠ placement (rowOutput max) :=
    hd _ _ (by simp [scratch, rowOutput])
  have htableOut : placement (table max) ≠ placement (rowOutput max) :=
    hd _ _ (by simp [table, rowOutput])
  let mid := afterReverse n placement vertex ports direction base
  have hrev := MachineUnaryAffineAt.seededAffineTrace
    (placement (start max)) (placement (scratch max)) (placement (rowOutput max))
    (hd _ _ (by simp [start, scratch])) hsourceOut hscratchOut
    (blockSize d n) (reverseOffset d n ports direction)
    (labels (.inl .seed)) (labels (.inl .scan)) (labels (.inl .restore))
    (some (labels (tailEntry n direction))) program
    (atLabels (.inl .seed)) (atLabels (.inl .scan)) (atLabels (.inl .restore))
    base vertex.val suffix sourceWord scratchEmpty ambient register
  have hreverseTrace : (advance (TM2.step program))^[2 * (vertex.val + 1) + 1]
      (some ⟨some (labels (entry n)), (ambient, register), base⟩) =
      some ⟨some (labels (tailEntry n direction)), (ambient, none), mid⟩ := by
    simpa only [entry, mid, afterReverse, reverseValue] using hrev
  have hmidSource : mid (placement (start max)) = encodeWord vertex.val ++ suffix := by
    simpa only [mid, afterReverse, Function.update_of_ne hsourceOut] using sourceWord
  have hmidScratch : mid (placement (scratch max)) = [] := by
    simpa only [mid, afterReverse, Function.update_of_ne hscratchOut] using scratchEmpty
  have hmidTable : mid (placement (table max)) = PortTables.tableBits input := by
    simpa only [mid, afterReverse, Function.update_of_ne htableOut] using tableWord
  cases direction with
  | false =>
    have hcopy := MachineUnaryAffineAt.seededAffineTrace
      (placement (start max)) (placement (scratch max)) (placement (rowOutput max))
      (hd _ _ (by simp [start, scratch])) hsourceOut hscratchOut 1 0
      (labels (.inr (.inl .seed))) (labels (.inr (.inl .scan)))
      (labels (.inr (.inl .restore))) exit program
      (atLabels (.inr (.inl .seed))) (atLabels (.inr (.inl .scan)))
      (atLabels (.inr (.inl .restore))) mid vertex.val suffix hmidSource hmidScratch ambient none
    constructor
    · rw [steps, ite_eq_right Bool.false_ne_true, Function.iterate_add_apply, hreverseTrace]
      simpa only [tailEntry, Bool.false_eq_true, ite_false, finalTapes, Nat.one_mul,
        Nat.add_zero] using hcopy
    · simp only [finalTapes, Bool.false_eq_true, ite_false, Function.update_self,
        afterReverse, headerWords, tailVertex, encodeWords, List.append_nil, List.append_assoc]
  | true =>
    have hword := PoweringMachineWord.wordTrace input (n + 1)
      (placement ∘ headerPlacement h) (distinct.comp (headerPlacement_injective h)) vertex ports
      (fun z => labels (.inr (.inr z))) exit program (fun z => atLabels (.inr (.inr z))) mid
      (by simpa only [Function.comp_apply, headerPlacement_table] using hmidTable)
      (by simpa only [Function.comp_apply, headerPlacement_scratch] using hmidScratch)
      suffix (by simpa only [Function.comp_apply, headerPlacement_start] using hmidSource) ambient none
    constructor
    · rw [steps, ite_eq_left rfl, Nat.add_comm, Function.iterate_add_apply, hreverseTrace]
      simpa only [tailEntry, ite_true, finalTapes] using hword.1
    · have hout := hword.2
      simp only [Function.comp_apply, headerPlacement_output] at hout
      simpa only [finalTapes, ite_true, mid, afterReverse, Function.update_self,
        headerWords, tailVertex, encodeWords, List.append_nil, List.append_assoc] using hout

theorem finalTapes_other (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (base : K → List Bool) (k : K)
    (hquery : k ≠ placement (query max)) (hscan : k ≠ placement (scan max))
    (hreverse : k ≠ placement (reverse max)) (houtput : k ≠ placement (rowOutput max))
    (hpositions : ∀ i : Fin (n + 1), k ≠ placement (.inr (Fin.castLE h i))) :
    finalTapes input n h placement vertex ports direction base k = base k := by
  cases direction with
  | false => simp only [finalTapes, Bool.false_eq_true, ite_false,
      Function.update_of_ne houtput, afterReverse]
  | true =>
    let mid := afterReverse n placement vertex ports true base
    have hw := PoweringMachineWord.finalTapes_other input (n + 1)
      (placement ∘ headerPlacement h) vertex ports mid k
      (by simpa only [Function.comp_apply, headerPlacement_query] using hquery)
      (by simpa only [Function.comp_apply, headerPlacement_scan] using hscan)
      (by simpa only [Function.comp_apply, headerPlacement_reverse] using hreverse)
      (by simpa only [Function.comp_apply, headerPlacement_output] using houtput)
      (fun i => by simpa only [Function.comp_apply, headerPlacement_succ] using hpositions i)
    calc
      _ = mid k := hw
      _ = base k := by simp only [mid, afterReverse, Function.update_of_ne houtput]

theorem finalTapes_shared (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (base : K → List Bool) (i : Fin 11)
    (hquery : i ≠ 2) (hscan : i ≠ 3) (hreverse : i ≠ 4) (houtput : i ≠ 10) :
    finalTapes input n h placement vertex ports direction base (placement (.inl i)) =
      base (placement (.inl i)) := by
  apply finalTapes_other input n h placement vertex ports direction base
  · intro heq; exact hquery (Sum.inl.inj (distinct heq))
  · intro heq; exact hscan (Sum.inl.inj (distinct heq))
  · intro heq; exact hreverse (Sum.inl.inj (distinct heq))
  · intro heq; exact houtput (Sum.inl.inj (distinct heq))
  · intro j heq; cases distinct heq

theorem steps_le (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    steps input n vertex ports direction ≤
      (14 * (n + 1) + 4) * (PortTables.tableBits input).length + 12 * (n + 1) + 6 := by
  have hv : vertex.val ≤ (PortTables.tableBits input).length :=
    Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length input)
  have hw := PoweringMachineWord.steps_le input (n + 1) vertex ports
  cases direction <;> simp only [steps, Bool.false_eq_true, ite_false, ite_true]
  · simp only [Nat.add_mul]
    omega
  · calc
      _ ≤ (2 * (PortTables.tableBits input).length + 3) +
          ((14 * (n + 1) + 2) * (PortTables.tableBits input).length + 12 * (n + 1) + 3) :=
        Nat.add_le_add (by omega) hw
      _ = _ := by simp only [Nat.add_mul]; omega

def machine (degree n : Nat) (ports : Fin (n + 1) → Fin degree) (direction : Bool) : FinTM2 where
  K := PoweringMachineTapes.Tape (n + 1)
  k₀ := table (n + 1)
  k₁ := rowOutput (n + 1)
  Γ _ := Bool
  Λ := Label n
  main := entry n
  σ := (Unit × Bool × Option Bool) × Option Bool
  initialState := (((), false, none), none)
  m := instruction n (Nat.le_refl (n + 1)) id ports direction id none

end IndependentSetsGames.Foundations.Complexity.PoweringMachineRowHeaders

end OAI
