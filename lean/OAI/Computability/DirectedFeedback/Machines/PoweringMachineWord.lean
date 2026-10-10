import Mathlib
import OAI.Computability.DirectedFeedback.Machines.PoweringMachineLoop

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineWord

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

end DFVSGames.Foundations.Complexity.PoweringMachineWord
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineTapes

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

def wordSharedRole (target : Bool) (i : Fin 6) : Fin 11 :=
  if i = 0 then 0 else if i = 1 then 2 else if i = 2 then 3 else
  if i = 3 then 4 else if i = 4 then 5 else if target then 7 else 6

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

theorem shared_ne_wordPlacement_succ {t max : Nat} (ht : t ≤ max) (target : Bool)
    (role : Fin 11) (i : Fin t) :
    (Sum.inl role : Tape max) ≠ wordPlacement ht target (.inr i.succ) := by
  intro h
  change (Sum.inl role : Tape max) = .inr (Fin.castLE ht i) at h
  cases h

end DFVSGames.Foundations.Complexity.PoweringMachineTapes
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineInitialize

open Turing
open PoweringMachineLoop PoweringMasterState

abbrev ExtraTape (max : Nat) := PoweringMachineTapes.Tape max ⊕ Unit
abbrev GlobalTape (max : Nat) := HeaderTape ⊕ ExtraTape max
abbrev Label := HeaderLabel ⊕ MachineUnaryAffineAt.Label

def finalOutput (max : Nat) : GlobalTape max := .inr (.inr ())

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

end DFVSGames.Foundations.Complexity.PoweringMachineInitialize
end

section

namespace DFVSGames.Foundations.Complexity.PoweringGlobalEnumeration

open PoweringMachineLoop PoweringMachineInitialize

def headerTapeEquiv : HeaderTape ≃ Fin 4 where
  toFun
    | .source => 0
    | .counter => 1
    | .vertices => 2
    | .darts => 3
  invFun i := if i = 0 then .source else if i = 1 then .counter
    else if i = 2 then .vertices else .darts
  left_inv tape := by cases tape <;> rfl
  right_inv i := by fin_cases i <;> rfl

def unitTapeEquiv : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv i := (Fin.eq_zero i).symm

def sharedTapeEquiv (max : Nat) : PoweringMachineTapes.Tape max ≃ Fin (11 + max) :=
  finSumFinEquiv

def extraTapeEquiv (max : Nat) : ExtraTape max ≃ Fin (11 + max + 1) :=
  (Equiv.sumCongr (sharedTapeEquiv max) unitTapeEquiv).trans finSumFinEquiv

def globalTapeEquiv (max : Nat) : GlobalTape max ≃ Fin (4 + (11 + max + 1)) :=
  (Equiv.sumCongr headerTapeEquiv (extraTapeEquiv max)).trans finSumFinEquiv

def enumeration (max : Nat) : Fin (4 + (11 + max + 1)) ≃ GlobalTape max :=
  (globalTapeEquiv max).symm

@[simp] theorem globalTapeEquiv_enumeration (max : Nat) (i : Fin (4 + (11 + max + 1))) :
    globalTapeEquiv max (enumeration max i) = i :=
  (globalTapeEquiv max).apply_symm_apply i

@[simp] theorem enumeration_globalTapeEquiv (max : Nat) (tape : GlobalTape max) :
    enumeration max (globalTapeEquiv max tape) = tape :=
  (globalTapeEquiv max).symm_apply_apply tape

@[simp] theorem source_index (max : Nat) :
    (globalTapeEquiv max (.inl .source)).val = 0 := rfl

@[simp] theorem counter_index (max : Nat) :
    (globalTapeEquiv max (.inl .counter)).val = 1 := rfl

@[simp] theorem vertices_index (max : Nat) :
    (globalTapeEquiv max (.inl .vertices)).val = 2 := rfl

@[simp] theorem darts_index (max : Nat) :
    (globalTapeEquiv max (.inl .darts)).val = 3 := rfl

theorem sharedRole_index (max : Nat) (i : Fin 11) :
    (globalTapeEquiv max (.inr (.inl (.inl i)))).val = 4 + i.val := rfl

theorem trajectory_index (max : Nat) (i : Fin max) :
    (globalTapeEquiv max (.inr (.inl (.inr i)))).val = 4 + (11 + i.val) := rfl

@[simp] theorem finalOutput_index (max : Nat) :
    (globalTapeEquiv max (finalOutput max)).val = 4 + (11 + max) := rfl

theorem card_globalTape (max : Nat) :
    Fintype.card (GlobalTape max) = 4 + (11 + max + 1) := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (globalTapeEquiv max)

theorem natCard_globalTape (max : Nat) :
    Nat.card (GlobalTape max) = 4 + (11 + max + 1) := by
  simpa only [Nat.card_fin] using Nat.card_congr (globalTapeEquiv max)

def allTapes (max : Nat) : List (GlobalTape max) := List.ofFn (enumeration max)

theorem allTapes_length (max : Nat) : (allTapes max).length = 4 + (11 + max + 1) := by
  simpa only [allTapes] using (List.length_ofFn (f := enumeration max))

theorem mem_allTapes (max : Nat) (tape : GlobalTape max) : tape ∈ allTapes max := by
  change tape ∈ List.ofFn (enumeration max)
  apply List.mem_ofFn.mpr
  exact ⟨globalTapeEquiv max tape, enumeration_globalTapeEquiv max tape⟩

end DFVSGames.Foundations.Complexity.PoweringGlobalEnumeration
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineRelation

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

abbrev Alphabet (_ : K) := Bool

def address (vertex : Fin n) (port : Fin d) (position : Fin 4096) : Nat :=
  (4098 * d) * vertex.val + (4098 * port.val + 4 + position.val)

def value (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d)
    (position : Fin 4096) : Nat :=
  GraphTables.bitWord table.relations[PortTables.rowIndex n d (vertex, port)][position]

theorem selected (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d)
    (position : Fin 4096) :
    (PortTables.tableWords table)[address vertex port position]? =
      some (value table vertex port position) := by
  have h := PortTableLookup.relation_word table (PortTables.rowIndex n d (vertex, port)) position
  have hindex : address vertex port position =
      4 + 4098 * (PortTables.rowIndex n d (vertex, port)).val + position.val := by
    simp only [address, PortTables.rowIndex_val, Nat.mul_add, Nat.mul_assoc]
    omega
  rw [hindex]
  exact h

def instruction (source : K) (tape : Fin 5 → K) (port : Fin d) (position : Fin 4096)
    (labels : MachineAffineLookup.Label → Λ) (exit : Option Λ) :
    MachineAffineLookup.Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineAffineLookup.instruction source tape (4098 * d)
    (4098 * port.val + 4 + position.val) labels exit

theorem relationTrace (source : K) (tape : Fin 5 → K)
    (distinct : Function.Injective tape) (outside : ∀ i, source ≠ tape i)
    (port : Fin d) (position : Fin 4096)
    (labels : MachineAffineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction source tape port position labels exit l)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (tableWord : base (tape 0) = PortTables.tableBits table) (scratchEmpty : base (tape 4) = [])
    (suffix : List Bool) (sourceWord : base source = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineAffineLookup.steps (PortTables.tableWords table)
      vertex.val (4098 * d) (4098 * port.val + 4 + position.val)]
      (some ⟨some (labels .seed), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), MachineAffineLookup.finalTapes tape base
        (PortTables.tableWords table) (address vertex port position) (value table vertex port position)⟩ :=
  MachineAffineLookup.affineLookupTrace source tape distinct outside
    (4098 * d) (4098 * port.val + 4 + position.val) labels exit program atLabels
    base (PortTables.tableWords table) tableWord scratchEmpty vertex.val suffix sourceWord
    (value table vertex port position) (selected table vertex port position) ambient register

theorem steps_le (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d)
    (position : Fin 4096) :
    MachineAffineLookup.steps (PortTables.tableWords table) vertex.val
      (4098 * d) (4098 * port.val + 4 + position.val) ≤
      7 * (PortTables.tableBits table).length + 6 :=
  MachineAffineLookup.steps_le_table (PortTables.tableWords table) vertex.val
    (4098 * d) (4098 * port.val + 4 + position.val) (value table vertex port position)
    (selected table vertex port position)
    (Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length table))

theorem value_eq_accepts (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d)
    (left right : PortTables.Label) :
    value table vertex port (GraphTables.relationIndex (left, right)) =
      GraphTables.bitWord (PortTables.accepts table (vertex, port) left right) := rfl

def machine (degree : Nat) (port : Fin degree) (position : Fin 4096) : FinTM2 :=
  MachineAffineLookup.machine (4098 * degree) (4098 * port.val + 4 + position.val)

end DFVSGames.Foundations.Complexity.PoweringMachineRelation
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
