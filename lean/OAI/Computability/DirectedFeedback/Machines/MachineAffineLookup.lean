import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineLookupSpec

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineAffineLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

inductive Label
  | seed | scan | restore | copyFirst | copySecond
  | lookup (l : MachineLookup.Label)
  deriving DecidableEq, Fintype

def instruction (source : K) (tape : Fin 5 → K) (coefficient offset : Nat)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .seed => MachineUnaryAffineAt.seed (tape 1) offset (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source (tape 4) (tape 1)
      coefficient (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt (tape 4) source id false
      (labels .restore) (some (labels .copyFirst))
  | .copyFirst => Reduction.MachineTransfer.loopAt (tape 0) (tape 4) id false
      (labels .copyFirst) (some (labels .copySecond))
  | .copySecond => MachineCopy.forkLoop (tape 4) (tape 0) (tape 2) false
      (labels .copySecond) (some (labels (.lookup .guard)))
  | .lookup l => MachineSubroutine.statement (fun q => labels (.lookup q)) exit
      (MachineLookup.program (tape 1) (tape 2) (tape 3) l)

def steps (values : List Nat) (a coefficient offset : Nat) : Nat :=
  (2 * (a + 1) + 1) +
    (2 * ((encodeWords values).length + 1) +
      MachineLookupSpec.steps values (coefficient * a + offset) + 1)

def finalTapes (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat) : K → List Bool :=
  MachinePreservingLookup.finalTapes tape base values index value
    (base (tape 1)) (base (tape 2)) (base (tape 3))

theorem initialTapes_eq_update (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (i : Nat) :
    MachinePreservingLookup.initialTapes tape base i
      (base (tape 1)) (base (tape 2)) (base (tape 3)) =
      Function.update base (tape 1) (encodeWord i ++ base (tape 1)) := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b := fun h => hne (distinct h)
  funext k
  by_cases h₁ : k = tape 1
  · subst k
    simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes,
      hd 1 2 (by decide), hd 1 3 (by decide)]
  · by_cases h₂ : k = tape 2
    · subst k
      simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, h₁,
        hd 2 3 (by decide)]
    · by_cases h₃ : k = tape 3
      · subst k
        simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, h₁]
      · simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, h₁, h₂, h₃]

theorem affineLookupTrace (source : K) (tape : Fin 5 → K)
    (distinct : Function.Injective tape) (outside : ∀ i, source ≠ tape i)
    (coefficient offset : Nat) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction source tape coefficient offset labels exit l)
    (base : K → List Bool) (values : List Nat)
    (tableWord : base (tape 0) = encodeWords values) (scratchEmpty : base (tape 4) = [])
    (a : Nat) (suffix : List Bool) (sourceWord : base source = encodeWord a ++ suffix)
    (value : Nat) (selected : values[coefficient * a + offset]? = some value)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps values a coefficient offset]
      (some ⟨some (labels .seed), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), finalTapes tape base values (coefficient * a + offset) value⟩ := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have haffine := MachineUnaryAffineAt.seededAffineTrace source (tape 4) (tape 1)
    (outside 4) (outside 1) (hd 4 1 (by decide)) coefficient offset
    (labels .seed) (labels .scan) (labels .restore) (some (labels .copyFirst))
    program (atLabels .seed) (atLabels .scan) (atLabels .restore)
    base a suffix sourceWord scratchEmpty ambient register
  have hlookup := MachinePreservingLookup.preservingLookupTrace tape distinct
    (labels .copyFirst) (labels .copySecond) (fun q => labels (.lookup q)) exit
    program (atLabels .copyFirst) (atLabels .copySecond) (fun q => atLabels (.lookup q))
    base values tableWord scratchEmpty (coefficient * a + offset) value selected
    (base (tape 1)) (base (tape 2)) (base (tape 3)) ambient none
  rw [initialTapes_eq_update tape distinct] at hlookup
  rw [steps, Nat.add_comm, Function.iterate_add_apply, haffine]
  exact hlookup

theorem steps_le (values : List Nat) (a coefficient offset value : Nat)
    (selected : values[coefficient * a + offset]? = some value) :
    steps values a coefficient offset ≤ 2 * a + 5 * (encodeWords values).length + 6 := by
  have h := MachinePreservingLookup.preservingLookup_steps_le values
    (coefficient * a + offset) value selected
  unfold steps
  omega

theorem steps_le_table (values : List Nat) (a coefficient offset value : Nat)
    (selected : values[coefficient * a + offset]? = some value)
    (ha : a ≤ (encodeWords values).length) :
    steps values a coefficient offset ≤ 7 * (encodeWords values).length + 6 := by
  have h := steps_le values a coefficient offset value selected
  omega

theorem finalTapes_other (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat) (k : K)
    (h₁ : k ≠ tape 1) (h₂ : k ≠ tape 2) (h₃ : k ≠ tape 3) :
    finalTapes tape base values index value k = base k :=
  MachineLookup.tapes_other _ _ _ _ h₁ h₂ h₃ _ _ _ _

theorem finalTapes_output (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat) :
    finalTapes tape base values index value (tape 3) = encodeWord value ++ base (tape 3) :=
  MachineLookup.tapes_destination _ _ _ _ _ _ _

def machine (coefficient offset : Nat) : FinTM2 where
  K := Fin 6
  k₀ := 0
  k₁ := 4
  Γ _ := Bool
  Λ := Label
  main := .seed
  σ := Unit × Option Bool
  initialState := ((),none)
  m := instruction 0 Fin.succ coefficient offset id none

end DFVSGames.Foundations.Complexity.MachineAffineLookup


namespace DFVSGames.Explicit.MachineProductGather

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

abbrev Tape (width : Nat) := Fin 4 ⊕ (Fin width ⊕ Fin width)

def shift (width : Nat) : Tape width → Tape (width + 1) :=
  Sum.map id (Sum.map Fin.succ Fin.succ)

theorem shift_injective (width : Nat) : Function.Injective (shift width) := by
  intro a b h
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;> simp_all [shift]

def lookupRole (width : Nat) : Fin 5 → Tape (width + 1)
  | 0 => .inl 0
  | 1 => .inl 1
  | 2 => .inl 2
  | 3 => .inr (.inr 0)
  | 4 => .inl 3

theorem lookupRole_injective (width : Nat) : Function.Injective (lookupRole width) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [lookupRole]

def Label : Nat → Type
  | 0 => Unit
  | width + 1 => MachineAffineLookup.Label ⊕ Label width

instance labelFintype (width : Nat) : Fintype (Label width) := by
  induction width with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ width ih =>
    letI := ih
    exact inferInstanceAs (Fintype (MachineAffineLookup.Label ⊕ Label width))

instance labelDecidableEq (width : Nat) : DecidableEq (Label width) := by
  induction width with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ width ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (MachineAffineLookup.Label ⊕ Label width))

def entry : (width : Nat) → Label width
  | 0 => ()
  | _ + 1 => .inl .seed

def instruction : (width : Nat) → (Tape width → K) → Nat → (Fin width → Nat) →
    (Label width → Λ) → Option Λ → Label width →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | 0, placement, _, _, _, exit, _ =>
    .load (fun state => (state.1, none))
      (DFVSGames.Reduction.MachineTransfer.exitAt (placement (.inl 0)) exit)
  | width + 1, placement, coefficient, offsets, labels, exit, label =>
    match label with
    | .inl inner => MachineAffineLookup.instruction (placement (.inr (.inl 0)))
        (placement ∘ lookupRole width) coefficient (offsets 0)
        (fun l => labels (.inl l)) (some (labels (.inr (entry width)))) inner
    | .inr inner => instruction width (placement ∘ shift width) coefficient
        (fun i => offsets i.succ) (fun l => labels (.inr l)) exit inner

def steps (values : List Nat) (coefficient : Nat) :
    (width : Nat) → (Fin width → Nat) → (Fin width → Nat) → Nat
  | 0, _, _ => 1
  | width + 1, indices, offsets =>
    MachineAffineLookup.steps values (indices 0) coefficient (offsets 0) +
      steps values coefficient width (fun i => indices i.succ) (fun i => offsets i.succ)

def finalTapes (values : List Nat) (coefficient : Nat) :
    (width : Nat) → (Tape width → K) → (Fin width → Nat) →
      (Fin width → Nat) → (Fin width → Nat) → (K → List Bool) → K → List Bool
  | 0, _, _, _, _, base => base
  | width + 1, placement, indices, offsets, fields, base =>
    finalTapes values coefficient width (placement ∘ shift width)
      (fun i => indices i.succ) (fun i => offsets i.succ) (fun i => fields i.succ)
      (MachineAffineLookup.finalTapes (placement ∘ lookupRole width) base values
        (coefficient * indices 0 + offsets 0) (fields 0))

theorem finalTapes_other (values : List Nat) (coefficient width : Nat)
    (placement : Tape width → K) (indices offsets fields : Fin width → Nat)
    (base : K → List Bool) (k : K)
    (query : k ≠ placement (.inl 1)) (scan : k ≠ placement (.inl 2))
    (outputs : ∀ i, k ≠ placement (.inr (.inr i))) :
    finalTapes values coefficient width placement indices offsets fields base k = base k := by
  induction width generalizing base with
  | zero => rfl
  | succ width ih =>
    rw [finalTapes]
    rw [ih (placement ∘ shift width) (fun i => indices i.succ)
      (fun i => offsets i.succ) (fun i => fields i.succ) _ query scan
      (fun i => outputs i.succ)]
    exact MachineAffineLookup.finalTapes_other _ _ _ _ _ k query scan (outputs 0)

theorem gatherTrace (values : List Nat) (coefficient width : Nat)
    (placement : Tape width → K) (distinct : Function.Injective placement)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (labels : Label width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction width placement coefficient offsets labels exit l)
    (base : K → List Bool) (suffixes : Fin width → List Bool)
    (tableWord : base (placement (.inl 0)) = encodeWords values)
    (scratchEmpty : base (placement (.inl 3)) = [])
    (sourceWords : ∀ i, base (placement (.inr (.inl i))) = encodeWord (indices i) ++ suffixes i)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps values coefficient width indices offsets]
      (some ⟨some (labels (entry width)), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        finalTapes values coefficient width placement indices offsets fields base⟩ := by
  induction width generalizing base register with
  | zero =>
    change some (TM2.stepAux (program (labels (entry 0))) _ _) = _
    rw [atLabels]
    cases exit <;> simp [instruction, TM2.stepAux, finalTapes,
      DFVSGames.Reduction.MachineTransfer.exitAt]
  | succ width ih =>
    have hd (a b : Tape (width + 1)) (hne : a ≠ b) : placement a ≠ placement b :=
      fun h => hne (distinct h)
    have outside : ∀ i : Fin 5,
        placement (.inr (.inl 0)) ≠ (placement ∘ lookupRole width) i := by
      intro i
      apply hd
      fin_cases i <;> simp [lookupRole]
    have first := MachineAffineLookup.affineLookupTrace (placement (.inr (.inl 0)))
      (placement ∘ lookupRole width) (distinct.comp (lookupRole_injective width)) outside
      coefficient (offsets 0) (fun l => labels (.inl l))
      (some (labels (.inr (entry width)))) program (fun l => atLabels (.inl l))
      base values tableWord scratchEmpty (indices 0) (suffixes 0) (sourceWords 0)
      (fields 0) (selected 0) ambient register
    let mid := MachineAffineLookup.finalTapes (placement ∘ lookupRole width) base values
      (coefficient * indices 0 + offsets 0) (fields 0)
    have frame (k : Tape (width + 1)) (h1 : k ≠ .inl 1) (h2 : k ≠ .inl 2)
        (h3 : k ≠ .inr (.inr 0)) : mid (placement k) = base (placement k) :=
      MachineAffineLookup.finalTapes_other _ _ _ _ _ _ (hd _ _ h1) (hd _ _ h2) (hd _ _ h3)
    have middleTable : mid (placement (.inl 0)) = encodeWords values := by
      rw [frame (.inl 0) (by simp) (by simp) (by simp)]
      exact tableWord
    have middleScratch : mid (placement (.inl 3)) = [] := by
      rw [frame (.inl 3) (by simp) (by simp) (by simp)]
      exact scratchEmpty
    have middleSources (i : Fin width) : mid (placement (.inr (.inl i.succ))) =
        encodeWord (indices i.succ) ++ suffixes i.succ := by
      rw [frame (.inr (.inl i.succ)) (by simp) (by simp) (by simp)]
      exact sourceWords i.succ
    have rest := ih (placement ∘ shift width) (distinct.comp (shift_injective width))
      (fun i => indices i.succ) (fun i => offsets i.succ) (fun i => fields i.succ)
      (fun i => selected i.succ) (fun l => labels (.inr l))
      (fun l => atLabels (.inr l)) mid (fun i => suffixes i.succ)
      middleTable middleScratch middleSources none
    simp only [entry]
    rw [steps, Nat.add_comm, Function.iterate_add_apply, first]
    exact rest

theorem finalTapes_field (values : List Nat) (coefficient width : Nat)
    (placement : Tape width → K) (distinct : Function.Injective placement)
    (indices offsets fields : Fin width → Nat) (base : K → List Bool) (i : Fin width) :
    finalTapes values coefficient width placement indices offsets fields base
      (placement (.inr (.inr i))) =
      encodeWord (fields i) ++ base (placement (.inr (.inr i))) := by
  induction width generalizing base with
  | zero => exact Fin.elim0 i
  | succ width ih =>
    have hd (a b : Tape (width + 1)) (hne : a ≠ b) : placement a ≠ placement b :=
      fun h => hne (distinct h)
    let mid := MachineAffineLookup.finalTapes (placement ∘ lookupRole width) base values
      (coefficient * indices 0 + offsets 0) (fields 0)
    refine Fin.cases ?_ (fun j => ?_) i
    · change finalTapes values coefficient width (placement ∘ shift width)
        (fun j => indices j.succ) (fun j => offsets j.succ) (fun j => fields j.succ)
        mid (placement (.inr (.inr 0))) = _
      rw [finalTapes_other values coefficient width _ _ _ _ mid _
        (hd _ _ (by simp [shift])) (hd _ _ (by simp [shift]))
        (fun j => hd _ _ (by simp [shift, Fin.ext_iff]))]
      exact MachineAffineLookup.finalTapes_output _ _ _ _ _
    · change finalTapes values coefficient width (placement ∘ shift width)
        (fun j => indices j.succ) (fun j => offsets j.succ) (fun j => fields j.succ)
        mid ((placement ∘ shift width) (.inr (.inr j))) = _
      rw [ih (placement ∘ shift width) (distinct.comp (shift_injective width))
        (fun j => indices j.succ) (fun j => offsets j.succ) (fun j => fields j.succ) mid j]
      congr 1
      exact MachineAffineLookup.finalTapes_other (placement ∘ lookupRole width) base values
        (coefficient * indices 0 + offsets 0) (fields 0)
        (placement (.inr (.inr j.succ)))
        (hd _ _ (by simp [lookupRole])) (hd _ _ (by simp [lookupRole]))
        (hd _ _ (by simp [lookupRole, Fin.ext_iff]))

theorem steps_le (values : List Nat) (coefficient width magnitude : Nat)
    (indices offsets fields : Fin width → Nat)
    (selected : ∀ i, values[coefficient * indices i + offsets i]? = some (fields i))
    (bounded : ∀ i, indices i ≤ magnitude) :
    steps values coefficient width indices offsets ≤
      width * (2 * magnitude + 5 * (encodeWords values).length + 6) + 1 := by
  induction width with
  | zero => simp [steps]
  | succ width ih =>
    have first := MachineAffineLookup.steps_le values (indices 0) coefficient (offsets 0)
      (fields 0) (selected 0)
    have rest := ih (fun i => indices i.succ) (fun i => offsets i.succ)
      (fun i => fields i.succ) (fun i => selected i.succ) (fun i => bounded i.succ)
    have hb := bounded 0
    rw [steps, Nat.add_mul, Nat.one_mul]
    omega

end DFVSGames.Explicit.MachineProductGather


namespace DFVSGames.Foundations.Complexity.MachineCountedLoop

open Turing
open scoped BigOperators
open MachineUnaryCounter

variable {K Λ σ : Type} [DecidableEq K]

def guardConfiguration (counter : K) (guardLabel : Λ) (suffix : List Bool)
    (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (n : Nat) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some guardLabel, (ambient n, register n), counterTapes counter (base n) n suffix⟩

def bodyConfiguration (counter : K) (bodyLabel : Λ) (suffix : List Bool)
    (ambient : Nat → σ) (base : Nat → K → List Bool) (n : Nat) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some bodyLabel, (ambient (n + 1), none), counterTapes counter (base (n + 1)) n suffix⟩

def exitConfiguration (counter : K) (exitLabel : Λ) (suffix : List Bool)
    (ambient : Nat → σ) (base : Nat → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool) :=
  ⟨some exitLabel, (ambient 0, none), counterTapes counter (base 0) 0 suffix⟩

def BodyTraces (counter : K) (guardLabel bodyLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (suffix : List Bool) (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (cost : Nat → Nat) (n : Nat) : Prop :=
  ∀ r, r < n →
    (MachineComposition.advance (TM2.step program))^[cost r]
      (some (bodyConfiguration counter bodyLabel suffix ambient base r)) =
      some (guardConfiguration counter guardLabel suffix ambient register base r)

def totalSteps (cost : Nat → Nat) (n : Nat) : Nat :=
  (∑ r ∈ Finset.range n, cost r) + n + 1

@[simp] theorem totalSteps_zero (cost : Nat → Nat) : totalSteps cost 0 = 1 := by
  simp [totalSteps]

theorem totalSteps_succ (cost : Nat → Nat) (n : Nat) :
    totalSteps cost (n + 1) = (totalSteps cost n + cost n) + 1 := by
  simp only [totalSteps, Finset.sum_range_succ]
  omega

theorem loopTrace (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (suffix : List Bool) (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (cost : Nat → Nat) (n : Nat)
    (bodyTraces : BodyTraces counter guardLabel bodyLabel program suffix
      ambient register base cost n) :
    (MachineComposition.advance (TM2.step program))^[totalSteps cost n]
      (some (guardConfiguration counter guardLabel suffix ambient register base n)) =
      some (exitConfiguration counter exitLabel suffix ambient base) := by
  revert bodyTraces
  induction n with
  | zero =>
      intro _
      simpa only [totalSteps_zero, guardConfiguration, exitConfiguration] using
        guardTrace_zero counter guardLabel bodyLabel exitLabel program atGuard
          (base 0) suffix (ambient 0) (register 0)
  | succ n ih =>
      intro bodyTraces
      rw [totalSteps_succ, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[totalSteps cost n + cost n]
        (TM2.step program
          ⟨some guardLabel, (ambient (n + 1), register (n + 1)),
            counterTapes counter (base (n + 1)) (n + 1) suffix⟩) = _
      rw [guardStep_succ counter guardLabel bodyLabel exitLabel program atGuard
        (base (n + 1)) n suffix (ambient (n + 1)) (register (n + 1)),
        Function.iterate_add_apply]
      change (MachineComposition.advance (TM2.step program))^[totalSteps cost n]
        ((MachineComposition.advance (TM2.step program))^[cost n]
          (some (bodyConfiguration counter bodyLabel suffix ambient base n))) = _
      rw [bodyTraces n (Nat.lt_succ_self n)]
      exact ih (fun r hr => bodyTraces r (Nat.lt_trans hr (Nat.lt_succ_self n)))

theorem totalSteps_le (cost : Nat → Nat) (n B : Nat)
    (bodyBound : ∀ r, r < n → cost r ≤ B) :
    totalSteps cost n ≤ n * (B + 1) + 1 := by
  have hsum : (∑ r ∈ Finset.range n, cost r) ≤ n * B := by
    calc
      (∑ r ∈ Finset.range n, cost r) ≤ ∑ _r ∈ Finset.range n, B :=
        Finset.sum_le_sum (fun r hr => bodyBound r (Finset.mem_range.mp hr))
      _ = n * B := by simp
  simpa only [totalSteps, Nat.mul_add, Nat.mul_one] using
    Nat.add_le_add_right (Nat.add_le_add_right hsum n) 1

def loopInTime (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (suffix : List Bool) (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (cost : Nat → Nat) (n B : Nat)
    (bodyTraces : BodyTraces counter guardLabel bodyLabel program suffix
      ambient register base cost n)
    (bodyBound : ∀ r, r < n → cost r ≤ B) :
    StateTransition.EvalsToInTime (TM2.step program)
      (guardConfiguration counter guardLabel suffix ambient register base n)
      (some (exitConfiguration counter exitLabel suffix ambient base))
      (n * (B + 1) + 1) where
  steps := totalSteps cost n
  evals_in_steps := by
    change (MachineComposition.advance (TM2.step program))^[totalSteps cost n] _ = _
    exact loopTrace counter guardLabel bodyLabel exitLabel program atGuard suffix
      ambient register base cost n bodyTraces
  steps_le_m := totalSteps_le cost n B bodyBound

omit [DecidableEq K] in

theorem baseFrame (base : Nat → K → List Bool) (frame : K → Prop) (n : Nat)
    (bodyFrame : ∀ r, r < n → ∀ k, frame k → base (r + 1) k = base r k) :
    ∀ k, frame k → base n k = base 0 k := by
  revert bodyFrame
  induction n with
  | zero => intro _ k _; rfl
  | succ n ih =>
      intro bodyFrame k hk
      exact (bodyFrame n (Nat.lt_succ_self n) k hk).trans
        (ih (fun r hr => bodyFrame r (Nat.lt_trans hr (Nat.lt_succ_self n))) k hk)

theorem counterFrame (counter : K) (suffix : List Bool)
    (base : Nat → K → List Bool) (frame : K → Prop) (n : Nat)
    (counterOutside : ∀ k, frame k → k ≠ counter)
    (bodyFrame : ∀ r, r < n → ∀ k, frame k → base (r + 1) k = base r k) :
    ∀ k, frame k →
      counterTapes counter (base n) n suffix k = counterTapes counter (base 0) 0 suffix k := by
  intro k hk
  rw [counterTapes_other counter k (counterOutside k hk),
    counterTapes_other counter k (counterOutside k hk)]
  exact baseFrame base frame n bodyFrame k hk

theorem loopTrace_framed (counter : K) (guardLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atGuard : program guardLabel = guard counter bodyLabel exitLabel)
    (suffix : List Bool) (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (cost : Nat → Nat) (n : Nat)
    (bodyTraces : BodyTraces counter guardLabel bodyLabel program suffix
      ambient register base cost n)
    (frame : K → Prop) (counterOutside : ∀ k, frame k → k ≠ counter)
    (bodyFrame : ∀ r, r < n → ∀ k, frame k → base (r + 1) k = base r k) :
    ((MachineComposition.advance (TM2.step program))^[totalSteps cost n]
      (some (guardConfiguration counter guardLabel suffix ambient register base n)) =
      some (exitConfiguration counter exitLabel suffix ambient base)) ∧
    (∀ k, frame k →
      (guardConfiguration counter guardLabel suffix ambient register base n).stk k =
        (exitConfiguration counter exitLabel suffix ambient base).stk k) :=
  ⟨loopTrace counter guardLabel bodyLabel exitLabel program atGuard suffix
      ambient register base cost n bodyTraces,
    counterFrame counter suffix base frame n counterOutside bodyFrame⟩

end DFVSGames.Foundations.Complexity.MachineCountedLoop


namespace DFVSGames.Foundations.Complexity.MachineUnaryMultiply

open Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

inductive Label
  | copyDrain | copyFork | seed | guard | scan | emitFalse | emitTrue | restore | finish
  deriving DecidableEq

instance : Fintype Label :=
  Fintype.ofList [.copyDrain, .copyFork, .seed, .guard, .scan, .emitFalse, .emitTrue,
    .restore, .finish] (by intro label; cases label <;> simp)

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := (σ × Unit) × Option Bool

def transition (_ : Unit) (_ : Bool) : Unit := ()
def payload (_ : Unit) (bit : Bool) : List Bool := if bit then [true] else []

def emitterLabel (labels : Label → Λ) (_ : Unit) (bit : Bool) : Λ :=
  if bit then labels .emitTrue else labels .emitFalse

def statement (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .copyDrain => Reduction.MachineTransfer.loopAt (slots 1) (slots 4) id false
      (labels .copyDrain) (some (labels .copyFork))
  | .copyFork => MachineCopy.forkLoop (slots 4) (slots 1) (slots 3) false
      (labels .copyFork) (some (labels .seed))
  | .seed => .push (slots 2) (fun _ => false) (.goto fun _ => labels .guard)
  | .guard => MachineUnaryCounter.guard (slots 3) (labels .scan) (labels .finish)
  | .scan => MachineTransducerCopy.scanLoop (slots 0) (slots 4) ()
      (emitterLabel labels) (labels .restore)
  | .emitFalse => MachineTransducerCopy.emitter (slots 2) transition payload (labels .scan) () false
  | .emitTrue => MachineTransducerCopy.emitter (slots 2) transition payload (labels .scan) () true
  | .restore => Reduction.MachineTransfer.loopAt (slots 4) (slots 0) id false
      (labels .restore) (some (labels .guard))
  | .finish => .pop (slots 3) (fun state _ => (state.1, none))
      (Reduction.MachineTransfer.exitAt (slots 2) exit)

def program (slots : Fin 5 ↪ K) : Label → TM2.Stmt (Alphabet (K := K)) Label (State σ) :=
  statement slots id none

def machine : FinTM2 where
  K := Fin 5
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Label
  main := .copyDrain
  σ := State Unit
  initialState := (((), ()), none)
  m := program (Function.Embedding.refl (Fin 5))

def resultTapes (slots : Fin 5 ↪ K) (base : K → List Bool) (product : ℕ) : K → List Bool :=
  Function.update base (slots 2) (encodeWord product ++ base (slots 2))

@[simp] theorem resultTapes_output (slots : Fin 5 ↪ K) (base : K → List Bool) (p : ℕ) :
    resultTapes slots base p (slots 2) = encodeWord p ++ base (slots 2) := by
  simp [resultTapes]

theorem resultTapes_other (slots : Fin 5 ↪ K) (base : K → List Bool) (p : ℕ)
    (k : K) (hk : k ≠ slots 2) : resultTapes slots base p k = base k := by
  simp [resultTapes, hk]

def bodySteps (a : ℕ) : ℕ := 3 * (a + 1) + 2
def steps (a b : ℕ) : ℕ := 3 * a * b + 8 * b + 7

private theorem output_encodeWord_inline_MachineUnaryMultiply (a : ℕ) :
    Reduction.MachineTransducer.output transition payload () (encodeWord a) =
      List.replicate a true := by
  induction a with
  | zero => simp [encodeWord, Reduction.MachineTransducer.output, payload]
  | succ a ih =>
    simpa only [encodeWord, List.replicate_succ, List.cons_append,
      Reduction.MachineTransducer.output, payload, Bool.cond_true, transition,
      ite_true, List.singleton_append, List.nil_append] using congrArg (List.cons true) ih

private theorem prepend_payload_inline_MachineUnaryMultiply (a p : ℕ) (suffix : List Bool) :
    List.replicate a true ++ (encodeWord p ++ suffix) = encodeWord (a + p) ++ suffix := by
  simp only [encodeWord, List.replicate_add, List.append_assoc]

def loopBase (slots : Fin 5 ↪ K) (base : K → List Bool) (a b r : ℕ) : K → List Bool :=
  resultTapes slots base (a * (b - r))

private theorem bodyTrace_inline_MachineUnaryMultiply (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (a b r : ℕ) (hr : r < b)
    (operand : base (slots 0) = encodeWord a) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) :
    (MachineComposition.advance (TM2.step p))^[bodySteps a]
      (some (MachineCountedLoop.bodyConfiguration (slots 3) (labels .scan) []
        (fun _ => (ambient, ())) (loopBase slots base a b) r)) =
      some (MachineCountedLoop.guardConfiguration (slots 3) (labels .guard) []
        (fun _ => (ambient, ())) (fun _ => none) (loopBase slots base a b) r) := by
  have h04 : slots 0 ≠ slots 4 := slots.injective.ne (by decide)
  have h02 : slots 0 ≠ slots 2 := slots.injective.ne (by decide)
  have h42 : slots 4 ≠ slots 2 := slots.injective.ne (by decide)
  have h03 : slots 0 ≠ slots 3 := slots.injective.ne (by decide)
  have h43 : slots 4 ≠ slots 3 := slots.injective.ne (by decide)
  have h23 : slots 2 ≠ slots 3 := slots.injective.ne (by decide)
  let start := MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b (r + 1)) r []
  have hstartA : start (slots 0) = encodeWord a := by
    simp [start, MachineUnaryCounter.counterTapes, loopBase, resultTapes, h03, h02, operand]
  have hstartScratch : start (slots 4) = [] := by
    simp [start, MachineUnaryCounter.counterTapes, loopBase, resultTapes, h43, h42, scratchEmpty]
  have hscan : p (labels .scan) = MachineTransducerCopy.scanLoop (slots 0) (slots 4) ()
      (emitterLabel labels) (labels .restore) := atLabels .scan
  have hemit : ∀ control bit, p (emitterLabel labels control bit) =
      MachineTransducerCopy.emitter (slots 2) transition payload (labels .scan) control bit := by
    intro control bit
    cases control
    cases bit <;> exact atLabels _
  have hrestore : p (labels .restore) = Reduction.MachineTransfer.loopAt (slots 4) (slots 0)
      id false (labels .restore) (some (labels .guard)) := atLabels .restore
  have hcopy := MachineTransducerCopy.transduceCopyTrace (slots 0) (slots 4) (slots 2)
    h04 h02 h42 () transition payload (labels .scan) (labels .restore) (emitterLabel labels)
    (some (labels .guard)) p hscan hemit hrestore start hstartScratch ambient () none
  rw [hstartA, output_encodeWord_inline_MachineUnaryMultiply, List.reverse_replicate] at hcopy
  have hcount : a + a * (b - (r + 1)) = a * (b - r) := by
    have hr' : b - r = b - (r + 1) + 1 := by omega
    rw [hr']
    ring
  have hfinish : Function.update start (slots 2)
      (List.replicate a true ++ start (slots 2)) =
      MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b r) r [] := by
    funext k
    by_cases hk2 : k = slots 2
    · subst k
      simp only [Function.update_self]
      simp only [start, MachineUnaryCounter.counterTapes_other (slots 3) (slots 2) h23,
        loopBase, resultTapes_output]
      rw [prepend_payload_inline_MachineUnaryMultiply, hcount]
    · by_cases hk3 : k = slots 3
      · subst k
        simp [start, MachineUnaryCounter.counterTapes, hk2]
      · simp [start, MachineUnaryCounter.counterTapes, loopBase, resultTapes, hk2, hk3]
  rw [hfinish] at hcopy
  simpa only [bodySteps, encodeWord, List.length_append, List.length_replicate,
    List.length_singleton, MachineCountedLoop.bodyConfiguration,
    MachineCountedLoop.guardConfiguration] using hcopy

private theorem totalSteps_eq_inline_MachineUnaryMultiply (a b : ℕ) :
    MachineCountedLoop.totalSteps (fun _ => bodySteps a) b = b * (bodySteps a + 1) + 1 := by
  simp [MachineCountedLoop.totalSteps, Nat.mul_add, Nat.add_assoc]

theorem multiplyTrace (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (a b : ℕ)
    (operandA : base (slots 0) = encodeWord a)
    (operandB : base (slots 1) = encodeWord b)
    (counterEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step p))^[steps a b]
      (some ⟨some (labels .copyDrain), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (a * b)⟩ := by
  have h13 : slots 1 ≠ slots 3 := slots.injective.ne (by decide)
  have h14 : slots 1 ≠ slots 4 := slots.injective.ne (by decide)
  have h34 : slots 3 ≠ slots 4 := slots.injective.ne (by decide)
  have h23 : slots 2 ≠ slots 3 := slots.injective.ne (by decide)
  let copied := Function.update base (slots 3) (encodeWord b)
  have hcopy : (MachineComposition.advance (TM2.step p))^[2 * (b + 2)]
      (some ⟨some (labels .copyDrain), ((ambient, ()), register), base⟩) =
      some ⟨some (labels .seed), ((ambient, ()), none), copied⟩ := by
    have h := MachineCopy.copyTrace (slots 1) (slots 3) (slots 4) h13 h14 h34 false
      (labels .copyDrain) (labels .copyFork) (some (labels .seed)) p
      (atLabels .copyDrain) (atLabels .copyFork) base scratchEmpty (ambient, ()) register
    simpa only [copied, operandB, counterEmpty, List.append_nil, encodeWord, List.length_append,
      List.length_replicate, List.length_singleton, Nat.add_assoc, Nat.reduceAdd] using h
  have hseedTapes : Function.update copied (slots 2) (false :: copied (slots 2)) =
      MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b b) b [] := by
    funext k
    by_cases hk2 : k = slots 2
    · subst k
      simp [copied, MachineUnaryCounter.counterTapes, loopBase, resultTapes, h23, encodeWord]
    · by_cases hk3 : k = slots 3
      · subst k
        simp [copied, MachineUnaryCounter.counterTapes, hk2]
      · simp [copied, MachineUnaryCounter.counterTapes, loopBase, resultTapes, hk2, hk3]
  have hseed : (MachineComposition.advance (TM2.step p))^[1]
      (some ⟨some (labels .seed), ((ambient, ()), none), copied⟩) =
      some (MachineCountedLoop.guardConfiguration (slots 3) (labels .guard) []
        (fun _ => (ambient, ())) (fun _ => none) (loopBase slots base a b) b) := by
    change some (TM2.stepAux (p (labels .seed)) ((ambient, ()), none) copied) = _
    rw [atLabels .seed]
    change some (⟨some (labels .guard), ((ambient, ()), none),
      Function.update copied (slots 2) (false :: copied (slots 2))⟩ :
        TM2.Cfg (Alphabet (K := K)) Λ (State σ)) = _
    rw [hseedTapes]
    rfl
  have hloop := MachineCountedLoop.loopTrace (slots 3) (labels .guard) (labels .scan)
    (labels .finish) p (atLabels .guard) [] (fun _ => (ambient, ())) (fun _ => none)
    (loopBase slots base a b) (fun _ => bodySteps a) b
    (fun r hr => bodyTrace_inline_MachineUnaryMultiply slots labels exit p atLabels base a b r hr operandA scratchEmpty ambient)
  let finalCounter := MachineUnaryCounter.counterTapes (slots 3) (loopBase slots base a b 0) 0 []
  have hfinishTapes : Function.update finalCounter (slots 3) ((finalCounter (slots 3)).tail) =
      resultTapes slots base (a * b) := by
    funext k
    by_cases hk3 : k = slots 3
    · subst k
      simp [finalCounter, MachineUnaryCounter.counterTapes, encodeWord, resultTapes,
        Ne.symm h23, counterEmpty]
    · simp [finalCounter, MachineUnaryCounter.counterTapes, loopBase, hk3]
  have hfinish : (MachineComposition.advance (TM2.step p))^[1]
      (some (MachineCountedLoop.exitConfiguration (slots 3) (labels .finish) []
        (fun _ => (ambient, ())) (loopBase slots base a b))) =
      some ⟨exit, ((ambient, ()), none), resultTapes slots base (a * b)⟩ := by
    change some (TM2.stepAux (p (labels .finish)) ((ambient, ()), none) finalCounter) = _
    rw [atLabels .finish]
    cases exit <;>
      simpa only [statement, TM2.stepAux, Reduction.MachineTransfer.exitAt] using
        congrArg (fun tapes => some (⟨_, ((ambient, ()), none), tapes⟩ :
          TM2.Cfg (Alphabet (K := K)) Λ (State σ))) hfinishTapes
  rw [show steps a b = 1 + (MachineCountedLoop.totalSteps (fun _ => bodySteps a) b +
      (1 + 2 * (b + 2))) by rw [totalSteps_eq_inline_MachineUnaryMultiply]; unfold steps bodySteps; ring]
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    hcopy, hseed, hloop]
  exact hfinish

def multiplyInTime (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (a b : ℕ)
    (operandA : base (slots 0) = encodeWord a)
    (operandB : base (slots 1) = encodeWord b)
    (counterEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .copyDrain), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base (a * b)⟩) (steps a b) where
  steps := steps a b
  evals_in_steps := multiplyTrace slots labels exit p atLabels base a b operandA operandB
    counterEmpty scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

noncomputable def timePolynomial : Polynomial ℕ :=
  Polynomial.C 3 * Polynomial.X ^ 2 + Polynomial.C 8 * Polynomial.X + Polynomial.C 7

theorem steps_le_timePolynomial (a b : ℕ) :
    steps a b ≤ timePolynomial.eval (a + b + 2) := by
  have ha : a ≤ a + b + 2 := by omega
  have hb : b ≤ a + b + 2 := by omega
  have hab := Nat.mul_le_mul ha hb
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  unfold steps
  nlinarith

theorem multiplyFrame (slots : Fin 5 ↪ K) (base : K → List Bool) (a b : ℕ)
    (k : K) (hk : k ≠ slots 2) :
    resultTapes slots base (a * b) k = base k := resultTapes_other slots base _ k hk

theorem programTrace (slots : Fin 5 ↪ K) (base : K → List Bool) (a b : ℕ)
    (operandA : base (slots 0) = encodeWord a)
    (operandB : base (slots 1) = encodeWord b)
    (counterEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program (σ := σ) slots)))^[steps a b]
      (some ⟨some .copyDrain, ((ambient, ()), register), base⟩) =
      some ⟨none, ((ambient, ()), none), resultTapes slots base (a * b)⟩ :=
  multiplyTrace slots id none (program slots) (fun _ => rfl) base a b
    operandA operandB counterEmpty scratchEmpty ambient register

def programInPolynomialTime (slots : Fin 5 ↪ K) (base : K → List Bool) (a b : ℕ)
    (operandA : base (slots 0) = encodeWord a)
    (operandB : base (slots 1) = encodeWord b)
    (counterEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program (σ := σ) slots))
      ⟨some .copyDrain, ((ambient, ()), register), base⟩
      (some ⟨none, ((ambient, ()), none), resultTapes slots base (a * b)⟩)
      (timePolynomial.eval ((encodeWord a).length + (encodeWord b).length)) where
  steps := steps a b
  evals_in_steps := programTrace slots base a b operandA operandB counterEmpty scratchEmpty ambient register
  steps_le_m := by
    have hlength : (encodeWord a).length + (encodeWord b).length = a + b + 2 := by
      simp only [encodeWord, List.length_append, List.length_replicate, List.length_singleton]
      omega
    rw [hlength]
    exact steps_le_timePolynomial a b

end DFVSGames.Foundations.Complexity.MachineUnaryMultiply

end OAI
