import Mathlib
import OAI.Computability.DirectedFeedback.Games.AddressTupleLoaded

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

namespace DFVSGames.Reduction.MachineOutcomeRows

open Turing
open DFVSGames.Foundations.Complexity

structure Spec (q width : Nat) where
  left : List (MachineFieldTemplate.Token q)
  right : List (MachineFieldTemplate.Token q)
  permutation : List Bool

structure Values (width : Nat) where
  left : List Nat
  right : List Nat
  left_length : left.length = width
  right_length : right.length = width

abbrev Rhs (k : Nat) := Fin k → Bool
abbrev Row (k q width : Nat) := Rhs k → Spec q width
abbrev State (k : Nat) (σ : Type) := MachineRhsLoad.State k σ
abbrev Alphabet {K : Type} (_ : K) := Bool

variable {k q width : Nat} {K Λ σ : Type} [DecidableEq K]

abbrev LocalLabel (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :=
  MachineAddressEdge.Label row.left.length row.right.length width
    (MachineTemplateAddress.chosen (MachineAddressEdge.addressSlots slots))

def localMain (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :
    LocalLabel slots row :=
  MachineAddressEdge.leftLabel (MachineTemplateAddress.emitLabel
    (MachineFieldTemplate.startAt row.left.length 0))

def localInstruction (slots : MachineAddressEdge.Tape q width ↪ K)
    (row : Spec q width) (place : LocalLabel slots row → Λ) (exit : Option Λ) :
    LocalLabel slots row → TM2.Stmt (Alphabet (K := K)) Λ (MachineAddressEdge.State σ) :=
  MachineAddressEdge.instruction row.left row.right row.permutation slots place exit

def payload (B C : Nat) (values : Spec q width → Values width) (row : Spec q width) :
    List Bool :=
  MachineAddressEdge.edgeBits B C (values row).left (values row).right row.permutation

def rowResult (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (row : Spec q width)
    (base : K → List Bool) : K → List Bool :=
  MachineAddressEdge.appended slots base (payload B C values row)

def rowCost (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (row : Spec q width)
    (base : K → List Bool) : Nat :=
  MachineAddressEdge.phaseSteps row.left row.right slots base B C
    (values row).left (values row).right

def rowCosts (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) :
    List (Spec q width) → (K → List Bool) → List Nat
  | [], _ => []
  | row :: rows, base => rowCost slots B C values row base ::
      rowCosts slots B C values rows (rowResult slots B C values row base)

theorem rowCosts_length (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width)
    (rows : List (Spec q width)) (base : K → List Bool) :
    (rowCosts slots B C values rows base).length = rows.length := by
  induction rows generalizing base with
  | nil => rfl
  | cons row rows ih => simp only [rowCosts, List.length_cons, ih]

structure Invariant (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) : Prop where
  clean : MachineAddressEdge.Clean slots base
  radix : base (MachineAddressEdge.addressSlots slots .radix) = encodeWord B
  capacity : base (MachineAddressEdge.capacityTape slots) = encodeWord C
  correct : ∀ row ∈ rows,
    MachineFieldTemplate.templateOutput row.left
      (fun j => base (MachineAddressEdge.addressSlots slots (.field j))) =
        encodeWords (values row).left ∧
    MachineFieldTemplate.templateOutput row.right
      (fun j => base (MachineAddressEdge.addressSlots slots (.field j))) =
        encodeWords (values row).right

theorem Invariant.appended (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) (valid : Invariant slots B C values rows base) (bits : List Bool) :
    Invariant slots B C values rows (MachineAddressEdge.appended slots base bits) := by
  constructor
  · exact MachineAddressEdge.Clean.appended slots base valid.clean bits
  · simpa only [MachineAddressEdge.appended_address] using valid.radix
  · simpa only [MachineAddressEdge.appended_capacity] using valid.capacity
  · intro row hrow
    simpa only [MachineAddressEdge.appended_address] using valid.correct row hrow

theorem appended_nil (slots : MachineAddressEdge.Tape q width ↪ K) (base : K → List Bool) :
    MachineAddressEdge.appended slots base [] = base := by
  simp [MachineAddressEdge.appended, MachineFieldTemplate.outputTapes]

theorem sequence_result (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) :
    MachineFiniteSequence.resultOf (rowResult slots B C values) rows base =
      MachineAddressEdge.appended slots base (rows.flatMap (payload B C values)) := by
  induction rows generalizing base with
  | nil => simpa only [MachineFiniteSequence.resultOf, List.flatMap_nil] using
      (appended_nil slots base).symm
  | cons row rows ih =>
    rw [MachineFiniteSequence.resultOf, ih]
    exact MachineAddressEdge.appended_append slots base _ _

theorem sequence_steps (slots : MachineAddressEdge.Tape q width ↪ K)
    (B C : Nat) (values : Spec q width → Values width) (rows : List (Spec q width))
    (base : K → List Bool) :
    MachineFiniteSequence.steps (rowResult slots B C values) (rowCost slots B C values)
      rows base = (rowCosts slots B C values rows base).sum := by
  induction rows generalizing base with
  | nil => rfl
  | cons row rows ih => simp only [MachineFiniteSequence.steps, rowCosts, List.sum_cons, ih]

def sequenceInstruction (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width))
    (place : MachineFiniteSequence.Label (LocalLabel slots) rows → Λ) (exit : Option Λ) :=
  MachineFiniteSequence.instruction (LocalLabel slots) (localMain slots)
    (localInstruction (σ := σ) slots) rows place exit

theorem sequenceTrace (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width))
    (place : MachineFiniteSequence.Label (LocalLabel slots) rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (MachineAddressEdge.State σ))
    (atInstruction : ∀ label, P (place label) = sequenceInstruction slots rows place exit label)
    (base : K → List Bool) (B C : Nat) (values : Spec q width → Values width)
    (valid : Invariant slots B C values rows base) (ambient : σ) :
    (MachineComposition.advance (TM2.step P))^[(rowCosts slots B C values rows base).sum]
      (some ⟨MachineFiniteSequence.entry (LocalLabel slots) (localMain slots) rows place exit,
        ((ambient, ()), none), base⟩) =
      some ⟨exit, ((ambient, ()), none),
        MachineAddressEdge.appended slots base (rows.flatMap (payload B C values))⟩ := by
  have h := MachineFiniteSequence.trace (LocalLabel slots) (localMain slots)
    (localInstruction (σ := σ) slots) (rowResult slots B C values) (rowCost slots B C values)
    P (Invariant slots B C values rows) (fun _ => ((ambient, ()), none)) id rows
    (by
      intro row _ frame hframe
      exact Invariant.appended slots B C values rows frame hframe (payload B C values row))
    (by
      intro row hrow labels next placement frame hframe
      exact MachineAddressEdge.phaseTrace row.left row.right row.permutation slots
        labels next P placement frame B C (values row).left (values row).right
        (values row).left_length (values row).right_length hframe.clean hframe.radix
        hframe.capacity (hframe.correct row hrow).1 (hframe.correct row hrow).2 ambient none)
    place exit atInstruction base valid
  simpa only [sequence_steps, sequence_result, id_eq] using h

def selected (rows : List (Row k q width)) (rhs : Rhs k) : List (Spec q width) :=
  rows.map (fun row => row rhs)

@[simp] theorem selected_length (rows : List (Row k q width)) (rhs : Rhs k) :
    (selected rows rhs).length = rows.length := by simp [selected]

abbrev Label (slots : MachineAddressEdge.Tape q width ↪ K) (rows : List (Row k q width)) :=
  Unit ⊕ (Σ rhs : Rhs k, MachineFiniteSequence.Label (LocalLabel slots) (selected rows rhs))

instance localLabelFintype (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :
    Fintype (LocalLabel slots row) := by unfold LocalLabel; infer_instance

instance localLabelDecidableEq (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :
    DecidableEq (LocalLabel slots row) := by
  letI : DecidableEq (MachineTemplateAddress.Label row.left.length width
      (MachineTemplateAddress.chosen (MachineAddressEdge.addressSlots slots))) := by
    infer_instance
  letI : DecidableEq (MachineTemplateAddress.Label row.right.length width
      (MachineTemplateAddress.chosen (MachineAddressEdge.addressSlots slots))) := by
    infer_instance
  dsimp only [LocalLabel, MachineAddressEdge.Label]
  infer_instance

instance labelFintype (slots : MachineAddressEdge.Tape q width ↪ K) (rows : List (Row k q width)) :
    Fintype (Label slots rows) := by unfold Label; infer_instance

instance labelDecidableEq (slots : MachineAddressEdge.Tape q width ↪ K) (rows : List (Row k q width)) :
    DecidableEq (Label slots rows) := by unfold Label; infer_instance

def sequenceEntry (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (rhs : Rhs k)
    (place : Label slots rows → Λ) (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry (LocalLabel slots) (localMain slots) (selected rows rhs)
    (fun label => place (.inr ⟨rhs, label⟩)) exit

def dispatcher (slots : MachineAddressEdge.Tape q width ↪ K) :
    (rows : List (Row k q width)) → (Label slots rows → Λ) → Option Λ →
      TM2.Stmt (Alphabet (K := K)) Λ (State k σ)
  | [], _, exit => .load MachineFieldTemplate.reset (MachineFieldTemplate.jump exit)
  | row :: _rows, place, _ => .load MachineFieldTemplate.reset
      (.goto fun state => place (.inr ⟨MachineRhsLoad.rhs state,
        .inl (localMain slots (row (MachineRhsLoad.rhs state)))⟩))

def instruction (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ) :
    Label slots rows → TM2.Stmt (Alphabet (K := K)) Λ (State k σ)
  | .inl _ => dispatcher slots rows place exit
  | .inr ⟨rhs, label⟩ => sequenceInstruction slots (selected rows rhs)
      (fun l => place (.inr ⟨rhs, l⟩)) exit label

def program (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (exit : Option (Label slots rows)) :=
  instruction (σ := σ) slots rows id exit

theorem dispatcherStep (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atDispatcher : P (place (.inl ())) = dispatcher slots rows place exit)
    (base : K → List Bool) (rhs : Rhs k) (ambient : σ) (register : Option Bool) :
    TM2.step P ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩ =
      some ⟨sequenceEntry slots rows rhs place exit, (((rhs, ambient), ()), none), base⟩ := by
  change some (TM2.stepAux (P (place (.inl ()))) (((rhs, ambient), ()), register) base) = _
  rw [atDispatcher]
  cases rows with
  | nil => cases exit <;> rfl
  | cons row rows => rfl

theorem phaseTrace (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atInstruction : ∀ label, P (place label) = instruction slots rows place exit label)
    (base : K → List Bool) (rhs : Rhs k) (ambient : σ) (register : Option Bool)
    (B C : Nat) (values : Spec q width → Values width)
    (valid : Invariant slots B C values (selected rows rhs) base) :
    (MachineComposition.advance (TM2.step P))^[
      (rowCosts slots B C values (selected rows rhs) base).sum + 1]
      (some ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩) =
      some ⟨exit, (((rhs, ambient), ()), none), MachineAddressEdge.appended slots base
        ((selected rows rhs).flatMap (payload B C values))⟩ := by
  have first := dispatcherStep slots rows place exit P (atInstruction (.inl ()))
    base rhs ambient register
  have rest := sequenceTrace slots (selected rows rhs) (fun l => place (.inr ⟨rhs, l⟩))
    exit P (fun l => atInstruction (.inr ⟨rhs, l⟩)) base B C values valid (rhs, ambient)
  rw [Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step P))^[_]
    (TM2.step P ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩) = _
  rw [first]
  exact rest

def phaseInTime (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (place : Label slots rows → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State k σ))
    (atInstruction : ∀ label, P (place label) = instruction slots rows place exit label)
    (base : K → List Bool) (rhs : Rhs k) (ambient : σ) (register : Option Bool)
    (B C : Nat) (values : Spec q width → Values width)
    (valid : Invariant slots B C values (selected rows rhs) base) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (place (.inl ())), (((rhs, ambient), ()), register), base⟩
      (some ⟨exit, (((rhs, ambient), ()), none), MachineAddressEdge.appended slots base
        ((selected rows rhs).flatMap (payload B C values))⟩)
      ((rowCosts slots B C values (selected rows rhs) base).sum + 1) where
  steps := (rowCosts slots B C values (selected rows rhs) base).sum + 1
  evals_in_steps := phaseTrace slots rows place exit P atInstruction base rhs ambient register
    B C values valid
  steps_le_m := Nat.le_refl _

theorem emitted_output (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (rhs : Rhs k) (base : K → List Bool)
    (B C : Nat) (values : Spec q width → Values width) :
    MachineAddressEdge.appended slots base ((selected rows rhs).flatMap (payload B C values))
        (MachineAddressEdge.outputTape slots) =
      ((selected rows rhs).flatMap (payload B C values)).reverse ++
        base (MachineAddressEdge.outputTape slots) :=
  MachineAddressEdge.appended_output slots base _

theorem exact_row_count (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Row k q width)) (rhs : Rhs k) (base : K → List Bool)
    (B C : Nat) (values : Spec q width → Values width) :
    (rowCosts slots B C values (selected rows rhs) base).length = rows.length := by
  rw [rowCosts_length, selected_length]

noncomputable def timePolynomial (rows : List (Spec q width)) : Polynomial Nat :=
  (rows.map (fun row => MachineAddressEdge.timePolynomial
    row.left.length row.right.length width)).sum + 1

theorem rowCosts_sum_le (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width)) (base : K → List Bool)
    (B C : Nat) (values : Spec q width → Values width) (M : Nat)
    (clean : MachineAddressEdge.Clean slots base)
    (fieldsBound : ∀ j, (base (MachineAddressEdge.addressSlots slots (.field j))).length ≤ M)
    (radixBound : B ≤ M) (capacityBound : C ≤ M)
    (valuesBound : ∀ row ∈ rows,
      (encodeWords (values row).left).length ≤ M ∧
      (encodeWords (values row).right).length ≤ M ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).left i ≤ M) ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).right i ≤ M)) :
    (rowCosts slots B C values rows base).sum ≤
      ((rows.map (fun row => MachineAddressEdge.timePolynomial
        row.left.length row.right.length width)).sum).eval M := by
  induction rows generalizing base with
  | nil => simp [rowCosts]
  | cons row rows ih =>
    have bounds := valuesBound row (by simp)
    have first := MachineAddressEdge.phaseSteps_le_timePolynomial row.left row.right
      slots base B C (values row).left (values row).right
      (values row).left_length (values row).right_length clean M fieldsBound
      bounds.1 bounds.2.1 radixBound capacityBound bounds.2.2.1 bounds.2.2.2
    have rest := ih (rowResult slots B C values row base)
      (MachineAddressEdge.Clean.appended slots base clean (payload B C values row))
      (by simpa only [rowResult, MachineAddressEdge.appended_address] using fieldsBound)
      (fun r hr => valuesBound r (List.mem_cons_of_mem row hr))
    simpa only [rowCosts, List.sum_cons, List.map_cons, Polynomial.eval_add, rowCost] using
      Nat.add_le_add first rest

theorem phaseCost_le_timePolynomial (slots : MachineAddressEdge.Tape q width ↪ K)
    (rows : List (Spec q width)) (base : K → List Bool)
    (B C : Nat) (values : Spec q width → Values width) (M : Nat)
    (clean : MachineAddressEdge.Clean slots base)
    (fieldsBound : ∀ j, (base (MachineAddressEdge.addressSlots slots (.field j))).length ≤ M)
    (radixBound : B ≤ M) (capacityBound : C ≤ M)
    (valuesBound : ∀ row ∈ rows,
      (encodeWords (values row).left).length ≤ M ∧
      (encodeWords (values row).right).length ≤ M ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).left i ≤ M) ∧
      (∀ i, i < width → MachineTemplateAddress.digits (values row).right i ≤ M)) :
    (rowCosts slots B C values rows base).sum + 1 ≤ (timePolynomial rows).eval M := by
  have h := rowCosts_sum_le slots rows base B C values M clean fieldsBound
    radixBound capacityBound valuesBound
  simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one] using
    Nat.add_le_add_right h 1

end DFVSGames.Reduction.MachineOutcomeRows
end

section

namespace DFVSGames.Reduction.WeightedSource

open scoped BigOperators
open WeightRounding

structure RationalSource (Eqn : Type) where
  occurrences : Nat
  positive : 0 < occurrences
  equation : Fin occurrences → Eqn
  weight : Fin occurrences → ℚ
  nonnegative : ∀ i, 0 ≤ weight i
  normalized : ∑ i, weight i = 1

namespace RationalSource

variable {Eqn : Type} (S : RationalSource Eqn)

def denominator : Nat := ∏ i, (S.weight i).den

theorem denominator_positive : 0 < S.denominator := by
  exact Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => (S.weight i).den_ne_zero)

theorem den_dvd_denominator (i : Fin S.occurrences) :
    (S.weight i).den ∣ S.denominator := by
  exact Finset.dvd_prod_of_mem (fun j => (S.weight j).den) (Finset.mem_univ i)

def numerator (i : Fin S.occurrences) : Nat :=
  (S.weight i).num.toNat * (S.denominator / (S.weight i).den)

theorem numerator_cast (i : Fin S.occurrences) :
    (S.numerator i : ℚ) = S.weight i * S.denominator := by
  have hn : (((S.weight i).num.toNat : Nat) : ℚ) = ((S.weight i).num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (S.nonnegative i))
  have hd : ((S.weight i).den : ℚ) ≠ 0 := by
    exact_mod_cast (S.weight i).den_ne_zero
  have hdiv : ((S.denominator / (S.weight i).den : Nat) : ℚ) * (S.weight i).den = S.denominator := by
    exact_mod_cast Nat.div_mul_cancel (S.den_dvd_denominator i)
  have hnum : ((S.weight i).num : ℚ) = S.weight i * (S.weight i).den :=
    (div_eq_iff hd).mp (S.weight i).num_div_den
  rw [numerator, Nat.cast_mul, hn, hnum]
  calc
    S.weight i * (S.weight i).den * ↑(S.denominator / (S.weight i).den) =
        S.weight i * (↑(S.denominator / (S.weight i).den) * (S.weight i).den) := by ring
    _ = _ := by rw [hdiv]

theorem weight_eq_ratio (i : Fin S.occurrences) :
    S.weight i = (S.numerator i : ℚ) / S.denominator := by
  have hq : (S.denominator : ℚ) ≠ 0 := by exact_mod_cast S.denominator_positive.ne'
  rw [S.numerator_cast]
  field_simp

def numerators : List Nat := List.ofFn S.numerator

theorem length_numerators : S.numerators.length = S.occurrences := by
  simp [numerators]

theorem sum_numerators : S.numerators.sum = S.denominator := by
  have h : (∑ i, (S.numerator i : ℚ)) = (S.denominator : ℚ) := by
    simp_rw [S.numerator_cast]
    rw [← Finset.sum_mul, S.normalized, one_mul]
  simpa only [numerators, List.sum_ofFn] using (show (∑ i, S.numerator i) = S.denominator by exact_mod_cast h)

def equationAt (i : Nat) : Eqn :=
  if h : i < S.occurrences then S.equation ⟨i, h⟩ else S.equation ⟨0, S.positive⟩

@[simp] theorem equationAt_fin (i : Fin S.occurrences) :
    S.equationAt i.val = S.equation i := by simp [equationAt, i.isLt]

def roundedEquations (D : Nat) : List Eqn :=
  (uniformSource D S.denominator S.numerators).map S.equationAt

theorem roundedEquations_length (D : Nat) : (S.roundedEquations D).length = D := by
  simp only [roundedEquations, List.length_map]
  exact length_uniformSource D S.denominator S.numerators S.denominator_positive S.sum_numerators

theorem roundedEquations_nonempty (D : Nat) (hD : 0 < D) : S.roundedEquations D ≠ [] := by
  intro h
  have hl := S.roundedEquations_length D
  rw [h] at hl
  simp at hl
  omega

theorem roundedEquations_origin (D : Nat) (e : Eqn) (he : e ∈ S.roundedEquations D) :
    ∃ i : Fin S.occurrences, e = S.equation i := by
  obtain ⟨j, _, hj⟩ := List.mem_map.mp he
  rw [← hj]
  unfold equationAt
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

def weightedValue (accept : Eqn → Bool) : ℚ :=
  ∑ i, if accept (S.equation i) then S.weight i else 0

def roundedValue (D : Nat) (accept : Eqn → Bool) : ℚ :=
  ((S.roundedEquations D).filter accept).length / (D : ℚ)

end RationalSource

theorem selectedSum_ofFn {n : Nat} (p : Fin n → Nat) (keep : Nat → Bool) :
    selectedSum (List.ofFn p) keep = ∑ i, if keep i.val then p i else 0 := by
  induction n generalizing keep with
  | zero => simp [selectedSum]
  | succ n ih =>
    rw [List.ofFn_succ, selectedSum, Fin.sum_univ_succ]
    rw [ih]
    rfl

namespace RationalSource

variable {Eqn : Type} (S : RationalSource Eqn)

theorem selectedMass_cast (accept : Eqn → Bool) :
    (selectedSum S.numerators (fun i => accept (S.equationAt i)) : ℚ) =
      S.weightedValue accept * S.denominator := by
  rw [numerators, selectedSum_ofFn, Nat.cast_sum]
  simp only [S.equationAt_fin]
  rw [weightedValue, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  cases accept (S.equation i) <;> simp [S.numerator_cast]

theorem roundedValue_bounds (D : Nat) (hD : 0 < D) (accept : Eqn → Bool) :
    S.weightedValue accept - S.occurrences / (D : ℚ) ≤ S.roundedValue D accept ∧
    S.roundedValue D accept ≤ S.weightedValue accept + S.occurrences / (D : ℚ) := by
  have herr := uniformSource_error D S.denominator S.numerators
    (fun i => accept (S.equationAt i)) S.denominator_positive
  have hc : ((S.roundedEquations D).filter accept).length =
      ((uniformSource D S.denominator S.numerators).filter (fun i => accept (S.equationAt i))).length := by
    simp [roundedEquations, List.filter_map, Function.comp_def]
  have hupper : (((S.roundedEquations D).filter accept).length : ℚ) * S.denominator ≤
      D * (selectedSum S.numerators (fun i => accept (S.equationAt i)) : ℚ) +
        S.occurrences * (S.denominator : ℚ) := by
    rw [hc]
    exact_mod_cast (S.length_numerators ▸ herr.1)
  have hlower : (D : ℚ) * (selectedSum S.numerators (fun i => accept (S.equationAt i)) : ℚ) ≤
      ((S.roundedEquations D).filter accept).length * (S.denominator : ℚ) +
        S.occurrences * (S.denominator : ℚ) := by
    rw [hc]
    exact_mod_cast (S.length_numerators ▸ herr.2)
  rw [S.selectedMass_cast] at hupper hlower
  have hq : (0 : ℚ) < S.denominator := by exact_mod_cast S.denominator_positive
  have hd : (0 : ℚ) < D := by exact_mod_cast hD
  have hu : (((S.roundedEquations D).filter accept).length : ℚ) ≤
      D * S.weightedValue accept + S.occurrences := by
    apply le_of_mul_le_mul_right (a := (S.denominator : ℚ)) _ hq
    nlinarith [hupper]
  have hl : (D : ℚ) * S.weightedValue accept ≤
      ((S.roundedEquations D).filter accept).length + (S.occurrences : ℚ) := by
    apply le_of_mul_le_mul_right (a := (S.denominator : ℚ)) _ hq
    nlinarith [hlower]
  unfold roundedValue
  constructor
  · apply (le_div_iff₀ hd).mpr
    calc
      (S.weightedValue accept - S.occurrences / (D : ℚ)) * D =
          D * S.weightedValue accept - S.occurrences := by field_simp
      _ ≤ _ := by linarith
  · apply (div_le_iff₀ hd).mpr
    calc
      _ ≤ D * S.weightedValue accept + S.occurrences := hu
      _ = (S.weightedValue accept + S.occurrences / (D : ℚ)) * D := by field_simp

def roundingDenominator (γ : ℚ) : Nat :=
  targetDenominator S.occurrences γ.num.toNat γ.den

theorem roundingDenominator_positive (γ : ℚ) (hγ : 0 < γ) :
    0 < S.roundingDenominator γ := by
  exact targetDenominator_positive _ _ _ S.positive
    (Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr hγ)) γ.den_pos

theorem roundingDenominator_budget (γ : ℚ) (hγ : 0 < γ) :
    S.occurrences / (S.roundingDenominator γ : ℚ) ≤ γ / 4 := by
  have hn : 0 < γ.num.toNat := Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr hγ)
  have h := targetDenominator_error_budget S.occurrences γ.num.toNat γ.den hn
  have hncast : (γ.num.toNat : ℚ) = (γ.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hγ.le)
  have hnum : (γ.num.toNat : ℚ) = γ * γ.den := by
    rw [hncast]
    exact (div_eq_iff (by exact_mod_cast γ.den_ne_zero)).mp γ.num_div_den
  have hcast : (4 : ℚ) * S.occurrences * γ.den ≤
      S.roundingDenominator γ * (γ.num.toNat : ℚ) := by exact_mod_cast h
  rw [hnum] at hcast
  have hb : (0 : ℚ) < γ.den := by exact_mod_cast γ.den_pos
  have hd : (0 : ℚ) < S.roundingDenominator γ := by
    exact_mod_cast S.roundingDenominator_positive γ hγ
  apply (div_le_iff₀ hd).mpr
  have ht : (4 : ℚ) * S.occurrences ≤ S.roundingDenominator γ * γ := by
    apply le_of_mul_le_mul_right (a := (γ.den : ℚ)) _ hb
    nlinarith [hcast]
  nlinarith

theorem roundingDenominator_size (γ : ℚ) (hγ : 0 < γ) :
    S.roundingDenominator γ ≤ 4 * γ.den * S.occurrences :=
  targetDenominator_size _ _ _ (Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr hγ))

theorem completeness_transport (γ ξ : ℚ) (hγ : 0 < γ) (hξ : ξ ≤ γ / 4)
    (accept : Eqn → Bool) (hsource : 1 - ξ ≤ S.weightedValue accept) :
    1 - γ ≤ S.roundedValue (S.roundingDenominator γ) accept := by
  have h := (S.roundedValue_bounds _ (S.roundingDenominator_positive γ hγ) accept).1
  have hb := S.roundingDenominator_budget γ hγ
  linarith

theorem soundness_transport (γ ξ : ℚ) (hγ : 0 < γ) (hγsmall : γ ≤ 1 / 8)
    (hξ : ξ ≤ 1 / 16) (accept : Eqn → Bool)
    (hsource : S.weightedValue accept ≤ (1 + ξ) / 2) :
    S.roundedValue (S.roundingDenominator γ) accept ≤ 3 / 4 := by
  have h := (S.roundedValue_bounds _ (S.roundingDenominator_positive γ hγ) accept).2
  have hb := S.roundingDenominator_budget γ hγ
  linarith

theorem roundedEquations_for_nonempty (γ : ℚ) (hγ : 0 < γ) :
    S.roundedEquations (S.roundingDenominator γ) ≠ [] :=
  S.roundedEquations_nonempty _ (S.roundingDenominator_positive γ hγ)

end RationalSource

section E3Lin

variable {Name : Type} (S : RationalSource (CloneGap.Equation Name))

theorem e3lin_completeness (γ ξ : ℚ) (hγ : 0 < γ) (hξ : ξ ≤ γ / 4)
    (hsource : ∃ g : Name → Bool,
      1 - ξ ≤ S.weightedValue (fun e => CloneGap.satisfied e g)) :
    ∃ g : Name → Bool,
      (1 - γ) * (S.roundedEquations (S.roundingDenominator γ)).length ≤
        (((S.roundedEquations (S.roundingDenominator γ)).filter
          (fun e => CloneGap.satisfied e g)).length : ℚ) := by
  obtain ⟨g, hg⟩ := hsource
  refine ⟨g, ?_⟩
  have h := S.completeness_transport γ ξ hγ hξ (fun e => CloneGap.satisfied e g) hg
  have hd : (0 : ℚ) < S.roundingDenominator γ := by
    exact_mod_cast S.roundingDenominator_positive γ hγ
  unfold RationalSource.roundedValue at h
  have hc := (le_div_iff₀ hd).mp h
  simpa only [S.roundedEquations_length] using hc

theorem e3lin_soundness (γ ξ : ℚ) (hγ : 0 < γ) (hγsmall : γ ≤ 1 / 8)
    (hξ : ξ ≤ 1 / 16)
    (hsource : ∀ g : Name → Bool,
      S.weightedValue (fun e => CloneGap.satisfied e g) ≤ (1 + ξ) / 2) :
    ∀ g : Name → Bool,
      4 * ((S.roundedEquations (S.roundingDenominator γ)).filter
        (fun e => CloneGap.satisfied e g)).length ≤
      3 * (S.roundedEquations (S.roundingDenominator γ)).length := by
  intro g
  have h := S.soundness_transport γ ξ hγ hγsmall hξ
    (fun e => CloneGap.satisfied e g) (hsource g)
  have hd : (0 : ℚ) < S.roundingDenominator γ := by
    exact_mod_cast S.roundingDenominator_positive γ hγ
  unfold RationalSource.roundedValue at h
  have hc := (div_le_iff₀ hd).mp h
  rw [S.roundedEquations_length]
  have hc' : (4 : ℚ) * ((S.roundedEquations (S.roundingDenominator γ)).filter
      (fun e => CloneGap.satisfied e g)).length ≤ 3 * S.roundingDenominator γ := by
    linarith
  exact_mod_cast hc'

end E3Lin

end DFVSGames.Reduction.WeightedSource
end

section

namespace DFVSGames.Reduction.Preprocessing

open ActualSource WeightedSource

def rounded {n : Nat} (W : RationalSource (CloneGap.Equation (Fin n)))
    (γ : ℚ) (hγ : 0 < γ) : Source :=
  Source.ofList (W.roundedEquations (W.roundingDenominator γ))
    (W.roundedEquations_for_nonempty γ hγ)

theorem rounded_failure_add_value {n : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ : ℚ) (hγ : 0 < γ)
    (A : Fin n → Bool) :
    (rounded W γ hγ).failure A + W.roundedValue (W.roundingDenominator γ)
      (fun e => CloneGap.satisfied e A) = 1 := by
  have h := SourceProbability.failure_add_satisfaction (rounded W γ hγ) A
  simpa [rounded, Source.sourceList, Source.ofList,
    RationalSource.roundedEquations_length, RationalSource.roundedValue,
    List.countP_eq_length_filter] using h

theorem rounded_complete {n : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ ξ : ℚ)
    (hγ : 0 < γ) (hξ : ξ ≤ γ / 4)
    (hsource : ∃ A : Fin n → Bool,
      1 - ξ ≤ W.weightedValue (fun e => CloneGap.satisfied e A)) :
    ∃ A : Fin (rounded W γ hγ).«variables» → Bool, (rounded W γ hγ).failure A ≤ γ := by
  obtain ⟨A, hA⟩ := hsource
  refine ⟨A, ?_⟩
  have ht := W.completeness_transport γ ξ hγ hξ (fun e => CloneGap.satisfied e A) hA
  have he := rounded_failure_add_value W γ hγ A
  linarith

theorem rounded_sound {n : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ ξ : ℚ)
    (hγ : 0 < γ) (hγsmall : γ ≤ 1 / 8) (hξ : ξ ≤ 1 / 16)
    (hsource : ∀ A : Fin n → Bool,
      W.weightedValue (fun e => CloneGap.satisfied e A) ≤ (1 + ξ) / 2) :
    ∀ A : Fin (rounded W γ hγ).«variables» → Bool,
      (1 / 4 : ℚ) ≤ (rounded W γ hγ).failure A := by
  intro A
  have ht := W.soundness_transport γ ξ hγ hγsmall hξ
    (fun e => CloneGap.satisfied e A) (hsource A)
  have he := rounded_failure_add_value W γ hγ A
  linarith

def uniformSource {n : Nat} (W : RationalSource (CloneGap.Equation (Fin n)))
    (γ : ℚ) (hγ : 0 < γ) : Source := FiniteSource.cloned (rounded W γ hγ)

theorem cloned_failure_eq (S : Source) (A : Fin S.«variables» → Bool) :
    (FiniteSource.cloned S).failure
      (fun z => A ((FiniteSource.nameEquiv S).symm z).1) = S.failure A := by
  have hc := SourceProbability.failure_add_satisfaction (FiniteSource.cloned S)
    (fun z => A ((FiniteSource.nameEquiv S).symm z).1)
  have hs := SourceProbability.failure_add_satisfaction S A
  erw [FiniteSource.cloned_completeness_count S A, FiniteSource.cloned_length S] at hc
  simp only [Nat.cast_mul] at hc
  have hn : (S.occurrences : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt S.nonempty
  have hd : (CloneGap.distinctTriples.length : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt FiniteSource.distinctTriples_nonempty
  have hratio :
      ((S.sourceList.countP (fun e => CloneGap.satisfied e A) : ℚ) *
        (CloneGap.distinctTriples.length : ℚ)) /
        ((S.occurrences : ℚ) * (CloneGap.distinctTriples.length : ℚ)) =
      (S.sourceList.countP (fun e => CloneGap.satisfied e A) : ℚ) / S.occurrences := by
    field_simp [hn, hd]
  rw [hratio] at hc
  linarith

theorem uniformSource_complete {n : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ ξ : ℚ)
    (hγ : 0 < γ) (hξ : ξ ≤ γ / 4)
    (hsource : ∃ A : Fin n → Bool,
      1 - ξ ≤ W.weightedValue (fun e => CloneGap.satisfied e A)) :
    ∃ A : Fin (uniformSource W γ hγ).«variables» → Bool,
      (uniformSource W γ hγ).failure A ≤ γ := by
  obtain ⟨A, hA⟩ := rounded_complete W γ ξ hγ hξ hsource
  refine ⟨fun z => A ((FiniteSource.nameEquiv (rounded W γ hγ)).symm z).1, ?_⟩
  change (FiniteSource.cloned (rounded W γ hγ)).failure _ ≤ γ
  exact (cloned_failure_eq (rounded W γ hγ) A).trans_le hA

theorem uniformSource_distinct {n : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ : ℚ) (hγ : 0 < γ) :
    (uniformSource W γ hγ).DistinctNames := FiniteSource.cloned_distinct _

theorem uniformSource_sound {n : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ ξ : ℚ)
    (hγ : 0 < γ) (hγsmall : γ ≤ 1 / 8) (hξ : ξ ≤ 1 / 16)
    (hsource : ∀ A : Fin n → Bool,
      W.weightedValue (fun e => CloneGap.satisfied e A) ≤ (1 + ξ) / 2) :
    ∀ A : Fin (uniformSource W γ hγ).«variables» → Bool,
      (1 / 64 : ℚ) ≤ (uniformSource W γ hγ).failure A := by
  intro A
  have hr := rounded_sound W γ ξ hγ hγsmall hξ hsource
  have hgap : ∀ B : Fin (rounded W γ hγ).«variables» → Bool,
      (rounded W γ hγ).sourceList.length ≤
      4 * (rounded W γ hγ).sourceList.countP (fun e => !CloneGap.satisfied e B) := by
    intro B
    exact (SourceProbability.quarter_gap_iff _ B).mp (hr B)
  have hc := FiniteSource.cloned_gap (rounded W γ hγ) hgap A
  change (uniformSource W γ hγ).sourceList.length ≤
    64 * (uniformSource W γ hγ).sourceList.countP (fun e => !CloneGap.satisfied e A) at hc
  rw [SourceProbability.Source_failure_eq_count]
  have hn : (0 : ℚ) < (uniformSource W γ hγ).occurrences := by
    exact_mod_cast (uniformSource W γ hγ).nonempty
  apply (le_div_iff₀ hn).mpr
  rw [Source.sourceList_length] at hc
  have hc' : ((uniformSource W γ hγ).occurrences : ℚ) ≤
      64 * ((uniformSource W γ hγ).sourceList.countP
        (fun e => !CloneGap.satisfied e A) : ℚ) := by exact_mod_cast hc
  linarith

end DFVSGames.Reduction.Preprocessing
end

section

namespace DFVSGames.Reduction.OuterCompleteness

open ActualSource WeightedSource
open DFVSGames.Foundations.Target
open DFVSGames.Integration

theorem weighted_completeAt {n s d : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ ξ : ℚ)
    (hγ : 0 < γ) (hξ : ξ ≤ γ / 4) (k : Nat) (g : SplitGadget s d)
    (error : RationalError)
    (hsource : ∃ A : Fin n → Bool,
      1 - ξ ≤ W.weightedValue (fun e => CloneGap.satisfied e A))
    (hbudget : (k : ℚ) * γ + g.stabilityError / 2 ≤ GapSemantics.errorValue error) :
    CompleteAt error
      (ActualGame.outputInstance (Preprocessing.uniformSource W γ hγ) k g) := by
  obtain ⟨A, hA⟩ := Preprocessing.uniformSource_complete W γ ξ hγ hξ hsource
  apply ActualCompleteness.actual_completeAt _ k g A error
  have hm := mul_le_mul_of_nonneg_left hA (show (0 : ℚ) ≤ k by positivity)
  linarith

def sourceError (error : RationalError) (k : Nat) : ℚ :=
  FinalParameters.gamma (GapSemantics.errorValue error) k

theorem sourceError_pos (error : RationalError) {k : Nat} (hk : 0 < k) :
    0 < sourceError error k :=
  (FinalParameters.gamma_bounds (GapSemantics.errorValue_pos error)
    (GapSemantics.errorValue_lt_half error) hk).1

theorem weighted_completeAt_of_parameters {n s d : Nat}
    (error : RationalError) (W : RationalSource (CloneGap.Equation (Fin n)))
    (k : Nat) (hk : 0 < k) (ξ : ℚ)
    (hξ : ξ ≤ sourceError error k / 4) (g : SplitGadget s d)
    (hstable : g.stabilityError ≤ GapSemantics.errorValue error / 2)
    (hsource : ∃ A : Fin n → Bool,
      1 - ξ ≤ W.weightedValue (fun e => CloneGap.satisfied e A)) :
    CompleteAt error
      (ActualGame.outputInstance
        (Preprocessing.uniformSource W (sourceError error k) (sourceError_pos error hk)) k g) := by
  apply weighted_completeAt W (sourceError error k) ξ (sourceError_pos error hk)
    hξ k g error hsource
  calc
    (k : ℚ) * sourceError error k + g.stabilityError / 2 ≤
        (k : ℚ) * sourceError error k + (GapSemantics.errorValue error / 2) / 2 := by
      linarith
    _ = GapSemantics.errorValue error / 2 := FinalParameters.completeness_budget hk
    _ ≤ GapSemantics.errorValue error := by
      have h := GapSemantics.errorValue_pos error
      linarith

theorem weighted_explicit_completeAt_of_parameters {n s d : Nat}
    (error : RationalError) (W : RationalSource (CloneGap.Equation (Fin n)))
    (k : Nat) (hk : 0 < k) (ξ : ℚ)
    (hξ : ξ ≤ sourceError error k / 4) (g : SplitGadget s d)
    (en : NoiseEnumeration g)
    (hstable : g.stabilityError ≤ GapSemantics.errorValue error / 2)
    (hsource : ∃ A : Fin n → Bool,
      1 - ξ ≤ W.weightedValue (fun e => CloneGap.satisfied e A)) :
    CompleteAt error
      (ActualGame.outputInstanceWithEnumeration
        (Preprocessing.uniformSource W (sourceError error k) (sourceError_pos error hk))
        k g en) := by
  apply (ActualGame.completeAt_outputInstanceWithEnumeration_iff error _ k g en).mpr
  exact weighted_completeAt_of_parameters error W k hk ξ hξ g hstable hsource

end DFVSGames.Reduction.OuterCompleteness
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
