import OAI.NumberTheory.Ostmann.Construction.BranchingHistoryIntegrality
import OAI.NumberTheory.Ostmann.Arithmetic.RecursiveNodeExpansion

namespace OAI

/-! # The concrete transfer system of word products and reconstructed pivots -/

namespace Ostmann

open scoped Classical

universe u

structure WordTransferNode (σ : Type u) where
  target : σ
  left : List σ
  right : List σ
  childBound : ℕ
  pivotBound : ℕ

inductive WordTransferTemplate (σ : Type u) : ℕ → Type u where
  | leaf (word : List σ) : WordTransferTemplate σ 0
  | node {n : ℕ} (data : WordTransferNode σ)
      (left right : WordTransferTemplate σ n) : WordTransferTemplate σ (n + 1)

abbrev WordTransferState (σ : Type u) := Σ n : ℕ, WordTransferTemplate σ n × (σ → ℕ)

def WordTransferTemplate.state {σ : Type u} {n : ℕ}
    (template : WordTransferTemplate σ n) (x : σ → ℕ) : WordTransferState σ := ⟨n, template, x⟩

noncomputable def wordTransferLeft {σ : Type u} : WordTransferState σ → ℕ
  | ⟨0, _, _⟩ => 1
  | ⟨_ + 1, .node d _ _, x⟩ => (d.left.map x).prod

noncomputable def wordTransferRight {σ : Type u} : WordTransferState σ → ℕ
  | ⟨0, _, _⟩ => 1
  | ⟨_ + 1, .node d _ _, x⟩ => (d.right.map x).prod

noncomputable def wordTransferChildBound {σ : Type u} : WordTransferState σ → ℕ
  | ⟨0, _, _⟩ => 0
  | ⟨_ + 1, .node d _ _, _⟩ => d.childBound

noncomputable def wordTransferPivotBound {σ : Type u} : WordTransferState σ → ℕ
  | ⟨0, _, _⟩ => 0
  | ⟨_ + 1, .node d _ _, _⟩ => d.pivotBound

noncomputable def wordTransferLeftState {σ : Type u} : WordTransferState σ → ℕ → WordTransferState σ
  | ⟨0, t, x⟩, _ => ⟨0, t, x⟩
  | ⟨n + 1, .node d l _, x⟩, P => ⟨n, l, Function.update x d.target P⟩

noncomputable def wordTransferRightState {σ : Type u} : WordTransferState σ → ℕ → WordTransferState σ
  | ⟨0, t, x⟩, _ => ⟨0, t, x⟩
  | ⟨n + 1, .node d _ r, x⟩, P => ⟨n, r, Function.update x d.target P⟩

noncomputable def wordTransferSystem (σ : Type u) : TransferHistorySystem (WordTransferState σ) where
  leftProduct := wordTransferLeft
  rightProduct := wordTransferRight
  childBound := wordTransferChildBound
  pivotBound := wordTransferPivotBound
  leftState := wordTransferLeftState
  rightState := wordTransferRightState

def NonzeroInternalFrequencies : (n : ℕ) → FrequencyTree ℤ n → Prop
  | 0, _ => True
  | n + 1, t => t.1 ≠ 0 ∧ NonzeroInternalFrequencies n t.2.1 ∧ NonzeroInternalFrequencies n t.2.2

theorem ValidTransferHistory.nonzero_internal {State : Type*} (sys : TransferHistorySystem State)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) (ht : ValidTransferHistory sys n σ t) :
    NonzeroInternalFrequencies n t := by
  induction n generalizing σ with
  | zero => trivial
  | succ n ih =>
    obtain ⟨P, hp, hl, hr⟩ := ht
    exact ⟨hp.root_ne_zero, ih _ _ hl, ih _ _ hr⟩

def wordTransferStep {σ : Type u} (d : WordTransferNode σ)
    (s v w : ℤ) (hs : s ≠ 0) : HistoryPivotStep σ where
  target := d.target
  left := d.left
  right := d.right
  s := s
  v := v
  w := w
  s_ne_zero := hs

noncomputable def WordTransferTemplate.branching {σ : Type u} :
    {n : ℕ} → WordTransferTemplate σ n → (t : FrequencyTree ℤ n) →
      NonzeroInternalFrequencies n t → BranchingWordHistory σ
  | 0, .leaf word, _, _ => .leaf word
  | n + 1, .node d l r, t, ht =>
      .node (wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ht.1)
        (l.branching t.2.1 ht.2.1) (r.branching t.2.2 ht.2.2)

theorem wordTransferStep_numerator {σ : Type u} (d : WordTransferNode σ)
    (s v w : ℤ) (hs : s ≠ 0) (x : σ → ℕ) :
    (wordTransferStep d s v w hs).numerator (fun i => (x i : ℤ)) =
      v * ((d.right.map x).prod : ℤ) - w * ((d.left.map x).prod : ℤ) := by
  have hcast (word : List σ) : (word.map (fun i => (x i : ℤ))).prod = ((word.map x).prod : ℤ) := by
    induction word with
    | nil => rfl
    | cons i word ih => simp only [List.map_cons, List.prod_cons, Nat.cast_mul, ih]
  simp only [HistoryPivotStep.numerator, wordTransferStep, hcast]

theorem wordTransferStep_valid {σ : Type u} {n : ℕ} (d : WordTransferNode σ)
    (l r : WordTransferTemplate σ n) (x : σ → ℕ) (s v w : ℤ) (P : ℕ)
    (hp : ValidTransferNode (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x) s v w P) :
    (wordTransferStep d s v w hp.root_ne_zero).Valid (fun i => (x i : ℤ)) := by
  have hnum := wordTransferStep_numerator d s v w hp.root_ne_zero x
  change s ∣ (wordTransferStep d s v w hp.root_ne_zero).numerator (fun i => (x i : ℤ))
  rw [hnum]
  exact ⟨(P : ℤ), hp.relation⟩

theorem wordTransferStep_apply {σ : Type u} {n : ℕ} (d : WordTransferNode σ)
    (l r : WordTransferTemplate σ n) (x : σ → ℕ) (s v w : ℤ) (P : ℕ)
    (hp : ValidTransferNode (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x) s v w P) :
    (wordTransferStep d s v w hp.root_ne_zero).applyInteger (fun i => (x i : ℤ)) =
      fun i => (Function.update x d.target P i : ℤ) := by
  have hnum : (wordTransferStep d s v w hp.root_ne_zero).numerator (fun i => (x i : ℤ)) = s * P := by
    rw [wordTransferStep_numerator]
    exact hp.relation
  funext i
  by_cases hi : i = d.target
  · subst i
    simp only [HistoryPivotStep.applyInteger,
      show (wordTransferStep d s v w hp.root_ne_zero).target = d.target from rfl, Function.update_self]
    change (wordTransferStep d s v w hp.root_ne_zero).numerator (fun i => (x i : ℤ)) / s = (P : ℤ)
    rw [hnum]
    exact Int.mul_ediv_cancel_left (P : ℤ) hp.root_ne_zero
  · simp only [HistoryPivotStep.applyInteger, wordTransferStep, Function.update_of_ne hi]

end Ostmann

end OAI
