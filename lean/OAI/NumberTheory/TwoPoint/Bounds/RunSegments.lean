import OAI.NumberTheory.TwoPoint.Walks.BlockGeometry

namespace OAI

/-! Interval-shaped label uses bound omitted runs and regular segments. -/

namespace TwoPointCorrelations

open Finset

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- A sequence obtained by keeping run starts has no repeated label when
every label's original occurrences form an interval. -/
theorem run_labels_injective {m n : ℕ} (label : Fin n → α)
    (hinterval : ∀ i j k : Fin n, i ≤ j → j ≤ k → label i = label k → label j = label i)
    (start : Fin m → Fin n) (hstart : StrictMono start)
    (hchange : ∀ i j : Fin m, i.val + 1 = j.val → label (start i) ≠ label (start j)) :
    Function.Injective (label ∘ start) := by
  have hless : ∀ i j : Fin m, i < j → label (start i) ≠ label (start j) := by
    intro i j hij heq
    let next : Fin m := ⟨i.val + 1, by omega⟩
    have hinext : i ≤ next := by change i.val ≤ i.val + 1; omega
    have hnextj : next ≤ j := by change i.val + 1 ≤ j.val; exact hij
    have hn := hinterval (start i) (start next) (start j)
      (hstart.monotone hinext) (hstart.monotone hnextj) heq
    exact hchange i next rfl hn.symm
  intro i j heq
  rcases lt_trichotomy i j with hij | hij | hji
  · exact (hless i j hij heq).elim
  · exact hij
  · exact (hless j i hji heq.symm).elim

omit [DecidableEq α] in
theorem fin_label_intervals {n : ℕ} (label : Fin n → α)
    (h : OccurrenceIntervals (fun p i => ∃ hi : i < n, label ⟨i, hi⟩ = p) 0 n) :
    ∀ i j k : Fin n, i ≤ j → j ≤ k → label i = label k → label j = label i := by
  intro i j k hij hjk heq
  obtain ⟨_, hj⟩ := h (label i) i j k (Nat.zero_le _) hij hjk k.isLt
    ⟨i.isLt, rfl⟩ ⟨k.isLt, heq.symm⟩
  exact hj

def omittedRunPositions {m : ℕ} (label : Fin m → α) (omitted : Finset α) : Finset (Fin m) :=
  univ.filter (fun i => label i ∈ omitted)

/-- One omitted label contributes at most one run in a perfect block. -/
theorem omitted_runs_le {m : ℕ} (label : Fin m → α) (omitted : Finset α)
    (hinj : Function.Injective label) :
    (omittedRunPositions label omitted).card ≤ omitted.card := by
  apply card_le_card_of_injOn label
  · intro i hi
    exact (mem_filter.mp hi).2
  · intro i _ j _ hij
    exact hinj hij

/-- A regular segment starts at the first run or immediately after an
omitted run. Empty segments are not counted. -/
def RegularRunStart {m : ℕ} (label : Fin m → α) (omitted : Finset α) (i : Fin m) : Prop :=
  label i ∉ omitted ∧ (i.val = 0 ∨ ∃ j : Fin m, j.val + 1 = i.val ∧ label j ∈ omitted)

noncomputable def regularRunStarts {m : ℕ} (label : Fin m → α) (omitted : Finset α) :
    Finset (Fin m) := by
  classical
  exact univ.filter (RegularRunStart label omitted)

/-- Charge every noninitial regular segment to its immediately preceding
omitted run. This argument allows any numerical values of the labels. -/
theorem regular_segments_le {m : ℕ} (label : Fin m → α) (omitted : Finset α) :
    (regularRunStarts label omitted).card ≤ (omittedRunPositions label omitted).card + 1 := by
  classical
  let f : (regularRunStarts label omitted) → Option (omittedRunPositions label omitted) := fun i =>
    if hi : i.val.val = 0 then none else
      some ⟨(mem_filter.mp i.property).2.2.resolve_left hi |>.choose,
        mem_filter.mpr ⟨mem_univ _,
          ((mem_filter.mp i.property).2.2.resolve_left hi).choose_spec.2⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    by_cases hi : i.val.val = 0
    · by_cases hj : j.val.val = 0
      · exact hi.trans hj.symm
      · simp only [f, dite_eq_left hi, dite_eq_right hj] at hij
        cases hij
    · by_cases hj : j.val.val = 0
      · simp only [f, dite_eq_right hi, dite_eq_left hj] at hij
        cases hij
      · have hprev := congrArg (fun z : Option (omittedRunPositions label omitted) =>
          z.map (fun k => k.val.val)) hij
        simp only [f, dite_eq_right hi, dite_eq_right hj, Option.map_some, Option.some.injEq] at hprev
        have hip := ((mem_filter.mp i.property).2.2.resolve_left hi).choose_spec.1
        have hjp := ((mem_filter.mp j.property).2.2.resolve_left hj).choose_spec.1
        omega
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_option] using hc

theorem regular_segments_le_omitted_labels {m : ℕ} (label : Fin m → α)
    (omitted : Finset α) (hinj : Function.Injective label) :
    (regularRunStarts label omitted).card ≤ omitted.card + 1 :=
  (regular_segments_le label omitted).trans (Nat.add_le_add_right (omitted_runs_le label omitted hinj) 1)

/-- Across `B` perfect blocks these are the exact combinatorial budgets
used in the endpoint and omitted-label parts of the forest code. -/
theorem block_run_budgets {B : ℕ} (m : Fin B → ℕ)
    (label : ∀ b, Fin (m b) → α) (omitted : Finset α)
    (hinj : ∀ b, Function.Injective (label b)) :
    (∑ b, (omittedRunPositions (label b) omitted).card) ≤ omitted.card * B ∧
    (∑ b, (regularRunStarts (label b) omitted).card) ≤ (omitted.card + 1) * B := by
  constructor
  · calc
      _ ≤ ∑ _b : Fin B, omitted.card := sum_le_sum (fun b _ => omitted_runs_le _ _ (hinj b))
      _ = _ := by simp [mul_comm]
  · calc
      _ ≤ ∑ _b : Fin B, (omitted.card + 1) :=
        sum_le_sum (fun b _ => regular_segments_le_omitted_labels _ _ (hinj b))
      _ = _ := by simp [mul_comm]

end TwoPointCorrelations

end OAI
