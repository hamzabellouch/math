import OAI.NumberTheory.TwoPoint.Walks.HighRankMinor
import OAI.NumberTheory.TwoPoint.Bounds.FormalDepartures
import OAI.NumberTheory.TwoPoint.Walks.WordRelations
import OAI.NumberTheory.TwoPoint.Bounds.RandomPrimeRank

namespace OAI

/-! Integral coefficient rows of the lit-consistency equations. -/

namespace TwoPointCorrelations

open Finset Matrix

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- Each step has one label in the selected column; its coefficient contains
only its sign, padding, fixed shift and the primes in other columns. -/
noncomputable def integerColumnDeparture (label : ℕ → α) (t : ℕ → ℤ) (n : ℕ) (z : α) : ℤ :=
  ∑ a ∈ range n, if label a = z then t a else 0

lemma integerColumnDeparture_cast (label : ℕ → α) (t : ℕ → ℤ) (n : ℕ) (z : α) :
    (integerColumnDeparture label t n z : ℝ) =
      formalDeparture label (fun a => (t a : ℝ)) n z := by
  classical
  simp [integerColumnDeparture, formalDeparture, Pi.basisFun_apply, Pi.single_apply, eq_comm]

lemma integerColumnDeparture_eval (label : ℕ → α) (t : ℕ → ℤ) (n : ℕ) (value : α → ℤ) :
    (∑ z, integerColumnDeparture label t n z * value z) =
      ∑ a ∈ range n, t a * value (label a) := by
  classical
  simp only [integerColumnDeparture, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp [ite_mul, eq_comm]

noncomputable def columnDifference (label : ℕ → α) (t : ℕ → ℤ)
    (left right : ρ → ℕ) (i : ρ) (z : α) : ℤ :=
  integerColumnDeparture label t (left i) z - integerColumnDeparture label t (right i) z

omit [Fintype ρ] [DecidableEq ρ] in
lemma columnDifference_cast (label : ℕ → α) (t : ℕ → ℤ)
    (left right : ρ → ℕ) (i : ρ) :
    (fun z => (columnDifference label t left right i z : ℝ)) =
      formalDeparture label (fun a => (t a : ℝ)) (left i) -
        formalDeparture label (fun a => (t a : ℝ)) (right i) := by
  funext z
  simp only [columnDifference, Int.cast_sub, integerColumnDeparture_cast, Pi.sub_apply]

omit [Fintype ρ] [DecidableEq ρ] in
lemma columnDifference_eval (label : ℕ → α) (t : ℕ → ℤ)
    (left right : ρ → ℕ) (i : ρ) (value : α → ℤ) :
    (∑ z, columnDifference label t left right i z * value z) =
      (∑ a ∈ range (left i), t a * value (label a)) -
        ∑ a ∈ range (right i), t a * value (label a) := by
  simp only [columnDifference, sub_mul, sum_sub_distrib, integerColumnDeparture_eval]

omit [Fintype ρ] [DecidableEq ρ] in
/-- Only the selected lit departures are needed; unlit steps need not be
positive in the mixed-difference expansion. -/
theorem column_congruence_of_departure_divisibilities (h : ℕ) (word : List SignedStep)
    (base : ℤ) (label : ℕ → α) (t : ℕ → ℤ) (value : α → ℕ)
    (hstep : ∀ a < word.length, wordStepDisplacement h word a = t a * (value (label a) : ℤ))
    (left right : ρ → ℕ) (control : ρ → α)
    (hleft : ∀ i, left i ≤ word.length) (hright : ∀ i, right i ≤ word.length)
    (hlit : ∀ i, (value (control i) : ℤ) ∣ base + wordDisplacement h (word.take (left i)))
    (hrit : ∀ i, (value (control i) : ℤ) ∣ base + wordDisplacement h (word.take (right i)))
    (i : ρ) :
    (value (control i) : ℤ) ∣ ∑ z, columnDifference label t left right i z * (value z : ℤ) := by
  have heval (n : ℕ) (hn : n ≤ word.length) : wordDisplacement h (word.take n) =
      ∑ a ∈ range n, t a * (value (label a) : ℤ) := by
    rw [wordDisplacement_take]
    exact sum_congr rfl (fun a ha => hstep a ((mem_range.mp ha).trans_le hn))
  have hd := dvd_sub (hlit i) (hrit i)
  rw [add_sub_add_left_eq_sub, heval _ (hleft i), heval _ (hright i)] at hd
  simpa only [columnDifference_eval] using hd

omit [Fintype ρ] [DecidableEq ρ] in
/-- Positivity of the whole word is a convenient sufficient condition for
selected lit consistency. -/
theorem positiveWord_column_congruence (h : ℕ) (word : List SignedStep) (base : ℤ)
    (hw : PositiveWord h base word) (label : ℕ → α) (t : ℕ → ℤ) (value : α → ℕ)
    (hstep : ∀ a < word.length, wordStepDisplacement h word a = t a * (value (label a) : ℤ))
    (left right : ρ → ℕ) (control : ρ → α)
    (hleft : ∀ i, TuplePrimeAt word (value (control i)) (left i))
    (hright : ∀ i, TuplePrimeAt word (value (control i)) (right i)) (i : ρ) :
    (value (control i) : ℤ) ∣ ∑ z, columnDifference label t left right i z * (value z : ℤ) := by
  exact column_congruence_of_departure_divisibilities h word base label t value hstep
    left right control (fun i => (hleft i).index_lt.le) (fun i => (hright i).index_lt.le)
    (fun i => hw.tuplePrime_departure (hleft i)) (fun i => hw.tuplePrime_departure (hright i)) i

/-- Joint independence in the manuscript's formal departures gives the
actual nonzero integral minor with disjoint controlling coordinates. -/
theorem columnDifference_disjoint_minor (label : ℕ → α) (t : ℕ → ℤ)
    (left right : ρ → ℕ) (control : ρ → α)
    (hind : LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture label (fun a => (t a : ℝ)) (left i) -
        formalDeparture label (fun a => (t a : ℝ)) (right i))
      (fun i => Pi.basisFun ℝ α (control i)))) :
    Function.Injective control ∧ ∃ pivot : ρ → α, Function.Injective pivot ∧
      (∀ i j, pivot i ≠ control j) ∧
      (Matrix.of fun i j => columnDifference label t left right i (pivot j)).det ≠ 0 := by
  apply integral_independent_pairs_disjoint_minor (columnDifference label t left right) control
  have heq : (fun i z => (columnDifference label t left right i z : ℝ)) =
      (fun i => formalDeparture label (fun a => (t a : ℝ)) (left i) -
        formalDeparture label (fun a => (t a : ℝ)) (right i)) := by
    funext i
    exact columnDifference_cast label t left right i
  rw [heq]
  exact hind

end TwoPointCorrelations

end OAI
