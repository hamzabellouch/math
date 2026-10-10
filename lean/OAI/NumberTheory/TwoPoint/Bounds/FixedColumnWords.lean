import OAI.NumberTheory.TwoPoint.Walks.HighRankWordEvents
import Mathlib.Data.List.OfFn

namespace OAI

/-! The actual resampling model after every other column and padding are fixed. -/

namespace TwoPointCorrelations

structure ColumnWordPattern (α : Type*) where
  length : ℕ
  label : ℕ → α
  forward : ℕ → Bool
  padding : ℕ → ℕ
  otherColumns : ℕ → ℕ

namespace ColumnWordPattern

variable {α : Type*}

def step (w : ColumnWordPattern α) (value : α → ℕ) (j : ℕ) : SignedStep where
  forward := w.forward j
  tuple := value (w.label j) * w.otherColumns j
  padding := w.padding j

def word (w : ColumnWordPattern α) (value : α → ℕ) : List SignedStep :=
  List.ofFn (fun j : Fin w.length => w.step value j)

def coefficient (w : ColumnWordPattern α) (h j : ℕ) : ℤ :=
  (if w.forward j then 1 else -1) * (h : ℤ) * w.padding j * w.otherColumns j

@[simp] lemma word_length (w : ColumnWordPattern α) (value : α → ℕ) :
    (w.word value).length = w.length := by simp [word]

lemma displacement (w : ColumnWordPattern α) (h : ℕ) (value : α → ℕ)
    (j : ℕ) (hj : j < w.length) :
    wordStepDisplacement h (w.word value) j = w.coefficient h j * value (w.label j) := by
  rw [wordStepDisplacement_getElem h (w.word value) j (by simpa using hj)]
  simp only [word, List.getElem_ofFn, step, SignedStep.displacement, coefficient, Nat.cast_mul]
  ring

lemma coefficient_abs (w : ColumnWordPattern α) (h j : ℕ) :
    |w.coefficient h j| = (h : ℤ) * w.padding j * w.otherColumns j := by
  cases hb : w.forward j <;> simp [coefficient, hb, abs_mul]

lemma coefficient_bound (w : ColumnWordPattern α) (h Q D : ℕ)
    (hq : ∀ j < w.length, w.padding j ≤ Q)
    (hd : ∀ j < w.length, w.otherColumns j ≤ D) :
    ∀ j < w.length, |w.coefficient h j| ≤ (h * Q * D : ℕ) := by
  intro j hj
  rw [coefficient_abs]
  exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul_left h (hq j hj)) (hd j hj)

/-- The resampled step list has fixed coefficients independent of every
numerical prime in the chosen column. Only selected departures need be lit. -/
theorem high_rank_event_bound [Fintype α] [DecidableEq α]
    {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (w : ColumnWordPattern α) (h Q D B : ℕ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (μ : FiniteLaw P)
    (hbound : ∀ p ∈ P, p ≤ B)
    (hq : ∀ j < w.length, w.padding j ≤ Q)
    (hd : ∀ j < w.length, w.otherColumns j ≤ D)
    (left right : ρ → ℕ) (control : ρ → α)
    (hl : ∀ i, left i ≤ w.length) (hr : ∀ i, right i ≤ w.length)
    (hind : LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture w.label (fun j => (w.coefficient h j : ℝ)) (left i) -
        formalDeparture w.label (fun j => (w.coefficient h j : ℝ)) (right i))
      (fun i => Pi.basisFun ℝ α (control i))))
    (a : ℝ) (ha : 0 ≤ a) (hatom : ∀ p, μ.weight p ≤ a)
    (base : (α → P) → ℤ) (E : (α → P) → Prop)
    (hlit : ∀ x, E x → ∀ i, ((x (control i)).val : ℤ) ∣ base x +
      wordDisplacement h ((w.word (fun z => (x z).val)).take (left i)))
    (hrit : ∀ x, E x → ∀ i, ((x (control i)).val : ℤ) ∣ base x +
      wordDisplacement h ((w.word (fun z => (x z).val)).take (right i))) :
    (FiniteLaw.independent (fun _ : α => μ)).probability E ≤
      Real.sqrt ((a * (1 + (Nat.log 2 (2 * w.length * (h * Q * D) * B) : ℝ))) ^ Fintype.card ρ) := by
  apply high_rank_column_event_bound P hP μ w.label (w.coefficient h) left right control
    hind w.length (h * Q * D) B hl hr (w.coefficient_bound h Q D hq hd) hbound a ha hatom
    h (fun x => w.word (fun z => (x z).val)) base E
  · intro x _ j hj
    exact w.displacement h _ j (by simpa using hj)
  · intro x _ i
    simpa using hl i
  · intro x _ i
    simpa using hr i
  · exact hlit
  · exact hrit

end ColumnWordPattern

end TwoPointCorrelations

end OAI
