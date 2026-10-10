import OAI.NumberTheory.TwoPoint.Walks.HighRankColumns
import OAI.NumberTheory.TwoPoint.Walks.ColumnCoefficientBounds

namespace OAI

/-! Finite high-rank saving for actual selected lit departures of resampled words. -/

namespace TwoPointCorrelations

open Finset

variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- Coefficient bounds supply the size hypothesis uniformly for every
minor selected from the fixed column data. -/
theorem column_difference_rank_probability
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (μ : FiniteLaw P)
    (label : ℕ → α) (t : ℕ → ℤ) (left right : ρ → ℕ) (control : ρ → α)
    (hind : LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture label (fun a => (t a : ℝ)) (left i) -
        formalDeparture label (fun a => (t a : ℝ)) (right i))
      (fun i => Pi.basisFun ℝ α (control i))))
    (N T Q : ℕ) (hl : ∀ i, left i ≤ N) (hr : ∀ i, right i ≤ N)
    (ht : ∀ a < N, |t a| ≤ (T : ℤ)) (hQ : ∀ p ∈ P, p ≤ Q)
    (a : ℝ) (ha : 0 ≤ a) (hatom : ∀ p, μ.weight p ≤ a) :
    (FiniteLaw.independent (fun _ : α => μ)).probability (fun x =>
      ∀ i, ((x (control i)).val : ℤ) ∣
        ∑ z, columnDifference label t left right i z * ((x z).val : ℤ)) ≤
      Real.sqrt ((a * (1 + (Nat.log 2 (2 * N * T * Q) : ℝ))) ^ Fintype.card ρ) := by
  have hind' : LinearIndependent ℝ (Sum.elim
      (fun i z => (columnDifference label t left right i z : ℝ))
      (fun i => Pi.basisFun ℝ α (control i))) := by
    have heq : (fun i z => (columnDifference label t left right i z : ℝ)) =
        (fun i => formalDeparture label (fun a => (t a : ℝ)) (left i) -
          formalDeparture label (fun a => (t a : ℝ)) (right i)) := by
      funext i
      exact columnDifference_cast label t left right i
    rw [heq]
    exact hind
  apply independent_pairs_prime_rank_bound P hP μ
    (columnDifference label t left right) control hind' (2 * N * T * Q) a ha hatom
  intro pivot hp _ y z i
  exact primeDifference_natAbs_le P Q hQ (columnDifference label t left right)
    pivot hp (2 * N * T) (columnDifference_abs_sum_le_uniform label t left right N T hl hr ht) y z i

/-- The high-rank probability saving only uses the chosen lit occurrences.
The sampled word may vary with all primes in the column, while its integral
step coefficients and selected indices remain fixed. -/
theorem high_rank_column_event_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (μ : FiniteLaw P)
    (label : ℕ → α) (t : ℕ → ℤ) (left right : ρ → ℕ) (control : ρ → α)
    (hind : LinearIndependent ℝ (Sum.elim
      (fun i => formalDeparture label (fun a => (t a : ℝ)) (left i) -
        formalDeparture label (fun a => (t a : ℝ)) (right i))
      (fun i => Pi.basisFun ℝ α (control i))))
    (N T Q : ℕ) (hl : ∀ i, left i ≤ N) (hr : ∀ i, right i ≤ N)
    (ht : ∀ a < N, |t a| ≤ (T : ℤ)) (hQ : ∀ p ∈ P, p ≤ Q)
    (a : ℝ) (ha : 0 ≤ a) (hatom : ∀ p, μ.weight p ≤ a)
    (h : ℕ) (word : (α → P) → List SignedStep) (base : (α → P) → ℤ)
    (E : (α → P) → Prop)
    (hstep : ∀ x, E x → ∀ j < (word x).length,
      wordStepDisplacement h (word x) j = t j * ((x (label j)).val : ℤ))
    (hleft : ∀ x, E x → ∀ i, left i ≤ (word x).length)
    (hright : ∀ x, E x → ∀ i, right i ≤ (word x).length)
    (hlit : ∀ x, E x → ∀ i,
      ((x (control i)).val : ℤ) ∣ base x + wordDisplacement h ((word x).take (left i)))
    (hrit : ∀ x, E x → ∀ i,
      ((x (control i)).val : ℤ) ∣ base x + wordDisplacement h ((word x).take (right i))) :
    (FiniteLaw.independent (fun _ : α => μ)).probability E ≤
      Real.sqrt ((a * (1 + (Nat.log 2 (2 * N * T * Q) : ℝ))) ^ Fintype.card ρ) := by
  classical
  have hE (x : α → P) (hx : E x) : ∀ i, ((x (control i)).val : ℤ) ∣
      ∑ z, columnDifference label t left right i z * ((x z).val : ℤ) :=
    column_congruence_of_departure_divisibilities h (word x) (base x) label t
      (fun z => (x z).val) (hstep x hx) left right control (hleft x hx) (hright x hx)
      (hlit x hx) (hrit x hx)
  apply le_trans ?_ (column_difference_rank_probability P hP μ label t left right control
    hind N T Q hl hr ht hQ a ha hatom)
  unfold FiniteLaw.probability
  apply FiniteLaw.average_mono
  intro x
  by_cases hx : E x
  · simp [hx, hE x hx]
  · simp only [hx, ite_false]
    split_ifs <;> norm_num

end TwoPointCorrelations

end OAI
