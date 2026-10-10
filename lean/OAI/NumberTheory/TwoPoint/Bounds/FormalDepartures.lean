import OAI.NumberTheory.TwoPoint.Bounds.RegularQuotient
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

/-! Formal departures and exact quotient increments of constant runs. -/

namespace TwoPointCorrelations

open Finset

variable {K α V : Type*} [Field K] [Fintype α]
  [AddCommGroup V] [Module K V]

noncomputable def formalDeparture (label : ℕ → α) (coefficient : ℕ → K) (n : ℕ) : α → K :=
  ∑ i ∈ range n, coefficient i • Pi.basisFun K α (label i)

theorem formalDeparture_const_run (label : ℕ → α) (coefficient : ℕ → K)
    (a b : ℕ) (hab : a ≤ b) (z : α) (hz : ∀ i ∈ Ico a b, label i = z) :
    formalDeparture label coefficient b = formalDeparture label coefficient a +
      (∑ i ∈ Ico a b, coefficient i) • Pi.basisFun K α z := by
  unfold formalDeparture
  rw [← sum_range_add_sum_Ico _ hab]
  congr 1
  rw [Finset.sum_smul]
  apply sum_congr rfl
  intro i hi
  rw [hz i hi]

/-- Every regular run moves parallel to its independent quotient direction. -/
theorem quotient_departure_const_run (D : Submodule K (α → K))
    (label : ℕ → α) (coefficient : ℕ → K)
    (a b : ℕ) (hab : a ≤ b) (z : α) (hz : ∀ i ∈ Ico a b, label i = z) :
    D.mkQ (formalDeparture label coefficient b) =
      D.mkQ (formalDeparture label coefficient a) +
        (∑ i ∈ Ico a b, coefficient i) • D.mkQ (Pi.basisFun K α z) := by
  rw [formalDeparture_const_run label coefficient a b hab z hz, map_add, map_smul]

theorem affine_line_successor (anchor direction x y : V)
    (hx : ∃ t : K, x = anchor + t • direction)
    (c : K) (hy : y = x + c • direction) :
    ∃ t : K, y = anchor + t • direction := by
  obtain ⟨t, rfl⟩ := hx
  refine ⟨t + c, ?_⟩
  rw [hy, add_smul, add_assoc]

theorem nonzero_direction_increment {direction x y : V} {c : K}
    (hd : direction ≠ 0) (hc : c ≠ 0) (hy : y = x + c • direction) : x ≠ y := by
  intro heq
  have hz : c • direction = 0 := by
    have h := hy
    rw [← heq] at h
    exact (add_eq_left.mp h.symm)
  exact (smul_ne_zero hc hd) hz

/-- Scalar evaluation turns the formal displacement into the numerical
one in a column. A nonzero numerical run forces a nonzero scalar sum. -/
theorem run_coefficient_ne_zero (coefficient : ℕ → K) (a b : ℕ) (prime : K)
    (hnonzero : (∑ i ∈ Ico a b, coefficient i * prime) ≠ 0) :
    (∑ i ∈ Ico a b, coefficient i) ≠ 0 := by
  intro hz
  apply hnonzero
  rw [← Finset.sum_mul, hz, zero_mul]

/-- A regular run has distinct quotient endpoints as required by the
point--line--point non-reversal check. -/
theorem quotient_run_endpoints_ne (D : Submodule K (α → K))
    (label : ℕ → α) (coefficient : ℕ → K)
    (a b : ℕ) (hab : a ≤ b) (z : α) (hz : ∀ i ∈ Ico a b, label i = z)
    (hdir : D.mkQ (Pi.basisFun K α z) ≠ 0)
    (hc : (∑ i ∈ Ico a b, coefficient i) ≠ 0) :
    D.mkQ (formalDeparture label coefficient a) ≠ D.mkQ (formalDeparture label coefficient b) :=
  nonzero_direction_increment hdir hc
    (quotient_departure_const_run D label coefficient a b hab z hz)

end TwoPointCorrelations

end OAI
