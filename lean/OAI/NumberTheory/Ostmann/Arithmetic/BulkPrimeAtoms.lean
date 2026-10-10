import OAI.NumberTheory.Ostmann.Arithmetic.BulkAtomicProduct
import OAI.NumberTheory.Ostmann.Construction.PrimeLogCellMeasure

namespace OAI

/-! # Expanding the actual joint prime cells on the common sample space -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

noncomputable def primeCellAtomWeight (q a : ℕ) (u v : ℝ) (p : ℕ) : ℝ :=
  if p ∈ primeLogCellSet q a u v then (p : ℝ)⁻¹ else 0

theorem primeCellAtomWeight_nonneg (q a : ℕ) (u v : ℝ) (p : ℕ) :
    0 ≤ primeCellAtomWeight q a u v p := by
  unfold primeCellAtomWeight
  split_ifs <;> positivity

theorem primeLogCellMeasure_ambient (P : Finset ℕ) (q a : ℕ) (u v : ℝ)
    (hP : primeLogCellSet q a u v ⊆ P) :
    primeLogCellMeasure q a u v =
      ∑ p : P, ENNReal.ofReal (primeCellAtomWeight q a u v p) • Measure.dirac (Real.log (p : ℕ)) := by
  have hs : P.filter (fun p => p ∈ primeLogCellSet q a u v) = primeLogCellSet q a u v := by
    ext p
    exact ⟨fun h => (Finset.mem_filter.mp h).2,
      fun h => Finset.mem_filter.mpr ⟨hP h, h⟩⟩
  rw [Finset.sum_coe_sort P (fun p => ENNReal.ofReal (primeCellAtomWeight q a u v p) •
    Measure.dirac (Real.log p))]
  unfold primeLogCellMeasure
  rw [← hs, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p ∈ primeLogCellSet q a u v <;> simp [primeCellAtomWeight, hp]

/-- This equality retains each original atom and all residue restrictions;
there is no replacement by an independent uniform prime sample. -/
theorem BulkIntegrand.integral_prime_cell_product {J : Type*} [Fintype J]
    (f : BulkIntegrand J) (P : Finset ℕ) (q a : J → ℕ) (u v : J → ℝ)
    (hP : ∀ j, primeLogCellSet (q j) (a j) (u j) (v j) ⊆ P) :
    (∫ y, f y ∂Measure.pi (fun j => primeLogCellMeasure (q j) (a j) (u j) (v j))) =
      ∑ x : J → P, ((∏ j, primeCellAtomWeight (q j) (a j) (u j) (v j) (x j) : ℝ) : ℂ) *
        f (fun j => Real.log (x j : ℕ)) := by
  simp_rw [primeLogCellMeasure_ambient P _ _ _ _ (hP _)]
  exact f.integral_atomic_product _ _ (fun j x => primeCellAtomWeight_nonneg _ _ _ _ x)

end Ostmann

end OAI
