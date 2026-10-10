import OAI.NumberTheory.Ostmann.Construction.PrimeSubsetCellMixture
import OAI.NumberTheory.Ostmann.Arithmetic.BulkPrimeCellMass

namespace OAI

/-! # Exact mass and normalization of the original atomic prime laws -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem primeSubsetLogMeasure_mass (S : Finset ℕ) (Z : ℝ) (hZ : 0 ≤ Z) :
    (primeSubsetLogMeasure S Z).real Set.univ = Z * ∑ p ∈ S, (p : ℝ)⁻¹ := by
  have h := (bulkConstant (σ := Unit) 1).average_primeSubset S Z hZ () (fun _ => 0)
  rw [bulkConstant_average_one] at h
  simp only [bulkConstant, one_mul, ← Complex.ofReal_inv,
    ← Complex.ofReal_sum, ← Complex.ofReal_mul] at h
  exact_mod_cast h

theorem primeSubsetLogMeasure_normalized (S : Finset ℕ)
    (hS : (∑ p ∈ S, (p : ℝ)⁻¹) ≠ 0) :
    (primeSubsetLogMeasure S (∑ p ∈ S, (p : ℝ)⁻¹)⁻¹).real Set.univ = 1 := by
  rw [primeSubsetLogMeasure_mass _ _ (inv_nonneg.mpr (Finset.sum_nonneg fun p _ => by positivity)),
    inv_mul_cancel₀ hS]

theorem bulkPrimeCells_normalized {C : Type*} [Fintype C]
    (q : ℕ) (a : C → ℕ) (u v : C → ℝ)
    (hsep : ∀ c d, c ≠ d → ¬Nat.ModEq q (a c) (a d) ∨ v c ≤ u d ∨ v d ≤ u c)
    (hS : (∑ p ∈ primeCellSupport q a u v, (p : ℝ)⁻¹) ≠ 0) :
    (bulkCellMixture (∑ p ∈ primeCellSupport q a u v, (p : ℝ)⁻¹)⁻¹
      (fun c => primeLogCellMeasure q (a c) (u c) (v c))).real Set.univ = 1 := by
  rw [← primeSubsetLogMeasure_cells q a u v _ hsep]
  exact primeSubsetLogMeasure_normalized _ hS

end Ostmann

end OAI
