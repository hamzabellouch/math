import OAI.NumberTheory.Ostmann.Construction.PrimeSubsetLogMeasure
import OAI.NumberTheory.Ostmann.Arithmetic.BulkCellMixtures

namespace OAI

/-! # Exact cell reconstruction of the original harmonic prime law -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem primeSubsetLogMeasure_cells {C : Type*} [Fintype C]
    (q : ℕ) (a : C → ℕ) (u v : C → ℝ) (Z : ℝ)
    (hsep : ∀ c d, c ≠ d → ¬Nat.ModEq q (a c) (a d) ∨ v c ≤ u d ∨ v d ≤ u c) :
    primeSubsetLogMeasure (primeCellSupport q a u v) Z =
      bulkCellMixture Z (fun c => primeLogCellMeasure q (a c) (u c) (v c)) := by
  unfold primeSubsetLogMeasure primeCellSupport bulkCellMixture primeLogCellMeasure
  congr 1
  apply Finset.sum_biUnion
  intro c _ d _ hcd
  exact primeLogCellSet_disjoint q (a c) (a d) (u c) (v c) (u d) (v d) (hsep c d hcd)

/-- The original normalized subset prior equals the mixture of its complete
log/residue cells, with the same single normalization constant. -/
theorem BulkIntegrand.average_originalPrimeCells {σ C : Type*} [Fintype σ] [Fintype C]
    (f : BulkIntegrand σ) (P : Finset ℕ) (q : ℕ) (a : C → ℕ) (u v : C → ℝ)
    (hSP : primeCellSupport q a u v ⊆ P)
    (hsep : ∀ c d, c ≠ d → ¬Nat.ModEq q (a c) (a d) ∨ v c ≤ u d ∨ v d ≤ u c)
    (i : σ) (x : σ → ℝ) :
    let S := primeCellSupport q a u v
    f.average (bulkCellMixture (∑ p ∈ S, (p : ℝ)⁻¹)⁻¹
      (fun c => primeLogCellMeasure q (a c) (u c) (v c))) i x =
      ∑ p : P, (primeSubsetPrior P S p : ℂ) * f (Function.update x i (Real.log (p : ℕ))) := by
  dsimp only
  have h := f.average_originalPrimePrior P (primeCellSupport q a u v) hSP i x
  simpa only [primeSubsetLogMeasure_cells q a u v _ hsep] using h

end Ostmann

end OAI
