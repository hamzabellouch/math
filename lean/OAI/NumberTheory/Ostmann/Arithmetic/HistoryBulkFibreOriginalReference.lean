import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceSelection

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreOriginalReference
open Construction Conclusion HistoryGiantReferenceMean HistoryBulkSourceDisintegration
open HistoryGiantOriginalMeanFactorization (Choices)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
variable (a : SelectedNonbulkSample C l) (s t : ℤ) (c e : Choices (l:=l) C)

theorem primeFibreMean_eq_zero_or_reference :
    primeFibreMean C outside σ a s t c e = 0 ∨
    ∃y,∃r : PrimeDraw C.giant,
      0 < (selectedBulkPrior C l).mass y ∧ 0 < primeWeight C.giant r ∧
      fibreTerm C outside σ a s t c e y (primeP C.giant r) (primeQ C.giant r) ≠ 0 ∧
      FibreSupported C outside σ a s t c e y (primeP C.giant r) (primeQ C.giant r) := by
  rw [primeFibreMean_eq_weighted]
  exact weightedFibreMean_eq_zero_or_reference C outside σ a s t c e
    (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) (primeWeight_nonneg C.giant)

theorem mixedFibreMean_eq_zero_or_reference :
    mixedFibreMean C outside σ a s t c e = 0 ∨
    ∃y,∃r : MixedDraw C.giantCenter C.giant,
      0 < (selectedBulkPrior C l).mass y ∧ 0 < mixedWeight C.giantCenter C.giant r ∧
      fibreTerm C outside σ a s t c e y
        (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r) ≠ 0 ∧
      FibreSupported C outside σ a s t c e y
        (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r) := by
  rw [mixedFibreMean_eq_weighted]
  exact weightedFibreMean_eq_zero_or_reference C outside σ a s t c e
    (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant)
    (mixedQ C.giantCenter C.giant) (mixedWeight_nonneg C.giantCenter C.giant)

theorem fibreAssignment_mass_pos (y : SelectedBulkSample C l)
    (ha : 0 < (selectedNonbulkPrior C l).mass a) (hy : 0 < (selectedBulkPrior C l).mass y) :
    0 < (assignmentPrior C.sources (SelectedTemplate k L l)).mass (fibreAssignment C a y) := by
  rw [fibreAssignment_mass]
  exact mul_pos ha hy

end Ostmann.Arithmetic.HistoryBulkFibreOriginalReference

end

end OAI
