import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferencePermutation
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatchingActual

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIndependentFibreMass
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkFibreOriginalReference HistoryDiagonalRemainingRootMatching
open HistoryDiagonalCorrectedOriginalMean HistoryDiagonalSmallOriginalMean
open HistoryGiantOriginalMeanFactorization (Current)
open HistoryBulkIndependentReferenceFrequency CanonicalHistoryLeafBulk
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)
variable (a : SelectedNonbulkSample C l)
variable (e : Equiv.Perm (RemainingIndex
  (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l)))))
variable (he : PreservesRemainingBands _ e)
include he

theorem counterpart_fibreAssignment_bulk_coordinates (u : SelectedBulkSample C l)
    (hc : SmallCounterpartCompatible C.sources _ (smallAssignment C (fibreAssignment C a u)) e) :
    (selectedSourceEquiv C l (counterpartCurrentAssignment C (fibreAssignment C a u) e hc)).2 =
      fun j => u (inducedBulkPermutation (2*(bulkSize k L/2)) k l
        (fullPermutation (l+1) _ e he) (fullPermutation_bulk (l+1) _ e he) j) := by
  funext j
  apply Subtype.ext
  rw [selectedSourceEquiv_bulk_val]
  change bulkSamples C.sources (2*(bulkSize k L/2)) k l
    (counterpartCurrentAssignment C (fibreAssignment C a u) e hc) j.1 j.2 = _
  rw [counterpartCurrentAssignment_bulkSamples C (fibreAssignment C a u) e he hc]
  have h := selectedSourceEquiv_bulk_val C l (fibreAssignment C a u)
    (inducedBulkPermutation (2*(bulkSize k L/2)) k l
      (fullPermutation (l+1) _ e he) (fullPermutation_bulk (l+1) _ e he) j)
  simpa only [fibreAssignment, Equiv.apply_symm_apply, bulkSamples] using h.symm

theorem counterpart_fibreAssignment_nonbulk_coordinates (u₀ u : SelectedBulkSample C l)
    (hc₀ : SmallCounterpartCompatible C.sources _ (smallAssignment C (fibreAssignment C a u₀)) e)
    (hc : SmallCounterpartCompatible C.sources _ (smallAssignment C (fibreAssignment C a u)) e) :
    (selectedSourceEquiv C l (counterpartCurrentAssignment C (fibreAssignment C a u) e hc)).1 =
      (selectedSourceEquiv C l (counterpartCurrentAssignment C (fibreAssignment C a u₀) e hc₀)).1 := by
  funext i
  apply Subtype.ext
  exact counterpartCurrentAssignment_nonbulk_fixed C
    (fibreAssignment C a u₀) (fibreAssignment C a u) e he hc₀ hc
    (fibreAssignment_nonbulk_fixed C a u u₀) i.val i.property

theorem counterpart_fibreAssignment_mass (u₀ u : SelectedBulkSample C l)
    (hc₀ : SmallCounterpartCompatible C.sources _ (smallAssignment C (fibreAssignment C a u₀)) e)
    (hc : SmallCounterpartCompatible C.sources _ (smallAssignment C (fibreAssignment C a u)) e) :
    (assignmentPrior C.sources (SelectedTemplate k L l)).mass
        (counterpartCurrentAssignment C (fibreAssignment C a u) e hc) =
      (selectedNonbulkPrior C l).mass
        (selectedSourceEquiv C l
          (counterpartCurrentAssignment C (fibreAssignment C a u₀) e hc₀)).1 *
        (selectedBulkPrior C l).mass u := by
  rw [selectedSourceEquiv_mass,
    counterpart_fibreAssignment_nonbulk_coordinates C a e he u₀ u hc₀ hc,
    counterpart_fibreAssignment_bulk_coordinates C a e he u hc]
  congr 1
  exact bulkDrawPermutation_mass C
    (inducedBulkPermutation (2*(bulkSize k L/2)) k l
      (fullPermutation (l+1) _ e he) (fullPermutation_bulk (l+1) _ e he)) u

theorem counterpart_fibreAssignment_mass_ne_zero_iff (u₀ u : SelectedBulkSample C l)
    (hc₀ : SmallCounterpartCompatible C.sources _ (smallAssignment C (fibreAssignment C a u₀)) e)
    (hc : SmallCounterpartCompatible C.sources _ (smallAssignment C (fibreAssignment C a u)) e)
    (hu₀ : (selectedBulkPrior C l).mass u₀ ≠ 0)
    (hu : (selectedBulkPrior C l).mass u ≠ 0) :
    (assignmentPrior C.sources (SelectedTemplate k L l)).mass
        (counterpartCurrentAssignment C (fibreAssignment C a u) e hc) ≠ 0 ↔
      (assignmentPrior C.sources (SelectedTemplate k L l)).mass
        (counterpartCurrentAssignment C (fibreAssignment C a u₀) e hc₀) ≠ 0 := by
  rw [counterpart_fibreAssignment_mass C a e he u₀ u hc₀ hc,
    counterpart_fibreAssignment_mass C a e he u₀ u₀ hc₀ hc₀]
  simp only [ne_eq, mul_eq_zero, hu, hu₀, or_false]

theorem counterpart_fibreAssignment_mass_eq_zero_iff (u₀ u : SelectedBulkSample C l)
    (hc₀ : SmallCounterpartCompatible C.sources _ (smallAssignment C (fibreAssignment C a u₀)) e)
    (hc : SmallCounterpartCompatible C.sources _ (smallAssignment C (fibreAssignment C a u)) e)
    (hu₀ : (selectedBulkPrior C l).mass u₀ ≠ 0)
    (hu : (selectedBulkPrior C l).mass u ≠ 0) :
    (assignmentPrior C.sources (SelectedTemplate k L l)).mass
        (counterpartCurrentAssignment C (fibreAssignment C a u) e hc) = 0 ↔
      (assignmentPrior C.sources (SelectedTemplate k L l)).mass
        (counterpartCurrentAssignment C (fibreAssignment C a u₀) e hc₀) = 0 := by
  rw [counterpart_fibreAssignment_mass C a e he u₀ u hc₀ hc,
    counterpart_fibreAssignment_mass C a e he u₀ u₀ hc₀ hc₀]
  simp only [mul_eq_zero, hu, hu₀, or_false]

end Ostmann.Arithmetic.HistoryBulkIndependentFibreMass

end

end OAI
