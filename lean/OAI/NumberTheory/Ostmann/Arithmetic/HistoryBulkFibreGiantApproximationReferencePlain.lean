import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReferenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatchingAssigned
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesPermutation

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReference
open Construction Conclusion HistoryGiantReferenceMean HistoryBulkSourceDisintegration
open HistoryBulkFibreOriginalReference HistoryGiantOriginalMeanFactorization
open HistoryPairBulkCoordinates HistoryPairBulkTransport HistoryDiagonalRemainingRootMatching
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)
variable (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
variable (a : SelectedNonbulkSample C l)

theorem plain_reference_masses (y : SelectedBulkSample C l)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hy : 0 < (selectedBulkPrior C l).mass y) :
    (assignmentPrior C.sources (SelectedTemplate k L l)).mass (fibreAssignment C a y) ≠ 0 ∧
    (assignmentPrior C.sources (SelectedTemplate k L l)).mass
      (permuteAssignment C σ (fibreAssignment C a y)) ≠ 0 := by
  have hx := ne_of_gt (fibreAssignment_mass_pos C a y ha hy)
  refine ⟨hx,?_⟩
  simpa only [permuteAssignment,sourceAssignmentPermutation_mass] using hx

theorem plain_prime_reference_data (y : SelectedBulkSample C l) (r : PrimeDraw C.giant)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hy : 0 < (selectedBulkPrior C l).mass y) (hr : 0 < primeWeight C.giant r) :
    IntegerReferenceData C (fibreAssignment C a y)
      (permuteAssignment C σ (fibreAssignment C a y)) (primeP C.giant r) (primeQ C.giant r) := by
  have hm := plain_reference_masses C σ a y ha hy
  have hp := prime_draw_cells C r hr
  exact ⟨hm.1,hm.2,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2⟩

theorem plain_mixed_reference_data (y : SelectedBulkSample C l)
    (r : MixedDraw C.giantCenter C.giant)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hy : 0 < (selectedBulkPrior C l).mass y)
    (hr : 0 < mixedWeight C.giantCenter C.giant r) :
    IntegerReferenceData C (fibreAssignment C a y)
      (permuteAssignment C σ (fibreAssignment C a y))
      (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r) := by
  have hm := plain_reference_masses C σ a y ha hy
  have hp := mixed_draw_cells C r hr
  exact ⟨hm.1,hm.2,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2⟩

def plain_reference_matching (s t : ℤ) (c e : Choices (l:=l) C)
    (y : SelectedBulkSample C l) (P Q : ℤ) :
    RootMatching (history C (fibreAssignment C a y) s P Q c)
      (history C (permuteAssignment C σ (fibreAssignment C a y)) t P Q e) := by
  exact assignedRootMatching C.sources (Seed (k:=k) (L:=L))
    (frequencyBound Bs BD Bz k L) l s t P.toNat Q.toNat P.toNat Q.toNat
    (fibreAssignment C a y) (permuteAssignment C σ (fibreAssignment C a y)) c e
    (selectedLeafPermutation C l σ)
    (sourceAssignmentPermutation_val C.sources _ _ _ _)
    (leafBulkPermutation_bulk_iff (2*(bulkSize k L/2)) k l σ)

end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReference

end

end OAI
