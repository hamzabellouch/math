import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatchingAssigned
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatchingBulk
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatchingValues

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatching
open Construction Conclusion HistoryDiagonalCorrectedOriginalMean
open HistoryDiagonalSmallOriginalMean HistoryGiantOriginalMeanFactorization
open HistoryPairBulkTransport HistoryPairBulkCoordinates
open HistoryBulkIndependentReferenceFrequency CanonicalHistoryLeafBulk
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem counterpartCurrentAssignment_value (C : InitialSourceChoice d Bs BD Bz k L E)
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (e : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l)))))
    (he : PreservesRemainingBands _ e)
    (hc : SmallCounterpartCompatible C.sources _ (smallAssignment C x) e)
    (i : Fin (Current (k:=k) (L:=L) (l:=l)).length) :
    (counterpartCurrentAssignment C x e hc i).val =
      (x (fullPermutation (l+1) _ e he i)).val :=
  restoredCounterpart_value C.sources (l+1) _ x e he hc i

theorem counterpartCurrentAssignment_nonbulk_fixed
    (C : InitialSourceChoice d Bs BD Bz k L E)
    (x₀ x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (e : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l)))))
    (he : PreservesRemainingBands _ e)
    (hc₀ : SmallCounterpartCompatible C.sources _ (smallAssignment C x₀) e)
    (hc : SmallCounterpartCompatible C.sources _ (smallAssignment C x) e)
    (hfixed : ∀i, ((Current (k:=k) (L:=L) (l:=l)).get i).role ≠ .bulk →
      (x i).val = (x₀ i).val) :
    ∀i, ((Current (k:=k) (L:=L) (l:=l)).get i).role ≠ .bulk →
      (counterpartCurrentAssignment C x e hc i).val =
        (counterpartCurrentAssignment C x₀ e hc₀ i).val :=
  right_nonbulk_fixed (fullPermutation (l+1) _ e he)
    (fullPermutation_role (l+1) _ e he) x₀ _ x _
    (counterpartCurrentAssignment_value C x₀ e he hc₀)
    (counterpartCurrentAssignment_value C x e he hc) hfixed

def counterpartRootMatching (C : InitialSourceChoice d Bs BD Bz k L E)
    (V : ℕ→ℕ) (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (e : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l)))))
    (he : PreservesRemainingBands _ e)
    (hc : SmallCounterpartCompatible C.sources _ (smallAssignment C x) e)
    (s t : ℤ) (gp gm qp qm : ℕ)
    (c f : HistoryChoices C.sources (Seed (k:=k) (L:=L)) V l) :
    RootMatching (assignedHistory C.sources (Seed (k:=k) (L:=L)) V l s gp gm x c)
      (assignedHistory C.sources (Seed (k:=k) (L:=L)) V l t qp qm
        (counterpartCurrentAssignment C x e hc) f) :=
  assignedRootMatching C.sources _ V l s t gp gm qp qm x _ c f
    (fullPermutation (l+1) _ e he)
    (counterpartCurrentAssignment_value C x e he hc)
    (fullPermutation_bulk (l+1) _ e he)

theorem counterpartCurrentAssignment_bulkSamples
    (C : InitialSourceChoice d Bs BD Bz k L E)
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (e : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l)))))
    (he : PreservesRemainingBands _ e)
    (hc : SmallCounterpartCompatible C.sources _ (smallAssignment C x) e)
    (u : Fin (2^l) × Fin (2*(bulkSize k L/2))) :
    bulkSamples C.sources (2*(bulkSize k L/2)) k l (counterpartCurrentAssignment C x e hc) u.1 u.2 =
      bulkSamples C.sources (2*(bulkSize k L/2)) k l x
        (inducedBulkPermutation (2*(bulkSize k L/2)) k l
          (fullPermutation (l+1) _ e he) (fullPermutation_bulk (l+1) _ e he) u).1
        (inducedBulkPermutation (2*(bulkSize k L/2)) k l
          (fullPermutation (l+1) _ e he) (fullPermutation_bulk (l+1) _ e he) u).2 :=
  bulkSamples_fullPermutation C.sources (2*(bulkSize k L/2)) k l
    (fullPermutation (l+1) _ e he) (fullPermutation_bulk (l+1) _ e he) x _
    (counterpartCurrentAssignment_value C x e he hc) u

theorem counterpartCurrentAssignment_remainingBulkSamples
    (C : InitialSourceChoice d Bs BD Bz k L E)
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (e : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (Current (k:=k) (L:=L) (l:=l)))))
    (he : PreservesRemainingBands _ e)
    (hc : SmallCounterpartCompatible C.sources _ (smallAssignment C x) e)
    (u : Fin (2^l) × Fin (2*(bulkSize k L/2))) :
    bulkSamples C.sources (2*(bulkSize k L/2)) k l (counterpartCurrentAssignment C x e hc) u.1 u.2 =
      bulkSamples C.sources (2*(bulkSize k L/2)) k l x
        (DiagonalPermutationCount.remainingBulkPermutation (2*(bulkSize k L/2)) k l e u).1
        (DiagonalPermutationCount.remainingBulkPermutation (2*(bulkSize k L/2)) k l e u).2 := by
  simpa only [inducedBulkPermutation_fullPermutation] using
    counterpartCurrentAssignment_bulkSamples C x e he hc u

end Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatching

end

end OAI
