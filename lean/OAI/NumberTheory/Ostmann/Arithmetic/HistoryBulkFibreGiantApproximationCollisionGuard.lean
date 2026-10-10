import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentFibreReferenceDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalCollisionErrorGuard
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatchingActual

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
open Construction Conclusion HistoryPairBulkTransport HistorySignedResidueFactorization
open HistoryBulkReferencePeriodicMeanSource HistoryBulkSourceDisintegration
open HistoryBulkFibreOriginalReference HistoryBulkPrincipalCollisionError
open HistoryBulkIndependentFibreReference HistoryDiagonalRemainingRootMatching

theorem assignedSlots_values_perm (sources : SourceFamily) (T : List SourceSlot)
    (x y : SourceAssignment sources T) (π : Equiv.Perm (Fin T.length))
    (hnew : ∀ i, (y i).val = (x (π i)).val) :
    ((assignedSlots sources T y).map SmallSlot.value).Perm
      ((assignedSlots sources T x).map SmallSlot.value) := by
  simpa only [assignedSlots, Template.sample, List.map_ofFn, Function.comp_def, hnew] using
    π.ofFn_comp_perm (fun i => (x i).val)

theorem assignedSlots_pairwise_iff (sources : SourceFamily) (T : List SourceSlot)
    (outside : List ℕ) (x y : SourceAssignment sources T)
    (π : Equiv.Perm (Fin T.length)) (hnew : ∀ i, (y i).val = (x (π i)).val) :
    ((assignedSlots sources T y).map SmallSlot.value ++ outside).Pairwise Nat.Coprime ↔
      ((assignedSlots sources T x).map SmallSlot.value ++ outside).Pairwise Nat.Coprime :=
  ((assignedSlots_values_perm sources T x y π hnew).append_right outside).pairwise_iff
    Nat.Coprime.symm

variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth l : ℕ} {E : Finset ℕ}
variable {C : InitialSourceChoice d Bs BD Bz depth L E} {outside : List ℕ}

theorem Frame.staticPairMask_eq_leftGuard (r : Frame (l:=l) C outside)
    (x y : Frame.Source (C:=C) (l:=l))
    (π : Equiv.Perm (Fin (SelectedTemplate depth L l).length))
    (hnew : ∀ i, (y i).val = (x (π i)).val) :
    staticPairMask (r.newLeft x) (r.newRight y) outside =
      guardIndicator (((assignedSlots C.sources (SelectedTemplate depth L l) x).map
        SmallSlot.value ++ outside).Pairwise Nat.Coprime) := by
  have hp := assignedSlots_pairwise_iff C.sources (SelectedTemplate depth L l)
    outside x y π hnew
  simp only [staticPairMask, Frame.newLeft, Frame.newRight, assignedHistory,
    decodeHistory_root, assignedRoot, hp, and_self]

theorem Frame.staticPairMask_eq_fibreSmallOutsideGuard (r : Frame (l:=l) C outside)
    (a : SelectedNonbulkSample C l) (u : SelectedBulkSample C l)
    (y : Frame.Source (C:=C) (l:=l))
    (π : Equiv.Perm (Fin (SelectedTemplate depth L l).length))
    (hnew : ∀ i, (y i).val = (fibreAssignment C a u (π i)).val) :
    staticPairMask (r.newLeft (fibreAssignment C a u)) (r.newRight y) outside =
      guardIndicator (fibreSmallOutsideGuard C outside a u) :=
  r.staticPairMask_eq_leftGuard (fibreAssignment C a u) y π hnew

theorem Frame.plain_staticPairMask_eq_fibreSmallOutsideGuard
    (r : Frame (l:=l) C outside)
    (σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l)))
    (a : SelectedNonbulkSample C l) (u : SelectedBulkSample C l) :
    staticPairMask (r.newLeft (fibreAssignment C a u))
      (r.newRight (permuteAssignment C σ (fibreAssignment C a u))) outside =
      guardIndicator (fibreSmallOutsideGuard C outside a u) := by
  apply r.staticPairMask_eq_fibreSmallOutsideGuard a u _ (selectedLeafPermutation C l σ)
  intro i
  exact sourceAssignmentPermutation_val C.sources _ _ _ _ i

theorem Frame.corrected_staticPairMask_eq_fibreSmallOutsideGuard
    (r : Frame (l:=l) C outside) (a : SelectedNonbulkSample C l)
    (e : RemainingPermutation (k:=depth) (L:=L) (l:=l))
    (he : PreservesRemainingBands _ e) (u : SelectedBulkSample C l)
    (hc : Compatible C a e u) :
    staticPairMask (r.newLeft (fibreAssignment C a u))
      (r.newRight (rightAssignment C a e u hc)) outside =
      guardIndicator (fibreSmallOutsideGuard C outside a u) := by
  apply r.staticPairMask_eq_fibreSmallOutsideGuard a u _ (fullPermutation (l+1) _ e he)
  exact counterpartCurrentAssignment_value C (fibreAssignment C a u) e he hc

end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

end

end OAI
