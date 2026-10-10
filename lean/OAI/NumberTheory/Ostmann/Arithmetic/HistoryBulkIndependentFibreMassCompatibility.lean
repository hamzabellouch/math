import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatchingBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatchingPositionsValues

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIndependentFibreMass
open Construction Conclusion
open HistoryDiagonalCorrectedOriginalMean HistoryDiagonalRemainingRootMatching
open HistoryDiagonalSmallOriginalMean HistoryGiantOriginalMeanFactorization
open HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference

theorem smallCounterpartCoordinate_permutation (sources : SourceFamily) (T : List SourceSlot)
    (x : SourceAssignment sources T) (e : Equiv.Perm (RemainingIndex T))
    (he : PreservesRemainingBands T e) (i : Fin T.length) :
    smallCounterpartCoordinate sources T x e i = (x (smallPermutation e he i)).val := by
  unfold smallCounterpartCoordinate
  rw [←smallPermutation_succ e he i]
  rfl

theorem smallCounterpartCompatible_iff_of_nonbulk
    (sources : SourceFamily) (T : List SourceSlot) (bulk : PrimeSource)
    (hbulk : ∀i : Fin T.length, (T.get i).role = .bulk → sources (T.get i).origin = bulk)
    (x₀ x : SourceAssignment sources T) (e : Equiv.Perm (RemainingIndex T))
    (he : PreservesRemainingBands T e)
    (hfixed : ∀i : Fin T.length, (T.get i).role ≠ .bulk → (x i).val = (x₀ i).val) :
    SmallCounterpartCompatible sources T x e ↔ SmallCounterpartCompatible sources T x₀ e := by
  have step (a b : SourceAssignment sources T)
      (hab : ∀i : Fin T.length, (T.get i).role ≠ .bulk → (a i).val = (b i).val)
      (ha : SmallCounterpartCompatible sources T a e) :
      SmallCounterpartCompatible sources T b e := by
    intro i
    rw [smallCounterpartCoordinate_permutation sources T b e he i]
    by_cases hi : (T.get i).role = .bulk
    · have hj : (T.get (smallPermutation e he i)).role = .bulk :=
        (smallPermutation_role e he i).trans hi
      have hsource : sources (T.get (smallPermutation e he i)).origin = sources (T.get i).origin :=
        (hbulk _ hj).trans (hbulk _ hi).symm
      have hp := (b (smallPermutation e he i)).property
      change (b (smallPermutation e he i)).val ∈ (sources (T.get (smallPermutation e he i)).origin).candidates at hp
      rw [hsource] at hp
      exact hp
    · have hj : (T.get (smallPermutation e he i)).role ≠ .bulk := by
        simpa only [smallPermutation_role e he i] using hi
      have hmem := ha i
      rw [smallCounterpartCoordinate_permutation sources T a e he i, hab _ hj] at hmem
      exact hmem
  exact ⟨step x x₀ hfixed, step x₀ x (fun i hi => (hfixed i hi).symm)⟩

theorem restoringAssignment_nonbulk_fixed (sources : SourceFamily) (j : ℕ)
    (T : List SourceSlot) (x₀ x : SourceAssignment sources T)
    (hfixed : ∀i : Fin T.length, (T.get i).role ≠ .bulk → (x i).val = (x₀ i).val)
    (r : Fin (Template.remainder j T).length)
    (hr : ((Template.remainder j T).get r).role ≠ .bulk) :
    ((restoringAssignmentEquiv sources j T x).2 r).val =
      ((restoringAssignmentEquiv sources j T x₀).2 r).val := by
  let i := (splitPositions j T).symm (.inr r)
  have hi : splitPositions j T i = .inr r := (splitPositions j T).apply_symm_apply _
  have hs := splitPositions_slot_inr j T i r hi
  exact (restoringAssignment_value_inr sources j T x i r hi).symm.trans
    ((hfixed i (by simpa only [hs] using hr)).trans
      (restoringAssignment_value_inr sources j T x₀ i r hi))

variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem selected_remainder_bulk_source (C : InitialSourceChoice d Bs BD Bz k L E)
    (r : Fin (Template.remainder (l+1) (SelectedTemplate k L l)).length)
    (hr : ((Template.remainder (l+1) (SelectedTemplate k L l)).get r).role = .bulk) :
    C.sources ((Template.remainder (l+1) (SelectedTemplate k L l)).get r).origin = C.bulk := by
  let i := (splitPositions (l+1) (SelectedTemplate k L l)).symm (.inr r)
  have hi : splitPositions (l+1) (SelectedTemplate k L l) i = .inr r :=
    (splitPositions (l+1) (SelectedTemplate k L l)).apply_symm_apply _
  have hs := splitPositions_slot_inr (l+1) (SelectedTemplate k L l) i r hi
  rw [←hs]
  apply selected_bulk_source C l ⟨i, ?_⟩
  change ((SelectedTemplate k L l).get i).role = .bulk
  rw [hs]
  exact hr

theorem fibre_smallCounterpartCompatible_iff
    (C : InitialSourceChoice d Bs BD Bz k L E)
    (a : SelectedNonbulkSample C l) (u₀ u : SelectedBulkSample C l)
    (e : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (SelectedTemplate k L l))))
    (he : PreservesRemainingBands _ e) :
    SmallCounterpartCompatible C.sources _ (smallAssignment C (fibreAssignment C a u)) e ↔
      SmallCounterpartCompatible C.sources _ (smallAssignment C (fibreAssignment C a u₀)) e := by
  apply smallCounterpartCompatible_iff_of_nonbulk C.sources _ C.bulk
    (selected_remainder_bulk_source C) _ _ e he
  intro r hr
  exact restoringAssignment_nonbulk_fixed C.sources (l+1) (SelectedTemplate k L l)
    (fibreAssignment C a u₀) (fibreAssignment C a u)
    (fibreAssignment_nonbulk_fixed C a u u₀) r hr

end Ostmann.Arithmetic.HistoryBulkIndependentFibreMass

end

end OAI
