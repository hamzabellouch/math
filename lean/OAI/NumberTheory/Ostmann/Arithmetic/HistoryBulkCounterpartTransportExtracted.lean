import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferencePermutation
import OAI.NumberTheory.Ostmann.Construction.AssignmentReinsert
import OAI.NumberTheory.Ostmann.Construction.CanonicalEnumeration
import OAI.NumberTheory.Ostmann.Construction.DiagonalRegroupingCounterpart

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkCounterpartTransport
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference

theorem assignedSlots_compensation_filter_eq (sources : SourceFamily) (T : List SourceSlot)
    (j : ℕ) (x x₀ : SourceAssignment sources T)
    (hfixed : ∀ i : Fin T.length, (T.get i).role ≠ .bulk → (x i).val = (x₀ i).val) :
    (assignedSlots sources T x).filter (fun q => decide (q.role = .compensation j)) =
      (assignedSlots sources T x₀).filter (fun q => decide (q.role = .compensation j)) := by
  simp only [assignedSlots,Template.sample,List.ofFn_eq_map,List.filter_map,Function.comp_def]
  apply List.map_congr_left
  intro i hi
  have hrole : (T.get i).role = .compensation j := by
    simpa only [List.get_eq_getElem,Fin.getElem_fin,decide_eq_true_eq] using (List.mem_filter.mp hi).2
  have hn : (T.get i).role ≠ .bulk := by rw [hrole]; simp
  have hv := hfixed i hn
  congr 1

theorem restoringAssignment_first_slots (sources : SourceFamily) (T : List SourceSlot)
    (j : ℕ) (x : SourceAssignment sources T) :
    (assignedSlots sources T x).filter (fun q => decide (q.role = .compensation j)) =
      assignedSlots sources (Template.extracted j T) (restoringAssignmentEquiv sources j T x).1 := by
  rw [assignedSlots_split_reinsert]
  exact (reinsert_role_filters j T _ _ (Template.assignedSlots_matches _ _ _)
    (Template.assignedSlots_matches _ _ _)).1

theorem restoringAssignment_first_eq_of_nonbulk_fixed (sources : SourceFamily) (T : List SourceSlot)
    (j : ℕ) (x x₀ : SourceAssignment sources T)
    (hfixed : ∀ i : Fin T.length, (T.get i).role ≠ .bulk → (x i).val = (x₀ i).val) :
    (restoringAssignmentEquiv sources j T x).1 = (restoringAssignmentEquiv sources j T x₀).1 := by
  apply assignedSlots_injective sources (Template.extracted j T)
  rw [←restoringAssignment_first_slots,←restoringAssignment_first_slots]
  exact assignedSlots_compensation_filter_eq sources T j x x₀ hfixed

theorem restoringAssignment_first_permutation (sources : SourceFamily) (T : List SourceSlot)
    (j : ℕ) (σ : Equiv.Perm (Fin T.length))
    (hσ : ∀ i, sources (T.get (σ i)).origin = sources (T.get i).origin)
    (hnonbulk : ∀ i : Fin T.length, (T.get i).role ≠ .bulk → σ i = i)
    (x : SourceAssignment sources T) :
    (restoringAssignmentEquiv sources j T (sourceAssignmentPermutation sources T σ hσ x)).1 =
      (restoringAssignmentEquiv sources j T x).1 := by
  apply restoringAssignment_first_eq_of_nonbulk_fixed
  intro i hi
  rw [sourceAssignmentPermutation_val,hnonbulk i hi]

theorem restoringAssignment_first_permuted_redraw (sources : SourceFamily) (T : List SourceSlot)
    (j : ℕ) (σ : Equiv.Perm (Fin T.length))
    (hσ : ∀ i, sources (T.get (σ i)).origin = sources (T.get i).origin)
    (hnonbulk : ∀ i : Fin T.length, (T.get i).role ≠ .bulk → σ i = i)
    (x x₀ : SourceAssignment sources T)
    (hfixed : ∀ i : Fin T.length, (T.get i).role ≠ .bulk → (x i).val = (x₀ i).val) :
    (restoringAssignmentEquiv sources j T (sourceAssignmentPermutation sources T σ hσ x)).1 =
      (restoringAssignmentEquiv sources j T (sourceAssignmentPermutation sources T σ hσ x₀)).1 :=
  (restoringAssignment_first_permutation sources T j σ hσ hnonbulk x).trans
    ((restoringAssignment_first_eq_of_nonbulk_fixed sources T j x x₀ hfixed).trans
      (restoringAssignment_first_permutation sources T j σ hσ hnonbulk x₀).symm)

variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

theorem restoringAssignment_first_fibreAssignment (j : ℕ)
    (a : SelectedNonbulkSample C l) (y y₀ : SelectedBulkSample C l) :
    (restoringAssignmentEquiv C.sources j (SelectedTemplate k L l) (fibreAssignment C a y)).1 =
      (restoringAssignmentEquiv C.sources j (SelectedTemplate k L l) (fibreAssignment C a y₀)).1 :=
  restoringAssignment_first_eq_of_nonbulk_fixed C.sources _ j _ _
    (fibreAssignment_nonbulk_fixed C a y y₀)

theorem restoringAssignment_first_permuted_fibreAssignment (j : ℕ)
    (σ τ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (a : SelectedNonbulkSample C l) (y y₀ : SelectedBulkSample C l) :
    (restoringAssignmentEquiv C.sources j (SelectedTemplate k L l)
      (permuteAssignment C σ (fibreAssignment C a y))).1 =
    (restoringAssignmentEquiv C.sources j (SelectedTemplate k L l)
      (permuteAssignment C τ (fibreAssignment C a y₀))).1 := by
  rw [permute_fibreAssignment,permute_fibreAssignment]
  exact restoringAssignment_first_fibreAssignment C j a _ _

end Ostmann.Arithmetic.HistoryBulkCounterpartTransport

end

end OAI
