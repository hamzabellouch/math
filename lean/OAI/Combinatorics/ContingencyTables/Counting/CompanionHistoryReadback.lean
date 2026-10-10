import OAI.Combinatorics.ContingencyTables.Counting.CompanionStoredRepresentation
import OAI.Combinatorics.ContingencyTables.Counting.CompanionOuterPhaseSemantics
import OAI.Combinatorics.ContingencyTables.Counting.CompanionCanonicalHistoryLaw

namespace OAI

/-! # Reading a represented physical history as source matrix data -/
namespace ContingencyTables.CompanionHistoryReadback
open MatchingFPRAS CompanionMultiplierMatrixProgram CompanionStoredRepresentation
open CompanionFactorialApplication CompanionComputedInitial CompanionEvaluatedWeightProgram
open GridBoundary
open scoped Classical
noncomputable section

abbrev Stored := CompanionPhaseFinishProgram.Stored

def lookup (initial : Stored) (history : List Stored) : ℕ→Stored
  | 0 => initial
  | i+1 => history.getD i initial

def matrixAt (p : ℕ) (initial : Stored) (history : List Stored) (i : ℕ) :
    Fin p→Fin p→TreeFraction.Fraction := entries p (lookup initial history i).1

def estimateAt (initial : Stored) (history : List Stored) (i : ℕ) : TreeFraction.Fraction :=
  (lookup initial history i).2

lemma getD_rep {p : ℕ} (history : List Stored) (initial : Stored)
    (hi : StoredRep p initial) (hh : ∀ s∈history,StoredRep p s) (i : ℕ) :
    StoredRep p (history.getD i initial) := by
  by_cases h : i < history.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hh _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact hi

lemma lookup_rep {p : ℕ} (initial : Stored) (history : List Stored)
    (hi : StoredRep p initial) (hh : ∀ s∈history,StoredRep p s) (i : ℕ) :
    StoredRep p (lookup initial history i) := by
  cases i with
  | zero => exact hi
  | succ i => exact getD_rep history initial hi hh i

theorem lookup_readback {p : ℕ} (initial : Stored) (history : List Stored)
    (hi : StoredRep p initial) (hh : ∀ s∈history,StoredRep p s) (i : ℕ) :
    (matrixCode (matrixAt p initial history i),estimateAt initial history i)=
      lookup initial history i :=
  stored_readback (lookup_rep initial history hi hh i)

theorem initial_readback {p : ℕ} (initial : Stored) (history : List Stored)
    (hi : StoredRep p initial) :
    (matrixCode (matrixAt p initial history 0),estimateAt initial history 0)=initial :=
  stored_readback hi

theorem history_readback {p : ℕ} (initial : Stored) (history : List Stored)
    (hi : StoredRep p initial) (hh : ∀ s∈history,StoredRep p s) :
    List.ofFn (fun i : Fin history.length =>
      (matrixCode (matrixAt p initial history (i.val+1)),estimateAt initial history (i.val+1)))=
      history := by
  apply List.ext_getElem
  · exact List.length_ofFn
  · intro i _ hj
    simp only [List.getElem_ofFn]
    have h := lookup_readback initial history hi hh (i+1)
    change (matrixCode (matrixAt p initial history (i+1)),estimateAt initial history (i+1))=
      history.getD i initial at h
    rw [List.getD_eq_getElem _ _ hj] at h
    exact h

def viewLookup {Z : Type} (initial : Z) (history : List Z) : ℕ→Z
  | 0 => initial
  | i+1 => history.getD i initial

theorem view_lookup (p : ℕ) (initial : Stored) (history : List Stored) (i : ℕ) :
    CompanionPhaseFinishProgram.view (p := p) (lookup initial history i)=
      viewLookup (CompanionPhaseFinishProgram.view (p := p) initial)
        (history.map (CompanionPhaseFinishProgram.view (p := p))) i := by
  cases i with
  | zero => rfl
  | succ i => exact (List.getD_map history initial
      (CompanionPhaseFinishProgram.view (p := p))).symm

theorem old_eq_lookup (fixed : CompanionOuterHistoryProgram.Fixed) (history : List Stored)
    (bits : List Bool) :
    CompanionOuterPhaseProgram.old ((fixed,history),bits)=lookup fixed.2 history history.length := by
  cases history with
  | nil => rfl
  | cons s history =>
    change (s::history).getD history.length default=(s::history).getD history.length fixed.2
    rw [List.getD_eq_getElem _ _ (by simp : history.length < (s::history).length),
      List.getD_eq_getElem _ _ (by simp : history.length < (s::history).length)]

theorem view_old (p : ℕ) (fixed : CompanionOuterHistoryProgram.Fixed) (history : List Stored)
    (bits : List Bool) :
    CompanionPhaseFinishProgram.view (p := p) (CompanionOuterPhaseProgram.old ((fixed,history),bits))=
      viewLookup (CompanionPhaseFinishProgram.view (p := p) fixed.2)
        (history.map (CompanionPhaseFinishProgram.view (p := p))) history.length := by
  rw [old_eq_lookup,view_lookup]

theorem view_old_canonical {I J : Type} [Fintype I] [Fintype J]
    (A : Instance I J) {p : ℕ} (g : Fin p ≃ Labels A)
    (fixed : CompanionOuterHistoryProgram.Fixed) (history : List Stored) (bits : List Bool)
    (hi : CompanionPhaseFinishProgram.view (p := p) fixed.2=
      CompanionCanonicalHistory.project A g (RootedStoredEstimate.initialStored A)) :
    CompanionPhaseFinishProgram.view (p := p) (CompanionOuterPhaseProgram.old ((fixed,history),bits))=
      CompanionCanonicalHistory.canonicalLookup A g
        (history.map (CompanionPhaseFinishProgram.view (p := p))) history.length := by
  rw [view_old,hi]
  rfl

variable {m n : ℕ}

theorem outer_data_readback (A : Instance (Fin m) (Fin n)) (C K H T N R L : ℕ)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (initial : Stored) (history : List Stored)
    (hi : StoredRep (CanonicalInitialEncoding.copyOrder (capacities A)).length initial)
    (hh : ∀ s∈history,StoredRep (CanonicalInitialEncoding.copyOrder (capacities A)).length s)
    (bits : List Bool) :
    CompanionOuterPhaseProgram.data A C K H T N R L history.length epsilon z v
      (matrixAt (CanonicalInitialEncoding.copyOrder (capacities A)).length initial history)
      (estimateAt initial history) bits=
      (((CompanionRestartInitializer.data A C K H T N R L epsilon z v,initial),history),bits) := by
  unfold CompanionOuterPhaseProgram.data
  rw [initial_readback initial history hi,history_readback initial history hi hh]

end
end ContingencyTables.CompanionHistoryReadback

end OAI
