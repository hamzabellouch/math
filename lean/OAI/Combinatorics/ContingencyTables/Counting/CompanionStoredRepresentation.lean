import OAI.Combinatorics.ContingencyTables.Counting.CompanionInitialStoredProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionOuterHistoryProgram

namespace OAI

/-! # Exact square-matrix representations along the physical phase loop

Successful updates construct every entry in catalog order. Aborted updates
retain the previous stored value, so the same representation supports the
readback used in the projected history law.
-/
namespace ContingencyTables.CompanionStoredRepresentation
open MatchingFPRAS CompanionMultiplierMatrixProgram

def MatrixRep (p : ℕ) (M : FractionMatrix) : Prop :=
  ∃ w : Fin p→Fin p→TreeFraction.Fraction, M=matrixCode w

def StoredRep (p : ℕ) (s : CompanionPhaseFinishProgram.Stored) : Prop :=
  MatrixRep p s.1

def entries (p : ℕ) (M : FractionMatrix) (i j : Fin p) : TreeFraction.Fraction :=
  readEntry (M,(i.val,j.val))

theorem matrixCode_rep {p : ℕ} (w : Fin p→Fin p→TreeFraction.Fraction) :
    MatrixRep p (matrixCode w) := ⟨w,rfl⟩

theorem readback {p : ℕ} {M : FractionMatrix} (h : MatrixRep p M) :
    matrixCode (entries p M)=M := by
  obtain ⟨w,rfl⟩ := h
  have he : entries p (matrixCode w)=w := by
    funext i j
    exact readEntry_code w i j
  rw [he]

theorem stored_readback {p : ℕ} {s : CompanionPhaseFinishProgram.Stored}
    (h : StoredRep p s) : (matrixCode (entries p s.1),s.2)=s := by
  exact Prod.ext (readback h) rfl

theorem matrixCode_injective {p : ℕ} :
    Function.Injective (matrixCode (p := p)) := by
  intro w w' h
  funext i j
  have he := congrArg (fun M => readEntry (M,(i.val,j.val))) h
  simpa only [readEntry_code] using he

private theorem map_range_ofFn {α : Type} (f : ℕ→α) (p : ℕ) :
    (List.range p).map f=List.ofFn (fun i : Fin p => f i.val) := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]

theorem updateMatrix_rep (z : CompanionMultiplierMatrixProgram.Input) :
    MatrixRep z.1.1.length (updateMatrix z) := by
  refine ⟨fun i j => updateEntry (z,(i.val,j.val)),?_⟩
  simp only [updateMatrix,updateRow,rowEntry,indices,map_range_ofFn,matrixCode]

theorem finish_output_rep (z : CompanionPhaseFinishProgram.Input)
    (s : CompanionPhaseFinishProgram.Stored)
    (h : CompanionPhaseFinishProgram.output z=some s) :
    StoredRep z.1.1.1.1.length s := by
  unfold CompanionPhaseFinishProgram.output at h
  split_ifs at h
  · cases Option.some.inj h
    exact updateMatrix_rep z.1.1

theorem observed_output_rep (z : CompanionObservedUpdateProgram.Input)
    (s : CompanionPhaseFinishProgram.Stored)
    (h : CompanionObservedUpdateProgram.output z=some s) :
    StoredRep z.1.2.1.1.1.length s :=
  finish_output_rep (CompanionObservedUpdateProgram.finishInput z) s h

theorem trial_output_rep (z : CompanionPhaseTrialProgram.Input)
    (s : CompanionPhaseFinishProgram.Stored)
    (h : CompanionPhaseTrialProgram.output z=some s) :
    StoredRep (CompanionPhaseTrialProgram.catalogue z).length s :=
  observed_output_rep (CompanionPhaseTrialProgram.updateInput z) s h

theorem trial_getD_rep {p : ℕ} (z : CompanionPhaseTrialProgram.Input)
    (old : CompanionPhaseFinishProgram.Stored) (hold : StoredRep p old)
    (hlen : (CompanionPhaseTrialProgram.catalogue z).length=p) :
    StoredRep p ((CompanionPhaseTrialProgram.output z).getD old) := by
  cases h : CompanionPhaseTrialProgram.output z with
  | none => simpa only [Option.getD_none] using hold
  | some s =>
    simpa only [Option.getD_some,hlen] using trial_output_rep z s h

theorem old_rep {p : ℕ} (z : CompanionOuterPhaseProgram.Input)
    (hinit : StoredRep p z.1.1.2)
    (hh : ∀ s∈z.1.2,StoredRep p s) :
    StoredRep p (CompanionOuterPhaseProgram.old z) := by
  unfold CompanionOuterPhaseProgram.old CompanionOuterPhaseProgram.phase
    CompanionOuterPhaseProgram.history
  split_ifs with he
  · exact hinit
  · have hi : z.1.2.length-1 < z.1.2.length := by omega
    rw [List.getD_eq_getElem _ _ hi]
    exact hh _ (List.getElem_mem hi)

theorem outer_output_rep {p : ℕ} (z : CompanionOuterPhaseProgram.Input)
    (hinit : StoredRep p z.1.1.2)
    (hh : ∀ s∈z.1.2,StoredRep p s)
    (hlen : (CompanionPhaseTrialProgram.catalogue
      (CompanionOuterPhaseProgram.trialInput z)).length=p) :
    StoredRep p (CompanionOuterPhaseProgram.output z) :=
  trial_getD_rep (CompanionOuterPhaseProgram.trialInput z)
    (CompanionOuterPhaseProgram.old z) (old_rep z hinit hh) hlen

theorem history_rep {p : ℕ} (fixed : CompanionOuterHistoryProgram.Fixed)
    (hinit : StoredRep p fixed.2)
    (hcat : ∀ (history : List CompanionPhaseFinishProgram.Stored) (bits : List Bool),
      (∀ s∈history,StoredRep p s) →
      (CompanionPhaseTrialProgram.catalogue
        (CompanionOuterPhaseProgram.trialInput ((fixed,history),bits))).length=p)
    (words : List (List Bool)) :
    ∀ s∈CompanionOuterHistoryProgram.storedHistory (fixed,words),StoredRep p s := by
  have hf (ws : List (List Bool)) (history : List CompanionPhaseFinishProgram.Stored)
      (hh : ∀ s∈history,StoredRep p s) :
      ∀ s∈(ws.foldl (fun state bits => CompanionOuterHistoryProgram.advance (bits,state))
        (fixed,history)).2,StoredRep p s := by
    induction ws generalizing history with
    | nil => exact hh
    | cons bits ws ih =>
      apply ih
      intro s hs
      obtain hs|hs := List.mem_append.mp hs
      · exact hh s hs
      · have he : s=CompanionOuterHistoryProgram.next (bits,(fixed,history)) := by
          simpa only [List.mem_singleton] using hs
        subst s
        exact outer_output_rep ((fixed,history),bits) hinit hh (hcat history bits hh)
  exact hf words [] (by simp)

theorem history_output_rep {p : ℕ} (fixed : CompanionOuterHistoryProgram.Fixed)
    (hinit : StoredRep p fixed.2)
    (hcat : ∀ (history : List CompanionPhaseFinishProgram.Stored) (bits : List Bool),
      (∀ s∈history,StoredRep p s) →
      (CompanionPhaseTrialProgram.catalogue
        (CompanionOuterPhaseProgram.trialInput ((fixed,history),bits))).length=p)
    (words : List (List Bool)) :
    StoredRep p (CompanionOuterHistoryProgram.output (fixed,words)) :=
  old_rep ((fixed,CompanionOuterHistoryProgram.storedHistory (fixed,words)),[])
    hinit (history_rep fixed hinit hcat words)

theorem history_rep_bounded {p H : ℕ} (fixed : CompanionOuterHistoryProgram.Fixed)
    (hinit : StoredRep p fixed.2)
    (hcat : ∀ (history : List CompanionPhaseFinishProgram.Stored) (bits : List Bool),
      history.length < H → (∀ s∈history,StoredRep p s) →
      (CompanionPhaseTrialProgram.catalogue
        (CompanionOuterPhaseProgram.trialInput ((fixed,history),bits))).length=p)
    (words : List (List Bool)) (hwords : words.length ≤ H) :
    ∀ s∈CompanionOuterHistoryProgram.storedHistory (fixed,words),StoredRep p s := by
  have hf (ws : List (List Bool)) (history : List CompanionPhaseFinishProgram.Stored)
      (hh : ∀ s∈history,StoredRep p s) (hlen : history.length+ws.length ≤ H) :
      ∀ s∈(ws.foldl (fun state bits => CompanionOuterHistoryProgram.advance (bits,state))
        (fixed,history)).2,StoredRep p s := by
    induction ws generalizing history with
    | nil => exact hh
    | cons bits ws ih =>
      have hj : history.length < H := by
        simp only [List.length_cons] at hlen
        omega
      apply ih
      · intro s hs
        obtain hs|hs := List.mem_append.mp hs
        · exact hh s hs
        · have he : s=CompanionOuterHistoryProgram.next (bits,(fixed,history)) := by
            simpa only [List.mem_singleton] using hs
          subst s
          exact outer_output_rep ((fixed,history),bits) hinit hh (hcat history bits hj hh)
      · simp only [List.length_append,List.length_cons,List.length_nil] at *
        omega
  exact hf words [] (by simp) (by simpa only [List.length_nil,Nat.zero_add] using hwords)

theorem history_output_rep_bounded {p H : ℕ} (fixed : CompanionOuterHistoryProgram.Fixed)
    (hinit : StoredRep p fixed.2)
    (hcat : ∀ (history : List CompanionPhaseFinishProgram.Stored) (bits : List Bool),
      history.length < H → (∀ s∈history,StoredRep p s) →
      (CompanionPhaseTrialProgram.catalogue
        (CompanionOuterPhaseProgram.trialInput ((fixed,history),bits))).length=p)
    (words : List (List Bool)) (hwords : words.length ≤ H) :
    StoredRep p (CompanionOuterHistoryProgram.output (fixed,words)) :=
  old_rep ((fixed,CompanionOuterHistoryProgram.storedHistory (fixed,words)),[])
    hinit (history_rep_bounded fixed hinit hcat words hwords)

noncomputable section
open CompanionFactorialApplication
open scoped Classical
variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

theorem initial_output_rep (S : Set (Labels A×Bool)) :
    StoredRep (CanonicalInitialEncoding.copyOrder (CompanionComputedInitial.capacities A)).length
      (CompanionInitialStoredProgram.output (CompanionInitialStoredProgram.data A S)) :=
  ⟨CompanionInitialMatrixProgram.initialEntries A,CompanionInitialStoredProgram.output_matrix A S⟩

end
end ContingencyTables.CompanionStoredRepresentation

end OAI
