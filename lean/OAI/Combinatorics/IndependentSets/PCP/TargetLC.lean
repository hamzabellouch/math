import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.LCTable

namespace OAI

noncomputable section

namespace LargeIndependentSets.LabelCoverData
open scoped Classical
variable {U V L R C U' V' C' : Type}

def reindex (lc : LabelCoverData U V L R C) (eu : U ≃ U') (ev : V ≃ V') (ec : C ≃ C') :
    LabelCoverData U' V' L R C' where
  left c := eu (lc.left (ec.symm c))
  right c := ev (lc.right (ec.symm c))
  project c := lc.project (ec.symm c)

lemma reindex_complete (lc : LabelCoverData U V L R C) (eu : U ≃ U') (ev : V ≃ V') (ec : C ≃ C')
    (h : ∃ l r, lc.Satisfied l r) : ∃ l r, (lc.reindex eu ev ec).Satisfied l r := by
  obtain ⟨l,r,hr⟩ := h
  refine ⟨fun u => l (eu.symm u),fun v => r (ev.symm v),?_⟩
  intro c
  simpa only [reindex,Equiv.symm_apply_apply] using hr (ec.symm c)

lemma reindex_sound [Fintype C] [Fintype C'] (lc : LabelCoverData U V L R C)
    (eu : U ≃ U') (ev : V ≃ V') (ec : C ≃ C') {σ : ℝ} (h : lc.Sound σ) :
    (lc.reindex eu ev ec).Sound σ := by
  intro l r
  have hs := h (fun u => l (eu u)) (fun v => r (ev v))
  have he : (Finset.univ.filter (fun c : C => lc.project c (l (eu (lc.left c)))=r (ev (lc.right c)))).card =
      (Finset.univ.filter (fun c : C' => (lc.reindex eu ev ec).project c (l ((lc.reindex eu ev ec).left c))=
        r ((lc.reindex eu ev ec).right c))).card := by
    apply Finset.card_bij (fun c _ => ec c)
    · intro c hc
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change lc.project (ec.symm (ec c)) (l (eu (lc.left (ec.symm (ec c))))) =
        r (ev (lc.right (ec.symm (ec c))))
      simpa only [Equiv.symm_apply_apply] using (Finset.mem_filter.mp hc).2
    · intro c hc d hd he; exact ec.injective he
    · intro c hc
      refine ⟨ec.symm c,?_,Equiv.apply_symm_apply _ _⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,(Finset.mem_filter.mp hc).2⟩
  simpa only [he,Fintype.card_congr ec] using hs

end LargeIndependentSets.LabelCoverData

namespace LargeIndependentSets.TargetLC
open IndependentSetsGames.Foundations IndependentSetsGames.Foundations.Complexity
open IndependentSetsCut.CounterMachine
open Target PCP Hastad.SourceContexts Hastad.SourceGame UniformLC
open scoped Classical BigOperators

abbrev Input := {F : Target.Formula // F.clauses≠[]}

lemma clauses_pos (F : Input) : 0<F.val.clauses.length := List.length_pos_iff.mpr F.property
lemma vars_pos (F : Input) : 0<F.val.«variables» :=
  Nat.zero_lt_of_lt ((clauseAt F.val ⟨0,clauses_pos F⟩)[0].variableIndex.isLt)

variable (u : ℕ)
def eventEquiv (F : Target.Formula) : (Fin u → RandomEvent F) ≃ Fin ((F.clauses.length*3)^u) :=
  (Equiv.piCongrRight (fun _ : Fin u => RawInitialTables.eventOrder F)).trans finFunctionFinEquiv

def table (F : Input) : Table (J u) (I u) where
  nu := F.val.clauses.length^u
  nv := F.val.«variables»^u
  ne := (F.val.clauses.length*3)^u
  hu := pow_pos (clauses_pos F) _
  hv := pow_pos (vars_pos F) _
  he := pow_pos (Nat.mul_pos (clauses_pos F) (by decide)) _
  left e := finFunctionFinEquiv ((LCInput.labelCover F.val u).left ((eventEquiv u F.val).symm e))
  right e := finFunctionFinEquiv ((LCInput.labelCover F.val u).right ((eventEquiv u F.val).symm e))
  project e := (LCInput.labelCover F.val u).project ((eventEquiv u F.val).symm e)

lemma table_lc (F : Input) : (table u F).lc =
    (LCInput.labelCover F.val u).reindex finFunctionFinEquiv finFunctionFinEquiv (eventEquiv u F.val) := rfl

lemma complete (F : Input) (h : F.val.Satisfiable) : ∃ l r, (table u F).lc.Satisfied l r := by
  rw [table_lc]
  exact LabelCoverData.reindex_complete _ _ _ _ (LCInput.complete F.val u h)

lemma sound (F : Input) {σ : ℝ} (h : (LCInput.labelCover F.val u).Sound σ) : (table u F).lc.Sound σ := by
  rw [table_lc]
  exact LabelCoverData.reindex_sound _ _ _ _ h

lemma project_apply (F : Target.Formula) (e : Fin u → RandomEvent F) (j : J u) (k : Fin u) :
    (LCInput.labelCover F u).project e j k=
      answerAt (LCInput.repair (clauseAt F (e k).1) (j k)) (e k).2 := by
  change answerAt (LCInput.repair (clauseAt F (e k).1) (j k))
    (canonicalSlot (clauseAt F (e k).1) (nameAt (clauseAt F (e k).1) (e k).2)) = _
  apply (localConsistent_eq_true_iff _ _).mp (LCInput.repair_spec _ _).2
  exact canonicalSlot_name _ _ ⟨(e k).2,rfl⟩

end LargeIndependentSets.TargetLC

end

end OAI
