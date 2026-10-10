import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth
import OAI.Combinatorics.TriangleRemoval.Process.ValidAttachments

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def ValidIndexedAttachments {K s : ℕ} (E : Finset (Finset (Fin K))) (birth : Fin s → Fin K)
    (F : PathForest s) (f : Fin s → Finset (Fin K)) : Prop :=
  (∀ i, (f i).card ≤ 2) ∧ ∀ i,
    match F.parent i with
    | none => f i ∈ E
    | some p => ∃ u ∈ f p, f i = {birth p,u}

noncomputable def indexedAttachmentFamily {K s : ℕ} (E : Finset (Finset (Fin K))) (birth : Fin s → Fin K)
    (F : PathForest s) : Finset (Fin s → Finset (Fin K)) := by
  classical
  exact Finset.univ.filter (ValidIndexedAttachments E birth F)

@[simp] lemma mem_indexedAttachmentFamily {K s : ℕ} (E : Finset (Finset (Fin K))) (birth : Fin s → Fin K)
    (F : PathForest s) (f : Fin s → Finset (Fin K)) :
    f ∈ indexedAttachmentFamily E birth F ↔ ValidIndexedAttachments E birth F f := by
  classical
  simp only [indexedAttachmentFamily,Finset.mem_filter,Finset.mem_univ,true_and]

lemma indexed_attachment_choices_le_two {K s : ℕ} (E : Finset (Finset (Fin K))) (birth : Fin s → Fin K)
    (hE : E.card ≤ 2) (F : PathForest s) (f : Fin s → Finset (Fin K))
    (hf : f ∈ indexedAttachmentFamily E birth F) (i : Fin s) :
    (prefixChoiceValues (indexedAttachmentFamily E birth F) f i).card ≤ 2 := by
  classical
  have hf' : ValidIndexedAttachments E birth F f := (mem_indexedAttachmentFamily _ _ _ _).mp hf
  cases hp : F.parent i with
  | none =>
    apply (Finset.card_le_card (t := E) ?_).trans hE
    intro e he
    obtain ⟨g,hg,_,rfl⟩ := (mem_prefixChoiceValues _ _ _ _).mp he
    have hvalid : ValidIndexedAttachments E birth F g := (mem_indexedAttachmentFamily _ _ _ _).mp hg
    simpa only [hp] using hvalid.2 i
  | some p =>
    let C : Finset (Finset (Fin K)) :=
      (f p).image (fun u => {birth p,u})
    have hsub : prefixChoiceValues (indexedAttachmentFamily E birth F) f i ⊆ C := by
      intro e he
      obtain ⟨g,hgS,hprev,rfl⟩ := (mem_prefixChoiceValues _ _ _ _).mp he
      have hvalid : ValidIndexedAttachments E birth F g := (mem_indexedAttachmentFamily _ _ _ _).mp hgS
      have hgp : g p = f p := hprev p (F.property i p hp)
      have hgi := hvalid.2 i
      rw [hp] at hgi
      obtain ⟨u,hu,heq⟩ := hgi
      exact Finset.mem_image.mpr ⟨u,by simpa only [hgp] using hu,heq.symm⟩
    exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (hf'.1 p))

theorem fixed_forest_indexed_attachment_count {K s : ℕ} (E : Finset (Finset (Fin K))) (birth : Fin s → Fin K)
    (hE : E.card ≤ 2) (F : PathForest s) : (indexedAttachmentFamily E birth F).card ≤ 2^s :=
  finite_branching_family_bound _ 2 (indexed_attachment_choices_le_two E birth hE F)

end SharpTerminalLeave

open Filter
open scoped BigOperators Topology
open scoped BigOperators

end

end OAI
