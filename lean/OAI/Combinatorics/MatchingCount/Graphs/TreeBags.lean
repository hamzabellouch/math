import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.TreeBagCorrect
import OAI.Combinatorics.MatchingCount.Graphs.TreeHierarchyReindex

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck NumberedHierarchy

variable {V : Type} [Fintype V] [LinearOrder V]
variable (B : V→V→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
attribute [local instance] NumberedHierarchy.labelOrder
local instance (priority := 2000) treeBagsLabelLE {U : Type} [Fintype U] [LinearOrder U] {H : ℕ}
    (C : U→U→ℚ) : LE (Label C H) := (labelOrder C H).toLE
variable (xs : List Bool) {E : Type} [Fintype E] [DecidableEq E] (left right : E→V)
    (es : List (ℕ×ℕ))
    (hes : ∀ p,p∈es ↔ ∃ e,(index (left e),index (right e))=p)

include hB hes in
lemma arbitrary_bag_members (v : V) (i : ℕ) :
    i∈bag (((matrixRep (reindex B (orderedIso V)),xs),es),index v) ↔
      ∃ e,(v=left e ∨ v=right e) ∧ index (edgeLabel B hsym htri left right xs.length e)=i := by
  let f:=orderedIso V
  have hh:=bag_members (reindex B f) (fun a b=>hB (f a) (f b))
    (reindex_symm B f hsym) (reindex_tri B f htri) xs (f.symm ∘ left) (f.symm ∘ right)
    es hes (f.symm v) i
  change i∈bag (((matrixRep (reindex B f),xs),es),index v) ↔ _ at hh
  rw [hh]
  apply exists_congr
  intro a
  have he:=labelReindex_index B f xs.length (edgeLabel (reindex B f)
    (reindex_symm B f hsym) (reindex_tri B f htri)
    (f.symm ∘ left) (f.symm ∘ right) xs.length a)
  rw [edgeLabel_reindex B f hsym htri] at he
  change (f.symm v=f.symm (left a) ∨ f.symm v=f.symm (right a)) ∧ _ ↔ _
  simp only [f.symm.injective.eq_iff]
  simpa only [index] using iff_of_eq (congrArg (fun j=>(v=left a ∨ v=right a) ∧ j=i) he.symm)

noncomputable def arbitraryNumberedBags (v : V) :
    Finset (Fin (Fintype.card (Label B xs.length))) :=
  (NumberedHierarchy.bags B hsym htri left right xs.length v).map
    (UnitRefresh.orderedEnum (Label B xs.length)).symm.toEmbedding

include hB hes in
lemma arbitrary_bag_perm (v : V) :
    (bag (((matrixRep (reindex B (orderedIso V)),xs),es),index v)).Perm
      (ExecutableDP.bagRep (arbitraryNumberedBags B hsym htri xs left right v)) := by
  apply (List.perm_ext_iff_of_nodup (List.nodup_dedup _) ((Finset.nodup_toList _).map Fin.val_injective)).mpr
  intro i
  change i∈bag (((matrixRep (reindex B (orderedIso V)),xs),es),index v) ↔ _
  rw [arbitrary_bag_members B hB hsym htri xs left right es hes]
  simp only [List.mem_map,Finset.mem_toList,arbitraryNumberedBags,
    Finset.mem_map,Equiv.toEmbedding_apply,NumberedHierarchy.mem_bags]
  constructor
  · rintro ⟨e,he,hi⟩
    exact ⟨_,⟨_,⟨e,he,rfl⟩,rfl⟩,hi⟩
  · rintro ⟨a,⟨l,⟨e,he,hel⟩,hla⟩,hai⟩
    subst l
    subst a
    exact ⟨e,he,hai⟩

include hB hes in
lemma arbitrary_bagTable :
    List.Forall₂ List.Perm (bagTable ((matrixRep (reindex B (orderedIso V)),xs),es))
      (List.ofFn (fun i=>ExecutableDP.bagRep
        (arbitraryNumberedBags B hsym htri xs left right (UnitRefresh.orderedEnum V i)))) := by
  unfold bagTable
  rw [matrixRep_length,ExecutableDP.map_range_ofFn]
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp,?_⟩
  intro i hi _right_bound
  have hh:=arbitrary_bag_perm B hB hsym htri xs left right es hes
    (UnitRefresh.orderedEnum V ⟨i,by simpa using hi⟩)
  simpa only [List.get_eq_getElem,List.getElem_ofFn,index,Equiv.symm_apply_apply] using hh
include hB hes in
lemma arbitrary_bagTable_length (H : ℕ) (h : xs.length=H) :
    List.Forall₂ List.Perm (bagTable ((matrixRep (reindex B (orderedIso V)),xs),es))
      (List.ofFn (fun i=>ExecutableDP.bagRep
        ((NumberedHierarchy.bags B hsym htri left right H (UnitRefresh.orderedEnum V i)).map
          (UnitRefresh.orderedEnum (Label B H)).symm.toEmbedding))) := by
  subst H
  exact arbitrary_bagTable B hB hsym htri xs left right es hes

include hB hes in
lemma arbitrary_bagTable_numbered (H : ℕ) (h : xs.length=H) :
    List.Forall₂ List.Perm (bagTable ((matrixRep (reindex B (orderedIso V)),xs),es))
      (ExecutableDP.orderedRep (UnitRefresh.numberedBags
        (NumberedHierarchy.bags B hsym htri left right H))) :=
  arbitrary_bagTable_length B hB hsym htri xs left right es hes H h

include hB hes in
lemma arbitrary_bagTable_enumerated (H : ℕ) (h : xs.length=H) :
    List.Forall₂ List.Perm
      (bagTable ((matrixRep (fun i j=>B (UnitRefresh.orderedEnum V i) (UnitRefresh.orderedEnum V j)),xs),es))
      (ExecutableDP.orderedRep (UnitRefresh.numberedBags
        (NumberedHierarchy.bags B hsym htri left right H))) :=
  arbitrary_bagTable_numbered B hB hsym htri xs left right es hes H h

@[instance_reducible] def ordinaryLabelFintype (H : ℕ) : Fintype (Label B H) := inferInstance

include hB hes in
lemma arbitrary_bagTable_fintype (H : ℕ) (h : xs.length=H)
    (F : Fintype (Label B H)) :
    letI := F
    List.Forall₂ List.Perm
      (bagTable ((matrixRep (fun i j=>B (UnitRefresh.orderedEnum V i) (UnitRefresh.orderedEnum V j)),xs),es))
      (ExecutableDP.orderedRep (UnitRefresh.numberedBags
        (NumberedHierarchy.bags B hsym htri left right H))) := by
  have hf : F=ordinaryLabelFintype B H := Subsingleton.elim _ _
  subst F
  exact arbitrary_bagTable_enumerated B hB hsym htri xs left right es hes H h

end MatchingFPRAS.ExecutableHierarchy

end OAI
