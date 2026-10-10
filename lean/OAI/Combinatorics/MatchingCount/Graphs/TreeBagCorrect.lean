import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeDPRepresentation
import OAI.Combinatorics.MatchingCount.Graphs.TreeBagTable

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck

local instance {n H : ℕ} (B : Fin n→Fin n→ℚ) : LinearOrder (NumberedHierarchy.Label B H) := NumberedHierarchy.labelOrder B H
local instance (priority := 2000) {n H : ℕ} (B : Fin n→Fin n→ℚ) : LE (NumberedHierarchy.Label B H) := (NumberedHierarchy.labelOrder B H).toLE

variable {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) {E : Type} [Fintype E] [DecidableEq E] (left right : E→Fin n)
    (es : List (ℕ×ℕ))
    (hes : ∀ p,p∈es ↔ ∃ e,((left e).val,(right e).val)=p)

include hB hes
omit [DecidableEq E] in
lemma bag_members [DecidableEq E] (v : Fin n) (i : ℕ) :
    i∈bag (((matrixRep B,xs),es),v.val) ↔ ∃ e,(v=left e ∨ v=right e) ∧
      ((UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length)).symm
        (NumberedHierarchy.edgeLabel B hsym htri left right xs.length e)).val=i := by
  simp only [bag,List.mem_dedup,List.mem_map,List.mem_filter]
  constructor
  · rintro ⟨p,⟨hp,hv⟩,hi⟩
    obtain ⟨e,rfl⟩ := (hes p).mp hp
    refine ⟨e,?_,?_⟩
    · simpa only [incident,decide_eq_true_eq,Fin.val_inj] using hv
    · rw [edgeIndex_eq B hB hsym htri xs left right e] at hi
      exact hi
  · rintro ⟨e,hv,hi⟩
    refine ⟨((left e).val,(right e).val),⟨(hes _).mpr ⟨e,rfl⟩,?_⟩,?_⟩
    · simpa only [incident,decide_eq_true_eq,Fin.val_inj] using hv
    · rw [edgeIndex_eq B hB hsym htri xs left right e]
      exact hi

noncomputable def colorNumberedBags (v : Fin n) : Finset (Fin (Fintype.card (NumberedHierarchy.Label B xs.length))) :=
  (NumberedHierarchy.bags B hsym htri left right xs.length v).map
    (UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length)).symm.toEmbedding

lemma bag_perm (v : Fin n) :
    (bag (((matrixRep B,xs),es),v.val)).Perm
      (ExecutableDP.bagRep (colorNumberedBags B hsym htri xs left right v)) := by
  apply (List.perm_ext_iff_of_nodup (List.nodup_dedup _) ((Finset.nodup_toList _).map Fin.val_injective)).mpr
  intro i
  change i∈bag (((matrixRep B,xs),es),v.val) ↔ i∈ExecutableDP.bagRep (colorNumberedBags B hsym htri xs left right v)
  rw [bag_members B hB hsym htri xs left right es hes]
  simp only [ExecutableDP.bagRep,List.mem_map,Finset.mem_toList,colorNumberedBags,Finset.mem_map,
    Equiv.toEmbedding_apply,NumberedHierarchy.mem_bags]
  constructor
  · rintro ⟨e,he,hi⟩
    exact ⟨_,⟨_,⟨e,he,rfl⟩,rfl⟩,hi⟩
  · rintro ⟨a,⟨l,⟨e,he,hel⟩,hla⟩,hai⟩
    subst l
    subst a
    exact ⟨e,he,hai⟩
lemma bagTable_represented :
    List.Forall₂ List.Perm (bagTable ((matrixRep B,xs),es))
      (ExecutableDP.orderedRep (colorNumberedBags B hsym htri xs left right)) := by
  unfold bagTable ExecutableDP.orderedRep
  rw [matrixRep_length,ExecutableDP.map_range_ofFn]
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp, ?_⟩
  intro i hi _hi'
  simpa only [List.get_eq_getElem,List.getElem_ofFn] using bag_perm B hB hsym htri xs left right es hes ⟨i,by simpa using hi⟩

end MatchingFPRAS.ExecutableHierarchy

end OAI
