import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeParentTable
import OAI.Combinatorics.MatchingCount.Graphs.TreeHierarchyReindex
import OAI.Combinatorics.MatchingCount.Graphs.TreeRankPlan

namespace OAI

namespace MatchingFPRAS.TreeTyped.Numbered
variable {A B C : Type} [Fintype A] [Fintype B] [LinearOrder A] [LinearOrder B]
lemma ordered_lists_transport (e : A≃o B) (f : A→C) (g : B→C)
    (h : ∀ a,f a=g (e a)) :
    List.ofFn (fun i=>f (UnitRefresh.orderedEnum A i))=
      List.ofFn (fun i=>g (UnitRefresh.orderedEnum B i)) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn]
    exact Fintype.card_congr e.toEquiv
  · intro i hi hj
    simp only [List.length_ofFn] at hi hj
    simp only [List.getElem_ofFn,h]
    congr 1
    apply index_injective
    rw [index_orderIso,index_orderedEnum,index_orderedEnum]
lemma parentTag_transport (e : A≃o B) (o : Option A) :
    ExecutableDP.parentTag (o.map (UnitRefresh.orderedEnum A).symm)=
      ExecutableDP.parentTag ((o.map e).map (UnitRefresh.orderedEnum B).symm) := by
  cases o with
  | none=>rfl
  | some a=>
    change (true,index a)=(true,index (e a))
    rw [index_orderIso]
end MatchingFPRAS.TreeTyped.Numbered

namespace MatchingFPRAS.NumberedHierarchy
variable {V W : Type} [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]
variable (B : W→W→ℚ) (e : V≃o W)
variable (hsym : ∀ a b,B a b=B b a)
variable (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
lemma parent_reindex {H : ℕ} (l : Label (reindex B e) H) :
    (parent (reindex B e) (reindex_symm B e hsym) (reindex_tri B e htri) l).map
      (labelReindex B e H)=parent B hsym htri (labelReindex B e H l) := by
  unfold parent
  change (if h : 0<l.1.val then some (labelAt (reindex B e) (reindex_symm B e hsym)
    (reindex_tri B e htri) ⟨l.1.val-1,by omega⟩ l.2.val) else none).map (labelReindex B e H)=
    if h : 0<l.1.val then some (labelAt B hsym htri ⟨l.1.val-1,by omega⟩ (e l.2.val)) else none
  split_ifs with h
  · rw [Option.map_some]
    exact congrArg some (labelAt_reindex B e hsym htri _ _)
  · rfl
end MatchingFPRAS.NumberedHierarchy

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeTyped.Numbered ExecutableBottleneck NumberedHierarchy

variable {V : Type} [Fintype V] [LinearOrder V]
variable (B : V→V→ℚ) (hB : ∀ a b,0≤B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
attribute [local instance] NumberedHierarchy.labelOrder
local instance (priority := 2000) {U : Type} [Fintype U] [LinearOrder U] {H : ℕ}
    (C : U→U→ℚ) : LE (Label C H) := (labelOrder C H).toLE
include hB in
lemma arbitrary_parents (xs : List Bool) :
    parents (matrixRep (reindex B (orderedIso V)),xs)=
      ExecutableDP.parentRep (UnitRefresh.numberedParent
        (NumberedHierarchy.parent B hsym htri (H:=xs.length))) := by
  let e:=orderedIso V
  rw [parents_eq _ (fun a b=>hB (e a) (e b)) (reindex_symm B e hsym) (reindex_tri B e htri)]
  unfold ExecutableDP.parentRep UnitRefresh.numberedParent
  exact ordered_lists_transport (labelOrderReindex B e xs.length)
    (fun a=>ExecutableDP.parentTag ((NumberedHierarchy.parent (reindex B e)
      (reindex_symm B e hsym) (reindex_tri B e htri) a).map
        (UnitRefresh.orderedEnum (Label (reindex B e) xs.length)).symm))
    (fun a=>ExecutableDP.parentTag ((NumberedHierarchy.parent B hsym htri a).map
      (UnitRefresh.orderedEnum (Label B xs.length)).symm)) (fun a=>by
    rw [parentTag_transport (labelOrderReindex B e xs.length)]
    change ExecutableDP.parentTag (Option.map (UnitRefresh.orderedEnum (Label B xs.length)).symm
      (Option.map (labelReindex B e xs.length)
        (NumberedHierarchy.parent (reindex B e) (reindex_symm B e hsym) (reindex_tri B e htri) a)))=_
    rw [parent_reindex B e hsym htri]
    rfl)
include hB in
lemma arbitrary_ranks (xs : List Bool) :
    ranks (matrixRep (reindex B (orderedIso V)),xs)=
      List.ofFn (UnitRefresh.numberedRank (fun a : Label B xs.length=>a.1.val)) := by
  let e:=orderedIso V
  rw [ranks_eq _ (fun a b=>hB (e a) (e b))]
  exact ordered_lists_transport (labelOrderReindex B e xs.length) (fun a=>a.1.val) (fun a=>a.1.val) (fun _=>rfl)
include hB in
lemma arbitrary_plan (xs : List Bool) :
    rankPlan (ranks (matrixRep (reindex B (orderedIso V)),xs))=
      (UnitRefresh.Materialized.plan (UnitRefresh.numberedRank
        (fun a : Label B xs.length=>a.1.val))).map Fin.val := by
  rw [arbitrary_ranks B hB,rankPlan_eq]
end MatchingFPRAS.ExecutableHierarchy

end OAI
