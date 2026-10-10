import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeRefreshTables

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeTyped.Numbered ExecutableBottleneck NumberedHierarchy

attribute [local instance] NumberedHierarchy.labelOrder
variable {V : Type} [Fintype V] [LinearOrder V]
variable (B : V→V→ℚ) (hB : ∀ a b,0≤B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
variable (xs : List Bool) {E : Type} [Fintype E] [DecidableEq E] (left right : E→V)
include hB in
lemma arbitrary_edgeIndex (a : E) :
    edgeIndex (((matrixRep (reindex B (orderedIso V)),xs),
      labels (matrixRep (reindex B (orderedIso V)),xs)),(index (left a),index (right a)))=
      index (edgeLabel B hsym htri left right xs.length a) := by
  let e:=orderedIso V
  have h:=edgeIndex_eq (reindex B e) (fun a b=>hB (e a) (e b))
    (reindex_symm B e hsym) (reindex_tri B e htri) xs (e.symm ∘ left) (e.symm ∘ right) a
  change edgeIndex (((matrixRep (reindex B e),xs),labels (matrixRep (reindex B e),xs)),
    (index (left a),index (right a)))=index (edgeLabel (reindex B e)
      (reindex_symm B e hsym) (reindex_tri B e htri) (e.symm ∘ left) (e.symm ∘ right) xs.length a) at h
  rw [h,←labelReindex_index B e xs.length,edgeLabel_reindex B e hsym htri]

include hB in
lemma arbitrary_edgeIndex_fintype (H : ℕ) (hH : xs.length=H)
    (F : Fintype (Label B H)) (a : E) :
    letI := F
    edgeIndex (((matrixRep (fun i j=>B (UnitRefresh.orderedEnum V i) (UnitRefresh.orderedEnum V j)),xs),
      labels (matrixRep (fun i j=>B (UnitRefresh.orderedEnum V i) (UnitRefresh.orderedEnum V j)),xs)),
        (index (left a),index (right a)))=index (edgeLabel B hsym htri left right H a) := by
  subst H
  have hF : F=ordinaryLabelFintype B xs.length := Subsingleton.elim _ _
  subst F
  exact arbitrary_edgeIndex B hB hsym htri xs left right a

omit [Fintype E] [DecidableEq E] in
include hB in
lemma arbitrary_labelIndices_fintype (H : ℕ) (hH : xs.length=H)
    (F : Fintype (Label B H)) :
    letI := F
    labelIndices (matrixRep (fun i j=>B (UnitRefresh.orderedEnum V i)
      (UnitRefresh.orderedEnum V j)),xs)=List.range (Fintype.card (Label B H)) := by
  subst H
  have hF : F=ordinaryLabelFintype B xs.length := Subsingleton.elim _ _
  subst F
  exact arbitrary_labelIndices B hB xs

end MatchingFPRAS.ExecutableHierarchy

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered UnitRefresh Transport

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
variable {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
variable {bags : V→Finset L}
lemma sourceKey_mk (e : BagEdge bags) (a b : V) (l : L)
    (he : e.val.val=(s(a,b),l)) :
    sourceKey e=((min (index a) (index b),max (index a) (index b)),index l) := by
  unfold sourceKey
  rw [he]
  simp only [Sym2.inf_mk,Sym2.sup_mk,index_min,index_max]

lemma storedCatalog_source (a : ExecutableDP.Bags)
    (ha : List.Forall₂ List.Perm a (ExecutableDP.orderedRep (numberedBags bags))) :
    storedCatalog (a,List.range (Fintype.card L))=sourceCatalog bags := by
  rw [storedCatalog_eq ha,sourceCatalog_eq]
end MatchingFPRAS.ExecutableRefresh

end OAI
