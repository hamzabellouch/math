import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.TreeGeometry
import OAI.Combinatorics.MatchingCount.Machines.TreeLabelCorrect

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

attribute [local instance] Transport.prodOrder Transport.sumOrder
local instance (priority := 2000) {A B : Type} [LinearOrder A] [LinearOrder B] : LE (A×B) := Transport.prodOrder.toLE
local instance (priority := 2000) {A B : Type} [LinearOrder A] [LinearOrder B] : LT (A×B) := Transport.prodOrder.toLT
local instance (priority := 2000) {A B : Type} [LinearOrder A] [LinearOrder B] : Preorder (A×B) := Transport.prodOrder.toPreorder
local instance (priority := 2000) {A B : Type} [LinearOrder A] [LinearOrder B] : LE (A⊕B) := Transport.sumOrder.toLE
local instance (priority := 2000) {A B : Type} [LinearOrder A] [LinearOrder B] : LT (A⊕B) := Transport.sumOrder.toLT
local instance (priority := 2000) {A B : Type} [LinearOrder A] [LinearOrder B] : Preorder (A⊕B) := Transport.sumOrder.toPreorder

lemma pairwise_product {A B : Type} [LinearOrder A] [LinearOrder B]
    {as : List A} {bs : List B} (ha : as.Pairwise (· < ·)) (hb : bs.Pairwise (· < ·)) :
    (as.product bs).Pairwise (· < ·) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a _
    apply List.pairwise_map.mpr
    exact hb.imp (fun h=>Prod.Lex.right _ h)
  · apply ha.imp
    intro a b hab x hx y hy
    obtain ⟨u,hu,rfl⟩:=List.mem_map.mp hx
    obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hy
    exact Prod.Lex.left _ _ hab

lemma logicalEdges_pairwise (n : ℕ) :
    (logicalEdges (List.range n)).Pairwise (· < ·) :=
  List.Pairwise.filter _ (pairwise_product (List.pairwise_lt_range) (List.pairwise_lt_range))
lemma vertices_pairwise (n : ℕ) (fuel : List Bool) :
    (vertices (List.range n,fuel)).Pairwise (· < ·) := by
  unfold vertices
  apply List.pairwise_append.mpr
  refine ⟨?_,?_,?_⟩
  · apply List.pairwise_map.mpr
    exact (List.pairwise_lt_range (n:=n)).imp (fun h=>Sum.Lex.inl h)
  · apply List.pairwise_map.mpr
    exact (pairwise_product (logicalEdges_pairwise n) List.pairwise_lt_range).imp
      (fun h=>Sum.Lex.inr h)
  · intro a ha b hb
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ha
    obtain ⟨e,he,rfl⟩:=List.mem_map.mp hb
    exact Sum.Lex.sep _ _

lemma logicalRepr_le {n : ℕ} (a b : LogicalEdge (Fin n)) :
    logicalRepr a ≤ logicalRepr b ↔ a ≤ b := by
  change toLex (logicalRepr a) ≤ toLex (logicalRepr b) ↔ toLex a.val ≤ toLex b.val
  simp only [Prod.Lex.le_iff,logicalRepr,ofLex_toLex,Fin.lt_def,Fin.le_def,Fin.val_inj]
lemma vertexRepr_le {n m : ℕ} (a b : Vertex (Fin n) (LogicalEdge (Fin n)) m) :
    vertexRepr a ≤ vertexRepr b ↔ a ≤ b := by
  cases a with
  | inl a => cases b with
    | inl b =>
      change toLex (Sum.inl a.val : ℕ⊕RawReal) ≤ toLex (Sum.inl b.val : ℕ⊕RawReal) ↔
        toLex (Sum.inl a : Fin n⊕LogicalEdge (Fin n)×Fin m) ≤ toLex (Sum.inl b : Fin n⊕LogicalEdge (Fin n)×Fin m)
      simp only [Sum.Lex.inl_le_inl_iff,Fin.le_def]
    | inr b =>
      change toLex (Sum.inl a.val : ℕ⊕RawReal) ≤ toLex (Sum.inr (logicalRepr b.1,b.2.val) : ℕ⊕RawReal) ↔
        toLex (Sum.inl a : Fin n⊕LogicalEdge (Fin n)×Fin m) ≤ toLex (Sum.inr b : Fin n⊕LogicalEdge (Fin n)×Fin m)
      simp
  | inr a => cases b with
    | inl b =>
      change toLex (Sum.inr (logicalRepr a.1,a.2.val) : ℕ⊕RawReal) ≤ toLex (Sum.inl b.val : ℕ⊕RawReal) ↔
        toLex (Sum.inr a : Fin n⊕LogicalEdge (Fin n)×Fin m) ≤ toLex (Sum.inl b : Fin n⊕LogicalEdge (Fin n)×Fin m)
      simp
    | inr b =>
      change toLex (Sum.inr (logicalRepr a.1,a.2.val) : ℕ⊕RawReal) ≤ toLex (Sum.inr (logicalRepr b.1,b.2.val) : ℕ⊕RawReal) ↔
        toLex (Sum.inr a : Fin n⊕LogicalEdge (Fin n)×Fin m) ≤ toLex (Sum.inr b : Fin n⊕LogicalEdge (Fin n)×Fin m)
      simp only [Sum.Lex.inr_le_inr_iff]
      change toLex (logicalRepr a.1,a.2.val) ≤ toLex (logicalRepr b.1,b.2.val) ↔ toLex a ≤ toLex b
      simp only [Prod.Lex.le_iff,ofLex_toLex,Fin.le_def,logicalRepr_injective.eq_iff]
      have hlt : logicalRepr a.1 < logicalRepr b.1 ↔ a.1 < b.1 := by
        rw [lt_iff_not_ge,lt_iff_not_ge,logicalRepr_le]
      rw [hlt]

lemma vertices_eq_ofFn (n : ℕ) (fuel : List Bool) :
    vertices (List.range n,fuel)=List.ofFn (fun i=>vertexRepr
      (UnitRefresh.orderedEnum (Vertex (Fin n) (LogicalEdge (Fin n)) (4*fuel.length)) i)) := by
  classical
  let V:=Vertex (Fin n) (LogicalEdge (Fin n)) (4*fuel.length)
  rw [show (fun i=>vertexRepr (UnitRefresh.orderedEnum V i))=vertexRepr ∘ UnitRefresh.orderedEnum V from rfl,
    ←List.map_ofFn,UnitRefresh.ofFn_orderedEnum]
  have ha : (vertices (List.range n,fuel)).Pairwise (· ≤ ·) :=
    (vertices_pairwise n fuel).imp (fun h=>le_of_lt h)
  have hb : (((Finset.univ : Finset V).sort (· ≤ ·)).map vertexRepr).Pairwise (· ≤ ·) := by
    apply List.pairwise_map.mpr
    exact (Finset.pairwise_sort _ _).imp (fun h=>(vertexRepr_le _ _).mpr h)
  have hn : (vertices (List.range n,fuel)).Nodup := (vertices_pairwise n fuel).imp (fun h=>h.ne)
  have hm := (Finset.sort_nodup (Finset.univ : Finset V) (· ≤ ·)).map vertexRepr_injective
  have hp : (vertices (List.range n,fuel)).Perm (((Finset.univ : Finset V).sort (· ≤ ·)).map vertexRepr) := by
    apply List.perm_of_nodup_nodup_toFinset_eq hn hm
    ext v
    simp only [List.mem_toFinset,List.mem_map,Finset.mem_sort,Finset.mem_univ,true_and]
    constructor
    · exact vertices_complete fuel v
    · rintro ⟨a,rfl⟩; exact vertexRepr_mem fuel a
  apply hp.eq_of_pairwise (fun _ _ _ _ h₁ h₂=>@le_antisymm _ Transport.sumOrder.toPartialOrder _ _ h₁ h₂) ha hb
end MatchingFPRAS.ExecutableSource

end OAI
