import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialGrid
import OAI.Combinatorics.MatchingCount.Machines.TreeQuad
import OAI.Combinatorics.MatchingCount.Machines.TreeSum

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped Polynomial Enlargement RealGeometry

abbrev RawLogical := ℕ×ℕ
abbrev RawReal := RawLogical×ℕ
abbrev RawVertex := ℕ⊕RawReal
abbrev GeometryInput := List ℕ×List Bool

def logicalEdges (vs : List ℕ) : List RawLogical :=
  (vs.product vs).filter (fun e=>decide (e.1<e.2))
def logicalEdgesRealizer : Realizer logicalEdges :=
  (composition (composition (pair identity identity) listProduct) (filter less)).congr (fun _=>rfl)
lemma polynomial_logicalEdges : PolynomialTime logicalEdgesRealizer := by
  unfold logicalEdgesRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity polynomial_identity) polynomial_listProduct)
    (polynomial_filter polynomial_less)

def internalCount (x : GeometryInput) : ℕ := 4*x.2.length
def internalCountRealizer : Realizer internalCount :=
  (composition (pair (constant 4) (composition second listLength)) multiply).congr (fun _=>rfl)
lemma polynomial_internalCount : PolynomialTime internalCountRealizer := by
  unfold internalCountRealizer; apply polynomial_congr; tree_cost
lemma internalCount_bound (x : GeometryInput) : internalCount x≤(4*X).eval (weight x) := by
  have h: x.2.length≤weight x := (list_length_le_weight x.2).trans (weight_snd x)
  simpa [internalCount] using Nat.mul_le_mul_left 4 h

def realEdges (x : GeometryInput) : List RawReal :=
  (logicalEdges x.1).product (List.range (internalCount x+1))
def realEdgesRealizer : Realizer realEdges := (composition
  (pair (composition first logicalEdgesRealizer)
    (composition (composition internalCountRealizer successor) range)) listProduct).congr (fun _=>rfl)
lemma polynomial_realEdges : PolynomialTime realEdgesRealizer := by
  have hr:PolynomialTime (composition (composition internalCountRealizer successor) range) := by
    apply polynomial_boundedRange (polynomial_composition polynomial_internalCount polynomial_successor) (4*X+1)
    intro x
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one,Function.comp_apply]
    have h:=internalCount_bound x
    simpa only [eval_mul,eval_ofNat,eval_X] using Nat.add_le_add_right h 1
  unfold realEdgesRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_logicalEdges) hr) polynomial_listProduct

def vertices (x : GeometryInput) : List RawVertex :=
  x.1.map Sum.inl ++ ((logicalEdges x.1).product (List.range (internalCount x))).map Sum.inr
def verticesRealizer : Realizer vertices := (composition (pair
  (composition first (map inl))
  (composition (composition (pair (composition first logicalEdgesRealizer)
    (composition internalCountRealizer range)) listProduct) (map inr))) append).congr (fun _=>rfl)
lemma polynomial_vertices : PolynomialTime verticesRealizer := by
  have hr:=polynomial_boundedRange polynomial_internalCount (4*X) internalCount_bound
  unfold verticesRealizer
  apply polynomial_congr
  have := polynomial_logicalEdges
  have := polynomial_listProduct (A:=RawLogical) (B:=ℕ)
  have := polynomial_inl (A:=ℕ) (B:=RawReal)
  have := polynomial_inr (A:=ℕ) (B:=RawReal)
  have := polynomial_successor
  have := polynomial_predecessor
  tree_cost

def position (x : ℕ×RawReal) : RawVertex :=
  if x.2.2=0 then .inl x.2.1.1
  else if x.2.2=x.1+1 then .inl x.2.1.2
  else .inr (x.2.1,x.2.2-1)
def atRealizer : Realizer position :=
  (choose (composition (pair second.snd (constant 0)) natEqual)
    (composition second.fst.fst inl)
    (choose (composition (pair second.snd (composition first successor)) natEqual)
      (composition second.fst.snd inl)
      (composition (pair second.fst (composition second.snd predecessor)) inr))).congr (by
        intro x; simp [position])
lemma polynomial_at : PolynomialTime atRealizer := by
  unfold atRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_inl (A:=ℕ) (B:=RawReal)
  have := polynomial_inr (A:=ℕ) (B:=RawReal)
  have := polynomial_successor
  have := polynomial_predecessor
  tree_cost

def left (x : GeometryInput×RawReal) : RawVertex := position (internalCount x.1,x.2)
def right (x : GeometryInput×RawReal) : RawVertex := position (internalCount x.1,(x.2.1,x.2.2+1))
def leftRealizer : Realizer left := (composition (pair (composition first internalCountRealizer) second) atRealizer).congr (fun _=>rfl)
def rightRealizer : Realizer right := (composition (pair (composition first internalCountRealizer)
  (pair second.fst (composition second.snd successor))) atRealizer).congr (fun _=>rfl)
lemma polynomial_left : PolynomialTime leftRealizer := by
  unfold leftRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_internalCount)
    polynomial_second) polynomial_at
lemma polynomial_right : PolynomialTime rightRealizer := by
  unfold rightRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_successor
  have := polynomial_internalCount
  have := polynomial_at
  tree_cost

variable {n m : ℕ}
def logicalRepr (e : LogicalEdge (Fin n)) : RawLogical := (e.val.1.val,e.val.2.val)
def realRepr (e : LogicalEdge (Fin n)×Fin (m+1)) : RawReal := (logicalRepr e.1,e.2.val)
def vertexRepr : Vertex (Fin n) (LogicalEdge (Fin n)) m→RawVertex
  | .inl v => .inl v.val
  | .inr (e,i) => .inr (logicalRepr e,i.val)
lemma logicalRepr_injective : Function.Injective (logicalRepr (n:=n)) := by
  intro a b h
  apply Subtype.ext
  exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
lemma vertexRepr_injective : Function.Injective (vertexRepr (n:=n) (m:=m)) := by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => exact congrArg Sum.inl (Fin.ext (Sum.inl.inj h))
    | inr b => cases h
  | inr a => cases b with
    | inl b => cases h
    | inr b =>
      have h':(logicalRepr a.1,a.2.val)=(logicalRepr b.1,b.2.val):=Sum.inr.inj h
      exact congrArg Sum.inr (Prod.ext (logicalRepr_injective (congrArg Prod.fst h'))
        (Fin.ext (congrArg Prod.snd h')))
lemma at_repr (e : LogicalEdge (Fin n)) (i : Fin (m+2)) :
    position (m,(logicalRepr e,i.val))=vertexRepr (atVertex source target m e i) := by
  unfold position atVertex
  split_ifs <;> rfl
lemma left_repr (vs : List ℕ) (fuel : List Bool) (e : LogicalEdge (Fin n)×Fin (4*fuel.length+1)) :
    left ((vs,fuel),realRepr e)=vertexRepr (atVertex source target (4*fuel.length) e.1 e.2.castSucc) := by
  exact at_repr e.1 e.2.castSucc
lemma right_repr (vs : List ℕ) (fuel : List Bool) (e : LogicalEdge (Fin n)×Fin (4*fuel.length+1)) :
    right ((vs,fuel),realRepr e)=vertexRepr (atVertex source target (4*fuel.length) e.1 e.2.succ) := by
  exact at_repr e.1 e.2.succ

lemma mem_logicalEdges (vs : List ℕ) (e : RawLogical) :
    e∈logicalEdges vs ↔ e.1∈vs ∧ e.2∈vs ∧ e.1<e.2 := by
  rcases e with ⟨a,b⟩
  simp [logicalEdges,and_assoc]
lemma logicalRepr_mem (e : LogicalEdge (Fin n)) : logicalRepr e∈logicalEdges (List.range n) := by
  rw [mem_logicalEdges]
  exact ⟨List.mem_range.mpr e.val.1.isLt,List.mem_range.mpr e.val.2.isLt,e.property⟩
lemma logicalEdges_complete (e : RawLogical) (h : e∈logicalEdges (List.range n)) :
    ∃ a : LogicalEdge (Fin n),logicalRepr a=e := by
  rw [mem_logicalEdges] at h
  exact ⟨⟨(⟨e.1,List.mem_range.mp h.1⟩,⟨e.2,List.mem_range.mp h.2.1⟩),h.2.2⟩,rfl⟩
lemma vertexRepr_mem (fuel : List Bool) (v : Vertex (Fin n) (LogicalEdge (Fin n)) (4*fuel.length)) :
    vertexRepr v∈vertices (List.range n,fuel) := by
  cases v with
  | inl v => simp only [vertices,List.mem_append,List.mem_map]; exact Or.inl ⟨v.val,List.mem_range.mpr v.isLt,rfl⟩
  | inr q =>
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨(logicalRepr q.1,q.2.val),List.mem_product.mpr ⟨logicalRepr_mem q.1,List.mem_range.mpr q.2.isLt⟩,rfl⟩
lemma vertices_complete (fuel : List Bool) (v : RawVertex) (h : v∈vertices (List.range n,fuel)) :
    ∃ a : Vertex (Fin n) (LogicalEdge (Fin n)) (4*fuel.length),vertexRepr a=v := by
  simp only [vertices,List.mem_append,List.mem_map] at h
  rcases h with ⟨i,hi,rfl⟩|⟨⟨e,i⟩,hi,rfl⟩
  · exact ⟨.inl ⟨i,List.mem_range.mp hi⟩,rfl⟩
  · obtain ⟨he,hj⟩:=List.mem_product.mp hi
    obtain ⟨a,rfl⟩:=logicalEdges_complete e he
    exact ⟨.inr (a,⟨i,List.mem_range.mp hj⟩),rfl⟩
lemma realRepr_mem (fuel : List Bool) (e : LogicalEdge (Fin n)×Fin (4*fuel.length+1)) :
    realRepr e∈realEdges (List.range n,fuel) := by
  exact List.mem_product.mpr ⟨logicalRepr_mem e.1,List.mem_range.mpr e.2.isLt⟩
lemma realEdges_complete (fuel : List Bool) (e : RawReal) (h : e∈realEdges (List.range n,fuel)) :
    ∃ a : LogicalEdge (Fin n)×Fin (4*fuel.length+1),realRepr a=e := by
  obtain ⟨he,hi⟩:=List.mem_product.mp h
  obtain ⟨a,ha⟩:=logicalEdges_complete e.1 he
  exact ⟨(a,⟨e.2,List.mem_range.mp hi⟩),Prod.ext ha rfl⟩
end MatchingFPRAS.ExecutableSource

end OAI
