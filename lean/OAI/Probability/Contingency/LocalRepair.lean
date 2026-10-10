import Mathlib
import OAI.Probability.Contingency.GreedyTable

namespace OAI

/-! Local Repair. -/

noncomputable section

open scoped BigOperators
open scoped BigOperators
namespace Contingency.PaddedGraph
variable {m n : ℕ} (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)

 

def inverseRepair (s t : Cell m n) (Y : State m n) : State m n :=
  let x := fun w => Y.x w + unit t w -
    if IsSmall U r c (receiver s t) then unit (receiver s t) w else 0
  ⟨x, fun w => x w - unit t w + unit s w⟩

theorem inverseRepair_repair (s t : Cell m n) (X : State m n)
    (h : DefectAt U r c s t X) :
    inverseRepair U r c s t (repair U r c s t X) = X := by
  have hx : (inverseRepair U r c s t (repair U r c s t X)).x = X.x := by
    funext w; dsimp [inverseRepair,repair]; ring
  have hq : (inverseRepair U r c s t (repair U r c s t X)).q = X.q := by
    funext w
    change (inverseRepair U r c s t (repair U r c s t X)).x w - unit t w + unit s w = X.q w
    rw [hx,h.2.2.2]
  exact congrArg₂ State.mk hx hq

theorem repair_inverseRepair (s t : Cell m n) (Y : State m n)
    (h : Transversal Y) :
    repair U r c s t (inverseRepair U r c s t Y) = Y := by
  have hx : (repair U r c s t (inverseRepair U r c s t Y)).x = Y.x := by
    funext w; dsimp [inverseRepair,repair]; ring
  have hq : (repair U r c s t (inverseRepair U r c s t Y)).q = Y.q := by
    change (repair U r c s t (inverseRepair U r c s t Y)).x = Y.q
    exact hx.trans h.symm
  exact congrArg₂ State.mk hx hq

theorem inverseRepair_defect (s t : Cell m n) (Y : State m n)
    (hs : IsSmall U r c s) (ht : IsSmall U r c t) (hst : s ≠ t) :
    DefectAt U r c s t (inverseRepair U r c s t Y) := ⟨hs,ht,hst,rfl⟩

 
def slotList (m n : ℕ) : List (Cell m n) :=
  (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n => (i,j)).flatten

@[simp] theorem mem_slotList (s : Cell m n) : s ∈ slotList m n := by
  rcases s with ⟨i,j⟩
  simp [slotList]

@[simp] theorem length_slotList : (slotList m n).length = m*n := by
  simp [slotList,List.length_flatten,Function.comp_def]

def typeList (m n : ℕ) : List (Cell m n × Cell m n) :=
  (slotList m n).flatMap fun s => (slotList m n).map fun t => (s,t)

@[simp] theorem mem_typeList (st : Cell m n × Cell m n) : st ∈ typeList m n := by
  rcases st with ⟨s,t⟩; simp [typeList]

@[simp] theorem length_typeList : (typeList m n).length=(m*n)^2 := by
  simp [typeList,List.length_flatMap,pow_two]

instance feasibleDecidable (X : State m n) : Decidable (Feasible U r c X) :=
  by unfold Feasible; infer_instance

instance transversalDecidable (X : State m n) : Decidable (Transversal X) :=
  inferInstanceAs (Decidable (X.q = X.x))

instance defectAtDecidable (s t : Cell m n) (X : State m n) :
    Decidable (DefectAt U r c s t X) :=
  inferInstanceAs (Decidable (IsSmall U r c s ∧ IsSmall U r c t ∧ s ≠ t ∧ _))

 

def inverseNeighbors (Y : State m n) : List (State m n) :=
  if Transversal Y then
    ((typeList m n).filter fun st =>
      IsSmall U r c st.1 ∧ IsSmall U r c st.2 ∧ st.1 ≠ st.2 ∧
      Feasible U r c (inverseRepair U r c st.1 st.2 Y)).map
        fun st => inverseRepair U r c st.1 st.2 Y
  else []

theorem length_inverseNeighbors (Y : State m n) :
    (inverseNeighbors U r c Y).length ≤ (m*n)^2 := by
  unfold inverseNeighbors
  split_ifs
  · simpa only [List.length_map,length_typeList] using List.length_filter_le
      (p:=fun st : Cell m n × Cell m n => decide
        (IsSmall U r c st.1 ∧ IsSmall U r c st.2 ∧ st.1 ≠ st.2 ∧
          Feasible U r c (inverseRepair U r c st.1 st.2 Y))) (typeList m n)
  · simp

theorem repairedState_eq (s t : Cell m n) (X : DefectiveState U r c)
    (h : DefectAt U r c s t X.val) :
    (repairedState U r c X).val = repair U r c s t X.val := by
  obtain ⟨hs,ht⟩ := defect_type_unique U r c X.val _ _ s t (defectPair_spec U r c X) h
  change repair U r c _ _ X.val = _
  rw [hs,ht]

 

theorem mem_inverseNeighbors (X Y : GraphState U r c) :
    graphUnderlying U r c Y ∈ inverseNeighbors U r c (graphUnderlying U r c X) ↔
      Y ∈ (incomingDefects U r c X).image Sum.inr := by
  classical
  constructor
  · intro hh
    unfold inverseNeighbors at hh
    split_ifs at hh with ht
    · obtain ⟨⟨s,t⟩,hst,he⟩ := List.mem_map.mp hh
      have hst' := (List.mem_filter.mp hst).2
      simp only [decide_eq_true_eq] at hst'
      have hd := inverseRepair_defect U r c s t (graphUnderlying U r c X) hst'.1 hst'.2.1 hst'.2.2.1
      let Z : DefectiveState U r c := ⟨inverseRepair U r c s t (graphUnderlying U r c X),
        hst'.2.2.2,⟨s,t,hd⟩⟩
      have hy : Sum.inr Z=Y := graphUnderlying_injective U r c he
      have hx : Sum.inl (repairedState U r c Z)=X := by
        apply graphUnderlying_injective U r c
        change (repairedState U r c Z).val = _
        rw [repairedState_eq U r c s t Z hd]
        exact repair_inverseRepair U r c s t _ ht
      exact Finset.mem_image.mpr ⟨Z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,hy⟩
    · simp at hh
  · intro hh
    obtain ⟨Z,hZ,rfl⟩ := Finset.mem_image.mp hh
    have hx := (Finset.mem_filter.mp hZ).2
    rw [← hx]
    change Z.val ∈ inverseNeighbors U r c (repairedState U r c Z).val
    unfold inverseNeighbors
    rw [ite_eq_left (repairedState U r c Z).property.2]
    let s := (defectPair U r c Z).1
    let t := (defectPair U r c Z).2
    have hd : DefectAt U r c s t Z.val := defectPair_spec U r c Z
    have hi : inverseRepair U r c s t (repairedState U r c Z).val=Z.val :=
      inverseRepair_repair U r c s t Z.val hd
    apply List.mem_map.mpr
    refine ⟨(s,t),List.mem_filter.mpr ⟨mem_typeList _,?_⟩,hi⟩
    simp only [decide_eq_true_eq]
    exact ⟨hd.1,hd.2.1,hd.2.2.1,hi ▸ Z.property.1⟩

end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
variable {m n : ℕ} (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)

def smallList : List (SmallSlot U r c) :=
  (slotList m n).filterMap fun s => if hs : IsSmall U r c s then some ⟨s,hs⟩ else none

@[simp] theorem mem_smallList (s : SmallSlot U r c) : s ∈ smallList U r c := by
  apply List.mem_filterMap.mpr
  exact ⟨s.val,mem_slotList _,by simp [s.property]⟩

theorem length_smallList : (smallList U r c).length ≤ m*n := by
  simpa only [smallList,length_slotList] using List.length_filterMap_le
    (f:=fun s => if hs : IsSmall U r c s then some (⟨s,hs⟩ : SmallSlot U r c) else none)
    (l:=slotList m n)

def coordList : List (SmallCoord U r c) := (smallList U r c).product [false,true]

@[simp] theorem mem_coordList (i : SmallCoord U r c) : i ∈ coordList U r c := by
  rcases i with ⟨s,b⟩; cases b <;> simp [coordList]

theorem length_coordList : (coordList U r c).length ≤ 2*(m*n) := by
  have hh := length_smallList U r c
  change ((smallList U r c) ×ˢ [false,true]).length ≤ _
  rw [List.length_product]
  simp only [List.length_cons,List.length_nil]
  omega

def allowedState (X : State m n) : Prop :=
  Feasible U r c X ∧ (Transversal X ∨ ∃ s t, DefectAt U r c s t X)

instance allowedStateDecidable (X : State m n) : Decidable (allowedState U r c X) := by
  unfold allowedState; infer_instance

theorem graph_allowed (X : GraphState U r c) : allowedState U r c (graphUnderlying U r c X) := by
  cases X with
  | inl X => exact ⟨X.property.1,Or.inl X.property.2⟩
  | inr X => exact ⟨X.property.1,Or.inr X.property.2⟩

 

def localExchange (X : State m n) (i j : SmallCoord U r c) : State m n :=
  let v := fun w : SmallCoord U r c =>
    (if w.2 then X.x w.1.val else (U:ℤ)-X.q w.1.val) +
      (if w=i then 1 else 0) - (if w=j then 1 else 0)
  ⟨fun w => if hw : IsSmall U r c w then v (⟨w,hw⟩,true) else 0,
   fun w => if hw : IsSmall U r c w then (U:ℤ)-v (⟨w,hw⟩,false) else 0⟩

theorem localExchange_eq (X : State m n) (i j : SmallCoord U r c) :
    localExchange U r c X i j = coordinatesState U r c
      (fun w => stateCoordinates U r c X w + (if w=i then 1 else 0) - (if w=j then 1 else 0)) := rfl

theorem localExchange_coordinates (X : State m n) (i j : SmallCoord U r c) :
    stateCoordinates U r c (localExchange U r c X i j) =
      fun w => stateCoordinates U r c X w + (if w=i then 1 else 0) - (if w=j then 1 else 0) := by
  rw [localExchange_eq,stateCoordinates_coordinatesState]

def unitNeighbors (X : State m n) : List (State m n) :=
  (((coordList U r c).product (coordList U r c)).filter fun ij =>
    ij.1 ≠ ij.2 ∧ allowedState U r c (localExchange U r c X ij.1 ij.2)).map
      fun ij => localExchange U r c X ij.1 ij.2

theorem length_unitNeighbors (X : State m n) :
    (unitNeighbors U r c X).length ≤ 4*(m*n)^2 := by
  have hh := List.length_filter_le
    (p:=fun ij : SmallCoord U r c × SmallCoord U r c => decide
      (ij.1 ≠ ij.2 ∧ allowedState U r c (localExchange U r c X ij.1 ij.2)))
    ((coordList U r c).product (coordList U r c))
  have hc := length_coordList U r c
  change _ ≤ ((coordList U r c) ×ˢ (coordList U r c)).length at hh
  rw [List.length_product] at hh
  simp only [unitNeighbors,List.length_map]
  nlinarith

theorem unitNeighbors_allowed (X Y : State m n) (h : Y ∈ unitNeighbors U r c X) :
    allowedState U r c Y := by
  obtain ⟨ij,hij,rfl⟩ := List.mem_map.mp h
  exact (of_decide_eq_true (List.mem_filter.mp hij).2).2

theorem graph_vertex (X : GraphState U r c) : graphCoordinates U r c X ∈ fullVertices U r c := by
  cases X with
  | inl X => exact stateCoordinates_transverse_vertex U r c X
  | inr X => exact stateCoordinates_defect_vertex U r c X

theorem unitEdge_of_exchange (X Y : GraphState U r c) (i j : SmallCoord U r c)
    (hij : i ≠ j) (he : graphCoordinates U r c Y =
      fun w => graphCoordinates U r c X w+(if w=i then 1 else 0)-(if w=j then 1 else 0)) :
    s(graphCoordinates U r c X,graphCoordinates U r c Y) ∈ fullUnitEdges U r c := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mk_mem_sym2_iff.mpr ⟨graph_vertex U r c X,graph_vertex U r c Y⟩,?_⟩
  let D := fun w => graphCoordinates U r c X w+(if w=i then 1 else 0)
  have hi : removeOne D i=graphCoordinates U r c X := by funext w; simp [D,removeOne]
  have hj : removeOne D j=graphCoordinates U r c Y := by rw [he]; rfl
  exact ⟨D,i,j,hij,by rw [hi,hj]⟩

 

theorem mem_unitNeighbors (X Y : GraphState U r c) :
    graphUnderlying U r c Y ∈ unitNeighbors U r c (graphUnderlying U r c X) ↔
    s(graphCoordinates U r c X,graphCoordinates U r c Y) ∈ fullUnitEdges U r c := by
  classical
  constructor
  · intro hh
    obtain ⟨⟨i,j⟩,hij,he⟩ := List.mem_map.mp hh
    have h := of_decide_eq_true (List.mem_filter.mp hij).2
    apply unitEdge_of_exchange U r c X Y i j h.1
    change stateCoordinates U r c (graphUnderlying U r c Y) = _
    rw [← he,localExchange_coordinates]
    rfl
  · intro hh
    obtain ⟨_,D,i,j,hij,he⟩ := Finset.mem_filter.mp hh
    have mk (i j : SmallCoord U r c) (hij : i ≠ j)
        (h : graphCoordinates U r c Y = fun w => graphCoordinates U r c X w+
          (if w=i then 1 else 0)-(if w=j then 1 else 0)) :
        graphUnderlying U r c Y ∈ unitNeighbors U r c (graphUnderlying U r c X) := by
      have he : localExchange U r c (graphUnderlying U r c X) i j=graphUnderlying U r c Y := by
        rw [localExchange_eq]
        change coordinatesState U r c (fun w => graphCoordinates U r c X w+_ - _) = _
        rw [← h]
        exact coordinates_state_inverse U r c _ (graph_feasible U r c Y).2.1
      apply List.mem_map.mpr
      refine ⟨(i,j),List.mem_filter.mpr ⟨List.mem_product.mpr ⟨mem_coordList U r c i,mem_coordList U r c j⟩,?_⟩,he⟩
      simp only [decide_eq_true_eq]
      exact ⟨hij,he ▸ graph_allowed U r c Y⟩
    rcases Sym2.eq_iff.mp he with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · apply mk i j hij
      funext w; rw [hx,hy]; simp only [removeOne]; ring
    · apply mk j i hij.symm
      funext w; rw [hx,hy]; simp only [removeOne]; ring

end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency.PaddedGraph
variable {m n : ℕ} (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)

 

def localRepair (s t : Cell m n) (X : State m n) : State m n :=
  let x' := fun w => X.x w-unit t w+
    if IsSmall U r c (receiver s t) then unit (receiver s t) w else 0
  ⟨x',x'⟩

theorem localRepair_eq (s t : Cell m n) (X : State m n) :
    localRepair U r c s t X=repair U r c s t X := rfl

 
def findDefect (X : State m n) : Option (Cell m n × Cell m n) :=
  (typeList m n).find? fun st => DefectAt U r c st.1 st.2 X

theorem findDefect_some (X : State m n) (st : Cell m n × Cell m n)
    (h : findDefect U r c X=some st) : DefectAt U r c st.1 st.2 X :=
  of_decide_eq_true (List.find?_some
    (p:=fun ij : Cell m n × Cell m n => decide (DefectAt U r c ij.1 ij.2 X)) h)

theorem findDefect_none (X : State m n) :
    findDefect U r c X=none ↔ ∀ s t, ¬DefectAt U r c s t X := by
  rw [findDefect,List.find?_eq_none]
  simp only [mem_typeList,decide_eq_true_eq,true_implies,Prod.forall]

theorem findDefect_transverse (X : TransverseState U r c) : findDefect U r c X.val=none := by
  apply (findDefect_none U r c X.val).mpr
  intro s t h
  exact defect_not_transversal U r c s t X.val h X.property.2

theorem findDefect_defective (X : DefectiveState U r c) :
    findDefect U r c X.val=some (defectPair U r c X) := by
  cases he : findDefect U r c X.val with
  | none =>
    have hh := (findDefect_none U r c X.val).mp he
    exact (hh _ _ (defectPair_spec U r c X)).elim
  | some st =>
    have hd := findDefect_some U r c X.val st he
    obtain ⟨hs,ht⟩ := defect_type_unique U r c X.val st.1 st.2 _ _ hd (defectPair_spec U r c X)
    rw [Prod.ext hs ht]

def localOutgoing (X : State m n) : List (State m n) :=
  match findDefect U r c X with
  | none => []
  | some st => [localRepair U r c st.1 st.2 X]

theorem length_localOutgoing (X : State m n) : (localOutgoing U r c X).length≤1 := by
  unfold localOutgoing
  split <;> simp

theorem localOutgoing_transverse (X : TransverseState U r c) :
    localOutgoing U r c X.val=[] := by rw [localOutgoing,findDefect_transverse]

theorem localOutgoing_defective (X : DefectiveState U r c) :
    localOutgoing U r c X.val=[(repairedState U r c X).val] := by
  rw [localOutgoing,findDefect_defective]; rfl

theorem mem_localOutgoing (X Y : GraphState U r c) :
    graphUnderlying U r c Y ∈ localOutgoing U r c (graphUnderlying U r c X) ↔
      Y ∈ outgoing U r c X := by
  classical
  cases X with
  | inl X => simp [graphUnderlying,localOutgoing_transverse,outgoing]
  | inr X =>
    change graphUnderlying U r c Y ∈ localOutgoing U r c X.val ↔ _
    rw [localOutgoing_defective]
    simp only [List.mem_singleton,outgoing,Finset.mem_singleton]
    exact (graphUnderlying_injective U r c).eq_iff (a:=Y) (b:=Sum.inl (repairedState U r c X))

theorem repairAdj_iff (X Y : GraphState U r c) :
    s(graphCoordinates U r c X,graphCoordinates U r c Y)∈fullRepairEdges U r c ↔
      Y ∈ outgoing U r c X ∨ Y ∈ (incomingDefects U r c X).image Sum.inr := by
  classical
  constructor
  · intro hh
    obtain ⟨Z,_,he⟩ := Finset.mem_image.mp hh
    rcases Sym2.eq_iff.mp he with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · have hx' : Sum.inr Z=X := graphCoordinates_injective U r c hx
      have hy' : Sum.inl (repairedState U r c Z)=Y := graphCoordinates_injective U r c hy
      left
      rw [← hx',← hy']; simp [outgoing]
    · have hx' : Sum.inr Z=Y := graphCoordinates_injective U r c hx
      have hy' : Sum.inl (repairedState U r c Z)=X := graphCoordinates_injective U r c hy
      right
      exact Finset.mem_image.mpr ⟨Z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy'⟩,hx'⟩
  · intro hh
    rcases hh with ho | hi
    · cases X with
      | inl X => simp [outgoing] at ho
      | inr X =>
        simp only [outgoing,Finset.mem_singleton] at ho
        subst Y
        exact Finset.mem_image.mpr ⟨X,Finset.mem_univ _,rfl⟩
    · obtain ⟨Z,hZ,rfl⟩ := Finset.mem_image.mp hi
      have hx := (Finset.mem_filter.mp hZ).2
      rw [← hx]
      exact Finset.mem_image.mpr ⟨Z,Finset.mem_univ _,Sym2.eq_swap⟩

 

def localNeighbors (X : State m n) : List (State m n) :=
  (unitNeighbors U r c X ++ localOutgoing U r c X ++ inverseNeighbors U r c X).dedup

theorem localNeighbors_nodup (X : State m n) : (localNeighbors U r c X).Nodup :=
  List.nodup_dedup _

theorem length_localNeighbors (X : State m n) :
    (localNeighbors U r c X).length≤5*(m*n)^2+1 := by
  have hh := (List.dedup_sublist
    (unitNeighbors U r c X ++ localOutgoing U r c X ++ inverseNeighbors U r c X)).length_le
  have hu := length_unitNeighbors U r c X
  have ho := length_localOutgoing U r c X
  have hi := length_inverseNeighbors U r c X
  simp only [List.length_append] at hh
  exact hh.trans (by omega)

 

theorem mem_localNeighbors (X Y : GraphState U r c) :
    graphUnderlying U r c Y ∈ localNeighbors U r c (graphUnderlying U r c X) ↔
      GraphAdj U r c X Y := by
  classical
  simp only [localNeighbors,List.mem_dedup,List.mem_append,mem_unitNeighbors,
    mem_localOutgoing,mem_inverseNeighbors,GraphAdj,fullEdges,Finset.mem_union,repairAdj_iff]
  exact or_assoc

theorem localNeighbors_allowed (X : GraphState U r c) (Y : State m n)
    (h : Y ∈ localNeighbors U r c (graphUnderlying U r c X)) : allowedState U r c Y := by
  simp only [localNeighbors,List.mem_dedup,List.mem_append] at h
  rcases h with (hu | ho) | hi
  · exact unitNeighbors_allowed U r c _ _ hu
  · cases X with
    | inl X => simp [graphUnderlying,localOutgoing_transverse] at ho
    | inr X =>
      change Y ∈ localOutgoing U r c X.val at ho
      rw [localOutgoing_defective] at ho
      have he := List.mem_singleton.mp ho
      rw [he]
      exact graph_allowed U r c (Sum.inl (repairedState U r c X))
  · unfold inverseNeighbors at hi
    split_ifs at hi
    · obtain ⟨⟨s,t⟩,hst,rfl⟩ := List.mem_map.mp hi
      have hh := of_decide_eq_true (List.mem_filter.mp hst).2
      exact ⟨hh.2.2.2,Or.inr ⟨s,t,inverseRepair_defect U r c s t _ hh.1 hh.2.1 hh.2.2.1⟩⟩
    · simp at hi

end Contingency.PaddedGraph

 

 

open scoped BigOperators
namespace Contingency
namespace IntegerDraw
variable {α : Type*}

def unitWeights (xs : List α) : List (α×ℕ) := xs.map fun x => (x,1)

theorem unitWeights_total (xs : List α) : total (unitWeights xs)=xs.length := by
  induction xs with
  | nil => simp [unitWeights,total]
  | cons x xs ih =>
    change 1 + total (unitWeights xs) = xs.length + 1
    rw [ih]; omega

theorem unitWeights_weight [DecidableEq α] (xs : List α) (h : xs.Nodup) (a : α) :
    weight (unitWeights xs) a = if a∈xs then 1 else 0 := by
  simp only [weight,unitWeights,List.map_map,Function.comp_def]
  rw [← List.sum_toFinset (fun x => if x=a then (1:ℕ) else 0) h]
  simp

end IntegerDraw
namespace PaddedGraph
variable {m n : ℕ} (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)

def graphStateOf (X : State m n) (h : allowedState U r c X) : GraphState U r c :=
  if ht : Transversal X then Sum.inl ⟨X,h.1,ht⟩ else Sum.inr ⟨X,h.1,h.2.resolve_left ht⟩

@[simp] theorem graphStateOf_underlying (X : State m n) (h : allowedState U r c X) :
    graphUnderlying U r c (graphStateOf U r c X h)=X := by
  unfold graphStateOf; split <;> rfl

 

def graphNeighborList (X : GraphState U r c) : List (GraphState U r c) :=
  (localNeighbors U r c (graphUnderlying U r c X)).attach.map fun Y =>
    graphStateOf U r c Y.val (localNeighbors_allowed U r c X Y.val Y.property)

theorem graphNeighborList_nodup (X : GraphState U r c) : (graphNeighborList U r c X).Nodup := by
  apply List.Nodup.map _ (localNeighbors_nodup U r c (graphUnderlying U r c X)).attach
  intro Y Z he
  apply Subtype.ext
  have hh := congrArg (graphUnderlying U r c) he
  simpa only [graphStateOf_underlying] using hh

@[simp] theorem mem_graphNeighborList (X Y : GraphState U r c) :
    Y ∈ graphNeighborList U r c X ↔ GraphAdj U r c X Y := by
  constructor
  · intro hh
    obtain ⟨Z,_,rfl⟩ := List.mem_map.mp hh
    apply (mem_localNeighbors U r c X _).mp
    simpa only [graphStateOf_underlying] using Z.property
  · intro hh
    have hY := (mem_localNeighbors U r c X Y).mpr hh
    apply List.mem_map.mpr
    refine ⟨⟨graphUnderlying U r c Y,hY⟩,List.mem_attach _ _,?_⟩
    apply graphUnderlying_injective U r c
    exact graphStateOf_underlying U r c _ _

theorem graphNeighborList_length (X : GraphState U r c) :
    (graphNeighborList U r c X).length≤5*(m*n)^2+1 := by
  simpa only [graphNeighborList,List.length_map,List.length_attach] using
    length_localNeighbors U r c (graphUnderlying U r c X)

theorem graphNeighborList_card (X : GraphState U r c) :
    (graphNeighborList U r c X).length=(Finset.univ.filter (GraphAdj U r c X)).card := by
  classical
  have he : (graphNeighborList U r c X).toFinset=Finset.univ.filter (GraphAdj U r c X) := by
    ext Y; simp
  rw [← he,List.toFinset_card_of_nodup (graphNeighborList_nodup U r c X)]

 

def selectLocalNeighbor (X : GraphState U r c) (z : ℕ) : GraphState U r c :=
  (IntegerDraw.scan (IntegerDraw.unitWeights (graphNeighborList U r c X)) z).getD X

noncomputable def localProposal (X : GraphState U r c) (R : ℕ) : DyadicLaw (GraphState U r c) :=
  (bitWordLaw R).map (fun z => selectLocalNeighbor U r c X z.val)

 

theorem localProposal_actual (X : GraphState U r c) (R : ℕ) :
    localProposal U r c X R=(bitWordLaw R).map (fun z => selectLocalNeighbor U r c X z.val) := rfl

theorem localProposal_count_offdiag (X Y : GraphState U r c) (R : ℕ)
    (hR : (graphNeighborList U r c X).length≤2^R) (hxy : X≠Y) :
    (localProposal U r c X R).count Y = if GraphAdj U r c X Y then 1 else 0 := by
  classical
  have hb : IntegerDraw.total (IntegerDraw.unitWeights (graphNeighborList U r c X))≤2^R := by
    simpa only [IntegerDraw.unitWeights_total] using hR
  rw [localProposal,DyadicLaw.map_count]
  change (∑ z : Fin (2^R), if
    (IntegerDraw.scan (IntegerDraw.unitWeights (graphNeighborList U r c X)) z.val).getD X=Y
    then 1 else 0)=_
  simp only [Option.getD_eq_iff,hxy,and_false,or_false]
  rw [Fin.sum_univ_eq_sum_range (fun z : ℕ => if
    IntegerDraw.scan (IntegerDraw.unitWeights (graphNeighborList U r c X)) z=some Y then (1:ℕ) else 0)]
  rw [IntegerDraw.scan_count_padded _ _ _ hb,
    IntegerDraw.unitWeights_weight _ (graphNeighborList_nodup U r c X)]
  simp only [mem_graphNeighborList]

 

theorem localProposal_toLaw (X : GraphState U r c) (R : ℕ)
    (hb : (Finset.univ.filter (GraphAdj U r c X)).card≤2^R) :
    (localProposal U r c X R).toLaw=
      (DyadicLaw.neighborProposal (GraphAdj U r c) X R (GraphAdj.irrefl U r c X) hb).toLaw := by
  classical
  apply Law.ext_offdiag _ _ X
  intro Y hxy
  rw [DyadicLaw.neighborProposal_offdiag _ _ _ _ _ _ hxy]
  change ((localProposal U r c X R).count Y:ℝ)/(2:ℝ)^(localProposal U r c X R).bits=_
  rw [localProposal_count_offdiag U r c X Y R (by rw [graphNeighborList_card]; exact hb) hxy]
  have hbits : (localProposal U r c X R).bits=R := by
    simp [localProposal,DyadicLaw.map_bits,bitWordLaw]
  rw [hbits]
  split_ifs <;> norm_cast

end PaddedGraph
end Contingency

end

end OAI
