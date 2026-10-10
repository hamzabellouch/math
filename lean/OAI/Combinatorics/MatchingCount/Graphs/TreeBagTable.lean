import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeParentTable

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck Polynomial

abbrev BagInput := HierarchyInput×List (ℕ×ℕ)

def edgeKey (x : HierarchyInput×(ℕ×ℕ)) : LabelKey :=
  let k:=level (x.1.2.length,cell (x.1.1,x.2))
  (k,labelRoot (x.1,(k,x.2.1)))
def edgeKeyRealizer : Realizer edgeKey := by
  let k : Realizer (fun x : HierarchyInput×(ℕ×ℕ)=>level (x.1.2.length,cell (x.1.1,x.2))) :=
    composition (pair (composition first.snd listLength) (composition (pair first.fst second) cellRealizer)) levelRealizer
  exact (pair k (composition (pair first (pair k second.fst)) labelRootRealizer)).congr (fun _=>rfl)
lemma polynomial_edgeKey : PolynomialTime edgeKeyRealizer := by
  unfold edgeKeyRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_labelRoot
  have := polynomial_level
  have := polynomial_cell
  tree_cost

def incident (x : ℕ×(ℕ×ℕ)) : Bool := decide (x.1=x.2.1 ∨ x.1=x.2.2)
def incidentRealizer : Realizer incident :=
  (composition (pair (composition (pair first second.fst) natEqual)
    (composition (pair first second.snd) natEqual)) boolOr).congr (fun _=>by simp only [incident,Bool.decide_or,Function.comp_apply])
lemma polynomial_incident : PolynomialTime incidentRealizer := by
  unfold incidentRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  tree_cost

def edgeIndex (x : (HierarchyInput×List LabelKey)×(ℕ×ℕ)) : ℕ :=
  x.1.2.idxOf (edgeKey (x.1.1,x.2))
def edgeIndexRealizer : Realizer edgeIndex := composition
  (pair (composition (pair first.fst second) edgeKeyRealizer) first.snd) (indexOf (pairEqual natEqual natEqual))
lemma polynomial_edgeIndex : PolynomialTime edgeIndexRealizer := by
  unfold edgeIndexRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_fst polynomial_first) polynomial_second) polynomial_edgeKey)
    (polynomial_snd polynomial_first)) (polynomial_indexOf (polynomial_pairEqual polynomial_natEqual polynomial_natEqual))

def bag (x : BagInput×ℕ) : List ℕ :=
  ((x.1.2.filter fun e=>incident (x.2,e)).map fun e=>edgeIndex ((x.1.1,labels x.1.1),e)).dedup
def bagRealizer : Realizer bag :=
  (composition (composition (pair (pair first.fst (composition first.fst labelsRealizer))
    (composition (pair second first.snd) (filterWith incidentRealizer))) (mapWith edgeIndexRealizer)) (dedup natEqual)).congr (fun _=>rfl)
lemma polynomial_bag : PolynomialTime bagRealizer := by
  unfold bagRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_labels
  have := polynomial_filterWithList polynomial_incident
  have := polynomial_mapWith polynomial_edgeIndex
  have := polynomial_dedup polynomial_natEqual
  tree_cost

def bagTable (x : BagInput) : ExecutableDP.Bags := (List.range x.1.1.length).map fun v=>bag (x,v)
def bagTableRealizer : Realizer bagTable := composition
  (pair identity (composition (composition first.fst listLength) range)) (mapWith bagRealizer)
lemma polynomial_bagTable : PolynomialTime bagTableRealizer := by
  have hr : PolynomialTime (composition (composition (first (A:=HierarchyInput) (B:=List (ℕ×ℕ))).fst listLength) range) := by
    apply polynomial_boundedRange (polynomial_composition (polynomial_fst polynomial_first) polynomial_listLength) X
    intro x
    simpa using (list_length_le_weight x.1.1).trans ((weight_fst x.1).trans (weight_fst x))
  exact polynomial_composition (polynomial_pair polynomial_identity hr) (polynomial_mapWith polynomial_bag)

local instance {n H : ℕ} (B : Fin n→Fin n→ℚ) : LinearOrder (NumberedHierarchy.Label B H) := NumberedHierarchy.labelOrder B H
local instance (priority := 2000) {n H : ℕ} (B : Fin n→Fin n→ℚ) : LE (NumberedHierarchy.Label B H) := (NumberedHierarchy.labelOrder B H).toLE
lemma edgeKey_eq {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) {E : Type} [Fintype E] (left right : E→Fin n) (e : E) :
    edgeKey ((matrixRep B,xs),((left e).val,(right e).val))=
      key (NumberedHierarchy.edgeLabel B hsym htri left right xs.length e) := by
  unfold edgeKey
  rw [cell_matrixRep,level_repr _ _ (hB _ _)]
  apply Prod.ext
  · rfl
  exact labelRoot_matrixRep B hB xs (NumberedHierarchy.level xs.length (B (left e) (right e))) (left e)
lemma edgeIndex_eq {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (hsym : ∀ a b,B a b=B b a)
    (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (xs : List Bool) {E : Type} [Fintype E] (left right : E→Fin n) (e : E) :
    edgeIndex (((matrixRep B,xs),labels (matrixRep B,xs)),((left e).val,(right e).val))=
      ((UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length)).symm
        (NumberedHierarchy.edgeLabel B hsym htri left right xs.length e)).val := by
  unfold edgeIndex
  rw [edgeKey_eq B hB hsym htri xs left right e]
  exact index_key B hB xs (NumberedHierarchy.edgeLabel B hsym htri left right xs.length e)

end MatchingFPRAS.ExecutableHierarchy

end OAI
