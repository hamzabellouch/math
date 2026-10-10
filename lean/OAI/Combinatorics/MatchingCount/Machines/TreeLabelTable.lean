import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.TreeHierarchyRoot
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeDyadic

namespace OAI

namespace MatchingFPRAS.TreeTyped
lemma polynomial_filterWithList {A B : Type} [Codec A] [Codec B] {p : A×B→Bool}
    {P : Realizer p} (hP : PolynomialTime P) : PolynomialTime (filterWith P) := by
  unfold filterWith
  exact polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_mapWith (polynomial_pair polynomial_second hP))
      (polynomial_filter polynomial_second)) (polynomial_map polynomial_first))
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck Polynomial

abbrev LabelKey := ℕ×ℕ
abbrev HierarchyInput := Matrix×List Bool

def labelRoot (x : HierarchyInput×LabelKey) : ℕ :=
  root ((x.1.1,threshold (x.1.2,x.2.1)),x.2.2)
def labelRootRealizer : Realizer labelRoot := composition
  (pair (pair first.fst (composition (pair first.snd second.fst) thresholdRealizer)) second.snd) rootRealizer
lemma polynomial_labelRoot : PolynomialTime labelRootRealizer := by
  apply polynomial_composition _ polynomial_root
  apply polynomial_pair _ (polynomial_snd polynomial_second)
  exact polynomial_pair (polynomial_fst polynomial_first) (polynomial_composition
    (polynomial_pair (polynomial_snd polynomial_first) (polynomial_fst polynomial_second)) polynomial_threshold)

def fixedRoot (x : HierarchyInput×LabelKey) : Bool := decide (labelRoot x=x.2.2)
def fixedRootRealizer : Realizer fixedRoot := composition (pair labelRootRealizer second.snd) natEqual
lemma polynomial_fixedRoot : PolynomialTime fixedRootRealizer :=
  polynomial_composition (polynomial_pair polynomial_labelRoot (polynomial_snd polynomial_second)) polynomial_natEqual

def labels (x : HierarchyInput) : List LabelKey :=
  ((List.range (x.2.length+1)).flatMap fun k=>(List.range x.1.length).map fun v=>(k,v)).filter fun l=>fixedRoot (x,l)
def labelsRealizer : Realizer labels := by
  let ks : Realizer (fun x : HierarchyInput=>List.range (x.2.length+1)) :=
    composition (composition (composition second listLength) successor) range
  let vs : Realizer (fun x : HierarchyInput=>List.range x.1.length) :=
    composition (composition first listLength) range
  let row : Realizer (fun x : HierarchyInput×ℕ=>(List.range x.1.1.length).map fun v=>(x.2,v)) :=
    composition (pair second (composition first vs)) (mapWith (pair first second))
  exact (composition (pair identity (composition (composition (pair identity ks) (mapWith row)) flatten))
    (filterWith fixedRootRealizer)).congr (fun _=>rfl)
lemma polynomial_labels : PolynomialTime labelsRealizer := by
  have hk : PolynomialTime (composition (composition (composition (second (A:=Matrix) (B:=List Bool)) listLength) successor) range) := by
    apply polynomial_boundedRange (polynomial_composition (polynomial_composition polynomial_second polynomial_listLength) polynomial_successor) (X+1)
    intro x
    have h:=(list_length_le_weight x.2).trans (weight_snd x)
    simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,Function.comp_apply,Nat.succ_eq_add_one] using Nat.add_le_add_right h 1
  have hv : PolynomialTime (composition (composition (first (A:=Matrix) (B:=List Bool)) listLength) range) := by
    apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength) X
    intro x
    simpa using (list_length_le_weight x.1).trans (weight_fst x)
  unfold labelsRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ (polynomial_filterWithList polynomial_fixedRoot)
  apply polynomial_pair polynomial_identity
  apply polynomial_composition _ polynomial_flatten
  apply polynomial_composition (polynomial_pair polynomial_identity hk)
  apply polynomial_mapWith
  apply polynomial_composition _ (polynomial_mapWith (polynomial_pair polynomial_first polynomial_second))
  exact polynomial_pair polynomial_second (polynomial_composition polynomial_first hv)

lemma mem_labels (x : HierarchyInput) (l : LabelKey) :
    l∈labels x ↔ l.1≤x.2.length ∧ l.2<x.1.length ∧ labelRoot (x,l)=l.2 := by
  simp only [labels,List.mem_filter,List.mem_flatMap,List.mem_map,List.mem_range,fixedRoot,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨k,hk,v,hv,he⟩,hr⟩
    cases he
    exact ⟨by omega,hv,hr⟩
  · rintro ⟨hk,hv,hr⟩
    exact ⟨⟨l.1,by omega,l.2,hv,rfl⟩,hr⟩

lemma labelRoot_matrixRep {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0≤B a b)
    (xs : List Bool) (k : Fin (xs.length+1)) (a : Fin n) :
    labelRoot ((matrixRep B,xs),(k.val,a.val))=(NumberedHierarchy.root B ((2:ℚ)^k.val) a).val := by
  unfold labelRoot
  dsimp only
  rw [threshold_repr xs k.val (by omega)]
  exact root_matrixRep B hB _ (by positivity) a

end MatchingFPRAS.ExecutableHierarchy

end OAI
