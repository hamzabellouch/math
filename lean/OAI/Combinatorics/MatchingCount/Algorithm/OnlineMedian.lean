import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.SortedList
import OAI.Combinatorics.MatchingCount.Machines.TreeFastLookup

namespace OAI

namespace MatchingFPRAS.OnlineMedian
open TreeTyped TreeFraction

def relation (a b : Fraction) : Prop := a.1*b.2≤b.1*a.2
instance : DecidableRel relation := fun _ _=>inferInstanceAs (Decidable (_≤_))
def compareRealizer : TreeTyped.Realizer (fun x : Fraction×Fraction=>decide (relation x.1 x.2)) :=
  (composition (composition (pair second first) lessRealizer) boolNot).congr (by
    intro x
    change (!(decide (x.2.1*x.1.2<x.1.1*x.2.2)))=decide (x.1.1*x.2.2≤x.2.1*x.1.2)
    simp only [←decide_not,not_lt])
lemma polynomial_compare : PolynomialTime compareRealizer := by
  unfold compareRealizer; apply polynomial_congr
  exact polynomial_composition (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_less) polynomial_boolNot

lemma relation_repr (a b : ℚ) (ha : 0≤a) (hb : 0≤b) : relation (TreeFraction.repr a) (TreeFraction.repr b) ↔ a≤b := by
  have hl:=less_val (TreeFraction.repr b) (TreeFraction.repr a) b.pos a.pos
  rw [val_repr ha,val_repr hb] at hl
  have he : relation (TreeFraction.repr a) (TreeFraction.repr b) ↔ ¬b<a := by
    unfold relation
    have hlt : (TreeFraction.repr b).1*(TreeFraction.repr a).2 < (TreeFraction.repr a).1*(TreeFraction.repr b).2 ↔ b<a := by
      have := congrArg (fun b : Bool=>b=true) hl
      exact Iff.of_eq (by simpa only [TreeFraction.less,decide_eq_true_eq] using this)
    exact (not_lt).symm.trans (not_congr hlt)
  exact he.trans not_lt

def sorted (xs : List Fraction) : List Fraction := xs.insertionSort relation
def sortedRealizer : TreeTyped.Realizer sorted := insertionSort relation compareRealizer
lemma polynomial_sorted : PolynomialTime sortedRealizer := polynomial_insertionSort relation polynomial_compare

def median (xs : List Fraction) : Fraction := (sorted xs).getD (xs.length/2) (0,1)
def medianRealizer : TreeTyped.Realizer median :=
  composition (pair sortedRealizer (composition (pair listLength (constant 2)) quotient)) (getDFast (0,1))
lemma polynomial_median : PolynomialTime medianRealizer :=
  polynomial_composition (polynomial_pair polynomial_sorted
    (polynomial_composition (polynomial_pair polynomial_listLength (polynomial_constant _)) polynomial_quotient)) (polynomial_getDFast _)

lemma sorted_repr (xs : List ℚ) (hs : ∀ q∈xs,0≤q) :
    sorted (xs.map TreeFraction.repr)=(xs.mergeSort (·≤·)).map TreeFraction.repr := by
  rw [List.mergeSort_eq_insertionSort (·≤·)]
  symm
  apply List.map_insertionSort (·≤·) relation TreeFraction.repr xs
  intro a ha b hb
  exact (relation_repr a b (hs a ha) (hs b hb)).symm

lemma median_repr {k : ℕ} (x : Fin (2*k+1)→ℚ) (hx : ∀ i,0≤x i) :
    median (List.ofFn (fun i=>TreeFraction.repr (x i)))=TreeFraction.repr (Amplification.median x) := by
  rw [show List.ofFn (fun i=>TreeFraction.repr (x i))=(List.ofFn x).map TreeFraction.repr by rw [List.map_ofFn]; rfl]
  unfold median
  rw [sorted_repr _ (by intro q hq; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq; exact hx i)]
  rw [List.length_map,List.length_ofFn,show (2*k+1)/2=k by omega]
  change (List.map TreeFraction.repr ((List.ofFn x).mergeSort (·≤·))).getD k (TreeFraction.repr 0)=_
  rw [List.getD_map _ 0 TreeFraction.repr]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  rfl
end MatchingFPRAS.OnlineMedian

end OAI
