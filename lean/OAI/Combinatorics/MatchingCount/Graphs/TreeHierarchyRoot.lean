import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.Related2
import OAI.Combinatorics.MatchingCount.Machines.TreeBottleneckCorrect
import OAI.Combinatorics.MatchingCount.Complexity.TreeCostTactic

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck Polynomial

abbrev RootInput := (Matrix×Fraction)×ℕ

def related (x : RootInput×ℕ) : Bool :=
  decide (x.1.2=x.2) || !(TreeFraction.less (cell (x.1.1.1,(x.1.2,x.2)),x.1.1.2))
def relatedRealizer : Realizer related :=
  composition (pair (composition (pair first.snd second) natEqual)
    (composition (composition (pair
      (composition (pair first.fst.fst (pair first.snd second)) cellRealizer) first.fst.snd)
        lessRealizer) boolNot)) boolOr
lemma polynomial_related : PolynomialTime relatedRealizer := by
  unfold relatedRealizer Realizer.fst Realizer.snd
  have hc:=polynomial_cell
  have hl:=TreeFraction.polynomial_less
  apply polynomial_composition _ polynomial_boolOr
  apply polynomial_pair
  · apply polynomial_composition _ polynomial_natEqual
    tree_cost
  · apply polynomial_composition _ polynomial_boolNot
    apply polynomial_composition _ hl
    apply polynomial_pair
    · apply polynomial_composition _ hc
      tree_cost
    · tree_cost

def component (x : RootInput) : List ℕ := (List.range x.1.1.length).filter (fun y=>related (x,y))
def componentRealizer : Realizer component := composition
  (pair identity (composition (composition first.fst listLength) range)) (filterWith relatedRealizer)
lemma polynomial_component : PolynomialTime componentRealizer := by
  have hr : PolynomialTime (composition (composition (first (A:=Matrix×Fraction) (B:=ℕ)).fst listLength) range) := by
    apply polynomial_boundedRange (by unfold Realizer.fst; tree_cost) X
    intro x
    simpa using (list_length_le_weight x.1.1).trans ((weight_fst x.1).trans (weight_fst x))
  unfold componentRealizer
  have:=polynomial_related
  apply polynomial_composition _ (polynomial_filterWith this)
  exact polynomial_pair polynomial_identity hr

def root (x : RootInput) : ℕ := listMin (component x,x.1.1.length)
def rootRealizer : Realizer root := composition (pair componentRealizer
  (composition first.fst listLength)) listMinRealizer
lemma polynomial_root : PolynomialTime rootRealizer := by
  unfold rootRealizer
  apply polynomial_composition _ polynomial_listMin
  exact polynomial_pair polynomial_component (polynomial_composition (polynomial_fst polynomial_first) polynomial_listLength)

lemma related_matrixRep {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0≤B a b)
    (t : ℚ) (ht : 0≤t) (a b : Fin n) :
    related (((matrixRep B,TreeFraction.repr t),a.val),b.val)=decide (NumberedHierarchy.related B t a b) := by
  unfold related NumberedHierarchy.related
  rw [cell_matrixRep,TreeFraction.less_val _ _ (B a b).pos t.pos,
    TreeFraction.val_repr (hB a b),TreeFraction.val_repr ht]
  apply Bool.eq_iff_iff.mpr
  simp [Fin.ext_iff,not_lt]
lemma component_mem_matrixRep {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0≤B a b)
    (t : ℚ) (ht : 0≤t) (a b : Fin n) :
    b.val∈component ((matrixRep B,TreeFraction.repr t),a.val) ↔ b∈NumberedHierarchy.component B t a := by
  simp only [component,List.mem_filter,List.mem_range,matrixRep_length,
    related_matrixRep B hB t ht,decide_eq_true_eq,NumberedHierarchy.component,
    Finset.mem_filter,Finset.mem_univ,true_and]
  exact and_iff_right b.isLt
lemma root_matrixRep {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0≤B a b)
    (t : ℚ) (ht : 0≤t) (a : Fin n) :
    root ((matrixRep B,TreeFraction.repr t),a.val)=(NumberedHierarchy.root B t a).val := by
  apply le_antisymm
  · apply listMin_le
    exact (component_mem_matrixRep B hB t ht a _).mpr (NumberedHierarchy.root_mem B t a)
  · unfold root
    apply le_listMin (by rw [matrixRep_length]; exact Nat.le_of_lt (NumberedHierarchy.root B t a).isLt)
    intro v hv
    have hvlt : v<n := by
      have h:=List.mem_range.mp (List.mem_filter.mp hv).1
      simpa only [matrixRep_length] using h
    have hv' := (component_mem_matrixRep B hB t ht a ⟨v,hvlt⟩).mp hv
    exact Finset.min'_le _ _ hv'
end MatchingFPRAS.ExecutableHierarchy

end OAI
