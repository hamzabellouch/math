import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeReachCorrect

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {A C : Type} [Codec A] [Codec C] [LinearOrder A]
attribute [local instance] Transport.Sparse.finsetOrder

variable (p : C×(A×A) → Bool)
def adjacent (x : (C×Finset A)×(A×A)) : Bool :=
  decide (x.2.1≠x.2.2) && (decide (x.2.1∈x.1.2) && (decide (x.2.2∈x.1.2) && p (x.1.1,x.2)))
variable {p}
def adjacentRealizer (P : Realizer p) (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (adjacent p) :=
  (composition (pair (composition (composition second E) boolNot)
    (composition (pair (composition (pair second.fst first.snd) (finsetMember E))
      (composition (pair (composition (pair second.snd first.snd) (finsetMember E))
        (composition (pair first.fst second) P)) boolAnd)) boolAnd)) boolAnd).congr (by
          intro x
          change (!decide (x.2.1=x.2.2) && _) = _
          apply Bool.eq_iff_iff.mpr
          simp only [adjacent, Function.comp_apply, Bool.and_eq_true,
            Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq])
lemma polynomial_adjacent {P : Realizer p} {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hP : PolynomialTime P) (hE : PolynomialTime E) : PolynomialTime (adjacentRealizer P E) := by
  unfold adjacentRealizer Realizer.fst Realizer.snd
  tree_poly

abbrev ComponentInput (C A : Type) := ((C×Finset A)×Finset A)×A

def component (x : ComponentInput C A) : Finset A :=
  x.1.2 ∩ FiniteReach.reach (adjacent p) (((x.1.1.1,x.1.2),x.1.1.2),{x.2})
def componentRealizer (P : Realizer p)
    (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (component (p:=p)) :=
  composition (pair first.snd (composition
    (pair (pair (pair first.fst.fst first.snd) first.fst.snd) (composition second finsetSingleton))
    (FiniteReach.reachRealizer (adjacentRealizer P E) E R))) (finsetInter E)
lemma polynomial_component {P : Realizer p}
    {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    (hP : PolynomialTime P) (hE : PolynomialTime E) (hR : PolynomialTime R) :
    PolynomialTime (componentRealizer P E R) := by
  unfold componentRealizer
  have hh:=FiniteReach.polynomial_reach (polynomial_adjacent hP hE) hE hR
  apply polynomial_composition _ (polynomial_finsetInter hE)
  apply polynomial_pair (polynomial_snd polynomial_first)
  apply polynomial_composition _ hh
  unfold Realizer.fst Realizer.snd
  tree_poly

def orderedSetEqual (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : Finset A×Finset A=>@decide (x.1=x.2) (LinearOrder.toDecidableEq x.1 x.2)) :=
  (finsetEqual E).congr (by intro x; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq])
lemma polynomial_orderedSetEqual {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (orderedSetEqual E) :=
  polynomial_congr _ (polynomial_finsetEqual hE)

def allComponents (x : (C×Finset A)×Finset A) : Finset (Finset A) :=
  x.2.image (fun a=>component (p:=p) (x,a))
def allComponentsRealizer (P : Realizer p)
    (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (allComponents (p:=p)) :=
  (composition (pair identity second) (finsetImageWith (componentRealizer P E R) (orderedSetEqual E) (colexLe E R))).congr (by
    intro x; ext a; simp only [Function.comp_apply,id_eq,allComponents,Finset.mem_image])
lemma polynomial_allComponents {P : Realizer p}
    {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    (hP : PolynomialTime P) (hE : PolynomialTime E) (hR : PolynomialTime R) :
    PolynomialTime (allComponentsRealizer P E R) := by
  unfold allComponentsRealizer
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair polynomial_identity polynomial_second)
  exact polynomial_finsetImageWith (polynomial_component hP hE hR) (polynomial_orderedSetEqual hE) (polynomial_colexLe hE hR)

def discrepancies (x : (C×Finset A)×(Finset A×Finset A)) : Finset (Finset A) :=
  (allComponents (p:=p) (x.1,x.2.1∪x.2.2)).filter (fun s=>¬s⊆x.2.1∩x.2.2)
def discrepanciesRealizer (P : Realizer p)
    (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (discrepancies (p:=p)) :=
  (composition (pair (composition second (finsetInter E))
    (composition (pair first (composition second (finsetUnion E R))) (allComponentsRealizer P E R)))
    (finsetFilterWith (composition (composition (pair second first) (finsetSubset E)) boolNot))).congr (by
      intro x
      simp only [discrepancies,Function.comp_apply,Bool.not_eq_true',decide_eq_false_iff_not])
lemma polynomial_discrepancies {P : Realizer p}
    {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    (hP : PolynomialTime P) (hE : PolynomialTime E) (hR : PolynomialTime R) :
    PolynomialTime (discrepanciesRealizer P E R) := by
  unfold discrepanciesRealizer
  have hh:=polynomial_allComponents hP hE hR
  apply polynomial_congr
  apply polynomial_composition
  · apply polynomial_pair
    · tree_poly
    · apply polynomial_composition _ hh
      tree_poly
  · tree_poly

omit [Codec A] [Codec C]
variable [Fintype A] {V : Type} [Fintype V] [DecidableEq V]
variable (ends : A → Sym2 V) (c : C)
variable (hp : ∀ a b,p (c,(a,b))=decide (∃ v,v∈ends a ∧ v∈ends b))
include hp
omit [Fintype A] in
lemma adjacent_eq (U : Finset A) (a b : A) :
    adjacent p ((c,U),(a,b))=decide ((Transport.overlayLineGraph (fun e v=>v∈ends e) U).Adj a b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [adjacent,Bool.and_eq_true,decide_eq_true_eq,hp]
  rfl
lemma component_eq (U : Finset A) (a : A) :
    component (p:=p) (((c,Finset.univ),U),a)=Transport.Sparse.component ends U a := by
  unfold component Transport.Sparse.component
  rw [FiniteReach.reach_closure _ (c,U) (adjacent_eq ends c hp U)]
lemma allComponents_eq (U : Finset A) :
    allComponents (p:=p) ((c,Finset.univ),U)=Transport.Sparse.allComponents ends U := by
  unfold allComponents Transport.Sparse.allComponents
  exact Finset.image_congr (fun a _=>component_eq ends c hp U a)
lemma discrepancies_eq (a b : Transport.PM (fun e v=>v∈ends e)) :
    discrepancies (p:=p) ((c,Finset.univ),(a.val,b.val))=Transport.Sparse.discrepancies ends a b := by
  unfold discrepancies Transport.Sparse.discrepancies
  dsimp only
  rw [allComponents_eq ends c hp]
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
