import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.TreeSparseComponents
import OAI.Combinatorics.MatchingCount.Machines.TreeLabelTable
import OAI.Combinatorics.MatchingCount.Graphs.TreeSwitchValid

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder

def pairSet (x : E×E) : Finset E := {x.1,x.2}
def pairSetRealizer (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2))) : Realizer (pairSet (E:=E)) :=
  (composition (pair first (composition second finsetSingleton)) (finsetInsert Eq Le)).congr (fun _=>rfl)
lemma polynomial_pairSet {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    {Le : Realizer (fun x : E×E=>decide (x.1≤x.2))} (hEq : PolynomialTime Eq) (hLe : PolynomialTime Le) :
    PolynomialTime (pairSetRealizer Eq Le) := by
  unfold pairSetRealizer
  apply polynomial_congr
  tree_cost

def switchEdit (x : Finset E×Quad E) : Finset E :=
  (x.1\pairSet (x.2.1.1,x.2.2.1))∪pairSet (x.2.1.2,x.2.2.2)
def switchEditRealizer (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2))) : Realizer (switchEdit (E:=E)) :=
  (composition (pair (composition (pair first (composition (pair second.fst.fst second.snd.fst)
    (pairSetRealizer Eq Le))) (finsetSDiff Eq))
    (composition (pair second.fst.snd second.snd.snd) (pairSetRealizer Eq Le))) (finsetUnion Eq Le)).congr (fun _=>rfl)
lemma polynomial_switchEdit {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    {Le : Realizer (fun x : E×E=>decide (x.1≤x.2))} (hEq : PolynomialTime Eq) (hLe : PolynomialTime Le) :
    PolynomialTime (switchEditRealizer Eq Le) := by
  unfold switchEditRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_pairSet hEq hLe
  tree_cost

abbrev RawSwitchInput (C E V : Type) := (C×(Finset V×Finset E))×Finset E
def switchList (p : C×(E×(V×V))→Bool) (x : RawSwitchInput C E V) : List (Quad V×Quad E) :=
  ((quads (x.1.2.1.sort (·≤·))).product (quads (x.1.2.2.sort (·≤·)))).filter
    (fun q=>switchValid p ((x.1.1,x.2),q))
def switchListRealizer {p : C×(E×(V×V))→Bool} (P : Realizer p)
    (EqE : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (EqV : Realizer (fun x : V×V=>decide (x.1=x.2)))
    (LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))) : Realizer (switchList p) :=
  (composition (pair (pair first.fst second)
    (composition (pair (composition (composition first.snd.fst finsetList) quadsRealizer)
      (composition (composition first.snd.snd finsetList) quadsRealizer)) listProduct))
    (filterWith (switchValidRealizer P EqE EqV LeV))).congr (fun _=>rfl)
lemma polynomial_switchList {p : C×(E×(V×V))→Bool} {P : Realizer p}
    {EqE : Realizer (fun x : E×E=>decide (x.1=x.2))}
    {EqV : Realizer (fun x : V×V=>decide (x.1=x.2))}
    {LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))}
    (hP : PolynomialTime P) (hE : PolynomialTime EqE) (hV : PolynomialTime EqV) (hlV : PolynomialTime LeV) :
    PolynomialTime (switchListRealizer P EqE EqV LeV) := by
  unfold switchListRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_quads (A:=E)
  have := polynomial_quads (A:=V)
  have := polynomial_listProduct (A:=Quad V) (B:=Quad E)
  have hh := polynomial_filterWithList (polynomial_switchValid hP hE hV hlV)
  apply polynomial_composition _ hh
  tree_cost

def switchRaw (p : C×(E×(V×V))→Bool) (x : RawSwitchInput C E V) : Finset (Finset E) :=
  ((switchList p x).map fun q=>switchEdit (x.2,q.2)).toFinset

def switchRawRealizer {p : C×(E×(V×V))→Bool} (P : Realizer p)
    (EqE : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (LeE : Realizer (fun x : E×E=>decide (x.1≤x.2)))
    (EqV : Realizer (fun x : V×V=>decide (x.1=x.2)))
    (LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))) : Realizer (switchRaw p) :=
  (composition (composition (pair second (switchListRealizer P EqE EqV LeV))
    (mapWith (composition (pair first second.snd) (switchEditRealizer EqE LeE))))
    (listFinset (orderedSetEqual EqE) (colexLe EqE LeE))).congr (by
      intro x; ext a; simp only [Function.comp_apply, List.mem_toFinset, switchRaw])
lemma polynomial_switchRaw {p : C×(E×(V×V))→Bool} {P : Realizer p}
    {EqE : Realizer (fun x : E×E=>decide (x.1=x.2))}
    {LeE : Realizer (fun x : E×E=>decide (x.1≤x.2))}
    {EqV : Realizer (fun x : V×V=>decide (x.1=x.2))}
    {LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))}
    (hP : PolynomialTime P) (hE : PolynomialTime EqE) (hlE : PolynomialTime LeE)
    (hV : PolynomialTime EqV) (hlV : PolynomialTime LeV) :
    PolynomialTime (switchRawRealizer P EqE LeE EqV LeV) := by
  unfold switchRawRealizer Realizer.snd
  apply polynomial_congr
  have := polynomial_switchList hP hE hV hlV
  have := polynomial_switchEdit hE hlE
  have := polynomial_listFinset (polynomial_orderedSetEqual hE) (polynomial_colexLe hE hlE)
  tree_cost

omit [Codec E] [Codec V] [Codec C] in
lemma switchRaw_eq [Fintype E] [Fintype V] (ends : E→Sym2 V)
    (p : C×(E×(V×V))→Bool) (c : C)
    (hp : ∀ e v w,p (c,(e,(v,w)))=decide (ends e=s(v,w))) (M : Finset E) :
    switchRaw p ((c,(Finset.univ,Finset.univ)),M)=Transport.Sparse.switchRaw ends M := by
  ext B
  simp only [switchRaw,List.mem_toFinset,List.mem_map,switchList,List.mem_filter]
  constructor
  · rintro ⟨⟨v,e⟩,⟨_,hv⟩,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(quadFn v,quadFn e),(switchValid_eq ends p c hp M (v,e)).mp hv,?_⟩
    rfl
  · intro h
    obtain ⟨⟨v,e⟩,hpatt,rfl⟩:=Finset.mem_image.mp h
    refine ⟨(quadOfFn v,quadOfFn e),⟨?_,?_⟩,rfl⟩
    · rw [mem_listProduct,mem_quads,mem_quads]
      simp only [Finset.mem_sort,Finset.mem_univ,implies_true,and_self]
    · apply (switchValid_eq ends p c hp M (quadOfFn v,quadOfFn e)).mpr
      simpa only [quadFn_ofFn] using hpatt
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
