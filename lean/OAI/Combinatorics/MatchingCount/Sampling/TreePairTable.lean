import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.TreeSparseNeighbors
import OAI.Combinatorics.MatchingCount.Graphs.TreeCycleTable

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped ExecutableOptions

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder
abbrev PairInput (C E V : Type) := (C×(Finset V×Finset E))×PairState E

def pairTable (p : C×(E×V)→Bool) (q : C×(E×E)→Bool) (r : C×(E×(V×V))→Bool)
    (t : C×(E×E)→Bool) (x : PairInput C E V) : Options (PairState E) :=
  mix ((1,3),(ExecutableOptions.map (fun y : Finset E×Finset E=>(y.2,y.1))
    (x.2.2,switchTable p r (x.1,x.2.1)),
    mix ((1,2),(ExecutableOptions.map (fun y : Finset E×Finset E=>(y.2,y.1))
      (x.2.2,colorTable p q (x.1,x.2.1)),cycleTable t ((x.1.1,x.1.2.2),x.2)))))
def pairTableRealizer {p : C×(E×V)→Bool} {q : C×(E×E)→Bool} {r : C×(E×(V×V))→Bool}
    {t : C×(E×E)→Bool} (P : Realizer p) (Q : Realizer q) (R : Realizer r) (T : Realizer t)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2)))
    (EqV : Realizer (fun x : V×V=>decide (x.1=x.2)))
    (LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))) : Realizer (pairTable p q r t) :=
  (composition (pair (constant (1,3)) (pair
    (composition (pair second.snd (composition (pair first second.fst) (switchTableRealizer P R Eq Le EqV LeV)))
      (mapRealizer (pair second first)))
    (composition (pair (constant (1,2)) (pair
      (composition (pair second.snd (composition (pair first second.fst) (colorTableRealizer P Q Eq Le)))
        (mapRealizer (pair second first)))
      (composition (pair (pair first.fst first.snd.snd) second) (cycleTableRealizer T Eq Le)))) mixRealizer)))
    mixRealizer).congr (fun _=>rfl)
lemma polynomial_pairTable {p : C×(E×V)→Bool} {q : C×(E×E)→Bool} {r : C×(E×(V×V))→Bool}
    {t : C×(E×E)→Bool} {P : Realizer p} {Q : Realizer q} {R : Realizer r} {T : Realizer t}
    {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    {Le : Realizer (fun x : E×E=>decide (x.1≤x.2))}
    {EqV : Realizer (fun x : V×V=>decide (x.1=x.2))}
    {LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))}
    (hP : PolynomialTime P) (hQ : PolynomialTime Q) (hR : PolynomialTime R) (hT : PolynomialTime T)
    (hE : PolynomialTime Eq) (hL : PolynomialTime Le) (hV : PolynomialTime EqV) (hlV : PolynomialTime LeV) :
    PolynomialTime (pairTableRealizer P Q R T Eq Le EqV LeV) := by
  unfold pairTableRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_colorTable hP hQ hE hL
  have := polynomial_switchTable hP hR hE hL hV hlV
  have := polynomial_cycleTable hT hE hL
  have := ExecutableOptions.polynomial_mix (A:=PairState E)
  have := ExecutableOptions.polynomial_map (polynomial_pair
    (polynomial_second (A:=Finset E) (B:=Finset E)) polynomial_first)
  tree_cost

variable [Fintype E] [Fintype V] (ends : E→Sym2 V)
attribute [local instance] Transport.Sparse.pmOrder
variable (hloop : ∀ e,¬(ends e).IsDiag) (hpar : ∀ e,(Finset.univ.filter (fun f=>ends f=ends e)).card≤2)
omit [Codec E] [Codec V] [Codec C] in
lemma pairTable_eq (p : C×(E×V)→Bool) (q : C×(E×E)→Bool) (r : C×(E×(V×V))→Bool)
    (t : C×(E×E)→Bool) (c : C)
    (hp : ∀ e v,p (c,(e,v))=decide (v∈ends e)) (hq : ∀ e f,q (c,(e,f))=decide (ends e=ends f))
    (hr : ∀ e v w,r (c,(e,(v,w)))=decide (ends e=s(v,w)))
    (ht : ∀ e f,t (c,(e,f))=decide (∃ v,v∈ends e ∧ v∈ends f))
    (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e)) :
    pairTable p q r t ((c,(Finset.univ,Finset.univ)),pairRepr ends a)=
      repr (pairRepr ends) (Transport.Sparse.pairTable ends hloop hpar a) := by
  unfold pairTable
  simp only [pairRepr]
  rw [switchTable_eq ends hloop hpar p r c hp hr,colorTable_eq ends hloop hpar p q c hp hq]
  have hc:=cycleTable_eq ends t c ht a
  rw [show pairRepr ends a=(a.1.val,a.2.val) from rfl] at hc
  rw [hc]
  rw [map_repr Subtype.val (pairRepr ends) (fun b=>(b,a.2)) _ a.2.val (fun _=>rfl),
    map_repr Subtype.val (pairRepr ends) (fun b=>(b,a.2)) _ a.2.val (fun _=>rfl)]
  have h3 : (1,3)=TreeFraction.repr ((1:ℚ)/3) := by norm_num [TreeFraction.repr]
  have h2 : (1,2)=TreeFraction.repr ((1:ℚ)/2) := by norm_num [TreeFraction.repr]
  rw [h3,h2]
  rw [mix_repr _ _ (by norm_num) (by norm_num),mix_repr _ _ (by norm_num) (by norm_num)]
  rfl
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
