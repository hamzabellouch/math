import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreePairTable
import OAI.Combinatorics.MatchingCount.Sampling.TreeOptionsAccept
import OAI.Combinatorics.MatchingCount.Machines.TreeRationalWeight

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped ExecutableOptions TreeFraction

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]
attribute [local instance] Transport.Sparse.finsetOrder

def pairStepTable (p : C×(E×V)→Bool) (q : C×(E×E)→Bool) (r : C×(E×(V×V))→Bool)
    (t : C×(E×E)→Bool) (w z : C×E→Fraction) (x : PairInput C E V) : Options (PairState E) :=
  accept (metropolisProbability (pairWeight w z)) (((x.1.1,x.2),x.2),pairTable p q r t x)
def pairStepRealizer {p : C×(E×V)→Bool} {q : C×(E×E)→Bool} {r : C×(E×(V×V))→Bool}
    {t : C×(E×E)→Bool} {w z : C×E→Fraction}
    (P : Realizer p) (Q : Realizer q) (R : Realizer r) (T : Realizer t) (W : Realizer w) (Z : Realizer z)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2)))
    (EqV : Realizer (fun x : V×V=>decide (x.1=x.2)))
    (LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))) : Realizer (pairStepTable p q r t w z) :=
  (composition (pair (pair (pair first.fst second) second) (pairTableRealizer P Q R T Eq Le EqV LeV))
    (acceptRealizer (metropolisProbabilityRealizer (pairWeightRealizer W Z)))).congr (fun _=>rfl)
lemma polynomial_pairStep {p : C×(E×V)→Bool} {q : C×(E×E)→Bool} {r : C×(E×(V×V))→Bool}
    {t : C×(E×E)→Bool} {w z : C×E→Fraction}
    {P : Realizer p} {Q : Realizer q} {R : Realizer r} {T : Realizer t} {W : Realizer w} {Z : Realizer z}
    {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    {Le : Realizer (fun x : E×E=>decide (x.1≤x.2))}
    {EqV : Realizer (fun x : V×V=>decide (x.1=x.2))}
    {LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))}
    (hP : PolynomialTime P) (hQ : PolynomialTime Q) (hR : PolynomialTime R) (hT : PolynomialTime T)
    (hW : PolynomialTime W) (hZ : PolynomialTime Z)
    (hE : PolynomialTime Eq) (hL : PolynomialTime Le) (hV : PolynomialTime EqV) (hlV : PolynomialTime LeV) :
    PolynomialTime (pairStepRealizer P Q R T W Z Eq Le EqV LeV) := by
  unfold pairStepRealizer Realizer.fst
  apply polynomial_congr
  have := polynomial_pairTable hP hQ hR hT hE hL hV hlV
  have := polynomial_accept (polynomial_metropolisProbability (polynomial_pairWeight hW hZ))
  tree_cost

def pairDraw (p : C×(E×V)→Bool) (q : C×(E×E)→Bool) (r : C×(E×(V×V))→Bool)
    (t : C×(E×E)→Bool) (w z : C×E→Fraction) (x : PairInput C E V×List Bool) : PairState E :=
  draw (∅,∅) (pairStepTable p q r t w z x.1,x.2)
def pairDrawRealizer {p : C×(E×V)→Bool} {q : C×(E×E)→Bool} {r : C×(E×(V×V))→Bool}
    {t : C×(E×E)→Bool} {w z : C×E→Fraction}
    (P : Realizer p) (Q : Realizer q) (R : Realizer r) (T : Realizer t) (W : Realizer w) (Z : Realizer z)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2)))
    (EqV : Realizer (fun x : V×V=>decide (x.1=x.2)))
    (LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))) : Realizer (pairDraw p q r t w z) :=
  (composition (pair (composition first (pairStepRealizer P Q R T W Z Eq Le EqV LeV)) second)
    (drawRealizer (∅,∅))).congr (fun _=>rfl)
lemma polynomial_pairDraw {p : C×(E×V)→Bool} {q : C×(E×E)→Bool} {r : C×(E×(V×V))→Bool}
    {t : C×(E×E)→Bool} {w z : C×E→Fraction}
    {P : Realizer p} {Q : Realizer q} {R : Realizer r} {T : Realizer t} {W : Realizer w} {Z : Realizer z}
    {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    {Le : Realizer (fun x : E×E=>decide (x.1≤x.2))}
    {EqV : Realizer (fun x : V×V=>decide (x.1=x.2))}
    {LeV : Realizer (fun x : V×V=>decide (x.1≤x.2))}
    (hP : PolynomialTime P) (hQ : PolynomialTime Q) (hR : PolynomialTime R) (hT : PolynomialTime T)
    (hW : PolynomialTime W) (hZ : PolynomialTime Z)
    (hE : PolynomialTime Eq) (hL : PolynomialTime Le) (hV : PolynomialTime EqV) (hlV : PolynomialTime LeV) :
    PolynomialTime (pairDrawRealizer P Q R T W Z Eq Le EqV LeV) := by
  unfold pairDrawRealizer
  apply polynomial_congr
  have := polynomial_pairStep hP hQ hR hT hW hZ hE hL hV hlV
  have := polynomial_draw ((∅,∅) : PairState E)
  tree_cost

variable [Fintype E] [Fintype V] (ends : E→Sym2 V)
attribute [local instance] Transport.Sparse.pmOrder
variable (hloop : ∀ e,¬(ends e).IsDiag) (hpar : ∀ e,(Finset.univ.filter (fun f=>ends f=ends e)).card≤2)
variable (p : C×(E×V)→Bool) (q : C×(E×E)→Bool) (r : C×(E×(V×V))→Bool)
    (t : C×(E×E)→Bool) (w z : C×E→Fraction) (c : C)
    (hp : ∀ e v,p (c,(e,v))=decide (v∈ends e)) (hq : ∀ e f,q (c,(e,f))=decide (ends e=ends f))
    (hr : ∀ e v w,r (c,(e,(v,w)))=decide (ends e=s(v,w)))
    (ht : ∀ e f,t (c,(e,f))=decide (∃ v,v∈ends e ∧ v∈ends f))
    (u v : E→ℚ) (hu : ∀ e,0<u e) (hv : ∀ e,0<v e)
    (hw : ∀ e,w (c,e)=TreeFraction.repr (u e)) (hz : ∀ e,z (c,e)=TreeFraction.repr (v e))
include hp hq hr ht hw hz in
omit [Codec E] [Codec V] [Codec C] in
lemma pairStep_eq [Codec E] [Codec V] [Codec C]
    (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e)) :
    pairStepTable p q r t w z ((c,(Finset.univ,Finset.univ)),pairRepr ends a)=
      ExecutableOptions.repr (pairRepr ends) (Transport.Sparse.pairStepTable ends hloop hpar u v hu hv a) := by
  unfold pairStepTable
  rw [pairTable_eq ends hloop hpar p q r t c hp hq hr ht]
  unfold Transport.Sparse.pairStepTable WeightedOptions.metropolisChoice
  refine accept_repr (pairRepr ends) (metropolisProbability (pairWeight w z)) (c,pairRepr ends a) a
    (Transport.Sparse.pairTable ends hloop hpar a) _ _ _ ?_
  intro b
  exact metropolisProbability_repr (pairRepr ends) (pairWeight w z) c _
    (fun b=>(Transport.Sparse.rationalPairWeight_pos ends u v hu hv b).le)
    (pairWeight_repr ends w z c u v (fun e=>(hu e).le) (fun e=>(hv e).le) hw hz) a b
include hp hq hr ht hw hz in
omit [Codec E] [Codec V] [Codec C] in
lemma pairDraw_eq [Codec E] [Codec V] [Codec C]
    (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e))
    {k : ℕ} (bits : Fin k→Bool) :
    pairDraw p q r t w z (((c,(Finset.univ,Finset.univ)),pairRepr ends a),List.ofFn bits)=
      pairRepr ends ((Transport.Sparse.pairStepTable ends hloop hpar u v hu hv a).draw k bits) := by
  unfold pairDraw
  rw [pairStep_eq ends hloop hpar p q r t w z c hp hq hr ht u v hu hv hw hz]
  exact draw_repr _ _ _ bits
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
