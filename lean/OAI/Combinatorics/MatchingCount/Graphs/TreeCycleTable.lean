import Mathlib
import OAI.Combinatorics.MatchingCount.Tapes.TreeSparseComponents
import OAI.Combinatorics.MatchingCount.Sampling.TreeOptionsFinite

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped ExecutableOptions

variable {E C : Type} [Codec E] [Codec C] [LinearOrder E]
attribute [local instance] Transport.Sparse.finsetOrder
abbrev PairState (E : Type) := Finset E×Finset E
abbrev CycleInput (C E : Type) := (C×Finset E)×PairState E

def exchange (x : PairState E×Finset E) : Finset E := (x.1.1\x.2)∪(x.1.2∩x.2)
def exchangeRealizer (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2))) : Realizer (exchange (E:=E)) :=
  (composition (pair (composition (pair first.fst second) (finsetSDiff Eq))
    (composition (pair first.snd second) (finsetInter Eq))) (finsetUnion Eq Le)).congr (fun _=>rfl)
lemma polynomial_exchange {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    {Le : Realizer (fun x : E×E=>decide (x.1≤x.2))} (hE : PolynomialTime Eq) (hL : PolynomialTime Le) :
    PolynomialTime (exchangeRealizer Eq Le) := by
  unfold exchangeRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  tree_cost

def cycle (p : C×(E×E)→Bool) (x : CycleInput C E×Finset E) : PairState E :=
  if x.2∈allComponents (p:=p) (x.1.1,x.1.2.1∪x.1.2.2) then
    (exchange (x.1.2,x.2),exchange ((x.1.2.2,x.1.2.1),x.2)) else x.1.2

def cycleRealizer {p : C×(E×E)→Bool} (P : Realizer p)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2))) : Realizer (cycle p) :=
  (choose (composition (pair second (composition (pair first.fst
    (composition first.snd (finsetUnion Eq Le))) (allComponentsRealizer P Eq Le)))
      (finsetMember (orderedSetEqual Eq)))
    (pair (composition (pair first.snd second) (exchangeRealizer Eq Le))
      (composition (pair (pair first.snd.snd first.snd.fst) second) (exchangeRealizer Eq Le)))
    first.snd).congr (by intro x; simp only [Function.comp_apply,decide_eq_true_eq,cycle])
lemma polynomial_cycle {p : C×(E×E)→Bool} {P : Realizer p}
    {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    {Le : Realizer (fun x : E×E=>decide (x.1≤x.2))}
    (hP : PolynomialTime P) (hE : PolynomialTime Eq) (hL : PolynomialTime Le) :
    PolynomialTime (cycleRealizer P Eq Le) := by
  unfold cycleRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_allComponents hP hE hL
  have := polynomial_orderedSetEqual hE
  have := polynomial_exchange hE hL
  tree_cost

def cycleTable (p : C×(E×E)→Bool) (x : CycleInput C E) : Options (PairState E) :=
  if (discrepancies (p:=p) x).card=0 then pure x.2 else
    ExecutableOptions.map (cycle p) (x,uniform (discrepancies (p:=p) x))
def cycleTableRealizer {p : C×(E×E)→Bool} (P : Realizer p)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2)))
    (Le : Realizer (fun x : E×E=>decide (x.1≤x.2))) : Realizer (cycleTable p) :=
  (choose (composition (pair (composition (discrepanciesRealizer P Eq Le) finsetCard) (constant 0)) natEqual)
    (composition second pureRealizer)
    (composition (pair identity (composition (discrepanciesRealizer P Eq Le) uniformRealizer))
      (mapRealizer (cycleRealizer P Eq Le)))).congr (by intro x; simp only [Function.comp_apply,decide_eq_true_eq,cycleTable,id_eq])
lemma polynomial_cycleTable {p : C×(E×E)→Bool} {P : Realizer p}
    {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    {Le : Realizer (fun x : E×E=>decide (x.1≤x.2))}
    (hP : PolynomialTime P) (hE : PolynomialTime Eq) (hL : PolynomialTime Le) :
    PolynomialTime (cycleTableRealizer P Eq Le) := by
  unfold cycleTableRealizer
  apply polynomial_congr
  have := polynomial_discrepancies hP hE hL
  have := ExecutableOptions.polynomial_pure (A:=PairState E)
  have := ExecutableOptions.polynomial_uniform (A:=Finset E)
  have := ExecutableOptions.polynomial_map (polynomial_cycle hP hE hL)
  tree_cost

variable [Fintype E] {V : Type} [Fintype V] [DecidableEq V]
variable (ends : E→Sym2 V) (p : C×(E×E)→Bool) (c : C)
variable (hp : ∀ a b,p (c,(a,b))=decide (∃ v,v∈ends a ∧ v∈ends b))
def pairRepr (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e)) : PairState E :=
  (a.1.val,a.2.val)
omit [Codec E] [Codec C] in
include hp in
lemma cycle_eq (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e)) (s : Finset E) :
    cycle p (((c,Finset.univ),pairRepr ends a),s)=pairRepr ends (Transport.Sparse.cycle ends a s) := by
  unfold cycle pairRepr
  rw [allComponents_eq ends c hp]
  unfold Transport.Sparse.cycle
  split_ifs <;> rfl
omit [Codec E] [Codec C] in
include hp in
lemma cycleTable_eq (a : Transport.PM (fun e v=>v∈ends e)×Transport.PM (fun e v=>v∈ends e)) :
    cycleTable p ((c,Finset.univ),pairRepr ends a)=repr (pairRepr ends) (Transport.Sparse.cycleTable ends a) := by
  unfold cycleTable
  rw [show discrepancies (p:=p) ((c,Finset.univ),pairRepr ends a)=Transport.Sparse.discrepancies ends a.1 a.2 from
    discrepancies_eq ends c hp a.1 a.2]
  unfold Transport.Sparse.cycleTable
  split_ifs with h hn hn
  · exact False.elim (Finset.card_pos.mpr hn |>.ne' h)
  · exact pure_repr _ _
  · rw [uniform_repr _ hn]
    exact map_repr id (pairRepr ends) _ _ ((c,Finset.univ),pairRepr ends a) (cycle_eq ends p c hp a) _
  · exfalso
    exact h (Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn))
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
