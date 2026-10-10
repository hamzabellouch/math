import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreePairStep

namespace OAI

namespace MatchingFPRAS.ExecutablePair
open TreeTyped TreeFraction TreeTyped.SparseProgram

abbrev Context := List (ℕ×ℕ)×(List Fraction×List Fraction)
def endpoints (x : Context×ℕ) : ℕ×ℕ := x.1.1.getD x.2 (0,0)
def endpointsRealizer : Realizer endpoints := composition (pair first.fst second) (getDFast (0,0))
lemma polynomial_endpoints : PolynomialTime endpointsRealizer :=
  polynomial_composition (polynomial_pair (polynomial_fst polynomial_first) polynomial_second)
    (polynomial_getDFast (0,0))

def incident (x : (ℕ×ℕ)×ℕ) : Bool := decide (x.1.1=x.2 ∨ x.1.2=x.2)
def incidentRealizer : Realizer incident := (composition (pair
  (composition (pair first.fst second) natEqual) (composition (pair first.snd second) natEqual))
  boolOr).congr (by intro x; simp [incident])
lemma polynomial_incident : PolynomialTime incidentRealizer := by
  unfold incidentRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  tree_cost

def same (x : (ℕ×ℕ)×(ℕ×ℕ)) : Bool :=
  decide ((x.1.1=x.2.1 ∧ x.1.2=x.2.2) ∨ (x.1.1=x.2.2 ∧ x.1.2=x.2.1))
def sameRealizer : Realizer same := (composition (pair
  (composition (pair (composition (pair first.fst second.fst) natEqual)
    (composition (pair first.snd second.snd) natEqual)) boolAnd)
  (composition (pair (composition (pair first.fst second.snd) natEqual)
    (composition (pair first.snd second.fst) natEqual)) boolAnd)) boolOr).congr
    (by intro x; simp [same])
lemma polynomial_same : PolynomialTime sameRealizer := by
  unfold sameRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  tree_cost

def adjacent (x : (ℕ×ℕ)×(ℕ×ℕ)) : Bool :=
  incident (x.1,x.2.1) || incident (x.1,x.2.2)
def adjacentRealizer : Realizer adjacent := composition (pair
  (composition (pair first second.fst) incidentRealizer)
  (composition (pair first second.snd) incidentRealizer)) boolOr
lemma polynomial_adjacent : PolynomialTime adjacentRealizer := by
  unfold adjacentRealizer adjacent Realizer.fst Realizer.snd
  have := polynomial_incident
  tree_cost

def p (x : Context×(ℕ×ℕ)) : Bool := incident (endpoints (x.1,x.2.1),x.2.2)
def q (x : Context×(ℕ×ℕ)) : Bool := same (endpoints (x.1,x.2.1),endpoints (x.1,x.2.2))
def r (x : Context×(ℕ×(ℕ×ℕ))) : Bool := same (endpoints (x.1,x.2.1),x.2.2)
def t (x : Context×(ℕ×ℕ)) : Bool := adjacent (endpoints (x.1,x.2.1),endpoints (x.1,x.2.2))
def u (x : Context×ℕ) : Fraction := x.1.2.1.getD x.2 (0,1)
def v (x : Context×ℕ) : Fraction := x.1.2.2.getD x.2 (0,1)
def pRealizer : Realizer p := composition (pair (composition (pair first second.fst) endpointsRealizer) second.snd) incidentRealizer
def qRealizer : Realizer q := composition (pair (composition (pair first second.fst) endpointsRealizer)
  (composition (pair first second.snd) endpointsRealizer)) sameRealizer
def rRealizer : Realizer r := composition (pair (composition (pair first second.fst) endpointsRealizer) second.snd) sameRealizer
def tRealizer : Realizer t := composition (pair (composition (pair first second.fst) endpointsRealizer)
  (composition (pair first second.snd) endpointsRealizer)) adjacentRealizer
def uRealizer : Realizer u := composition (pair first.snd.fst second) (getDFast (0,1))
def vRealizer : Realizer v := composition (pair first.snd.snd second) (getDFast (0,1))
lemma polynomial_p : PolynomialTime pRealizer := by
  unfold pRealizer p Realizer.fst Realizer.snd
  have := polynomial_endpoints
  have := polynomial_incident
  tree_cost
lemma polynomial_q : PolynomialTime qRealizer := by
  unfold qRealizer q Realizer.fst Realizer.snd
  have := polynomial_endpoints
  have := polynomial_same
  tree_cost
lemma polynomial_r : PolynomialTime rRealizer := by
  unfold rRealizer r Realizer.fst Realizer.snd
  have := polynomial_endpoints
  have := polynomial_same
  tree_cost
lemma polynomial_t : PolynomialTime tRealizer := by
  unfold tRealizer t Realizer.fst Realizer.snd
  have := polynomial_endpoints
  have := polynomial_adjacent
  tree_cost
lemma polynomial_u : PolynomialTime uRealizer :=
  polynomial_composition
    (polynomial_pair (polynomial_fst (polynomial_snd polynomial_first)) polynomial_second)
    (polynomial_getDFast ((0,1) : Fraction))
lemma polynomial_v : PolynomialTime vRealizer :=
  polynomial_composition
    (polynomial_pair (polynomial_snd (polynomial_snd polynomial_first)) polynomial_second)
    (polynomial_getDFast ((0,1) : Fraction))

def draw := pairDraw p q r t u v
def drawRealizer : Realizer draw := pairDrawRealizer pRealizer qRealizer rRealizer tRealizer
  uRealizer vRealizer natEqual leNat natEqual leNat
lemma polynomial_draw : PolynomialTime drawRealizer :=
  polynomial_pairDraw polynomial_p polynomial_q polynomial_r polynomial_t polynomial_u polynomial_v
    polynomial_natEqual polynomial_leNat polynomial_natEqual polynomial_leNat
end MatchingFPRAS.ExecutablePair

end OAI
