import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeMarking

namespace OAI

namespace MatchingFPRAS.ExecutableMarking
open TreeTyped TreeFraction

variable {C E : Type} [Codec C] [Codec E] [LinearOrder E] [Inhabited E]

def zeroMarks (xs : Marks E) : Bool := xs.all (fun z=>decide (z.2=0))
def zeroMarksRealizer : Realizer (zeroMarks (E:=E)) :=
  (composition (map (composition (pair second (constant 0)) natEqual)) all).congr (by
    intro xs; simp only [zeroMarks,Function.comp_def,List.all_map,Function.id_def])
omit [Codec C] [LinearOrder E] [Inhabited E] in
lemma polynomial_zeroMarks : PolynomialTime (zeroMarksRealizer (E:=E)) := by
  unfold zeroMarksRealizer
  apply polynomial_congr
  have := polynomial_all
  tree_cost

def probeExpected (x : E×(E×ℕ)) : ℕ := if x.2.1=x.1 then 2 else 0
def probeExpectedRealizer (Eq : Realizer (fun x : E×E=>decide (x.1=x.2))) :
    Realizer (probeExpected (E:=E)) :=
  (choose (composition (pair second.fst first) Eq) (constant 2) (constant 0)).congr (by
    intro x; simp only [probeExpected,Function.comp_apply,decide_eq_true_eq])
omit [Codec C] [Inhabited E] in
lemma polynomial_probeExpected {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    (hE : PolynomialTime Eq) : PolynomialTime (probeExpectedRealizer Eq) := by
  unfold probeExpectedRealizer Realizer.fst
  apply polynomial_congr
  tree_cost

def probeFlag (x : E×Marks E) : Bool :=
  x.2.any (fun z=>decide (z.1=x.1)) && x.2.all (fun z=>decide (z.2=probeExpected (x.1,z)))
def probeFlagRealizer (Eq : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (probeFlag (E:=E)) :=
  (composition (pair (composition (mapWith (composition (pair second.fst first) Eq)) any)
    (composition (mapWith (composition (pair second.snd (probeExpectedRealizer Eq)) natEqual)) all)) boolAnd).congr (by
      intro x; simp only [probeFlag,Function.comp_def,List.any_map,List.all_map,Function.id_def])
omit [Codec C] [Inhabited E] in
lemma polynomial_probeFlag {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    (hE : PolynomialTime Eq) : PolynomialTime (probeFlagRealizer Eq) := by
  unfold probeFlagRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_probeExpected hE
  have := polynomial_all
  have := polynomial_any
  tree_cost

def weighted (q : C×E→Fraction) (x : C×Marks E) : Fraction :=
  product (x.2.map (fun z=>q (x.1,z.1)))
def weightedRealizer {q : C×E→Fraction} (Q : Realizer q) : Realizer (weighted q) :=
  (composition (mapWith (composition (pair first second.fst) Q)) productRealizer).congr (fun _=>rfl)
omit [LinearOrder E] [Inhabited E] in
lemma polynomial_weighted {q : C×E→Fraction} {Q : Realizer q} (hQ : PolynomialTime Q) :
    PolynomialTime (weightedRealizer Q) := by
  unfold weightedRealizer Realizer.fst
  apply polynomial_congr
  have := polynomial_product
  tree_cost

def observableA (x : Marks E) : Fraction := if zeroMarks x then (1,1) else (0,1)
def observableARealizer : Realizer (observableA (E:=E)) :=
  (choose zeroMarksRealizer (constant (1,1)) (constant (0,1))).congr (fun _=>rfl)
omit [Codec C] [LinearOrder E] [Inhabited E] in
lemma polynomial_observableA : PolynomialTime (observableARealizer (E:=E)) := by
  unfold observableARealizer
  apply polynomial_congr
  have := polynomial_zeroMarks (E:=E)
  tree_cost

def observableD (q : C×E→Fraction) (x : C×Marks E) : Fraction :=
  if zeroMarks x.2 then weighted q x else (0,1)
def observableDRealizer {q : C×E→Fraction} (Q : Realizer q) : Realizer (observableD q) :=
  (choose (composition second zeroMarksRealizer) (weightedRealizer Q) (constant (0,1))).congr (fun _=>rfl)
omit [LinearOrder E] [Inhabited E] in
lemma polynomial_observableD {q : C×E→Fraction} {Q : Realizer q} (hQ : PolynomialTime Q) :
    PolynomialTime (observableDRealizer Q) := by
  unfold observableDRealizer
  apply polynomial_congr
  have := polynomial_zeroMarks (E:=E)
  have := polynomial_weighted hQ
  tree_cost

def eraseMark (x : E×Marks E) : Marks E := x.2.filter (fun z=>decide (z.1≠x.1))
def eraseMarkRealizer (Eq : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (eraseMark (E:=E)) :=
  (filterWith (composition (composition (pair second.fst first) Eq) boolNot)).congr (by
    intro x; simp only [eraseMark,Function.comp_apply,decide_not])
omit [Codec C] [Inhabited E] in
lemma polynomial_eraseMark {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    (hE : PolynomialTime Eq) : PolynomialTime (eraseMarkRealizer Eq) := by
  unfold eraseMarkRealizer Realizer.fst
  apply polynomial_congr
  apply polynomial_filterWithList
  tree_cost

def observableProbe (q : C×E→Fraction) (x : C×(E×Marks E)) : Fraction :=
  if probeFlag x.2 then weighted q (x.1,eraseMark x.2) else (0,1)
def observableProbeRealizer {q : C×E→Fraction} (Q : Realizer q)
    (Eq : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (observableProbe q) :=
  (choose (composition second (probeFlagRealizer Eq))
    (composition (pair first (composition second (eraseMarkRealizer Eq))) (weightedRealizer Q)) (constant (0,1))).congr (fun _=>rfl)
omit [Inhabited E] in
lemma polynomial_observableProbe {q : C×E→Fraction} {Q : Realizer q}
    {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    (hQ : PolynomialTime Q) (hE : PolynomialTime Eq) : PolynomialTime (observableProbeRealizer Q Eq) := by
  unfold observableProbeRealizer
  apply polynomial_congr
  have := polynomial_probeFlag hE
  have := polynomial_eraseMark hE
  have := polynomial_weighted hQ
  tree_cost
end MatchingFPRAS.ExecutableMarking

end OAI
