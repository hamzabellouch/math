import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeBottleneck
import OAI.Combinatorics.MatchingCount.Sampling.TreeOptions

namespace OAI

namespace MatchingFPRAS.ExecutableOptions
open TreeTyped TreeFraction

variable {A C Ω : Type} [Codec A] [Codec C]

def accept (p : C×A→Fraction) (x : (C×A)×Options A) : Options A :=
  (x.2.map fun a=>(a.1,mul (a.2,p (x.1.1,a.1))))++
    (x.2.map fun a=>(x.1.2,mul (a.2,sub ((1,1),p (x.1.1,a.1)))))
def acceptRealizer {p : C×A→Fraction} (P : Realizer p) : Realizer (accept p) := by
  let probability : Realizer (fun x : (C×A)×(A×Fraction)=>p (x.1.1,x.2.1)) :=
    composition (pair first.fst second.fst) P
  let yes := pair second.fst (composition (pair second.snd probability) mulRealizer)
  let no := pair first.snd (composition (pair second.snd
    (composition (pair (constant (1,1)) probability) subRealizer)) mulRealizer)
  exact (composition (pair (mapWith yes) (mapWith no)) append).congr (fun _=>rfl)
lemma polynomial_accept {p : C×A→Fraction} {P : Realizer p} (hP : PolynomialTime P) :
    PolynomialTime (acceptRealizer P) := by
  unfold acceptRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_mul
  have := polynomial_sub
  tree_cost
omit [Codec A] [Codec C] in
lemma accept_repr [Codec A] [Codec C] (e : Ω→A) (p : C×A→Fraction) (z : C) (a : Ω) (c : WeightedOptions Ω)
    (q : Ω→ℚ) (hq : ∀ a,0≤q a) (hq1 : ∀ a,q a≤1)
    (he : ∀ a,p (z,e a)=TreeFraction.repr (q a)) :
    accept p ((z,e a),repr e c)=repr e (c.accept a q hq hq1) := by
  have h1 : (1,1)=TreeFraction.repr 1 := rfl
  simp only [accept,repr,List.map_ofFn,h1]
  simp only [WeightedOptions.accept]
  rw [List.ofFn_add]
  apply congrArg₂ List.append <;> apply List.ofFn_inj.mpr <;> funext i
  · simp only [Function.comp_def,he]
    change (e (c.out i),mul (TreeFraction.repr (c.mass i),TreeFraction.repr (q (c.out i)))) =
      (e (Fin.addCases c.out (fun _=>a) (i.castAdd c.size)),TreeFraction.repr (Fin.addCases (fun i=>c.mass i*q (c.out i)) (fun i=>c.mass i*(1-q (c.out i))) (i.castAdd c.size)))
    simp only [Fin.addCases_left,mul_repr (c.nonneg i) (hq _)]
  · simp only [Function.comp_def,Fin.addCases_right,he]
    rw [sub_repr (by decide) (hq _) (hq1 _),mul_repr (c.nonneg i) (sub_nonneg.mpr (hq1 _))]

def metropolisProbability (w : C×A→Fraction) (x : (C×A)×A) : Fraction :=
  minimum ((1,1),div (w (x.1.1,x.2),w x.1))
def metropolisProbabilityRealizer {w : C×A→Fraction} (W : Realizer w) :
    Realizer (metropolisProbability w) :=
  (composition (pair (constant (1,1)) (composition (pair (composition (pair first.fst second) W)
    (composition first W)) divRealizer)) minimumRealizer).congr (fun _=>rfl)
lemma polynomial_metropolisProbability {w : C×A→Fraction} {W : Realizer w}
    (hW : PolynomialTime W) : PolynomialTime (metropolisProbabilityRealizer W) := by
  unfold metropolisProbabilityRealizer Realizer.fst
  apply polynomial_congr
  have := polynomial_div
  have := TreeFraction.polynomial_minimum
  tree_cost
omit [Codec A] [Codec C] in
lemma metropolisProbability_repr [Codec A] [Codec C] (e : Ω→A) (w : C×A→Fraction) (z : C)
    (q : Ω→ℚ) (hq : ∀ a,0≤q a) (he : ∀ a,w (z,e a)=TreeFraction.repr (q a)) (a b : Ω) :
    metropolisProbability w ((z,e a),e b)=TreeFraction.repr (min 1 (q b/q a)) := by
  unfold metropolisProbability
  rw [he,he,div_repr (hq _) (hq _)]
  exact minimum_repr (x:=1) (y:=q b/q a) (by decide) (div_nonneg (hq _) (hq _))
end MatchingFPRAS.ExecutableOptions

end OAI
