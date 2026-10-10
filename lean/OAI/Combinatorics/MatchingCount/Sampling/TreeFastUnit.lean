import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeClippedRun
import OAI.Combinatorics.MatchingCount.Complexity.TreeChoiceCosts
import OAI.Combinatorics.MatchingCount.Sampling.TreeUnitDraw

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP Polynomial

def skipFast : Realizer skip := skipRealizer
lemma polynomial_skipFast : PolynomialTime skipFast := by
  unfold skipFast skipRealizer
  apply polynomial_congr
  exact polynomial_choose polynomial_less polynomial_first
    (polynomial_composition polynomial_first polynomial_successor)

def residualFast : Realizer residual := by
  let p : Realizer (fun x : (Bags×ℕ)×ℕ=>(x.1.1,skip (x.2,x.1.2))) :=
    pair first.fst (composition (pair second first.snd) skipFast)
  let n : Realizer (fun x : Bags×ℕ=>x.1.length-2) := composition (pair (composition first listLength) (constant 2)) subtract
  exact (composition (pair identity (composition n range))
    (mapWith (composition p (getDFast ([] : Bag))))).congr (fun _=>rfl)
lemma polynomial_residualFast : PolynomialTime residualFast := by
  unfold residualFast Realizer.fst Realizer.snd
  dsimp only
  apply polynomial_congr
  apply polynomial_composition
  · apply polynomial_pair polynomial_identity
    apply polynomial_boundedRange (by tree_poly) X
    intro x
    simpa only [Polynomial.eval_X] using (Nat.sub_le x.1.length 2).trans ((list_length_le_weight x.1).trans (weight_fst x))
  · apply polynomial_mapWith
    apply polynomial_composition _ (polynomial_getDFast [])
    have := polynomial_skipFast
    tree_poly

def validFast : Realizer valid := by
  let bs : Realizer (fun x : Context×(ℕ×ℕ)=>x.1.1.1) := first.fst.fst
  let b : Realizer (fun x : Context×(ℕ×ℕ)=>x.2.1) := second.fst
  let c : Realizer (fun x : Context×(ℕ×ℕ)=>x.2.2) := second.snd
  let a := composition (composition bs listLength) predecessor
  let ba := composition (pair bs a) (getDFast ([] : Bag))
  let bb := composition (pair bs b) (getDFast ([] : Bag))
  let p := composition (composition (pair b a) natEqual) boolNot
  let q := composition (pair ba c) membership
  let r := composition (pair bb c) membership
  exact (composition (pair (composition (pair p q) boolAnd) r) boolAnd).congr (by intro x; simp [valid])
lemma polynomial_validFast : PolynomialTime validFast := by
  unfold validFast Realizer.fst Realizer.snd
  dsimp only
  apply polynomial_congr
  have := polynomial_predecessor
  have := polynomial_getDFast ([] : Bag)
  have := polynomial_membership
  tree_poly

def fastBranch (x : Context×ℕ) : ℕ := cappedCount ((residual (x.1.1.1,x.2),x.1.1.2),x.1.2)
def fastBranchRealizer : Realizer fastBranch :=
  (composition (pair (pair (composition (pair first.fst.fst second) residualFast) first.fst.snd)
    first.snd) cappedCountRealizer).congr (fun _=>rfl)
lemma polynomial_fastBranch : PolynomialTime fastBranchRealizer := by
  unfold fastBranchRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  apply polynomial_composition _ polynomial_cappedCount
  have := polynomial_residualFast
  tree_poly

def fastEdgeCount (x : Context×(ℕ×ℕ)) : ℕ := if valid x then fastBranch (x.1,x.2.1) else 0
def fastEdgeCountRealizer : Realizer fastEdgeCount :=
  (choose validFast (composition (pair first second.fst) fastBranchRealizer) (constant 0)).congr (fun _=>rfl)
lemma polynomial_fastEdgeCount : PolynomialTime fastEdgeCountRealizer := by
  unfold fastEdgeCountRealizer
  apply polynomial_congr
  exact polynomial_choose polynomial_validFast
    (polynomial_composition (polynomial_pair polynomial_first (polynomial_fst polynomial_second)) polynomial_fastBranch)
    (polynomial_constant 0)

def fastProbability (x : Context×ℕ) : TreeFraction.Fraction :=
  (fastEdgeCount (x.1,decodeIndex (x.2,x.1.1.2.length)),cappedCount x.1)
def fastProbabilityRealizer : Realizer fastProbability := by
  let m : Realizer (fun x : Context×ℕ=>x.1.1.2.length) := composition first.fst.snd listLength
  let bc := composition (pair second m) decodeIndexRealizer
  exact (pair (composition (pair first bc) fastEdgeCountRealizer)
    (composition first cappedCountRealizer)).congr (fun _=>rfl)
lemma polynomial_fastProbability : PolynomialTime fastProbabilityRealizer := by
  unfold fastProbabilityRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_pair _ (polynomial_composition polynomial_first polynomial_cappedCount)
  apply polynomial_composition _ polynomial_fastEdgeCount
  apply polynomial_pair polynomial_first
  apply polynomial_composition _ polynomial_division
  exact polynomial_pair polynomial_second
    (polynomial_composition (polynomial_snd (polynomial_fst polynomial_first)) polynomial_listLength)

def fastProbabilities (x : Context) : List TreeFraction.Fraction :=
  (List.range (x.1.1.length*x.1.2.length)).map (fun i=>fastProbability (x,i))
def fastProbabilitiesRealizer : Realizer fastProbabilities := by
  let n : Realizer (fun x : Context=>x.1.1.length) := composition first.fst listLength
  let m : Realizer (fun x : Context=>x.1.2.length) := composition first.snd listLength
  exact (composition (pair identity (composition (composition (pair n m) multiply) range))
    (mapWith fastProbabilityRealizer)).congr (fun _=>rfl)
lemma polynomial_fastProbabilities : PolynomialTime fastProbabilitiesRealizer := by
  unfold fastProbabilitiesRealizer Realizer.fst Realizer.snd
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ (polynomial_mapWith polynomial_fastProbability)
  apply polynomial_pair polynomial_identity
  apply polynomial_boundedRange (by tree_poly) (X^2)
  intro x
  simp only [Function.comp_apply,Polynomial.eval_pow,Polynomial.eval_X]
  simpa only [pow_two] using Nat.mul_le_mul ((list_length_le_weight x.1.1).trans ((weight_fst x.1).trans (weight_fst x)))
      ((list_length_le_weight x.1.2).trans ((weight_snd x.1).trans (weight_fst x)))

def fastDraw (x : Context×List Bool) : ℕ×ℕ :=
  decodeIndex (ExecutableChoice.chooseBits (fastProbabilities x.1,x.2),x.1.1.2.length)
def fastDrawRealizer : Realizer fastDraw :=
  (composition (pair (composition (pair (composition first fastProbabilitiesRealizer) second)
      ExecutableChoice.chooseBitsFast) (composition first.fst.snd listLength)) decodeIndexRealizer).congr (fun _=>rfl)
lemma polynomial_fastDraw : PolynomialTime fastDrawRealizer := by
  unfold fastDrawRealizer decodeIndexRealizer
  apply polynomial_congr
  apply polynomial_composition _ polynomial_division
  apply polynomial_pair _ (polynomial_composition (polynomial_snd (polynomial_fst polynomial_first)) polynomial_listLength)
  exact polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_fastProbabilities) polynomial_second) ExecutableChoice.polynomial_chooseBitsFast
end MatchingFPRAS.ExecutableUnit

end OAI
