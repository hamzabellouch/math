import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeFastLookup
import OAI.Combinatorics.MatchingCount.Complexity.TreeFractionCosts

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A]

def takeFast : Realizer (fun x : List A×ℕ=>x.1.take x.2) :=
  (composition (composition (pair (composition first reverse)
    (composition (pair (composition first listLength) second) subtract)) dropFast) reverse).congr (by
      intro x
      change (x.1.reverse.drop (x.1.length-x.2)).reverse=x.1.take x.2
      rw [←List.reverse_take,List.reverse_reverse])
lemma polynomial_takeFast : PolynomialTime (takeFast (A:=A)) := by
  unfold takeFast
  apply polynomial_congr
  exact polynomial_composition (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_reverse)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_listLength)
      polynomial_second) polynomial_subtract)) polynomial_dropFast) polynomial_reverse
omit [Codec A] in
lemma polynomial_bitValue : PolynomialTime bitValue := by
  unfold bitValue
  apply polynomial_congr
  exact polynomial_composition (polynomial_composition (polynomial_pair polynomial_reverse
    (polynomial_constant (1,0))) polynomial_mulFold) polynomial_second
omit [Codec A] in
lemma polynomial_bitDenominator : PolynomialTime bitDenominatorRealizer := by
  unfold bitDenominatorRealizer
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant 1))
  apply polynomial_fold (polynomial_composition polynomial_second polynomial_double) (4*X+8*X+1)
  intro bs n pre post he
  have hfold : ∀ z,(pre.foldl (fun a (_ : Bool)=>2*a) z).size≤z.size+pre.length*2 := by
    clear he
    induction pre with
    | nil => intro z; simp
    | cons b pre ih =>
      intro z
      have hh:=nat_size_mul 2 z
      have ht:=ih (2*z)
      simp only [List.foldl_cons,List.length_cons]
      have h2 : Nat.size 2=2 := by decide
      omega
  let S:=weight (bs,n)
  have hn : n.size≤S := (size_le_weight n).trans (weight_snd (bs,n))
  have hp : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans (weight_fst (bs,n)))
  have hw:=weight_nat_le (pre.foldl (fun a (_ : Bool)=>2*a) n)
  have hh:=hfold n
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  change weight (pre.foldl (fun a (_ : Bool)=>2*a) n)≤4*S+8*S+1
  omega
omit [Codec A] in
lemma polynomial_minimum : PolynomialTime minimum := by
  unfold minimum
  exact polynomial_congr _ (polynomial_choose polynomial_less polynomial_first polynomial_second)
omit [Codec A] in
lemma polynomial_listMin : PolynomialTime listMinRealizer := by
  unfold listMinRealizer
  apply polynomial_congr
  apply polynomial_fold polynomial_minimum (4*X+1)
  intro as n pre post he
  have hm : pre.foldl (fun z a=>min a z) n=listMin (pre,n) := by
    unfold listMin
    congr 1
    funext z a
    exact Nat.min_comm _ _
  change weight (pre.foldl (fun z a=>min a z) n)≤_
  rw [hm]
  have hl:=listMin_le_default pre n
  have hs:=(Nat.size_le_size hl).trans (size_le_weight n)
  have hw:=weight_nat_le (listMin (pre,n))
  have hn : weight n≤weight (as,n) := weight_snd (as,n)
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  omega
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.TreeFraction
open TreeTyped

def cumulativeFast : Realizer cumulativeFraction := composition takeFast sumRealizer
lemma polynomial_cumulativeFast : PolynomialTime cumulativeFast :=
  polynomial_composition polynomial_takeFast polynomial_sum
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableChoice
open TreeTyped TreeFraction Polynomial

def predicateFast : Realizer predicate := by
  let C : Realizer (fun x : (List Fraction×Fraction)×ℕ=>cumulativeFraction (x.1.1,x.2+1)) :=
    (composition (pair first.fst (composition second successor)) cumulativeFast).congr (fun _=>rfl)
  exact (composition (pair first.snd C) lessRealizer).congr (fun _=>rfl)
lemma polynomial_predicateFast : PolynomialTime predicateFast := by
  unfold predicateFast
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ TreeFraction.polynomial_less
  apply polynomial_pair (polynomial_snd polynomial_first)
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair (polynomial_fst polynomial_first)
      (polynomial_composition polynomial_second polynomial_successor)) polynomial_cumulativeFast

def chooseFast : Realizer choose := by
  let rs : Realizer (fun x : List Fraction×Fraction=>List.range x.1.length) :=
    composition (composition first listLength) range
  let good:=composition (pair identity rs) (filterWith predicateFast)
  exact (composition (pair good (composition first listLength)) listMinRealizer).congr (fun _=>rfl)
lemma polynomial_chooseFast : PolynomialTime chooseFast := by
  unfold chooseFast
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ polynomial_listMin
  apply polynomial_pair _ (polynomial_composition polynomial_first polynomial_listLength)
  apply polynomial_composition _ (polynomial_filterWith polynomial_predicateFast)
  apply polynomial_pair polynomial_identity
  exact polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength) X
    (fun x=>by simpa using (list_length_le_weight x.1).trans (weight_fst x))

def chooseBitsFast : Realizer chooseBits :=
  composition (pair first (pair (composition second bitValue) (composition second bitDenominatorRealizer))) chooseFast
lemma polynomial_chooseBitsFast : PolynomialTime chooseBitsFast :=
  polynomial_composition (polynomial_pair polynomial_first (polynomial_pair
    (polynomial_composition polynomial_second polynomial_bitValue)
    (polynomial_composition polynomial_second polynomial_bitDenominator))) polynomial_chooseFast
end MatchingFPRAS.ExecutableChoice

end OAI
