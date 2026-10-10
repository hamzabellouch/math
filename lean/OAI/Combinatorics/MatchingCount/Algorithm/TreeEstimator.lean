import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeSlotWeight

namespace OAI

namespace MatchingFPRAS.TreeFraction
lemma fold_sum_repr (xs : List ℚ) (hx : ∀ x∈xs,0≤x) (a : ℚ) (ha : 0≤a) :
    ((xs.map repr).foldl (fun a b=>add (b,a)) (repr a))=repr (xs.sum+a) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    have h : 0≤x:=hx x (by simp)
    simp only [List.map_cons,List.foldl_cons,add_repr h ha]
    rw [ih (fun y hy=>hx y (by simp [hy])) (x+a) (add_nonneg h ha)]
    congr 1
    simp only [List.sum_cons]
    ring
lemma sum_repr (xs : List ℚ) (hx : ∀ x∈xs,0≤x) : sum (xs.map repr)=repr xs.sum := by
  unfold sum
  have h:=fold_sum_repr xs hx 0 (by decide)
  simpa only [add_zero,show repr (0:ℚ)=(0,1) from rfl] using h
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableEstimator
open TreeTyped TreeFraction

def mean (xs : List Fraction) : Fraction := div (sum xs,(xs.length,1))
def meanRealizer : Realizer mean := composition
  (pair sumRealizer (pair listLength (constant 1))) divRealizer
lemma polynomial_mean : PolynomialTime meanRealizer := by
  unfold meanRealizer
  apply polynomial_composition _ polynomial_div
  exact polynomial_pair polynomial_sum (polynomial_pair polynomial_listLength (polynomial_constant _))
lemma mean_rep (xs : List ℚ) (hx : ∀ x∈xs,0≤x) :
    mean (xs.map TreeFraction.repr)=TreeFraction.repr (xs.sum/xs.length) := by
  unfold mean
  rw [sum_repr xs hx,List.length_map,←repr_nat xs.length,div_repr (List.sum_nonneg hx) (by positivity)]

def ratio (x : Fraction×Fraction) : Fraction :=
  if less ((0,1),x.1) then div (x.2,x.1) else (1,1)
def ratioRealizer : Realizer ratio :=
  (choose (composition (pair (constant (0,1)) first) lessRealizer)
    (composition (pair second first) divRealizer) (constant (1,1))).congr (fun _=>rfl)
lemma polynomial_ratio : PolynomialTime ratioRealizer := by
  unfold ratioRealizer
  apply polynomial_congr
  have := TreeFraction.polynomial_less
  have := polynomial_div
  tree_cost
lemma ratio_rep (a d : ℚ) (ha : 0≤a) (hd : 0≤d) :
    ratio (TreeFraction.repr a,TreeFraction.repr d)=TreeFraction.repr (Counting.ratioEstimate a d) := by
  unfold ratio Counting.ratioEstimate
  rw [show ((0,1) : Fraction)=TreeFraction.repr (0:ℚ) from rfl,
    less_val _ _ (by decide) a.pos,val_repr (by decide),val_repr ha]
  simp only [decide_eq_true_eq]
  split_ifs
  · exact div_repr hd ha
  · rfl

def upper (x : ℕ×(Fraction×Fraction)) : Fraction :=
  if less ((0,1),x.2.1) then
    maximum ((1,100000),minimum ((3,1),add (div (mul ((x.1,1),x.2.2),x.2.1),(1,100000))))
  else (1,1)
def upperRealizer : Realizer upper := by
  let q : Realizer (fun x : ℕ×(Fraction×Fraction)=>
      div (mul ((x.1,1),x.2.2),x.2.1)) :=
    (composition (pair (composition (pair (pair first (constant 1)) second.snd) mulRealizer) second.fst) divRealizer).congr (fun _=>rfl)
  exact (choose (composition (pair (constant (0,1)) second.fst) lessRealizer)
    (composition (pair (constant (1,100000)) (composition (pair (constant (3,1))
      (composition (pair q (constant (1,100000))) addRealizer)) minimumRealizer)) maximumRealizer)
    (constant (1,1))).congr (fun _=>rfl)
lemma polynomial_upper : PolynomialTime upperRealizer := by
  unfold upperRealizer Realizer.fst Realizer.snd
  dsimp only
  apply polynomial_congr
  have := TreeFraction.polynomial_less
  have := polynomial_div
  have := polynomial_mul
  have := TreeFraction.polynomial_add
  have := TreeFraction.polynomial_minimum
  have := polynomial_maximum
  tree_cost
lemma upper_rep (D : ℕ) (d z : ℚ) (hd : 0≤d) (hz : 0≤z) :
    upper (D,(TreeFraction.repr d,TreeFraction.repr z))=TreeFraction.repr (Counting.upperEstimate D d z) := by
  have ha : ((1,100000) : Fraction)=TreeFraction.repr Counting.alpha := by norm_num [TreeFraction.repr,Counting.alpha]
  have ha0 : (0:ℚ)≤Counting.alpha := by norm_num [Counting.alpha]
  have h0 : ((0,1) : Fraction)=TreeFraction.repr (0:ℚ) := rfl
  have h3 : ((3,1) : Fraction)=TreeFraction.repr (3:ℚ) := rfl
  unfold upper Counting.upperEstimate
  rw [h0,less_val _ _ (by decide) d.pos,val_repr (by decide),val_repr hd]
  simp only [decide_eq_true_eq]
  split_ifs
  · rw [ha,h3,←repr_nat D,mul_repr (by positivity) hz,div_repr (by positivity) hd,
      add_repr (by positivity) ha0,minimum_repr (by decide) (by positivity),maximum_repr ha0 (by positivity)]
  · rfl
end MatchingFPRAS.ExecutableEstimator

end OAI
