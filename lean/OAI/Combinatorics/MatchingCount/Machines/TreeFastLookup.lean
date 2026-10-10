import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeFiniteOps

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A]

def minNat : Realizer (fun x : ℕ×ℕ=>min x.1 x.2) :=
  (choose leNat first second).congr (by intro x; simp only [decide_eq_true_eq]; exact (min_def x.1 x.2).symm)
lemma polynomial_minNat : PolynomialTime minNat :=
  polynomial_congr _ (polynomial_choose polynomial_leNat polynomial_first polynomial_second)

def dropInit : Realizer (fun x : List A×ℕ=>(min x.2 x.1.length,x.1)) :=
  pair (composition (pair second (composition first listLength)) minNat) first
lemma polynomial_dropInit : PolynomialTime (dropInit (A:=A)) := by
  unfold dropInit
  exact polynomial_pair (polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_first polynomial_listLength)) polynomial_minNat) polynomial_first

def dropFast : Realizer (fun x : List A×ℕ=>x.1.drop x.2) :=
  (composition dropInit (iterateDown (composition second tail))).congr (by
    intro x
    change countDown dropStep (min x.2 x.1.length) x.1=x.1.drop x.2
    rw [countDown_drop]
    by_cases h : x.2≤x.1.length
    · rw [min_eq_left h]
    · rw [min_eq_right (by omega),List.drop_length,List.drop_eq_nil_of_le (by omega)])
lemma polynomial_dropFast : PolynomialTime (dropFast (A:=A)) := by
  unfold dropFast
  apply polynomial_congr
  apply polynomial_boundedRepeat polynomial_dropInit
    (polynomial_composition polynomial_second polynomial_tail) X X
    (fun x _ z=>z.Sublist x.1)
  · intro x
    simp only [Polynomial.eval_X]
    exact (min_le_right _ _).trans ((list_length_le_weight x.1).trans (by rw [weight_prod]; omega))
  · intro x; exact List.Sublist.refl _
  · intro x k hk z hz
    exact (List.tail_sublist z).trans hz
  · intro x k z hz
    simp only [Polynomial.eval_X]
    exact (weight_sublist hz).trans (by rw [weight_prod]; omega)

def getDFast (d : A) : Realizer (fun x : List A×ℕ=>x.1.getD x.2 d) :=
  (composition dropFast (head d)).congr (by
    intro x
    simp only [Function.comp_apply, List.headD_eq_head?_getD, List.head?_drop,
      List.getD_eq_getElem?_getD])
lemma polynomial_getDFast (d : A) : PolynomialTime (getDFast d) :=
  polynomial_congr _ (polynomial_composition polynomial_dropFast (polynomial_head d))

end MatchingFPRAS.TreeTyped

end OAI
