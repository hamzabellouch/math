import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.TreeCostMeasure
import OAI.Combinatorics.MatchingCount.Machines.TreeSum

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A]

def indexStep (x : A×(A×ℕ)) : A×ℕ := (x.2.1,if x.2.1=x.1 then 0 else x.2.2+1)
def indexStepRealizer (E : Realizer (fun x : A×A=>decide (x.1=x.2))) : Realizer (indexStep (A:=A)) :=
  (pair second.fst (choose (composition (pair second.fst first) E) (constant 0)
    (composition second.snd successor))).congr (fun x=>by simp only [indexStep,Function.comp_apply,decide_eq_true_eq,Nat.succ_eq_add_one])
omit [BEq A] [LawfulBEq A] in
lemma polynomial_indexStep [BEq A] [LawfulBEq A] {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (indexStepRealizer E) := by
  unfold indexStepRealizer
  apply polynomial_congr
  exact polynomial_pair (polynomial_fst polynomial_second)
    (polynomial_choose (polynomial_composition (polynomial_pair (polynomial_fst polynomial_second) polynomial_first) hE)
      (polynomial_constant 0) (polynomial_composition (polynomial_snd polynomial_second) polynomial_successor))
omit [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A] in
lemma indexStep_fold_first [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A]
    (xs : List A) (a : A) (i : ℕ) :
    (xs.foldl (fun z x=>indexStep (x,z)) (a,i)).1=a := by
  induction xs generalizing i with
  | nil=>rfl
  | cons x xs ih=>exact ih _
omit [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A] in
lemma indexStep_fold_le [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A]
    (xs : List A) (a : A) (i : ℕ) :
    (xs.foldl (fun z x=>indexStep (x,z)) (a,i)).2 ≤ i+xs.length := by
  induction xs generalizing i with
  | nil=>simp
  | cons x xs ih=>
    have h:=ih (if a=x then 0 else i+1)
    change (xs.foldl _ (a,if a=x then 0 else i+1)).2 ≤ _
    have hb : (if a=x then 0 else i+1) ≤ i+1 := by split_ifs <;> omega
    simpa only [List.length_cons] using h.trans (by omega)
lemma polynomial_indexFold {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (fold (indexStepRealizer E)) := by
  apply polynomial_fold (polynomial_indexStep hE) (10*X+20)
  rintro xs ⟨a,i⟩ pre post he
  have hp:=(list_length_le_weight pre).trans (weight_prefix he)
  have hb:=indexStep_fold_le pre a i
  have hi:=Nat.size_le_size hb
  have hs:=nat_size_add i pre.length
  have hn : pre.length.size ≤ pre.length := Nat.size_le.mpr Nat.lt_two_pow_self
  rw [←Prod.eta (pre.foldl _ (a,i)),weight_prod,indexStep_fold_first]
  have hw:=weight_nat_le (pre.foldl (fun z x=>indexStep (x,z)) (a,i)).2
  have ha:=weight_pos a
  have hn':=size_le_weight i
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  omega

omit [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A] in
lemma indexStep_fold_reverse [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A]
    (xs : List A) (a : A) :
    (xs.reverse.foldl (fun z x=>indexStep (x,z)) (a,0)).2=xs.idxOf a := by
  rw [List.foldl_reverse]
  have h : xs.foldr (fun x z=>indexStep (x,z)) (a,0)=(a,xs.idxOf a) := by
    induction xs with
    | nil=>simp
    | cons x xs ih=>
      rw [List.foldr_cons,ih]
      simp only [indexStep,List.idxOf_cons]
      by_cases he : a=x
      · subst x; simp
      · simp [he,beq_eq_false_iff_ne.mpr (Ne.symm he)]
  rw [h]

def indexOf (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : A×List A=>x.2.idxOf x.1) :=
  (composition (composition (pair (composition second reverse) (pair first (constant 0)))
    (fold (indexStepRealizer E))) second).congr (fun x=>indexStep_fold_reverse x.2 x.1)
lemma polynomial_indexOf {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (indexOf E) := by
  unfold indexOf
  apply polynomial_congr
  exact polynomial_composition (polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_second polynomial_reverse)
      (polynomial_pair polynomial_first (polynomial_constant 0)))
      (polynomial_indexFold hE)) polynomial_second
end MatchingFPRAS.TreeTyped

end OAI
