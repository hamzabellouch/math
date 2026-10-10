import Mathlib
import OAI.Algebra.GroupRing.WordFrames

namespace OAI



section
namespace TorsionFreeZeroDivisors.PathCharges
open scoped Classical BigOperators
open WordCursor WordFrames WordBlocks
noncomputable section
variable {D G M : Type} [Group G] [AddCommGroup M] (v : D→G) (c : G→D→M)
def charge (g : G) : List D→M
  | []=>0
  | d::w=>c g d+charge (g*v d) w
@[simp] lemma charge_nil (g : G) : charge v c g []=0 := rfl
@[simp] lemma charge_cons (g : G) (d : D) (w : List D) :
    charge v c g (d::w)=c g d+charge v c (g*v d) w := rfl
lemma charge_append (g : G) (w u : List D) :
    charge v c g (w++u)=charge v c g w+charge v c (g*value v w) u := by
  induction w generalizing g with
  | nil=>simp
  | cons d w ih=>
    rw [List.cons_append,charge_cons,ih,charge_cons,value_cons,mul_assoc,add_assoc]
lemma charge_sum (g : G) (w : List D) :
    (∑i : Fin w.length,c (g*cursor v w i.val) (w.get i))=charge v c g w := by
  induction w generalizing g with
  | nil=>simp
  | cons d w ih=>
    change (∑i : Fin (w.length+1),c (g*cursor v (d::w) i.val) ((d::w).get i))=_
    rw [Fin.sum_univ_succ,charge_cons]
    change c (g*1) d+(∑i : Fin w.length,c (g*(v d*cursor v w i.val)) (w.get i))=_
    simp only [mul_one,←mul_assoc]
    rw [ih]
lemma frames_sum (bs : List (G×List D)) :
    (∑i : Occ (words bs),c (WordFrames.position v bs i) (letter (words bs) i))=
    (bs.map (fun b=>charge v c b.1 b.2)).sum := by
  induction bs with
  | nil=>
    change (∑i : Empty,c (WordFrames.position v [] i) (letter (words []) i))=0
    simp only [Finset.univ_eq_empty,Finset.sum_empty]
  | cons b bs ih=>
    change (∑i : Fin b.2.length⊕Occ (words bs),c (WordFrames.position v (b::bs) i) (letter (words (b::bs)) i))=_
    rw [Fintype.sum_sum_type]
    cases b with
    | mk g w=>
      change (∑i : Fin w.length,c (g*cursor v w i.val) (w.get i))+
        (∑i : Occ (words bs),c (WordFrames.position v bs i) (letter (words bs) i))=_
      rw [charge_sum,ih]
      rfl
variable (rev : D→D) (hv : ∀d,v (rev d)=(v d)⁻¹)
  (hc : ∀g d,c (g*v d) (rev d)=-c g d)
include hv in
lemma value_reverse (w : List D) : value v (w.reverse.map rev)=(value v w)⁻¹ := by
  induction w with
  | nil=>simp
  | cons d w ih=>simp only [List.reverse_cons,List.map_append,List.map_singleton,
      value_append,value_cons,value_nil,mul_one,ih,hv,mul_inv_rev]
include hv hc in
lemma charge_reverse (g : G) (w : List D) :
    charge v c (g*value v w) (w.reverse.map rev)=-charge v c g w := by
  induction w generalizing g with
  | nil=>simp
  | cons d w ih=>
    rw [List.reverse_cons,List.map_append,List.map_singleton,value_cons,←mul_assoc,charge_append,ih]
    rw [value_reverse v rev hv]
    simp only [charge_cons,charge_nil,add_zero,mul_inv_cancel_right]
    rw [hc,neg_add]
    exact add_comm _ _
end
end TorsionFreeZeroDivisors.PathCharges

end



end OAI
