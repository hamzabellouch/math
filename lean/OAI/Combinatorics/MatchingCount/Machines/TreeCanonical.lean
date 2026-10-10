import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialCollections

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A]

def contains [DecidableEq A] (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : A×List A=>decide (x.1∈x.2)) :=
  (composition (mapWith E) any).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,List.any_map,List.any_eq_true,id_eq,decide_eq_true_eq]
    constructor
    · rintro ⟨a,ha,he⟩; simpa [he] using ha
    · intro h; exact ⟨x.1,h,rfl⟩)
lemma polynomial_contains [DecidableEq A] {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (contains E) := by
  unfold contains
  exact polynomial_congr _ (polynomial_composition (polynomial_mapWith hE) polynomial_any)

def dedupStep [DecidableEq A] (x : A×List A) : List A := if x.1∈x.2 then x.2 else x.1::x.2
def dedupStepRealizer [DecidableEq A] (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (dedupStep (A:=A)) :=
  (choose (contains E) second listCons).congr (by intro x; simp [dedupStep])
omit [Codec A] in
lemma dedup_fold [DecidableEq A] (as : List A) :
    as.reverse.foldl (fun bs a=>dedupStep (a,bs)) []=as.dedup := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]
    exact (List.dedup_cons' a as).symm
def dedup [DecidableEq A] (E : Realizer (fun x : A×A=>decide (x.1=x.2))) : Realizer (List.dedup (α:=A)) :=
  (composition (pair reverse (constant [])) (fold (dedupStepRealizer E))).congr dedup_fold
lemma weight_dedupFold [DecidableEq A] (as bs : List A) :
    weight (as.foldl (fun bs a=>dedupStep (a,bs)) bs)≤weight as+weight bs := by
  induction as generalizing bs with
  | nil => simp
  | cons a as ih =>
    rw [List.foldl_cons]
    have hh:=ih (dedupStep (a,bs))
    simp only [weight_cons]
    have hs : weight (dedupStep (a,bs))≤1+weight a+weight bs := by
      change weight (if a∈bs then bs else a::bs)≤_
      split_ifs
      · omega
      · rw [weight_cons]
    omega
lemma polynomial_dedup [DecidableEq A] {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (dedup E) := by
  unfold dedup
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair polynomial_reverse (polynomial_constant []))
  apply polynomial_fold (polynomial_congr _ (polynomial_choose (polynomial_contains hE) polynomial_second polynomial_listCons)) (2*X+1)
  intro as bs pre post he
  have hh:=weight_dedupFold pre bs
  have hp:=weight_prefix he
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  omega

variable (r : A → A → Prop) [DecidableRel r]
def insertStep (x : A×(A×(List A×List A))) : A×(List A×List A) :=
  (x.2.1,(x.1::x.2.2.1,if r x.2.1 x.1 then x.2.1::x.1::x.2.2.1 else x.1::x.2.2.2))
def insertStepRealizer (R : Realizer (fun x : A×A=>decide (r x.1 x.2))) : Realizer (insertStep r) :=
  (pair (composition second first) (pair (composition (pair first (composition (composition second second) first)) listCons)
    (choose (composition (pair (composition second first) first) R)
      (composition (pair (composition second first) (composition (pair first (composition (composition second second) first)) listCons)) listCons)
      (composition (pair first (composition (composition second second) second)) listCons)))).congr (by intro x; simp [insertStep])
omit [Codec A] in
lemma insert_fold (as bs : List A) (a : A) :
    as.reverse.foldl (fun z b=>insertStep r (b,z)) (a,(bs,List.orderedInsert r a bs))=
      (a,(as++bs,List.orderedInsert r a (as++bs))) := by
  induction as with
  | nil => rfl
  | cons b as ih =>
    rw [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,ih]
    rfl
def orderedInsert (R : Realizer (fun x : A×A=>decide (r x.1 x.2))) :
    Realizer (fun x : A×List A=>List.orderedInsert r x.1 x.2) :=
  (composition (composition (pair (composition second reverse)
    (pair first (pair (constant []) (composition (pair first (constant [])) listCons))))
      (fold (insertStepRealizer r R))) (composition second second)).congr (by
        intro x
        change (x.2.reverse.foldl (fun z b=>insertStep r (b,z)) (x.1,([],[x.1]))).2.2=_
        have h:=insert_fold r x.2 [] x.1
        simpa only [List.append_nil,List.orderedInsert_nil] using congrArg (fun x=>x.2.2) h)
lemma weight_perm {as bs : List A} (h : as.Perm bs) : weight as=weight bs := by
  simp only [weight,size_encode_list,h.length_eq,(h.map (fun a=>TreeFunction.size (encode a))).sum_eq]
lemma weight_orderedInsert (a : A) (as : List A) :
    weight (List.orderedInsert r a as)=1+weight a+weight as := by
  rw [weight_perm (List.perm_orderedInsert r a as),weight_cons]
lemma polynomial_insertStep {R : Realizer (fun x : A×A=>decide (r x.1 x.2))}
    (hR : PolynomialTime R) : PolynomialTime (insertStepRealizer r R) := by
  unfold insertStepRealizer
  apply polynomial_congr
  apply polynomial_pair (polynomial_fst polynomial_second)
  apply polynomial_pair (polynomial_composition (polynomial_pair polynomial_first (polynomial_fst (polynomial_snd polynomial_second))) polynomial_listCons)
  exact polynomial_choose (polynomial_composition (polynomial_pair (polynomial_fst polynomial_second) polynomial_first) hR)
    (polynomial_composition (polynomial_pair (polynomial_fst polynomial_second)
      (polynomial_composition (polynomial_pair polynomial_first (polynomial_fst (polynomial_snd polynomial_second))) polynomial_listCons)) polynomial_listCons)
    (polynomial_composition (polynomial_pair polynomial_first (polynomial_snd (polynomial_snd polynomial_second))) polynomial_listCons)
lemma insert_fold_bound (as bs cs : List A) (a : A) :
    weight ((as.foldl (fun z b=>insertStep r (b,z)) (a,(bs,cs))).2.1)≤weight as+weight bs ∧
    weight ((as.foldl (fun z b=>insertStep r (b,z)) (a,(bs,cs))).2.2)≤2*weight as+weight bs+weight cs+weight a+1 ∧
    (as.foldl (fun z b=>insertStep r (b,z)) (a,(bs,cs))).1=a := by
  induction as generalizing bs cs with
  | nil =>
    change weight bs≤1+weight bs ∧ weight cs≤2+weight bs+weight cs+weight a+1 ∧ a=a
    exact ⟨by omega,by omega,rfl⟩
  | cons b as ih =>
    rw [List.foldl_cons]
    by_cases h : r a b
    · have hs : insertStep r (b,(a,(bs,cs)))=(a,(b::bs,a::b::bs)) := by simp [insertStep,h]
      rw [hs]
      have he:=insert_fold r as.reverse (b::bs) a
      simp only [List.reverse_reverse] at he
      have ho : List.orderedInsert r a (b::bs)=a::b::bs := by simp [h]
      rw [ho] at he
      rw [he]
      have hw:=weight_append as.reverse (b::bs)
      rw [weight_reverse,weight_cons] at hw
      simp only [weight_orderedInsert,weight_cons]
      exact ⟨by omega,by omega,trivial⟩
    · have hs : insertStep r (b,(a,(bs,cs)))=(a,(b::bs,b::cs)) := by simp [insertStep,h]
      rw [hs]
      have hh:=ih (b::bs) (b::cs)
      simp only [weight_cons] at hh ⊢
      exact ⟨by omega,by omega,hh.2.2⟩
lemma polynomial_orderedInsert {R : Realizer (fun x : A×A=>decide (r x.1 x.2))}
    (hR : PolynomialTime R) : PolynomialTime (orderedInsert r R) := by
  unfold orderedInsert
  apply polynomial_congr
  apply polynomial_composition _ (polynomial_snd polynomial_second)
  apply polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_reverse)
    (polynomial_pair polynomial_first (polynomial_pair (polynomial_constant [])
      (polynomial_composition (polynomial_pair polynomial_first (polynomial_constant [])) polynomial_listCons))))
  apply polynomial_fold (polynomial_insertStep r hR) (5*X+10)
  rintro as ⟨a,bs,cs⟩ pre post he
  have hh:=insert_fold_bound r pre bs cs a
  have hp:=weight_prefix he
  rw [weight_prod,hh.2.2,weight_prod]
  calc
    _ ≤ 1+weight a+(1+(weight pre+weight bs)+(2*weight pre+weight bs+weight cs+weight a+1)) := by
      gcongr
      · exact hh.1
      · exact hh.2.1
    _ ≤ _ := by
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
      omega

def insertionSort (R : Realizer (fun x : A×A=>decide (r x.1 x.2))) :
    Realizer (List.insertionSort r) :=
  (composition (pair reverse (constant [])) (fold (orderedInsert r R))).congr (by
    intro as
    change as.reverse.foldl (fun bs a=>List.orderedInsert r a bs) []=as.insertionSort r
    rw [List.foldl_reverse]
    rfl)
lemma weight_insertFold (as bs : List A) :
    weight (as.foldl (fun bs a=>List.orderedInsert r a bs) bs)+1=weight as+weight bs := by
  induction as generalizing bs with
  | nil => simp only [List.foldl_nil,weight_nil]; omega
  | cons a as ih =>
    rw [List.foldl_cons]
    have hh:=ih (List.orderedInsert r a bs)
    rw [weight_orderedInsert] at hh
    rw [weight_cons]
    omega
lemma polynomial_insertionSort {R : Realizer (fun x : A×A=>decide (r x.1 x.2))}
    (hR : PolynomialTime R) : PolynomialTime (insertionSort r R) := by
  unfold insertionSort
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair polynomial_reverse (polynomial_constant []))
  apply polynomial_fold (polynomial_orderedInsert r hR) (2*X+1)
  intro as bs pre post he
  have hh:=weight_insertFold r pre bs
  have hp:=weight_prefix he
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  omega

variable [DecidableEq A]
def canonical (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (r x.1 x.2))) :
    Realizer (fun as : List A=>as.dedup.insertionSort r) := composition (dedup E) (insertionSort r R)
lemma polynomial_canonical {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (r x.1 x.2))}
    (hE : PolynomialTime E) (hR : PolynomialTime R) : PolynomialTime (canonical r E R) :=
  polynomial_composition (polynomial_dedup hE) (polynomial_insertionSort r hR)
omit [Codec A] in
lemma canonical_eq_sort [IsTrans A r] [Std.Total r] [Std.Antisymm r] (as : List A) :
    as.dedup.insertionSort r=as.toFinset.sort r := by
  have hn:=(List.perm_insertionSort r as.dedup).nodup_iff.mpr (List.nodup_dedup as)
  have hh:=(List.toFinset_sort (r:=r) hn).mpr (List.pairwise_insertionSort r as.dedup)
  have he : (as.dedup.insertionSort r).toFinset=as.toFinset := by ext a; simp
  rw [he] at hh
  exact hh.symm
end MatchingFPRAS.TreeTyped

end OAI
