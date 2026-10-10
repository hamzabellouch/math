import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeFinite

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]
omit [Codec A] [Codec B] [Codec C] in
lemma fold_prepend (as : List (List A)) (bs : List A) :
    as.foldl (fun bs a=>a++bs) bs=as.reverse.flatten++bs := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih => simp [List.foldl_cons,ih,List.flatten_append,List.append_assoc]
lemma weight_flatten (as : List (List A)) : weight as.flatten≤weight as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.flatten_cons,weight_cons]
    have h:=weight_append a as.flatten
    omega

def flatten : Realizer (List.flatten (α:=A)) :=
  (composition (pair reverse (constant ([] : List A))) (fold append)).congr (by
    intro as
    change as.reverse.foldl (fun bs a=>a++bs) []=as.flatten
    rw [fold_prepend,List.reverse_reverse,List.append_nil])
lemma polynomial_flatten : PolynomialTime (flatten (A:=A)) := by
  unfold flatten
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair polynomial_reverse (polynomial_constant []))
  apply polynomial_fold polynomial_append (2*X+1)
  intro as bs pre post he
  rw [fold_prepend]
  have h1:=weight_append pre.reverse.flatten bs
  have h2:=weight_flatten pre.reverse
  rw [weight_reverse] at h2
  have h3:=weight_prefix he
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  omega

def flatMapPoly {f : A → List B} (F : Realizer f) : Realizer (List.flatMap f) :=
  (composition (map F) flatten).congr (by intro as; rfl)
lemma polynomial_flatMapPoly {f : A → List B} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (flatMapPoly F) :=
  polynomial_congr _ (polynomial_composition (polynomial_map hF) polynomial_flatten)

variable [LinearOrder A]
def finsetSingleton : Realizer (fun a : A=>({a} : Finset A)) :=
  (composition (pair identity (constant ([] : List A))) listCons).recode id
    (fun a=>({a} : Finset A)) (fun _=>rfl) (by intro a; simp only [Function.comp_apply,encode_finset,Finset.sort_singleton]; rfl)
lemma polynomial_finsetSingleton : PolynomialTime (finsetSingleton (A:=A)) := by
  unfold finsetSingleton
  exact polynomial_recode _ _ _ _ (polynomial_composition
    (polynomial_pair polynomial_identity (polynomial_constant [])) polynomial_listCons)

def finsetInsert (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (R : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (fun x : A×Finset A=>insert x.1 x.2) :=
  (composition (pair (composition first finsetSingleton) second) (finsetUnion E R)).congr (by intro x; simp)
lemma polynomial_finsetInsert {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    (hE : PolynomialTime E) (hR : PolynomialTime R) : PolynomialTime (finsetInsert E R) :=
  polynomial_congr _ (polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_first polynomial_finsetSingleton) polynomial_second)
    (polynomial_finsetUnion hE hR))

variable [LinearOrder B]
def finsetBiUnion {f : C×A → Finset B} (F : Realizer f)
    (E : Realizer (fun x : B×B=>decide (x.1=x.2)))
    (R : Realizer (fun x : B×B=>decide (x.1≤x.2))) :
    Realizer (fun x : C×Finset A=>x.2.biUnion (fun a=>f (x.1,a))) :=
  (composition (composition (composition (pair first (composition second finsetList))
    (mapWith (composition F finsetList))) flatten) (listFinset E R)).congr (by
      intro x
      ext b
      simp only [Function.comp_apply,List.mem_toFinset,List.mem_flatten,List.mem_map,
        Finset.mem_biUnion,Finset.mem_sort]
      constructor
      · rintro ⟨bs,⟨a,ha,rfl⟩,hb⟩
        exact ⟨a,ha,(Finset.mem_sort (r:=fun x y : B=>x≤y)).mp hb⟩
      · rintro ⟨a,ha,hb⟩
        exact ⟨(f (x.1,a)).sort (·≤·),⟨a,ha,rfl⟩,(Finset.mem_sort (r:=fun x y : B=>x≤y)).mpr hb⟩)
lemma polynomial_finsetBiUnion {f : C×A → Finset B} {F : Realizer f}
    {E : Realizer (fun x : B×B=>decide (x.1=x.2))}
    {R : Realizer (fun x : B×B=>decide (x.1≤x.2))}
    (hF : PolynomialTime F) (hE : PolynomialTime E) (hR : PolynomialTime R) :
    PolynomialTime (finsetBiUnion F E R) := by
  unfold finsetBiUnion
  apply polynomial_congr
  exact polynomial_composition (polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_finsetList))
    (polynomial_mapWith (polynomial_composition hF polynomial_finsetList))) polynomial_flatten)
    (polynomial_listFinset hE hR)
end MatchingFPRAS.TreeTyped

end OAI
