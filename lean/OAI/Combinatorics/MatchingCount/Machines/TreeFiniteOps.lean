import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeFinite

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

def all : Realizer (fun bs : List Bool=>bs.all id) :=
  (composition (composition (map boolNot) any) boolNot).congr (by
    intro bs
    change (!((bs.map Bool.not).any id))=bs.all id
    induction bs with
    | nil => rfl
    | cons b bs ih => cases b <;> simp_all)
lemma polynomial_all : PolynomialTime all := by
  unfold all
  exact polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_map polynomial_boolNot) polynomial_any) polynomial_boolNot)

def pairEqual [DecidableEq A] [DecidableEq B]
    (E : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (F : Realizer (fun x : B×B=>decide (x.1=x.2))) :
    Realizer (fun x : (A×B)×(A×B)=>decide (x.1=x.2)) :=
  (composition (pair (composition (pair first.fst second.fst) E)
    (composition (pair first.snd second.snd) F)) boolAnd).congr (by
      intro x
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq,Prod.ext_iff])
lemma polynomial_pairEqual [DecidableEq A] [DecidableEq B]
    {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {F : Realizer (fun x : B×B=>decide (x.1=x.2))}
    (hE : PolynomialTime E) (hF : PolynomialTime F) : PolynomialTime (pairEqual E F) := by
  unfold pairEqual
  exact polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_fst polynomial_first) (polynomial_fst polynomial_second)) hE)
    (polynomial_composition (polynomial_pair (polynomial_snd polynomial_first) (polynomial_snd polynomial_second)) hF)) polynomial_boolAnd)

def leNat : Realizer (fun x : ℕ×ℕ=>decide (x.1≤x.2)) :=
  (composition (composition (pair second first) less) boolNot).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,Bool.not_eq_true',decide_eq_false_iff_not,decide_eq_true_eq,not_lt])
lemma polynomial_leNat : PolynomialTime leNat := by
  unfold leNat
  exact polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_less) polynomial_boolNot)

variable [LinearOrder A]
def finsetAny {p : B×A → Bool} (P : Realizer p) :
    Realizer (fun x : B×Finset A=>decide (∃ a∈x.2,p (x.1,a)=true)) :=
  (composition (composition (pair first (composition second finsetList)) (mapWith P)) any).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,List.any_map,List.any_eq_true,id_eq,decide_eq_true_eq,Finset.mem_sort])
lemma polynomial_finsetAny {p : B×A → Bool} {P : Realizer p} (hP : PolynomialTime P) :
    PolynomialTime (finsetAny P) := by
  unfold finsetAny
  exact polynomial_congr _ (polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_finsetList))
    (polynomial_mapWith hP)) polynomial_any)

def finsetAll {p : B×A → Bool} (P : Realizer p) :
    Realizer (fun x : B×Finset A=>decide (∀ a∈x.2,p (x.1,a)=true)) :=
  (composition (composition (pair first (composition second finsetList)) (mapWith P)) all).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,List.all_map,List.all_eq_true,id_eq,decide_eq_true_eq,Finset.mem_sort])
lemma polynomial_finsetAll {p : B×A → Bool} {P : Realizer p} (hP : PolynomialTime P) :
    PolynomialTime (finsetAll P) := by
  unfold finsetAll
  exact polynomial_congr _ (polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_finsetList))
    (polynomial_mapWith hP)) polynomial_all)

def finsetSubset (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : Finset A×Finset A=>decide (x.1⊆x.2)) :=
  (composition (pair second first) (finsetAll (composition (pair second first) (finsetMember E)))).congr (by
    intro x; simp only [Function.comp_apply,decide_eq_true_eq]; rfl)
lemma polynomial_finsetSubset {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (finsetSubset E) := by
  unfold finsetSubset
  exact polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_finsetAll (polynomial_composition (polynomial_pair polynomial_second polynomial_first) (polynomial_finsetMember hE))))

def finsetEqual (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : Finset A×Finset A=>decide (x.1=x.2)) :=
  (composition (pair (finsetSubset E) (composition (pair second first) (finsetSubset E))) boolAnd).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq,Finset.Subset.antisymm_iff])
lemma polynomial_finsetEqual {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (finsetEqual E) := by
  unfold finsetEqual
  exact polynomial_congr _ (polynomial_composition (polynomial_pair (polynomial_finsetSubset hE)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) (polynomial_finsetSubset hE))) polynomial_boolAnd)

def finsetSDiff (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : Finset A×Finset A=>x.1\x.2) :=
  (composition (pair second first) (finsetFilterWith (composition
    (composition (pair second first) (finsetMember E)) boolNot))).congr (by intro x; ext a; simp)
lemma polynomial_finsetSDiff {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (finsetSDiff E) := by
  unfold finsetSDiff
  exact polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_finsetFilterWith (polynomial_composition
      (polynomial_composition (polynomial_pair polynomial_second polynomial_first) (polynomial_finsetMember hE)) polynomial_boolNot)))

def finsetInter (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : Finset A×Finset A=>x.1∩x.2) :=
  (composition (pair second first) (finsetFilterWith (composition
    (pair second first) (finsetMember E)))).congr (by
      intro x; ext a
      simp only [Function.comp_apply,Finset.mem_filter,decide_eq_true_eq,Finset.mem_inter])
lemma polynomial_finsetInter {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (finsetInter E) := by
  unfold finsetInter
  exact polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_finsetFilterWith (polynomial_composition
      (polynomial_pair polynomial_second polynomial_first) (polynomial_finsetMember hE))))

def finsetErase (E : Realizer (fun x : A×A=>decide (x.1=x.2))) :
    Realizer (fun x : A×Finset A=>x.2.erase x.1) :=
  (finsetFilterWith (composition E boolNot)).congr (by
    intro x; ext a
    simp only [Function.comp_apply,Finset.mem_filter,Bool.not_eq_true',decide_eq_false_iff_not,Finset.mem_erase]
    tauto)
lemma polynomial_finsetErase {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (finsetErase E) := by
  unfold finsetErase
  exact polynomial_congr _ (polynomial_finsetFilterWith (polynomial_composition hE polynomial_boolNot))
end MatchingFPRAS.TreeTyped

end OAI
