import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeQuad

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A : Type} [Codec A] [LinearOrder A]
def listNodup (Eq : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (Le : Realizer (fun x : A×A=>decide (x.1≤x.2))) : Realizer (fun xs : List A=>decide xs.Nodup) :=
  (composition (pair (composition (listFinset Eq Le) finsetCard) listLength) natEqual).congr (by
    intro xs
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,decide_eq_true_eq]
    exact Multiset.toFinset_card_eq_card_iff_nodup (m:= (xs : Multiset A)))
lemma polynomial_listNodup {Eq : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {Le : Realizer (fun x : A×A=>decide (x.1≤x.2))} (hEq : PolynomialTime Eq) (hLe : PolynomialTime Le) :
    PolynomialTime (listNodup Eq Le) := by
  unfold listNodup
  apply polynomial_congr
  have := polynomial_listFinset hEq hLe
  tree_cost

def quadInjective (Eq : Realizer (fun x : A×A=>decide (x.1=x.2)))
    (Le : Realizer (fun x : A×A=>decide (x.1≤x.2))) :
    Realizer (fun q : Quad A=>decide (Function.Injective (quadFn q))) :=
  (composition quadListRealizer (listNodup Eq Le)).congr (by
    intro q
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,decide_eq_true_eq,quadList_ofFn,List.nodup_ofFn])
lemma polynomial_quadInjective {Eq : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {Le : Realizer (fun x : A×A=>decide (x.1≤x.2))} (hEq : PolynomialTime Eq) (hLe : PolynomialTime Le) :
    PolynomialTime (quadInjective Eq Le) :=
  polynomial_congr _ (polynomial_composition polynomial_quadList (polynomial_listNodup hEq hLe))
end MatchingFPRAS.TreeTyped

end OAI
