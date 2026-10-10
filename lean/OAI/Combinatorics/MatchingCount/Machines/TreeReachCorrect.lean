import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeReach
import OAI.Combinatorics.MatchingCount.Complexity.TreePolyTactic

namespace OAI

namespace MatchingFPRAS.TreeTyped.FiniteReach
variable {A C : Type} [Codec A] [Codec C] [LinearOrder A] [Fintype A]
variable {p : C×(A×A) → Bool}
omit [Codec A] [Codec C]
lemma grow_source (G : SimpleGraph A) [DecidableRel G.Adj] (c : C)
    (hp : ∀ a b,p (c,(a,b))=decide (G.Adj a b)) (s : Finset A) :
    grow p ((c,Finset.univ),s)=ComputableReach.grow G s := by
  ext a
  simp only [grow,ComputableReach.grow,Finset.mem_union,Finset.mem_filter,hp,decide_eq_true_eq]
lemma reach_source (G : SimpleGraph A) [DecidableRel G.Adj] (c : C)
    (hp : ∀ a b,p (c,(a,b))=decide (G.Adj a b)) (s : Finset A) :
    reach p ((c,Finset.univ),s)=ComputableReach.reached G s (Fintype.card A) := by
  rw [reach_eq,Finset.card_univ]
  have he : (fun s=>grow p ((c,Finset.univ),s))=ComputableReach.grow G := funext (grow_source G c hp)
  rw [he]
  rfl
lemma reach_closure (G : SimpleGraph A) [DecidableRel G.Adj] (c : C)
    (hp : ∀ a b,p (c,(a,b))=decide (G.Adj a b)) (a : A) :
    reach p ((c,Finset.univ),{a})=ComputableReach.closure G a := reach_source G c hp {a}
end MatchingFPRAS.TreeTyped.FiniteReach

namespace MatchingFPRAS.TreeTyped
variable {A B C : Type} [Codec A] [Codec B] [Codec C] [LinearOrder A] [LinearOrder B]
def finsetImageWith {f : C×A → B} (F : Realizer f)
    (E : Realizer (fun x : B×B=>decide (x.1=x.2)))
    (R : Realizer (fun x : B×B=>decide (x.1≤x.2))) :
    Realizer (fun x : C×Finset A=>x.2.image (fun a=>f (x.1,a))) :=
  (composition (composition (pair first (composition second finsetList)) (mapWith F)) (listFinset E R)).congr (by
    intro x; ext b
    simp only [Function.comp_apply,List.mem_toFinset,List.mem_map,Finset.mem_sort,Finset.mem_image])
lemma polynomial_finsetImageWith {f : C×A → B} {F : Realizer f}
    {E : Realizer (fun x : B×B=>decide (x.1=x.2))}
    {R : Realizer (fun x : B×B=>decide (x.1≤x.2))}
    (hF : PolynomialTime F) (hE : PolynomialTime E) (hR : PolynomialTime R) :
    PolynomialTime (finsetImageWith F E R) := by
  unfold finsetImageWith
  apply polynomial_congr
  apply polynomial_composition _ (polynomial_listFinset hE hR)
  tree_poly
end MatchingFPRAS.TreeTyped

end OAI
