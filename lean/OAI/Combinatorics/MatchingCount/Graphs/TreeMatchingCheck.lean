import Mathlib
import OAI.Combinatorics.MatchingCount.Complexity.TreeCostTactic

namespace OAI

namespace MatchingFPRAS.TreeTyped.SparseProgram
open TreeTyped

variable {E V C : Type} [Codec E] [Codec V] [Codec C] [LinearOrder E] [LinearOrder V]

def matchingCheck (p : C×(E×V)→Bool) (x : (C×Finset V)×Finset E) : Bool :=
  decide (∀ v∈x.1.2,(x.2.filter (fun e=>p (x.1.1,(e,v))=true)).card=1)
def matchingCheckRealizer {p : C×(E×V)→Bool} (P : Realizer p) :
    Realizer (matchingCheck p) := by
  let incident : Realizer (fun x : (C×V)×E=>p (x.1.1,(x.2,x.1.2))) :=
    composition (pair first.fst (pair second first.snd)) P
  let degree : Realizer (fun x : (C×Finset E)×V=>
      (x.1.2.filter (fun e=>p (x.1.1,(e,x.2))=true)).card) :=
    (composition (composition (pair (pair first.fst second) first.snd)
      (finsetFilterWith incident)) finsetCard).congr (fun _=>rfl)
  exact (composition (pair (pair first.fst second) first.snd)
    (finsetAll (composition (pair degree (constant 1)) natEqual))).congr (by
      intro x; simp only [Function.comp_apply,decide_eq_true_eq]; rfl)
lemma polynomial_matchingCheck {p : C×(E×V)→Bool} {P : Realizer p} (hP : PolynomialTime P) :
    PolynomialTime (matchingCheckRealizer P) := by
  unfold matchingCheckRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  tree_cost

instance decideMatchingOn [Fintype E] [Fintype V] (inc : E→V→Prop) [DecidableRel inc] (M : Finset E) :
    Decidable (Transport.MatchingOn inc M Finset.univ) := by
  unfold Transport.MatchingOn ExistsUnique
  infer_instance

omit [Codec E] [Codec V] [Codec C] in
lemma matchingCheck_eq [Fintype E] [Fintype V] (p : C×(E×V)→Bool) (c : C) (inc : E→V→Prop)
    [DecidableRel inc] (hp : ∀ e v,p (c,(e,v))=decide (inc e v)) (M : Finset E) :
    matchingCheck p ((c,Finset.univ),M)=decide (Transport.MatchingOn inc M Finset.univ) := by
  apply Bool.eq_iff_iff.mpr
  simp only [matchingCheck,decide_eq_true_eq,Finset.mem_univ,forall_const,hp]
  unfold Transport.MatchingOn
  simp only [Finset.mem_univ,implies_true,true_and]
  apply forall_congr'
  intro v
  rw [Finset.card_eq_one_iff_existsUnique]
  simp
end MatchingFPRAS.TreeTyped.SparseProgram

end OAI
