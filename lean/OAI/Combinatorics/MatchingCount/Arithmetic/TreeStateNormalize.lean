import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeReach
import OAI.Combinatorics.MatchingCount.Machines.TreeStateTable

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped Polynomial

variable {I E : Type} [Codec I] [Codec E] [DecidableEq I] [Inhabited I] [LinearOrder E]
abbrev StateEnvelope (I E : Type) := List I×Finset E

def normalizeState (x : StateEnvelope I E×StateTable I (Finset E)) : StateTable I (Finset E) :=
  x.1.1.map (fun i=>(i,lookup ∅ (x.2,i)∩x.1.2))
def normalizeStateRealizer (Eq : Realizer (fun x : I×I=>decide (x.1=x.2)))
    (EqE : Realizer (fun x : E×E=>decide (x.1=x.2))) : Realizer (normalizeState (I:=I) (E:=E)) :=
  (composition (pair identity first.fst) (mapWith (pair second
    (composition (pair (composition (pair first.snd second) (lookupRealizer ∅ Eq)) first.fst.snd)
      (finsetInter EqE))))).congr (fun _=>rfl)
lemma polynomial_normalizeState {Eq : Realizer (fun x : I×I=>decide (x.1=x.2))}
    {EqE : Realizer (fun x : E×E=>decide (x.1=x.2))}
    (hEq : PolynomialTime Eq) (hE : PolynomialTime EqE) : PolynomialTime (normalizeStateRealizer Eq EqE) := by
  unfold normalizeStateRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_lookup (∅ : Finset E) hEq
  tree_cost

omit [Inhabited I] in
lemma normalizeState_weight (keys : List I) (univ : Finset E) (s : StateTable I (Finset E)) :
    weight (normalizeState ((keys,univ),s))≤(weight keys+1)*(weight univ+3) := by
  induction keys with
  | nil=>simp only [normalizeState,List.map_nil,weight_nil]; omega
  | cons i keys ih=>
    have hu : weight (lookup ∅ (s,i)∩univ)≤weight univ := weight_finset_subset Finset.inter_subset_right
    change weight ((i,lookup ∅ (s,i)∩univ)::normalizeState ((keys,univ),s))≤_
    rw [weight_cons,weight_prod,weight_cons]
    nlinarith

omit [Codec I] [Codec E] [Inhabited I] in
lemma normalizeState_rep {Ω : Type} (keys : List I) (univ : Finset E) (e : Ω→Finset E)
    (he : ∀ a,e a⊆univ) (s : I→Ω) :
    normalizeState ((keys,univ),stateRep keys (e ∘ s))=stateRep keys (e ∘ s) := by
  unfold normalizeState stateRep
  apply List.map_congr_left
  intro i hi
  change (i,lookup ∅ (stateRep keys (e ∘ s),i)∩univ)=(i,e (s i))
  rw [lookup_stateRep ∅ keys (e ∘ s) i hi]
  simp only [Function.comp_apply,Finset.inter_eq_left.mpr (he (s i))]
end MatchingFPRAS.ExecutableLadder

end OAI
