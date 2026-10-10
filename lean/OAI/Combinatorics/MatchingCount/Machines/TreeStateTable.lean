import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeLabelTable
import OAI.Combinatorics.MatchingCount.Machines.TreeSum

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped

variable {I A : Type} [Codec I] [Codec A] [DecidableEq I] [Inhabited I]
abbrev StateTable (I A : Type) := List (I×A)

def lookup (d : A) (x : StateTable I A×I) : A :=
  ((x.1.filter (fun z=>decide (z.1=x.2))).headD (x.2,d)).2
def lookupRealizer (d : A) (E : Realizer (fun x : I×I=>decide (x.1=x.2))) : Realizer (lookup (I:=I) d) := by
  let P : Realizer (fun x : I×(I×A)=>decide (x.2.1=x.1)) := composition (pair second.fst first) E
  let F := composition (pair second first) (filterWith P)

  let H : Realizer (fun x : I×List (I×A)=>((x.2.headD (x.1,d)).2)) :=
    (composition (choose (composition second isEmpty) (pair first (constant d))
      (composition second (head (default,d)))) second).congr (by
        intro x; rcases x with ⟨i,as⟩; cases as <;> rfl)
  exact (composition (pair second F) H).congr (fun _=>rfl)
lemma polynomial_lookup (d : A) {E : Realizer (fun x : I×I=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (lookupRealizer d E) := by
  unfold lookupRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_composition
  · exact polynomial_pair polynomial_second (polynomial_composition
      (polynomial_pair polynomial_second polynomial_first)
      (polynomial_filterWithList (polynomial_composition
        (polynomial_pair (polynomial_fst polynomial_second) polynomial_first) hE)))
  · apply polynomial_congr
    have := polynomial_isEmpty (A:=I×A)
    have := polynomial_head ((default : I),d)
    tree_cost

def stateRep (keys : List I) (s : I→A) : StateTable I A := keys.map (fun i=>(i,s i))
omit [Codec I] [Codec A] [Inhabited I] in
lemma lookup_stateRep (d : A) (keys : List I) (s : I→A) (i : I) (hi : i∈keys) :
    lookup d (stateRep keys s,i)=s i := by
  induction keys with
  | nil=>simp at hi
  | cons j keys ih=>
    simp only [List.mem_cons] at hi
    by_cases hji : j=i
    · subst j
      simp [lookup,stateRep]
    · have hn : i∈keys:=hi.resolve_left (Ne.symm hji)
      simpa [lookup,stateRep,hji] using ih hn

def setState (x : StateTable I A×(I×A)) : StateTable I A :=
  x.1.map fun z=>(z.1,if z.1=x.2.1 then x.2.2 else z.2)
def setStateRealizer (E : Realizer (fun x : I×I=>decide (x.1=x.2))) : Realizer (setState (I:=I) (A:=A)) :=
  (composition (pair second first) (mapWith (pair second.fst
    (choose (composition (pair second.fst first.fst) E) first.snd second.snd)))).congr (by
      intro x; simp only [setState,Function.comp_apply,decide_eq_true_eq])
omit [Inhabited I] in
lemma polynomial_setState {E : Realizer (fun x : I×I=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (setStateRealizer (A:=A) E) := by
  unfold setStateRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  tree_cost
omit [Codec I] [Codec A] [Inhabited I] in
lemma setState_rep (keys : List I) (s : I→A) (i : I) (a : A) :
    setState (stateRep keys s,(i,a))=stateRep keys (Function.update s i a) := by
  unfold setState stateRep
  simp only [List.map_map]
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_apply,Function.update_apply]

def setPair (x : StateTable I A×((I×I)×(A×A))) : StateTable I A :=
  setState (setState (x.1,(x.2.1.1,x.2.2.1)),(x.2.1.2,x.2.2.2))
def setPairRealizer (E : Realizer (fun x : I×I=>decide (x.1=x.2))) : Realizer (setPair (I:=I) (A:=A)) :=
  (composition (pair (composition (pair first (pair second.fst.fst second.snd.fst)) (setStateRealizer E))
    (pair second.fst.snd second.snd.snd)) (setStateRealizer E)).congr (fun _=>rfl)
omit [Inhabited I] in
lemma polynomial_setPair {E : Realizer (fun x : I×I=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (setPairRealizer (A:=A) E) := by
  unfold setPairRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_setState (A:=A) hE
  tree_cost
omit [Codec I] [Codec A] [Inhabited I] in
lemma setPair_rep (keys : List I) (s : I→A) (i j : I) (a : A×A) :
    setPair (stateRep keys s,((i,j),a))=stateRep keys (Replica.replacePair i j s a) := by
  simp only [setPair,setState_rep,Replica.replacePair]
end MatchingFPRAS.ExecutableLadder

end OAI
