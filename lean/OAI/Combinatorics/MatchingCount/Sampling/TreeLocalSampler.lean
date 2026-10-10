import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeStateTable

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped

variable {I A B C : Type} [Codec I] [Codec A] [Codec B] [Codec C]
variable [DecidableEq I] [Inhabited I] [Inhabited A]
local instance treeLocalSamplerUpdateInhabited : Inhabited (Replica.Update I) := ⟨Sum.inr default⟩

abbrev LocalContext (C I A B : Type) := C×(StateTable I A×B)
abbrev LocalPairInput (C I A B : Type) := (C×(I×I))×((A×A)×B)
abbrev LocalRefreshInput (C I B : Type) := (C×I)×B

def localPair (p : LocalPairInput C I A B→A×A)
    (x : LocalContext C I A B×(I×I)) : StateTable I A :=
  setPair (x.1.2.1,(x.2,p ((x.1.1,x.2),
    ((lookup default (x.1.2.1,x.2.1),lookup default (x.1.2.1,x.2.2)),x.1.2.2))))
def localPairRealizer {p : LocalPairInput C I A B→A×A} (P : Realizer p)
    (E : Realizer (fun x : I×I=>decide (x.1=x.2))) : Realizer (localPair p) := by
  let a : Realizer (fun x : LocalContext C I A B×(I×I)=>lookup default (x.1.2.1,x.2.1)) :=
    (composition (pair first.snd.fst second.fst) (lookupRealizer (default : A) E)).congr (fun _=>rfl)
  let b : Realizer (fun x : LocalContext C I A B×(I×I)=>lookup default (x.1.2.1,x.2.2)) :=
    (composition (pair first.snd.fst second.snd) (lookupRealizer (default : A) E)).congr (fun _=>rfl)
  exact (composition (pair first.snd.fst (pair second
    (composition (pair (pair first.fst second) (pair (pair a b) first.snd.snd)) P)))
      (setPairRealizer E)).congr (fun _=>rfl)
lemma polynomial_localPair {p : LocalPairInput C I A B→A×A} {P : Realizer p}
    {E : Realizer (fun x : I×I=>decide (x.1=x.2))}
    (hP : PolynomialTime P) (hE : PolynomialTime E) : PolynomialTime (localPairRealizer P E) := by
  unfold localPairRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_lookup (default : A) hE
  have := polynomial_setPair (A:=A) hE
  tree_cost

def localRefresh (r : LocalRefreshInput C I B→A)
    (x : LocalContext C I A B×I) : StateTable I A :=
  setState (x.1.2.1,(x.2,r ((x.1.1,x.2),x.1.2.2)))
def localRefreshRealizer {r : LocalRefreshInput C I B→A} (R : Realizer r)
    (E : Realizer (fun x : I×I=>decide (x.1=x.2))) : Realizer (localRefresh r) :=
  (composition (pair first.snd.fst (pair second
    (composition (pair (pair first.fst second) first.snd.snd) R))) (setStateRealizer E)).congr (fun _=>rfl)
omit [Inhabited I] [Inhabited A] in
lemma polynomial_localRefresh {r : LocalRefreshInput C I B→A} {R : Realizer r}
    {E : Realizer (fun x : I×I=>decide (x.1=x.2))}
    (hR : PolynomialTime R) (hE : PolynomialTime E) : PolynomialTime (localRefreshRealizer R E) := by
  unfold localRefreshRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_setState (A:=A) hE
  tree_cost

def localSampler (p : LocalPairInput C I A B→A×A) (r : LocalRefreshInput C I B→A)
    (x : LocalContext C I A B×Option (Replica.Update I)) : StateTable I A :=
  x.2.elim x.1.2.1 (Sum.elim (fun ij=>localPair p (x.1,ij)) (fun i=>localRefresh r (x.1,i)))
def localSamplerRealizer {p : LocalPairInput C I A B→A×A} {r : LocalRefreshInput C I B→A}
    (P : Realizer p) (R : Realizer r) (E : Realizer (fun x : I×I=>decide (x.1=x.2))) :
    Realizer (localSampler p r) :=
  (optionCases second.fst (sumCases (localPairRealizer P E) (localRefreshRealizer R E))).congr (fun _=>rfl)
lemma polynomial_localSampler {p : LocalPairInput C I A B→A×A} {r : LocalRefreshInput C I B→A}
    {P : Realizer p} {R : Realizer r} {E : Realizer (fun x : I×I=>decide (x.1=x.2))}
    (hP : PolynomialTime P) (hR : PolynomialTime R) (hE : PolynomialTime E) :
    PolynomialTime (localSamplerRealizer P R E) := by
  unfold localSamplerRealizer
  apply polynomial_congr
  exact polynomial_optionCases (polynomial_fst polynomial_second)
    (polynomial_sumCases (polynomial_localPair hP hE) (polynomial_localRefresh hR hE))

variable {Ω D : Type} [Fintype I] [Fintype Ω] [DecidableEq Ω] [Fintype D] [Nonempty D]
variable (e : Ω→A) (d : D→B) (c : C) (keys : List I) (hk : ∀ i,i∈keys)
variable (p : LocalPairInput C I A B→A×A) (r : LocalRefreshInput C I B→A)
variable (sp : I→I→(Ω×Ω)→D→Ω×Ω) (sr : I→D→Ω)
    (hp : ∀ i j a b,p ((c,(i,j)),((e a.1,e a.2),d b))=(e (sp i j a b).1,e (sp i j a b).2))
    (hr : ∀ i b,r ((c,i),d b)=e (sr i b))
omit [Codec I] [Codec A] [Codec B] [Codec C] [Inhabited I]
    [Fintype I] [Fintype Ω] [DecidableEq Ω] [Fintype D] [Nonempty D] in
include hp hr hk in
lemma localSampler_rep [Fintype I] [Fintype Ω] [DecidableEq Ω] [Fintype D] [Nonempty D]
    (s : I→Ω) (u : Option (Replica.Update I)) (b : D) :
    localSampler p r ((c,(stateRep keys (e ∘ s),d b)),u)=
      stateRep keys (e ∘ Replica.localSampler sp sr s u b) := by
  cases u with
  | none => rfl
  | some u=>cases u with
    | inl ij=>
      rcases ij with ⟨i,j⟩
      simp only [localSampler,Option.elim_some,Sum.elim_inl,localPair,
        lookup_stateRep default keys (e ∘ s) _ (hk _),Function.comp_apply,hp i j (s i,s j) b,setPair_rep,
        Replica.localSampler]
      congr 1
      funext z
      simp only [Replica.replacePair,Function.comp_apply,Function.update_apply]
      split_ifs <;> rfl
    | inr i=>
      simp only [localSampler,Option.elim_some,Sum.elim_inr,localRefresh,hr,setState_rep,
        Replica.localSampler]
      congr 1
      funext z
      simp only [Function.comp_apply,Function.update_apply]
      split_ifs <;> rfl
end MatchingFPRAS.ExecutableLadder

end OAI
