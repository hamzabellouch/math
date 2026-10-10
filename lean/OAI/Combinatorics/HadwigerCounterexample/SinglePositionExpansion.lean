import OAI.Combinatorics.HadwigerCounterexample.FourCornerViews
import OAI.Combinatorics.HadwigerCounterexample.ScriptGramCorrespondence

namespace OAI

/-! # Single Position Expansion -/

noncomputable section
namespace HadwigerCounterexample
open Finset Function Matrix
open scoped BigOperators
variable {I A B C : Type} [Fintype I] [DecidableEq I]
variable {p : Shape} {n N : ℕ}
variable {X : I → Type}

abbrev Aside (i : I) := {j:I//j≠i}
def chair (X : I →Type) (i:I) := Equiv.piSplitAt i X

theorem chair_split (p : ∀ i,Wgt (X i)) (x : ∀ i,X i) (a : I) :
    prodW p x = p a (x a) *
      prodW (fun i : Aside a=>p i.val) ((chair X a x).2) := by
  exact Fintype.prod_eq_mul_prod_subtype_ne _ _

variable [∀ i,Fintype (X i)]
set_option maxHeartbeats 600000 in
theorem chair_weight (p : ∀ i,Wgt (X i)) (a : I) :
    mapW (prodW p) (chair X a)= pairW (p a)
      (prodW (fun i : Aside a=>p i.val)) := by
  funext i
  obtain ⟨i,rfl⟩ := (chair X a).surjective i
  rw [mapW_equiv_val,Equiv.symm_apply_apply]; exact chair_split p i a

def arm (i j : I) (x : Corn) := if j=i then x.1 else x.2
omit [Fintype I] [∀ i,Fintype (X i)] in
theorem chair_arm (p : (∀ i,X i)×(∀ i,X i)) (i j : I) (x : Corn) :
    criss (chair X i) p x j=(onSide p (arm i j x)) j := by
  rcases x with ⟨a,b⟩
  have he := criss_pair p a b (chair X i)
  by_cases h : j=i
  · subst j
    rw [arm,ite_eq_left rfl]; exact congrArg Prod.fst he
  rw [arm,ite_eq_right h]
  exact congr_fun (congrArg Prod.snd he) (⟨j,h⟩:Aside i)

namespace Template
variable (v : Template p I)

def beyond (v : Template p I) (i : I) : Template p (Aside i) :=
  collect p v Subtype.val
def chairK (v : Template p I) (i : I) (N : ℕ) :
    Keys (p:=p) v.t N ≃ (AtomKey (p:=p) (v.t i) N × Keys (p:=p) (v.beyond i).t N) :=
  chair _ _
def chairI (_ : Template p I) (i : I) (n : ℕ) :
    Inputs p n I ≃ Knobs p.g n × Inputs p n (Aside i) := chair _ _

omit [Fintype I] in
theorem key_quoin (v : Template p I) (x : I) (o : UnitType p n N)
    (p' : Inputs p n I× Inputs p n I) (c : Corn) :
    criss (v.chairK x N) (Prod.map (v.resultKey o) (v.resultKey o) p') c=
      v.resultKey o (criss (v.chairI x n) p' c) := by
  classical
  funext i; unfold resultKey
  change criss (chair (fun i=>AtomKey (p:=p) (v.t i) N) x) _ _ i=keyOne p _ _ (lit _ _ (criss (chair (fun _=>Knobs p.g n) x) _ _ i)) _
  rw [chair_arm _ x,chair_arm _ x]
  cases arm x i c <;> rfl

omit [Fintype I] in
theorem key_split (v : Template p I) (x : I) (o : UnitType p n N)
    (z : Inputs p n I) :
    chairK v x N (v.resultKey o z) = (v.callOne x (z x) (onSide o (v.aim x)),
      (v.beyond x).resultKey o (fun i=>z i.val)) := by
  apply Prod.ext <;> rfl

def earns (v : Template p I) (s : Script p I) (m : Mixer p n) (q : I→F)
    (o : UnitType p n N) (x : Inputs p n I) :=
  (v.draw x).reads s m ∧ ownPart (p:=p) v.t q (v.resultKey o x)
end Template
end HadwigerCounterexample

end

end OAI
