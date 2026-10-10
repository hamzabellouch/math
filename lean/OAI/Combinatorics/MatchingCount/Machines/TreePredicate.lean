import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeListOps

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B : Type} [Codec A] [Codec B]

def boolNot : Realizer Bool.not :=
  (choose identity (constant false) (constant true)).congr (by intro b; cases b <;> rfl)
def boolAnd : Realizer (fun x : Bool×Bool=>x.1 && x.2) :=
  (choose first second (constant false)).congr (by intro x; cases x.1 <;> rfl)
def natEqual : Realizer (fun x : ℕ×ℕ=>decide (x.1=x.2)) :=
  (choose less (constant false)
    (choose (composition (pair second first) less) (constant false) (constant true))).congr (by
    intro x
    change (if decide (x.1<x.2) then false else if decide (x.2<x.1) then false else true)=_
    by_cases h : x.1<x.2
    · simp [h,Nat.ne_of_lt h]
    · by_cases h' : x.2<x.1
      · simp [h,h',Ne.symm (Nat.ne_of_lt h')]
      · have e : x.1=x.2 := by omega
        simp [e])

def any : Realizer (fun bs : List Bool=>bs.any id) :=
  (composition (pair identity (constant false))
    (fold (choose first (constant true) second))).congr (by
      intro bs
      change bs.foldl (fun z b=>if b then true else z) false=bs.any id
      have h : ∀ z, bs.foldl (fun z b=>if b then true else z) z=(bs.any id || z) := by
        induction bs with
        | nil => intro z; rfl
        | cons b bs ih =>
          intro z
          simp only [List.foldl_cons,ih,List.any_cons]
          cases b <;> cases bs.any id <;> cases z <;> rfl
      rw [h]
      cases bs.any id <;> rfl)

def membership : Realizer (fun x : List ℕ×ℕ=>decide (x.2∈x.1)) :=
  (composition (composition (pair second first) (mapWith natEqual)) any).congr (by
    intro x
    simp only [Function.comp_apply,List.any_map]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true,Function.comp_apply,decide_eq_true_eq,id_eq]
    constructor
    · rintro ⟨a,ha,e⟩; simpa [←e] using ha
    · intro h; exact ⟨x.2,h,rfl⟩)

def countTrue : Realizer (fun bs : List Bool=>(bs.filter id).length) :=
  composition (filter identity) listLength

def countWith {p : A×B → Bool} (P : Realizer p) :
    Realizer (fun x : A×List B=>(x.2.filter fun b=>p (x.1,b)).length) :=
  (composition (mapWith P) countTrue).congr (by
    intro x; simp only [Function.comp_apply,List.filter_map,List.length_map]; rfl)

def listSum : Realizer (List.sum : List ℕ → ℕ) :=
  (composition (pair identity (constant 0)) (fold add)).congr (by
    intro as
    change as.foldl (fun n a=>a+n) 0=as.sum
    have h : ∀ z,as.foldl (fun n a=>a+n) z=as.sum+z := by
      induction as with
      | nil => intro z; simp
      | cons a as ih => intro z; simp only [List.foldl_cons,ih,List.sum_cons]; omega
    simpa using h 0)

def listProd : Realizer (List.prod : List ℕ → ℕ) :=
  (composition (pair identity (constant 1)) (fold multiply)).congr (by
    intro as
    change as.foldl (fun n a=>a*n) 1=as.prod
    have h : ∀ z,as.foldl (fun n a=>a*n) z=as.prod*z := by
      induction as with
      | nil => intro z; simp
      | cons a as ih => intro z; simp only [List.foldl_cons,ih,List.prod_cons]; ring
    simpa using h 1)

end MatchingFPRAS.TreeTyped

end OAI
