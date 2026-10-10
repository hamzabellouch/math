import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeFrame
import OAI.Combinatorics.MatchingCount.Machines.TreeRepeat

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B X : Type} [Codec A] [Codec B] [Codec X]

def listCase (b : B) {g : A×List A → B} (G : Realizer g) :
    Realizer (fun as : List A=>match as with | []=>b | a::as=>g (a,as)) where
  program := RegisterStructured.select 0 (constant b (A:=List A)).program G.program
  cost := fun as=>3+match as with | []=>(constant b (A:=List A)).cost [] | a::as=>G.cost (a,as)
  correct := by
    intro as s
    cases as with
    | nil =>
      have hh:=RegisterStructured.select_nil 0 _ G.program (env (encode ([] : List A)) .nil s)
        (env (encode b) .nil s) _ rfl ((constant b (A:=List A)).correct [] s)
      exact hh.mono (by dsimp; omega)
    | cons a as =>
      have hh:=RegisterStructured.select_cons 0 (constant b (A:=List A)).program _
        (env (encode (a::as)) .nil s) (env (encode (g (a,as))) .nil s) _ (encode a) (encode as) rfl
        (G.correct (a,as) s)
      exact hh.mono (by dsimp; omega)

def head (d : A) : Realizer (fun as : List A=>as.headD d) :=
  (listCase d first).congr (by intro as; cases as <;> rfl)

def tail : Realizer (List.tail : List A → List A) := listCase [] second

def isEmpty : Realizer (List.isEmpty : List A → Bool) := listCase true (constant false)

def dropStep (x : ℕ×List A) : List A := x.2.tail
omit [Codec A] [Codec B] [Codec X] in
lemma countDown_drop (n : ℕ) (as : List A) : countDown (dropStep (A:=A)) n as=as.drop n := by
  induction n generalizing as with
  | zero => rfl
  | succ n ih =>
    rw [countDown,ih]
    exact List.drop_tail

def drop : Realizer (fun x : List A×ℕ=>x.1.drop x.2) :=
  (composition (pair second first) (iterateDown (composition second tail))).congr (by
    intro x; exact countDown_drop x.2 x.1)
def getD (d : A) : Realizer (fun x : List A×ℕ=>x.1.getD x.2 d) :=
  (composition drop (head d)).congr (by
    intro x
    simp only [Function.comp_apply, List.headD_eq_head?_getD, List.head?_drop,
      List.getD_eq_getElem?_getD])

def mapStep (g : X×A → B) (z : A×(X×List B)) : X×List B :=
  (z.2.1,g (z.2.1,z.1)::z.2.2)
def mapStepRealizer {g : X×A → B} (G : Realizer g) : Realizer (mapStep g) :=
  pair (composition second first)
    (composition (pair (composition (pair (composition second first) first) G)
      (composition second second)) listCons)

omit [Codec A] [Codec B] [Codec X] in
lemma mapStep_fold (g : X×A → B) (as : List A) (x : X) (bs : List B) :
    as.foldl (fun z a=>mapStep g (a,z)) (x,bs)=(x,(as.map (fun a=>g (x,a))).reverse++bs) := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
    change as.foldl _ (x,g (x,a)::bs)=_
    rw [ih]
    simp only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append]

def mapWith {g : X×A → B} (G : Realizer g) : Realizer (fun xas : X×List A=>xas.2.map (fun a=>g (xas.1,a))) :=
  (composition (composition (pair second (pair first (constant ([] : List B)))) (fold (mapStepRealizer G)))
    (composition second reverse)).congr (by
      intro xas
      change ((xas.2.foldl _ (xas.1,[])).2).reverse=_
      rw [mapStep_fold]
      simp)

def map {g : A → B} (G : Realizer g) : Realizer (List.map g) := by
  let S : Realizer (fun x : A×List B=>g x.1::x.2) := composition (pair (composition first G) second) listCons
  exact (composition (composition (pair identity (constant ([] : List B))) (fold S)) reverse).congr (by
    intro as
    change (as.foldl (fun bs a=>g a::bs) []).reverse=as.map g
    simp)

def listLength : Realizer (List.length : List A → ℕ) :=
  (composition (pair identity (constant 0))
    (fold (composition (pair second (constant 1)) add))).congr (by
      intro as
      change as.foldl (fun n (_ : A)=>n+1) 0=as.length
      have h : ∀ n,as.foldl (fun n (_ : A)=>n+1) n=n+as.length := by
        induction as with
        | nil => intro n; simp
        | cons a as ih => intro n; simp only [List.foldl_cons,ih,List.length_cons]; omega
      simpa only [Nat.zero_add] using h 0)

def append : Realizer (fun x : List A×List A=>x.1++x.2) :=
  (composition (pair (composition first reverse) second) (fold listCons)).congr (by
    intro x
    change x.1.reverse.foldl (fun bs a=>a::bs) x.2=x.1++x.2
    rw [List.foldl_flip_cons_eq_append',List.reverse_reverse])

def filter {f : A → Bool} (F : Realizer f) : Realizer (List.filter f) := by
  let S : Realizer (fun x : A×List A=>if f x.1 then x.1::x.2 else x.2) :=
    choose (composition first F) listCons second
  exact (composition (composition (pair identity (constant ([] : List A))) (fold S)) reverse).congr (by
    intro as
    change (as.foldl (fun bs a=>if f a then a::bs else bs) []).reverse=as.filter f
    have h : ∀ bs,as.foldl (fun bs a=>if f a then a::bs else bs) bs=(as.filter f).reverse++bs := by
      induction as with
      | nil => intro bs; rfl
      | cons a as ih =>
        intro bs
        cases hf : f a <;> simp [List.foldl_cons,hf,ih,List.append_assoc]
    rw [h]
    simp)
end MatchingFPRAS.TreeTyped

end OAI
