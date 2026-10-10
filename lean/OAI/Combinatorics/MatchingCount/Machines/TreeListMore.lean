import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeListOps

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B X : Type} [Codec A] [Codec B] [Codec X]

def takeStep (z : ℕ×(List A×List A)) : List A×List A :=
  match z.2.1 with
  | [] => z.2
  | a::as => (as,a::z.2.2)

def takeStepRealizer (d : A) : Realizer (takeStep (A:=A)) :=
  (choose (composition (composition second first) isEmpty) second
    (pair (composition (composition second first) tail)
      (composition (pair (composition (composition second first) (head d))
        (composition second second)) listCons))).congr (by
        intro z; cases h : z.2.1 <;> simp [takeStep,h])

omit [Codec A] in
lemma countDown_take (n : ℕ) (as bs : List A) :
    countDown (takeStep (A:=A)) n (as,bs)=(as.drop n,(as.take n).reverse++bs) := by
  induction n generalizing as bs with
  | zero => simp [countDown]
  | succ n ih =>
    cases as with
    | nil => simpa [countDown,takeStep] using ih [] bs
    | cons a as =>
      simp only [countDown,takeStep,ih,List.drop_succ_cons,List.take_succ_cons,
        List.reverse_cons,List.append_assoc,List.singleton_append]

def take (d : A) : Realizer (fun x : List A×ℕ=>x.1.take x.2) :=
  (composition (composition (pair second (pair first (constant ([] : List A))))
    (iterateDown (takeStepRealizer d))) (composition second reverse)).congr (by
      intro x
      change ((countDown takeStep x.2 (x.1,[])).2).reverse=_
      rw [countDown_take]
      simp)

def flatMap {f : A → List B} (F : Realizer f) : Realizer (List.flatMap f) := by
  let S : Realizer (fun x : A×List B=>(f x.1).reverse++x.2) :=
    composition (pair (composition (composition first F) reverse) second) append
  exact (composition (composition (pair identity (constant ([] : List B))) (fold S)) reverse).congr (by
    intro as
    change (as.foldl (fun bs a=>(f a).reverse++bs) []).reverse=as.flatMap f
    have h : ∀ bs,as.foldl (fun bs a=>(f a).reverse++bs) bs=(as.flatMap f).reverse++bs := by
      induction as with
      | nil => intro bs; rfl
      | cons a as ih => intro bs; simp [List.foldl_cons,ih,List.reverse_append,List.append_assoc]
    rw [h]
    simp)

def minimum : Realizer (fun x : ℕ×ℕ=>min x.1 x.2) :=
  (choose less first second).congr (by intro x; simp only [decide_eq_true_eq]; split_ifs with h <;> omega)
def maximum : Realizer (fun x : ℕ×ℕ=>max x.1 x.2) :=
  (choose less second first).congr (by intro x; simp only [decide_eq_true_eq]; split_ifs with h <;> omega)

def listMin (x : List ℕ×ℕ) : ℕ := x.1.foldl min x.2
def listMinRealizer : Realizer listMin :=
  (fold minimum).congr (by intro x; dsimp only [listMin]; congr 1; funext a b; exact Nat.min_comm b a)

lemma listMin_le_default (as : List ℕ) (d : ℕ) : listMin (as,d)≤d := by
  induction as generalizing d with
  | nil => rfl
  | cons a as ih => exact (ih (min d a)).trans (min_le_left _ _)

lemma listMin_le {as : List ℕ} {d a : ℕ} (ha : a∈as) : listMin (as,d)≤a := by
  induction as generalizing d with
  | nil => simp at ha
  | cons b bs ih =>
    simp only [List.mem_cons] at ha
    rcases ha with rfl|ha
    · exact (listMin_le_default bs (min d a)).trans (min_le_right _ _)
    · exact ih ha

lemma le_listMin {as : List ℕ} {d a : ℕ} (hd : a≤d) (ha : ∀ b∈as,a≤b) :
    a≤listMin (as,d) := by
  induction as generalizing d with
  | nil => exact hd
  | cons b bs ih =>
    apply ih (le_min hd (ha b (by simp)))
    intro c hc; exact ha c (by simp [hc])
end MatchingFPRAS.TreeTyped

end OAI
