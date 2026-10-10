import Mathlib
import OAI.Computability.QuantumFactoring.TensorPreparation
import OAI.Computability.QuantumFactoring.SortedWords

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork
namespace SortedWords

def layout (w : ℕ) : (r : ℕ)→List (Basis w)→Basis (tensorWidth w r)
  | 0,_=>Fin.elim0
  | r+1,xs=>Fin.append (xs.head?.getD (fun _=>false)) (layout w r xs.tail)

def headNet (w r : ℕ) : BooleanNetwork (tensorWidth w (r+1)) w := select (Fin.castAdd (tensorWidth w r))
def tailNet (w r : ℕ) : BooleanNetwork (tensorWidth w (r+1)) (tensorWidth w r) := select (Fin.natAdd w)
lemma headNet_eval (w r : ℕ) (a : Basis w) (x : Basis (tensorWidth w r)) :
    (headNet w r).eval (Fin.append a x)=a := by
  funext i
  exact Fin.append_left _ _ _
lemma tailNet_eval (w r : ℕ) (a : Basis w) (x : Basis (tensorWidth w r)) :
    (tailNet w r).eval (Fin.append a x)=x := by
  funext i
  exact Fin.append_right _ _ _

/-- A recursive subnetwork is used ONCE, with its prefix wire retained. -/
def keepHead {w r : ℕ} (c : BooleanNetwork (tensorWidth w r) (tensorWidth w r)) :
    BooleanNetwork (tensorWidth w (r+1)) (tensorWidth w (r+1)) :=
  (headNet w r).pair ((tailNet w r).comp c)
lemma keepHead_eval {w r : ℕ} (c : BooleanNetwork (tensorWidth w r) (tensorWidth w r))
    (a : Basis w) (x : Basis (tensorWidth w r)) :
    (keepHead c).eval (Fin.append a x)=Fin.append a (c.eval x) := by
  rw [keepHead,eval_pair,eval_comp,headNet_eval,tailNet_eval]
lemma keepHead_count {w r : ℕ} (c : BooleanNetwork (tensorWidth w r) (tensorWidth w r)) :
    (keepHead c).net.count=c.net.count := by
  simp only [keepHead,count_pair,count_comp,headNet,tailNet,count_select,zero_add]

def compareStep (w r : ℕ) : BooleanNetwork (tensorWidth w (r+2)) (tensorWidth w (r+2)) :=
  let a := headNet w (r+1)
  let b := (tailNet w (r+1)).comp (headNet w r)
  let rest := (tailNet w (r+1)).comp (tailNet w r)
  (wordMux (paddedPair a b) a b).pair ((wordMux (paddedPair a b) b a).pair rest)

lemma compareStep_eval (w r : ℕ) (a b : Basis w) (x : Basis (tensorWidth w r)) :
    (compareStep w r).eval (Fin.append a (Fin.append b x))=
      if LEWord a b then Fin.append a (Fin.append b x) else Fin.append b (Fin.append a x) := by
  have hc : (paddedPair (headNet w (r+1)) ((tailNet w (r+1)).comp (headNet w r))).eval
      (Fin.append a (Fin.append b x)) 0=true ↔ LEWord a b := by
    rw [paddedPair_value,headNet_eval,eval_comp,tailNet_eval,headNet_eval]
    rfl
  simp only [compareStep,eval_pair,wordMux_eval,eval_comp,headNet_eval,tailNet_eval]
  by_cases hab : LEWord a b
  · have ht := hc.mpr hab
    simp only [ite_eq_left ht,ite_eq_left hab]
  · have ht : ¬(paddedPair (headNet w (r+1)) ((tailNet w (r+1)).comp (headNet w r))).eval
        (Fin.append a (Fin.append b x)) 0=true := fun h=>hab (hc.mp h)
    simp only [ite_eq_right ht,ite_eq_right hab]

lemma compareStep_count (w r : ℕ) : (compareStep w r).net.count ≤ 498*w+114 := by
  have hp := paddedPair_count (headNet w (r+1)) ((tailNet w (r+1)).comp (headNet w r))
  simp only [headNet,tailNet,count_comp,count_select,mul_zero,zero_add] at hp
  simp only [compareStep,count_pair,wordMux_count,headNet,tailNet,count_comp,count_select]
  omega

def insertNet (w : ℕ) : (r : ℕ)→BooleanNetwork (tensorWidth w (r+1)) (tensorWidth w (r+1))
  | 0=>select id
  | r+1=>(compareStep w r).comp (keepHead (insertNet w r))
def sortNet (w : ℕ) : (r : ℕ)→BooleanNetwork (tensorWidth w r) (tensorWidth w r)
  | 0=>select id
  | r+1=>(keepHead (sortNet w r)).comp (insertNet w r)

lemma insertNet_eval (w r : ℕ) (a : Basis w) (xs : List (Basis w)) (hx : xs.length=r) :
    (insertNet w r).eval (layout w (r+1) (a::xs))=layout w (r+1) (insert a xs) := by
  induction r generalizing a xs with
  | zero=>have he : xs=[] := List.length_eq_zero_iff.mp hx;subst xs;rfl
  | succ r ih=>
    cases xs with
    | nil=>simp at hx
    | cons b bs=>
      have hb : bs.length=r := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hx
      change (insertNet w (r+1)).eval (Fin.append a (Fin.append b (layout w r bs)))=_
      rw [insertNet,eval_comp,compareStep_eval,insert]
      split_ifs with hab
      · rw [keepHead_eval]
        change Fin.append a ((insertNet w r).eval (layout w (r+1) (b::bs)))=_
        rw [ih b bs hb]
        rfl
      · rw [keepHead_eval]
        change Fin.append b ((insertNet w r).eval (layout w (r+1) (a::bs)))=_
        rw [ih a bs hb]
        rfl
lemma sortNet_eval (w r : ℕ) (xs : List (Basis w)) (hx : xs.length=r) :
    (sortNet w r).eval (layout w r xs)=layout w r (sort xs) := by
  induction r generalizing xs with
  | zero=>have he : xs=[] := List.length_eq_zero_iff.mp hx;subst xs;rfl
  | succ r ih=>
    cases xs with
    | nil=>simp at hx
    | cons a as=>
      have ha : as.length=r := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hx
      change (sortNet w (r+1)).eval (Fin.append a (layout w r as))=_
      rw [sortNet,eval_comp,keepHead_eval,ih as ha]
      change (insertNet w r).eval (layout w (r+1) (a::sort as))=_
      rw [insertNet_eval w r a (sort as) ((sort_length as).trans ha)]
      rfl
lemma insertNet_count (w r : ℕ) : (insertNet w r).net.count ≤ r*(498*w+114) := by
  induction r with
  | zero=>simp [insertNet,count_select]
  | succ r ih=>
    have hc := compareStep_count w r
    rw [insertNet,count_comp,keepHead_count,Nat.succ_mul]
    omega
/-- Quadratic number of word comparisons, each a polynomial Boolean network.
No expanded sorting expression duplicates its recursively generated circuits. -/
theorem sortNet_count (w r : ℕ) : (sortNet w r).net.count ≤ r*r*(498*w+114) := by
  induction r with
  | zero=>simp [sortNet,count_select]
  | succ r ih=>
    have hc := insertNet_count w r
    rw [sortNet,count_comp,keepHead_count]
    calc
      _ ≤ r*r*(498*w+114)+r*(498*w+114) := Nat.add_le_add ih hc
      _ ≤ (r+1)*(r+1)*(498*w+114) := by nlinarith

end SortedWords
end ExactQuantumFactoring.BitArithmetic


end

end OAI
