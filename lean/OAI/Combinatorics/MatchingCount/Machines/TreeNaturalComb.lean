import Mathlib
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeNatDivision
import OAI.Combinatorics.MatchingCount.Machines.TreeRepeat

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

def successor : Realizer Nat.succ :=
  (composition (pair identity (constant 1)) add).congr (fun _=>rfl)

def quotient : Realizer (fun x : ℕ×ℕ=>x.1/x.2) := composition division first
def remainder : Realizer (fun x : ℕ×ℕ=>x.1%x.2) := composition division second

def factStep (x : ℕ×ℕ) : ℕ := x.1*x.2
lemma fact_countDown (n a : ℕ) : countDown factStep n a=n.factorial*a := by
  induction n generalizing a with
  | zero => simp [countDown]
  | succ n ih =>
    rw [countDown,ih]
    simp only [factStep,Nat.factorial_succ]
    ring

def factorial : Realizer Nat.factorial :=
  (composition (pair identity (constant 1))
    (iterateDown multiply)).congr (by
      intro n
      change countDown factStep n 1=_
      rw [fact_countDown,Nat.mul_one])

def natChoose : Realizer (fun x : ℕ×ℕ=>x.1.choose x.2) := by
  let Q := composition (pair (composition first factorial)
    (composition (pair (composition second factorial) (composition subtract factorial)) multiply)) quotient
  exact (choose (composition (pair second first) less) Q
    (choose (composition (pair first second) less) (constant 0) (constant 1))).congr (by
    intro x
    change (if decide (x.2<x.1) then _ else if decide (x.1<x.2) then 0 else 1)=x.1.choose x.2
    by_cases h : x.2<x.1
    · simp only [h,decide_true,↓reduceIte,Function.comp_apply]
      exact (Nat.choose_eq_factorial_div_factorial (Nat.le_of_lt h)).symm
    · simp only [h,decide_false,Bool.false_eq_true,↓reduceIte]
      by_cases h' : x.1<x.2
      · simp [h',Nat.choose_eq_zero_of_lt h']
      · have e : x.1=x.2 := by omega
        simp [e])

def pairingStep (x : ℕ×(ℕ×ℕ)) : ℕ×ℕ := (x.2.2,(x.1+1)*x.2.1)
lemma pairing_range (n : ℕ) :
    (List.range n).foldl (fun z i=>pairingStep (i,z)) (1,0)=
      (UnitRefresh.pairingCount n,UnitRefresh.pairingCount (n+1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ,List.foldl_append,ih]
    simp [pairingStep,UnitRefresh.pairingCount]

def pairingNumber : Realizer UnitRefresh.pairingCount :=
  (composition (composition (pair range (constant (1,0)))
    (fold (pair (composition second second)
      (composition (pair (composition first successor) (composition second first)) multiply)))) first).congr (by
        intro n
        change ((List.range n).foldl (fun z i=>pairingStep (i,z)) (1,0)).1=_
        rw [pairing_range])

end MatchingFPRAS.TreeTyped

end OAI
