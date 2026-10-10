import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeList
import OAI.Combinatorics.MatchingCount.Machines.TreePartialChoice

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

def digitValue : Realizer Bool.toNat :=
  (choose identity (constant 1) (constant 0)).congr (fun b=>by cases b <;> rfl)

def divStep (x : Bool×(ℕ×(ℕ×ℕ))) : ℕ×(ℕ×ℕ) :=
  let n:=x.2.1
  let q:=x.2.2.1
  let r:=2*x.2.2.2+x.1.toNat
  (n,if r<n then (2*q,r) else (2*q+1,r-n))

def divStepRealizer : Realizer divStep := by
  let nP : Realizer (fun x : Bool×(ℕ×(ℕ×ℕ))=>x.2.1) := composition second first
  let qP : Realizer (fun x : Bool×(ℕ×(ℕ×ℕ))=>2*x.2.2.1) :=
    composition (composition (composition second second) first) double
  let rP : Realizer (fun x : Bool×(ℕ×(ℕ×ℕ))=>2*x.2.2.2+x.1.toNat) :=
    composition (pair (composition (composition (composition second second) second) double)
      (composition first digitValue)) add
  let lP := composition (pair rP nP) less
  let q1P := composition (pair qP (constant 1)) add
  let r1P := composition (pair rP nP) subtract
  exact (pair nP (choose lP (pair qP rP) (pair q1P r1P))).congr (by
    intro x; simp only [Function.comp_apply,divStep,decide_eq_true_eq])

lemma divStep_first (b : Bool) (n q r : ℕ) : (divStep (b,(n,q,r))).1=n := rfl
lemma divStep_lt (b : Bool) (n q r : ℕ) (_ : 0<n) (hr : r<n) :
    (divStep (b,(n,q,r))).2.2<n := by
  have hb : b.toNat ≤ 1 := Bool.toNat_le b
  simp only [divStep]
  split_ifs <;> simp only
  · assumption
  · omega
lemma divStep_mass (b : Bool) (n q r : ℕ) :
    n*(divStep (b,(n,q,r))).2.1+(divStep (b,(n,q,r))).2.2=
      2*(n*q+r)+b.toNat := by
  simp only [divStep]
  split_ifs with h
  · simp only; ring
  · simp only
    have hh : n ≤ 2*r+b.toNat := by omega
    have hs:=Nat.sub_add_cancel hh
    nlinarith

lemma divFold_first (A : List Bool) (n q r : ℕ) :
    (A.foldl (fun z b=>divStep (b,z)) (n,q,r)).1=n := by
  induction A generalizing q r with
  | nil => rfl
  | cons b A ih =>
    change (A.foldl _ (divStep (b,(n,q,r)))).1=n
    rw [←Prod.eta (divStep (b,(n,q,r))),divStep_first]
    rw [←Prod.eta (divStep (b,(n,q,r))).2]
    exact ih _ _

lemma divFold_lt (A : List Bool) (n q r : ℕ) (hn : 0<n) (hr : r<n) :
    (A.foldl (fun z b=>divStep (b,z)) (n,q,r)).2.2<n := by
  induction A generalizing q r with
  | nil => exact hr
  | cons b A ih =>
    change (A.foldl _ (divStep (b,(n,q,r)))).2.2<n
    rw [←Prod.eta (divStep (b,(n,q,r))),divStep_first]
    rw [←Prod.eta (divStep (b,(n,q,r))).2]
    exact ih _ _ (divStep_lt b n q r hn hr)

lemma divFold_mass (A : List Bool) (n q r : ℕ) :
    n*(A.reverse.foldl (fun z b=>divStep (b,z)) (n,q,r)).2.1+
      (A.reverse.foldl (fun z b=>divStep (b,z)) (n,q,r)).2.2=
      (n*q+r)*2^A.length+StackAddition.value A := by
  induction A with
  | nil => simp [StackAddition.value]
  | cons b A ih =>
    simp only [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]
    let z := A.reverse.foldl (fun z b=>divStep (b,z)) (n,q,r)
    have hz : z=(n,z.2.1,z.2.2) := by
      apply Prod.ext
      · exact divFold_first A.reverse n q r
      · rfl
    change n*(divStep (b,z)).2.1+(divStep (b,z)).2.2=_
    rw [hz,divStep_mass]
    change n*z.2.1+z.2.2=_ at ih
    rw [ih]
    simp only [StackAddition.value,List.length_cons,pow_succ]
    ring

lemma divFold_correct (m n : ℕ) (hn : 0<n) :
    (m.bits.reverse.foldl (fun z b=>divStep (b,z)) (n,0,0)).2=(m/n,m%n) := by
  have hm:=divFold_mass m.bits n 0 0
  have hr:=divFold_lt m.bits.reverse n 0 0 hn hn
  simp only [Nat.mul_zero,Nat.zero_add,Nat.zero_mul,StackAddition.value_bits] at hm
  have hu : m/n=(m.bits.reverse.foldl (fun z b=>divStep (b,z)) (n,0,0)).2.1 ∧
      m%n=(m.bits.reverse.foldl (fun z b=>divStep (b,z)) (n,0,0)).2.2 :=
    (Nat.div_mod_unique hn).2 ⟨by omega,hr⟩
  exact Prod.ext hu.1.symm hu.2.symm

def divCore : Realizer (fun ab : ℕ×ℕ=>
    (ab.1.bits.reverse.foldl (fun z b=>divStep (b,z)) (ab.2,0,0)).2) :=
  composition (composition (pair (composition (composition first toBits) reverse)
    (pair second (pair (constant 0) (constant 0)))) (fold divStepRealizer)) second

def division : Realizer (fun ab : ℕ×ℕ=>(ab.1/ab.2,ab.1%ab.2)) := by
  let posP : Realizer (fun ab : ℕ×ℕ=>decide (0<ab.2)) := composition (pair (constant 0) second) less
  let zeroP : Realizer (fun ab : ℕ×ℕ=>(0,ab.1)) := pair (constant 0) first
  exact (choose posP divCore zeroP).congr (by
    intro ab
    by_cases h : 0<ab.2
    · simp only [h,decide_true,↓reduceIte]
      exact divFold_correct ab.1 ab.2 h
    · have hn : ab.2=0 := by omega
      simp [hn])
end MatchingFPRAS.TreeTyped

end OAI
