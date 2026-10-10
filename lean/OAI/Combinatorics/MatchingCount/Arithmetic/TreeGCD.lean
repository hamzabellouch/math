import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreeNaturalComb
import OAI.Combinatorics.MatchingCount.Machines.TreePredicate

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

def digits : Realizer Nat.bits where
  program := identity.program (A:=ℕ)
  cost := fun _=>1
  correct := fun a s=>identity.correct a s

def bitSize : Realizer Nat.size :=
  (composition digits listLength).congr (fun a=>Nat.size_eq_bits_len a)

def sortedPair (x : ℕ×ℕ) : ℕ×ℕ := if x.1<x.2 then (x.2,x.1) else x
def sortedPairRealizer : Realizer sortedPair :=
  (choose less (pair second first) identity).congr (fun x=>by simp [sortedPair])

lemma sortedPair_order (x : ℕ×ℕ) : (sortedPair x).2≤(sortedPair x).1 := by
  unfold sortedPair; split_ifs <;> (try dsimp only) <;> omega
lemma sortedPair_gcd (x : ℕ×ℕ) : (sortedPair x).1.gcd (sortedPair x).2=x.1.gcd x.2 := by
  unfold sortedPair; split_ifs <;> simp [Nat.gcd_comm]
lemma sortedPair_size (x : ℕ×ℕ) : (sortedPair x).1.size+(sortedPair x).2.size=x.1.size+x.2.size := by
  unfold sortedPair
  split_ifs
  · exact Nat.add_comm _ _
  · rfl

def gcdStep (x : ℕ×ℕ) : ℕ×ℕ := if x.2=0 then x else (x.2,x.1%x.2)
def gcdStepRealizer : Realizer gcdStep :=
  (choose (composition (pair second (constant 0)) natEqual) identity (pair second remainder)).congr
    (fun x=>by simp only [gcdStep,Function.comp_apply,decide_eq_true_eq,id_eq])

lemma mod_size_lt {a b : ℕ} (hb : 0<b) (hab : b≤a) : (a%b).size<a.size := by
  have ha : 0<a := hb.trans_le hab
  have hr := Nat.mod_lt a hb
  have hq : 1≤a/b := Nat.div_pos hab hb
  have hd := Nat.mod_add_div a b
  have hm : 2*(a%b)<a := by nlinarith [Nat.mul_le_mul_left b hq]
  have hs := Nat.size_pos.mpr ha
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a.size≠0)
  have hpow:=Nat.lt_size_self a
  rw [hk,pow_succ] at hpow
  have hh : a%b<2^k := by omega
  have hsz := Nat.size_le.mpr hh
  omega

lemma gcdStep_order {x : ℕ×ℕ} (h : x.2≤x.1) : (gcdStep x).2≤(gcdStep x).1 := by
  unfold gcdStep; split_ifs with hz
  · exact h
  · exact (Nat.mod_lt _ (by omega)).le
lemma gcdStep_gcd (x : ℕ×ℕ) : (gcdStep x).1.gcd (gcdStep x).2=x.1.gcd x.2 := by
  unfold gcdStep; split_ifs
  · rfl
  · simpa [Nat.gcd_comm] using (Nat.gcd_rec x.2 x.1).symm
lemma gcdStep_decrease {x : ℕ×ℕ} (h : x.2≤x.1) (hz : x.2≠0) :
    (gcdStep x).1.size+(gcdStep x).2.size<x.1.size+x.2.size := by
  simp only [gcdStep,hz,↓reduceIte]
  have hh:=mod_size_lt (by omega : 0<x.2) h
  omega

def gcdIterStep (x : ℕ×(ℕ×ℕ)) : ℕ×ℕ := gcdStep x.2
lemma gcdIter_zero (k a : ℕ) : countDown gcdIterStep k (a,0)=(a,0) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [countDown,gcdIterStep,gcdStep,↓reduceIte] using ih

lemma gcdIter_result (k : ℕ) (x : ℕ×ℕ) (h : x.2≤x.1) (hs : x.1.size+x.2.size≤k) :
    countDown gcdIterStep k x=(x.1.gcd x.2,0) := by
  induction k generalizing x with
  | zero =>
    have hsz : x.1.size=0 := by omega
    have ha:=Nat.size_eq_zero.mp hsz
    have hb : x.2=0 := by omega
    simp [countDown,ha,hb]
    exact Prod.ext ha hb
  | succ k ih =>
    by_cases hz : x.2=0
    · obtain ⟨a,b⟩:=x; dsimp only at hz; subst b
      simp only [gcdIter_zero,Nat.gcd_zero_right]
    · rw [countDown]
      change countDown gcdIterStep k (gcdStep x)=_
      rw [ih _ (gcdStep_order h) (by have hd:=gcdStep_decrease h hz; omega),gcdStep_gcd]

def gcd : Realizer (fun x : ℕ×ℕ=>x.1.gcd x.2) :=
  (composition (composition (pair (composition (pair (composition first bitSize)
    (composition second bitSize)) add) sortedPairRealizer)
    (iterateDown (composition second gcdStepRealizer))) first).congr (by
      intro x
      change (countDown gcdIterStep (x.1.size+x.2.size) (sortedPair x)).1=x.1.gcd x.2
      rw [gcdIter_result _ _ (sortedPair_order x) (by rw [sortedPair_size]),sortedPair_gcd])

end MatchingFPRAS.TreeTyped

end OAI
