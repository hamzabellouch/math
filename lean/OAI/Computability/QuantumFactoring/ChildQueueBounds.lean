import Mathlib
import OAI.Computability.QuantumFactoring.ChildQueue

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic.ChildQueue
open BooleanNetwork

lemma wordMember_count {k w c : ℕ} (a : BooleanNetwork k w) (as : List (BooleanNetwork k w))
    (ha : a.net.count ≤ c) (hs : ∀ b∈as,b.net.count ≤ c) :
    (wordMember a as).net.count ≤ as.length*(2*c+96*w+25)+1 := by
  have h := any_count (as.map (fun b=>(a.pair b).comp (wordEq w))) (c:=2*c+96*w+21) (by
    intro d hd
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hd
    have hh := hs b hb
    have he := wordEq_count w
    simp only [count_comp,count_pair]
    omega)
  simpa only [wordMember,List.length_map,Nat.add_assoc] using h

lemma active_count {k w c : ℕ} (a : BooleanNetwork k w) (as : List (BooleanNetwork k w))
    (ha : a.net.count ≤ c) (hs : ∀ b∈as,b.net.count ≤ c) :
    (active a as).net.count ≤ c+49*w+11+as.length*(2*c+96*w+25) := by
  have hm := wordMember_count a as ha hs
  have hl := wordLt_count (wordConstant (n:=k) (BitVec.ofNat w 2)) a
  rw [wordConstant_count] at hl
  simp only [active,count_band,count_bnot]
  omega

def oneBound (s w c r : ℕ) := c+49*w+11+r*(2*c+96*w+25)+s*w*(c+159*w+6)+7*(s*w)

lemma pushOne_count {k w c : ℕ} (s : ℕ) (a : BooleanNetwork k w) (as : List (BooleanNetwork k w))
    (ha : a.net.count ≤ c) (hs : ∀ b∈as,b.net.count ≤ c) :
    (pushOne s a as).net.count ≤ oneBound s w c as.length := by
  have hac := active_count a as ha hs
  have hsub := sub_count w
  have hh : ((((liftWord s a).pair (wordConstant (BitVec.ofNat w 1))).comp (sub w))).net.count ≤
      c+159*w+6 := by
    simp only [count_comp,count_pair,liftWord,source,count_select,zero_add,wordConstant_count]
    omega
  have hpush := stackPush_count (((liftWord s a).pair (wordConstant (BitVec.ofNat w 1))).comp (sub w))
    (queue k s w)
  simp only [queue,count_select,add_zero] at hpush
  have hpush' := hpush.trans (Nat.mul_le_mul_left (s*w) hh)
  simp only [pushOne,count_pair,wordMux_count,count_comp,source,queue,count_select,zero_add,add_zero]
  dsimp only [oneBound]
  omega

lemma oneBound_mono (s w c : ℕ) {r t : ℕ} (h : r ≤ t) : oneBound s w c r ≤ oneBound s w c t := by
  have hh := Nat.mul_le_mul_right (2*c+96*w+25) h
  dsimp only [oneBound]
  omega

/-- The all-child queue update is quadratic in the number of prime fields,
not an exponentially duplicated expression. Bounds hold on ALL inputs. -/
theorem pushAll_count {k w c : ℕ} (s : ℕ) (as : List (BooleanNetwork k w))
    (hs : ∀ b∈as,b.net.count ≤ c) :
    (pushAll s as).net.count ≤ as.length*oneBound s w c as.length := by
  induction as with
  | nil=>simp [pushAll,count_select]
  | cons a as ih=>
    have ha := hs a (by simp)
    have ht : ∀ b∈as,b.net.count ≤ c := fun b hb=> hs b (by simp [hb])
    have hi := ih ht
    have hp := pushOne_count s a as ha ht
    have hb := oneBound_mono s w c (Nat.le_succ as.length)
    simp only [pushAll,count_comp,List.length_cons]
    calc
      _ ≤ as.length*oneBound s w c as.length+oneBound s w c as.length := Nat.add_le_add hi hp
      _ ≤ as.length*oneBound s w c (as.length+1)+oneBound s w c (as.length+1) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hb) hb
      _ = _ := by ring

end ExactQuantumFactoring.BitArithmetic.ChildQueue


end

end OAI
