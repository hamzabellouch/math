import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Normalize

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing Turing.TM2 StateTransition
namespace BinarySubtraction
open BinaryArithmetic

def borrowBit (c x y : Bool) : Bool := ((!x) && (c || y)) || (c && y)

lemma fullSubtractor (c x y : Bool) :
    (sumBit c x y).toNat+y.toNat+c.toNat=x.toNat+2*(borrowBit c x y).toNat := by
  cases c <;> cases x <;> cases y <;> rfl

def difference : Bool → List Bool → List Bool → List Bool × Bool
  | c,[],[] => ([],c)
  | c,x::xs,[] => let r := difference (borrowBit c x false) xs []
    (sumBit c x false::r.1,r.2)
  | c,[],y::ys => let r := difference (borrowBit c false y) [] ys
    (sumBit c false y::r.1,r.2)
  | c,x::xs,y::ys => let r := difference (borrowBit c x y) xs ys
    (sumBit c x y::r.1,r.2)
termination_by _ xs ys => xs.length+ys.length

lemma difference_length (c : Bool) (xs ys : List Bool) :
    (difference c xs ys).1.length=max xs.length ys.length := by
  induction xs generalizing c ys with
  | nil =>
    induction ys generalizing c with
    | nil => simp only [difference,List.length_nil,Nat.max_self]
    | cons y ys ih => simp only [difference,List.length_cons,ih,List.length_nil,Nat.zero_max]
  | cons x xs ih =>
    cases ys with
    | nil => simp only [difference,List.length_cons,ih,List.length_nil,Nat.max_zero]
    | cons y ys => simp only [difference,List.length_cons,ih,max_add_add_right]

lemma value_lt (xs : List Bool) : value xs<2^xs.length := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
    cases b <;> simp only [value,List.length_cons,pow_succ,Bool.toNat_true,Bool.toNat_false] <;> omega

lemma difference_balance (c : Bool) (xs ys : List Bool) :
    value (difference c xs ys).1+value ys+c.toNat=
      value xs+2^(max xs.length ys.length)*(difference c xs ys).2.toNat := by
  induction xs generalizing c ys with
  | nil =>
    induction ys generalizing c with
    | nil => simp [difference,value]
    | cons y ys ih =>
      have h := ih (borrowBit c false y)
      have hs := fullSubtractor c false y
      simp only [difference,value,List.length_cons,List.length_nil,Nat.zero_max,pow_succ] at ⊢
      simp only [List.length_nil,Nat.zero_max,value,Bool.toNat_false] at h hs
      nlinarith
  | cons x xs ih =>
    cases ys with
    | nil =>
      have h := ih (borrowBit c x false) []
      have hs := fullSubtractor c x false
      simp only [difference,value,List.length_cons,List.length_nil,Nat.max_zero,pow_succ] at ⊢
      simp only [List.length_nil,Nat.max_zero,value,Bool.toNat_false] at h hs
      nlinarith
    | cons y ys =>
      have h := ih (borrowBit c x y) ys
      have hs := fullSubtractor c x y
      simp only [difference,value,List.length_cons,max_add_add_right,pow_succ] at ⊢
      nlinarith

def subtract (xs ys : List Bool) : List Bool :=
  let r := difference false xs ys
  if r.2 then [] else r.1

lemma value_subtract (xs ys : List Bool) : value (subtract xs ys)=value xs-value ys := by
  have h := difference_balance false xs ys
  have hb := value_lt (difference false xs ys).1
  rw [difference_length] at hb
  simp only [Bool.toNat_false,Nat.add_zero] at h
  dsimp only [subtract]
  split_ifs with hc
  · simp only [hc,Bool.toNat_true,Nat.mul_one] at h
    simp only [value]
    omega
  · have he : (difference false xs ys).2=false := Bool.eq_false_of_not_eq_true hc
    simp only [he,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at h
    omega

lemma borrow_iff_lt (xs ys : List Bool) :
    (difference false xs ys).2=true ↔ value xs<value ys := by
  have h := difference_balance false xs ys
  have hb := value_lt (difference false xs ys).1
  rw [difference_length] at hb
  cases he : (difference false xs ys).2 <;> simp only [he,Bool.toNat_true,Bool.toNat_false,
    Nat.mul_zero,Nat.mul_one,Nat.add_zero,Bool.false_eq_true,true_iff,false_iff] at h ⊢ <;> omega

lemma normalize_subtract (x y : ℕ) : normalize (subtract x.bits y.bits)=(x-y).bits := by
  rw [normalize_eq_bits,value_subtract,value_bits,value_bits]

end BinarySubtraction
end MetricKMedianRecovery.BitMachine

end OAI
