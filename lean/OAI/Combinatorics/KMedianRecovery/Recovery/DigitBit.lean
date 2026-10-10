import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Pack

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open Turing
namespace BinaryDivision
open BinaryArithmetic BinarySubtraction WordOperations

def digitBit (b : Bool) (y r : List Bool) : Bool := decide (value y ≤ value (b::r))
def digitRem (b : Bool) (y r : List Bool) : List Bool :=
  if digitBit b y r then BinaryArithmetic.normalize (subtract (b::r) y) else b::r

def process : List Bool → List Bool → List Bool → List Bool → List Bool × List Bool
  | [],_,q,r => (q,r)
  | b::ds,y,q,r => process ds y (digitBit b y r::q) (digitRem b y r)

def evalMSB : List Bool → ℕ → ℕ
  | [],n => n
  | b::bs,n => evalMSB bs (2*n+b.toNat)

lemma evalMSB_eq (ds : List Bool) (a : ℕ) :
    evalMSB ds a=2^ds.length*a+value ds.reverse := by
  induction ds generalizing a with
  | nil => simp [evalMSB,value]
  | cons b ds ih =>
    simp only [evalMSB,ih,List.length_cons,pow_succ,List.reverse_cons,value_append,
      List.length_reverse,value,Nat.mul_zero,Nat.add_zero]
    ring

lemma digit_balance (b : Bool) (y q r : List Bool) (hr : value r < value y) :
    value (digitBit b y r::q)*value y+value (digitRem b y r)=
      2*(value q*value y+value r)+b.toNat ∧
    value (digitRem b y r)<value y := by
  have hb : b.toNat ≤ 1 := by cases b <;> decide
  have htwo : value (b::r)<2*value y := by simp only [value]; omega
  by_cases h : value y ≤ value (b::r)
  · have ht : digitBit b y r=true := by simp only [digitBit,h,decide_true]
    have he := Nat.sub_add_cancel h
    simp only [value] at he htwo
    simp only [digitRem,ht,ite_true,normalize_eq_bits,value_bits,
      value_subtract,value,Bool.toNat_true]
    constructor <;> nlinarith
  · have ht : digitBit b y r=false := by simp only [digitBit,h,decide_false]
    have hl : value (b::r)<value y := Nat.lt_of_not_ge h
    simp only [value] at hl
    simp only [digitRem,ht,Bool.false_eq_true,ite_false,value,
      Bool.toNat_false,Nat.zero_add]
    constructor
    · ring
    · exact hl

lemma process_spec (ds y q r : List Bool) (hr : value r<value y) :
    value (process ds y q r).1*value y+value (process ds y q r).2=
      evalMSB ds (value q*value y+value r) ∧
    value (process ds y q r).2<value y := by
  induction ds generalizing q r with
  | nil => exact ⟨rfl,hr⟩
  | cons b ds ih =>
    have hb := digit_balance b y q r hr
    have hh := ih (digitBit b y r::q) (digitRem b y r) hb.2
    simpa only [process,evalMSB,hb.1] using hh

lemma next_pack_nil (y q r : List Bool) :
    next (pack true [] y q r)=pack false [] y q r := by
  change step (pack true [] y q r)=_
  simp only [step,digits_pack,divisor_pack,quotient_pack,remainder_pack,ite_true]

lemma next_pack_cons (b : Bool) (ds y q r : List Bool) :
    next (pack true (b::ds) y q r)=
      pack true ds y (digitBit b y r::q) (digitRem b y r) := by
  change step (pack true (b::ds) y q r)=_
  simp only [step,digits_pack,divisor_pack,quotient_pack,remainder_pack,List.cons_ne_nil,
    ite_false,List.tail_cons,nextBit,doubled,List.head?_cons,Option.getD_some,reduced,
    digitRem,digitBit]
  rfl

lemma iterate_pack (ds y q r : List Bool) :
    next^[ds.length+1] (pack true ds y q r)=
      pack false [] y (process ds y q r).1 (process ds y q r).2 := by
  induction ds generalizing q r with
  | nil => exact next_pack_nil y q r
  | cons b ds ih =>
    simp only [List.length_cons,Function.iterate_succ_apply,next_pack_cons,process]
    exact ih _ _

lemma rank_pack (ds y q r : List Bool) : rank (pack true ds y q r)=ds.length+1 := by
  have h : (pack true ds y q r).head?=some true := rfl
  simp only [BinaryDivision.rank,h,ite_true,digits_pack]

noncomputable def normalize_computes : PolyComputes BinaryArithmetic.normalize :=
  (reverse_computes.comp trim_computes).comp reverse_computes

noncomputable def zeroTest_computes : PolyComputes (fun x=>[decide (value x=0)]) := by
  have h := normalize_computes.comp isEmpty_computes
  simpa only [Function.comp_def,normalize_eq_bits,bits_eq_nil] using h

def setupWords (x : List Bool) : List Bool :=
  pack true (extractPrefix x).reverse (discardPrefix x) [] []

def withDivision (x : List Bool) : List Bool := next^[rank (setupWords x)] (setupWords x)

def rawDivide (x : List Bool) : List Bool :=
  pairBits (normalize (quotient (withDivision x)),normalize (remainder (withDivision x)))

def divide (x : List Bool) : List Bool :=
  if value (discardPrefix x)=0 then pairBits ([],normalize (extractPrefix x)) else rawDivide x

noncomputable def setupWords_computes : PolyComputes setupWords :=
  pack_computes true (extractPrefix_computes.comp reverse_computes) discardPrefix_computes
    (const_computes []) (const_computes [])

noncomputable def withDivision_computes : PolyComputes withDivision := by
  have hh := setupWords_computes.comp loop_computes
  unfold withDivision
  simpa only [Function.comp_def] using hh

noncomputable def rawDivide_computes : PolyComputes rawDivide := by
  have hq := quotient_computes.comp normalize_computes
  have hr := remainder_computes.comp normalize_computes
  have hh := withDivision_computes.comp (hq.pair hr)
  unfold rawDivide
  simpa only [Function.comp_def] using hh

noncomputable def divide_computes : PolyComputes divide := by
  have hz := discardPrefix_computes.comp zeroTest_computes
  have hf := (const_computes []).pair (extractPrefix_computes.comp normalize_computes)
  have hh := hz.cond hf rawDivide_computes
  change PolyComputes (fun x=>if value (discardPrefix x)=0 then _ else _)
  simpa only [Function.comp_def,decide_eq_true_eq] using hh

lemma divide_pair (x y : List Bool) :
    divide (pairBits (x,y))=pairBits ((value x/value y).bits,(value x%value y).bits) := by
  have ep : extractPrefix (pairBits (x,y))=x := extractPrefix_pair x y
  have er : discardPrefix (pairBits (x,y))=y := discardPrefix_pair x y
  by_cases hy : value y=0
  · simp only [divide,er,ep,hy,ite_true,Nat.div_zero,show Nat.bits 0=[] from rfl,Nat.mod_zero,normalize_eq_bits]
  · have hpos : 0<value y := Nat.pos_of_ne_zero hy
    have hs := process_spec x.reverse y [] [] hpos
    simp only [evalMSB_eq,List.reverse_reverse,value,Nat.zero_mul,Nat.mul_zero,Nat.zero_add] at hs
    have hdiv : value x/value y=value (process x.reverse y [] []).1 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · nlinarith [hs.2]
    have hmod : value x%value y=value (process x.reverse y [] []).2 := by
      have hd := Nat.mod_add_div (value x) (value y)
      rw [hdiv] at hd
      nlinarith [hs.1]
    simp only [divide,er,hy,ite_false,rawDivide,withDivision,setupWords,ep,rank_pack,
      iterate_pack,quotient_pack,remainder_pack,normalize_eq_bits,hdiv,hmod]

noncomputable def division : TM2ComputableInPolyTime
    (fun p : ℕ×ℕ=>pairBits (p.1.bits,p.2.bits))
    (fun p : ℕ×ℕ=>pairBits (p.1.bits,p.2.bits)) (fun p=>(p.1/p.2,p.1%p.2)) :=
  divide_computes.reencode _ _ (fun p=>by simpa only [value_bits] using divide_pair p.1.bits p.2.bits)

end BinaryDivision
end MetricKMedianRecovery.BitMachine

end OAI
