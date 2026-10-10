import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.LeftNum

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace Signed

lemma signed_ediv_nat (s : Bool) (n d : ℕ) : signed s n/(d:ℤ)=
    if d=0 then 0 else if s then
      if n%d=0 then signed true (n/d) else signed true (n/d+1)
    else signed false (n/d) := by
  by_cases hd : d=0
  · simp only [hd,Int.natCast_zero,Int.ediv_zero,ite_true]
  · have hp : (0:ℤ)<d := by exact_mod_cast Nat.pos_of_ne_zero hd
    cases s with
    | false => simp only [ite_eq_right hd,Bool.false_eq_true,ite_false,signed,Int.natCast_ediv]
    | true =>
      simp only [ite_eq_right hd,ite_true,signed,Int.neg_ediv,Int.natCast_ediv,
        Int.natCast_dvd_natCast,Nat.dvd_iff_mod_eq_zero,Int.sign_eq_one_of_pos hp]
      split_ifs <;> omega

def divNatWords (x : List Bool) : List Bool :=
  if value (discardPrefix x)=0 then encode 0
  else if sign (extractPrefix x) then
    if mag (extractPrefix x)%value (discardPrefix x)=0 then
      pack true (mag (extractPrefix x)/value (discardPrefix x)).bits
    else pack true (mag (extractPrefix x)/value (discardPrefix x)+1).bits
  else pack false (mag (extractPrefix x)/value (discardPrefix x)).bits

noncomputable def divNatWords_computes : PolyComputes divNatWords := by
  have hm := extractPrefix_computes.comp tail_computes
  have hq := NatOps.div hm discardPrefix_computes
  have hq1 := NatOps.add hq (const_computes (Nat.bits 1))
  have hz := NatOps.zero (NatOps.mod hm discardPrefix_computes)
  have hneg := hz.cond (pack_computes (const_computes [true]) hq)
    (pack_computes (const_computes [true]) hq1)
  have hs := extractPrefix_computes.comp sign_computes
  have hsign := hs.cond hneg (pack_computes (const_computes [false]) hq)
  have hd := NatOps.zero discardPrefix_computes
  have hh := hd.cond (const_computes (encode 0)) hsign
  unfold divNatWords mag
  convert hh using 1
  funext x
  simp only [Function.comp_def,value_bits,decide_eq_true_eq]

lemma divNatWords_spec (x : List Bool) : divNatWords x=
    encode (decode (extractPrefix x)/(value (discardPrefix x):ℤ)) := by
  change _=encode (signed (sign (extractPrefix x)) (mag (extractPrefix x))/_)
  rw [signed_ediv_nat]
  unfold divNatWords
  split_ifs <;> simp only [pack_bits]

noncomputable def divisionNat : Turing.TM2ComputableInPolyTime
    (fun p : ℤ×ℕ=>pairBits (encode p.1,p.2.bits)) encode (fun p=>p.1/(p.2:ℤ)) :=
  divNatWords_computes.reencode _ _ (fun p=>by
    simp only [divNatWords_spec,extractPrefix_pairBits,discardPrefix_pairBits,encode_decode,value_bits])

end Signed
namespace BinaryRational

def floorWords : List Bool → List Bool := Signed.divNatWords
noncomputable def floorWords_computes : PolyComputes floorWords := Signed.divNatWords_computes
lemma floorWords_encode (x : ℚ) : floorWords (encode x)=Signed.encode (⌊x⌋:ℤ) := by
  simp only [floorWords,Signed.divNatWords_spec,encode,extractPrefix_pairBits,discardPrefix_pairBits,
    Signed.encode_decode,value_bits,Rat.floor_def']
noncomputable def floor : Turing.TM2ComputableInPolyTime encode Signed.encode (fun x:ℚ=>(⌊x⌋:ℤ)) :=
  floorWords_computes.reencode _ _ floorWords_encode

def ceilWords : List Bool → List Bool := (fun x=>Signed.encode (-Signed.decode x)) ∘ floorWords ∘ negWords
noncomputable def ceilWords_computes : PolyComputes ceilWords :=
  (negWords_computes.comp floorWords_computes).comp Signed.neg_computes
lemma ceilWords_encode (x : ℚ) : ceilWords (encode x)=Signed.encode (⌈x⌉:ℤ) := by
  simp only [ceilWords,Function.comp_apply,negWords_encode,floorWords_encode,Signed.encode_decode,
    Int.floor_neg,neg_neg]
noncomputable def ceil : Turing.TM2ComputableInPolyTime encode Signed.encode (fun x:ℚ=>(⌈x⌉:ℤ)) :=
  ceilWords_computes.reencode _ _ ceilWords_encode

def castIntWords (x : List Bool) : List Bool := pairBits (x,Nat.bits 1)
noncomputable def castIntWords_computes : PolyComputes castIntWords := id_computes.pair (const_computes (Nat.bits 1))
lemma castIntWords_encode (z : ℤ) : castIntWords (Signed.encode z)=encode (z:ℚ) := by
  simp only [castIntWords,encode,Rat.num_intCast,Rat.den_intCast]
noncomputable def castInt : Turing.TM2ComputableInPolyTime Signed.encode encode (fun z:ℤ=>(z:ℚ)) :=
  castIntWords_computes.reencode _ _ castIntWords_encode

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
