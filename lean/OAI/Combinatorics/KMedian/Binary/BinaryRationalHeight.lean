import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryRational
import OAI.Combinatorics.KMedian.Compression.RationalOperationHeight

namespace OAI


                                            
section
namespace MetricKMedian.Binary
open Polynomial
namespace NatBinary
 theorem length_le_height {n L : ℕ} (h : n ≤ 2^L) : n.bits.length ≤ L+1 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have hp : 0<2^L := pow_pos (by decide) _
  rw [pow_succ]
  omega
 theorem le_two_pow_length (n : ℕ) : n ≤ 2^n.bits.length := by
  simpa only [Nat.size_eq_bits_len] using (Nat.lt_size_self n).le
end NatBinary

namespace Signed
 theorem encode_length (z : ℤ) : (encode z).length=3+z.natAbs.bits.length := by
  simp only [encode,parts,encodePair_length,encodeBool,List.length_singleton]

 theorem encode_injective : Function.Injective encode := by
  intro a b h
  have hh := encodePair_injective encodeBool_injective (fun n m he => by
    have hg := congrArg Word.value he
    simpa only [Word.value_bits] using hg) h
  have hx := congrArg (fun x : Bool × ℕ => value x.1 x.2) hh
  simpa only [parts,value_parts] using hx
end Signed
namespace Ratio
 theorem encode_length (q : ℚ) : (encode q).length=7+2*q.num.natAbs.bits.length+q.den.bits.length := by
  simp only [encode,parts,encodePair_length,Signed.encode_length]
  omega
 theorem encode_injective : Function.Injective encode := by
  intro a b h
  have hh := encodePair_injective Signed.encode_injective (fun n m he => by
    have hg := congrArg Word.value he
    simpa only [Word.value_bits] using hg) h
  have hn := congrArg Prod.fst hh
  have hd := congrArg Prod.snd hh
  exact Rat.ext hn hd
 theorem height_length (q : ℚ) : HasHeight q (encode q).length := by
  have hn := NatBinary.le_two_pow_length q.num.natAbs
  have hd := NatBinary.le_two_pow_length q.den
  have hlen := encode_length q
  have hnb : q.num.natAbs.bits.length ≤ (encode q).length := by omega
  have hdb : q.den.bits.length ≤ (encode q).length := by omega
  have hN := hn.trans (Nat.pow_le_pow_right (by decide : 1≤2) hnb)
  have hD := hd.trans (Nat.pow_le_pow_right (by decide : 1≤2) hdb)
  constructor
  · simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using (Nat.cast_le (α:=ℤ)).mpr hN
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using (Nat.cast_le (α:=ℤ)).mpr hD
 theorem length_height {q : ℚ} {L : ℕ} (h : HasHeight q L) : (encode q).length ≤ 3*L+10 := by
  have hN : q.num.natAbs ≤ 2^L := (Nat.cast_le (α:=ℤ)).mp (by
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using h.1)
  have hD : q.den ≤ 2^L := (Nat.cast_le (α:=ℤ)).mp (by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using h.2)
  have hnb := NatBinary.length_le_height hN
  have hdb := NatBinary.length_le_height hD
  rw [encode_length]
  omega
end Ratio
end MetricKMedian.Binary
end

end OAI
