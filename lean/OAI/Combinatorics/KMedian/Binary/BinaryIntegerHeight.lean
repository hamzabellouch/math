import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryRationalHeight

namespace OAI


                                           
section
namespace MetricKMedian.Binary.Signed
 theorem height_length (z : ℤ) : |z| ≤ (2:ℤ)^(encode z).length := by
  have h := NatBinary.le_two_pow_length z.natAbs
  have hl : z.natAbs.bits.length≤(encode z).length := by rw [encode_length]; omega
  have hh := h.trans (Nat.pow_le_pow_right (by decide : 1≤2) hl)
  simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using (Nat.cast_le (α:=ℤ)).mpr hh
 theorem length_height {z : ℤ} {L : ℕ} (h : |z|≤(2:ℤ)^L) : (encode z).length≤L+4 := by
  have hN : z.natAbs≤2^L := (Nat.cast_le (α:=ℤ)).mp (by simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using h)
  have hnb := NatBinary.length_le_height hN
  rw [encode_length]
  omega
end MetricKMedian.Binary.Signed
end

end OAI
