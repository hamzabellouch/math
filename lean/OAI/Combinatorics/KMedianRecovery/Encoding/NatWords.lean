import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.DivNatWords

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace Signed
noncomputable def natWords (x : List Bool) : List Bool := if sign x then [] else normalize x.tail
noncomputable def natWords_computes : PolyComputes natWords :=
  sign_computes.cond (const_computes []) (tail_computes.comp normalize_computes)
lemma natWords_eq (x : List Bool) : natWords x=(decode x).toNat.bits := by
  cases h : sign x <;> simp [natWords,decode,h,normalize_eq_bits,mag]
lemma natWords_encode (z : ℤ) : natWords (encode z)=z.toNat.bits := by
  rw [natWords_eq,encode_decode]
end Signed
namespace RatOps
noncomputable def natCeil {f : List Bool → ℚ} (hf : PolyComputes (fun x=>BinaryRational.encode (f x))) :
    PolyComputes (fun x=>(⌈f x⌉₊).bits) := by
  have hh := (hf.comp BinaryRational.ceilWords_computes).comp Signed.natWords_computes
  simpa only [Function.comp_def,BinaryRational.ceilWords_encode,Signed.natWords_encode,Int.ceil_toNat] using hh
end RatOps
end MetricKMedianRecovery.BitMachine

end OAI
