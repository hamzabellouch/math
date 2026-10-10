import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Values
import OAI.Combinatorics.KMedianRecovery.Encoding.NatWords

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace NatOps
noncomputable def min {f g : List Bool→List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(Min.min (value (f x)) (value (g x))).bits) := by
  have hh:=(le hf hg).cond (hf.comp normalize_computes) (hg.comp normalize_computes)
  convert hh using 1
  funext x
  simp only [decide_eq_true_eq,Function.comp_def,normalize_eq_bits]
  split_ifs with h
  · rw [min_eq_left h]
  · rw [min_eq_right (le_of_not_ge h)]
noncomputable def max {f g : List Bool→List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>(Max.max (value (f x)) (value (g x))).bits) := by
  have hh:=(le hf hg).cond (hg.comp normalize_computes) (hf.comp normalize_computes)
  convert hh using 1
  funext x
  simp only [decide_eq_true_eq,Function.comp_def,normalize_eq_bits]
  split_ifs with h
  · rw [max_eq_right h]
  · rw [max_eq_left (le_of_not_ge h)]
end NatOps
namespace BinaryRound
open WordList BinaryOpeningPayment

def pack (q u : ℚ) (cap : ℕ) : List Bool := encode [BinaryRational.encode q,BinaryRational.encode u,cap.bits]
noncomputable def ceil (x : List Bool) : List Bool :=
  (⌈BinaryRational.decode (field 0 x)/BinaryRational.decode (field 1 x)⌉₊).bits
noncomputable def ceil_computes : PolyComputes ceil :=
  RatOps.natCeil (RatOps.div (RatOps.ofWords (field_computes 0)) (RatOps.ofWords (field_computes 1)))
noncomputable def positive (x : List Bool) : List Bool := (min (value (field 2 x)) (max 1 (value (ceil x)))).bits
noncomputable def positive_computes : PolyComputes positive := by
  have hh:=NatOps.min (field_computes 2) (NatOps.max (const_computes (1:ℕ).bits) ceil_computes)
  change PolyComputes (fun x=>(min (value (field 2 x)) (max 1 (value (ceil x)))).bits)
  simpa only [value_bits] using hh
lemma positive_pack (q u : ℚ) (cap : ℕ) :
    positive (pack q u cap)=(min cap (max 1 ⌈q/u⌉₊)).bits := by
  simp only [positive,ceil,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinaryRational.decode_encode,value_bits]
noncomputable def rational (x : List Bool) : List Bool := BinaryRational.encode (value (positive x):ℚ)
noncomputable def rational_computes : PolyComputes rational := RatOps.nat positive_computes
lemma rational_pack (q u : ℚ) (cap : ℕ) :
    rational (pack q u cap)=BinaryRational.encode (min cap (max 1 ⌈q/u⌉₊):ℕ) := by
  rw [rational,positive_pack,value_bits]
end BinaryRound
end MetricKMedianRecovery.BitMachine

end OAI
