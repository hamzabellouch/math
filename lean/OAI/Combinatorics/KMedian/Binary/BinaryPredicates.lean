import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryRational

namespace OAI


                                        
section
namespace MetricKMedian.Binary.PolyProgram
noncomputable def natLE : PolyProgram (encodePair Nat.bits Nat.bits) encodeBool (fun x : ℕ × ℕ => decide (x.1≤x.2)) :=
  (((exchange Nat.bits Nat.bits).comp natLT).comp boolNot).congr _ (fun x => by
    by_cases h : x.1≤x.2
    · simp [Function.comp_def,h,not_lt.mpr h]
    · simp [Function.comp_def,h,lt_of_not_ge h])
noncomputable def natEQ : PolyProgram (encodePair Nat.bits Nat.bits) encodeBool (fun x : ℕ × ℕ => decide (x.1=x.2)) :=
  ((natLE.fanout ((exchange Nat.bits Nat.bits).comp natLE)).comp boolAnd).congr _ (fun x => by
    by_cases h₁ : x.1≤x.2 <;> by_cases h₂ : x.2≤x.1 <;> simp [Function.comp_apply,Prod.swap,h₁,h₂,le_antisymm_iff])
noncomputable def ratZero : PolyProgram Ratio.encode encodeBool (fun q => decide (q=0)) :=
  ((ratNum.comp intAbs).comp natZero).congr _ (fun q => by
    simp only [Function.comp_apply,Int.natAbs_eq_zero,Rat.num_eq_zero])
noncomputable def ratNonzero : PolyProgram Ratio.encode encodeBool (fun q => decide (q≠0)) :=
  (ratZero.comp boolNot).congr _ (fun q => by simp)
noncomputable def ratEQ : PolyProgram (encodePair Ratio.encode Ratio.encode) encodeBool (fun x : ℚ × ℚ => decide (x.1=x.2)) :=
  (ratSub.comp ratZero).congr _ (fun q => by simp only [Function.comp_apply,sub_eq_zero])
noncomputable def ratLE : PolyProgram (encodePair Ratio.encode Ratio.encode) encodeBool (fun x : ℚ × ℚ => decide (x.1≤x.2)) :=
  (((exchange Ratio.encode Ratio.encode).comp ratLT).comp boolNot).congr _ (fun x => by
    by_cases h : x.1≤x.2
    · simp [Function.comp_def,h,not_lt.mpr h]
    · simp [Function.comp_def,h,lt_of_not_ge h])
end MetricKMedian.Binary.PolyProgram
end

end OAI
