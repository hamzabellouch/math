import OAI.Combinatorics.ContingencyTables.Counting.CountingOracleScheduleProgram

namespace OAI

/-! # Numeric bounds for the executed oracle schedule -/

namespace ContingencyTables.CountingOracleScheduleProgram
open MatchingFPRAS

lemma sampleCount_bound (j E F : ℕ) (delta failure : Fraction)
    (hd : 0 < TreeFraction.val delta) (_hf : 0 < TreeFraction.val failure)
    (hE : 1/TreeFraction.val delta ≤ (E:ℚ))
    (hF : 1/TreeFraction.val failure ≤ (F:ℚ)) :
    sampleCount (j,(delta,failure)) ≤ 65536*(j+1)*F*E^2 := by
  rw [sampleCount_val]
  apply Nat.ceil_le.mpr
  have hs : (1/TreeFraction.val delta)^2 ≤ (E:ℚ)^2 := by
    have h0 := (one_div_pos.mpr hd).le
    nlinarith
  have hh := mul_le_mul hF hs (sq_nonneg _) (Nat.cast_nonneg F)
  have hm := mul_le_mul_of_nonneg_left hh (show (0:ℚ) ≤ 65536*(j+1) by positivity)
  convert hm using 1 <;> push_cast <;> ring

lemma offsetAccuracy_bound (d E : ℕ) (delta : Fraction)
    (hE : 1/TreeFraction.val delta ≤ (E:ℚ)) :
    offsetAccuracy (d,delta) ≤ 4096*d*E := by
  rw [offsetAccuracy_val]
  apply Nat.ceil_le.mpr
  have hh := mul_le_mul_of_nonneg_left hE (show (0:ℚ) ≤ 4096*d by positivity)
  convert hh using 1 <;> push_cast <;> ring

lemma oracleTime_bound (M B E : ℕ) (theta : Fraction)
    (hE : 1/TreeFraction.val theta ≤ (E:ℚ)) :
    oracleTime ((M,B),theta) ≤ M*(B+16*E) := by
  rw [oracleTime_val]
  apply Nat.ceil_le.mpr
  have ht : 16/TreeFraction.val theta ≤ 16*(E:ℚ) := by
    have hh := mul_le_mul_of_nonneg_left hE (show (0:ℚ) ≤ 16 by norm_num)
    simpa only [mul_one_div] using hh
  have hh := mul_le_mul_of_nonneg_left (add_le_add_left ht (B:ℚ)) (Nat.cast_nonneg M)
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,add_comm] using hh

end ContingencyTables.CountingOracleScheduleProgram

end OAI
