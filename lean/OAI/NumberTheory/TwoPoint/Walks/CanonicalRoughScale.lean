import OAI.NumberTheory.TwoPoint.Bounds.QualitativeStrongRoughShifts

namespace OAI

/-! Reparametrizing the stronger qualitative estimate at the actual
quantitative prime-band endpoint exp(L^.995). The gain survives the
finite tuple expansion and the final reciprocal L normalizer. -/

namespace TwoPointCorrelations

open Filter

noncomputable def canonicalRoughParameter (L : ℝ) : ℝ := L ^ (9950 / 9999 : ℝ)

lemma canonicalRoughParameter_prime_endpoint (L : ℝ) (hL : 0 ≤ L) :
    canonicalRoughParameter L ^ (9999 / 10000 : ℝ) = L ^ (199 / 200 : ℝ) := by
  unfold canonicalRoughParameter
  rw [← Real.rpow_mul hL]
  norm_num

lemma canonicalRoughParameter_square_ge (L : ℝ) (hL : 1 ≤ L) :
    L ≤ canonicalRoughParameter L ^ (2 : ℕ) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  calc
    L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
    _ ≤ L ^ (19900 / 9999 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    _ = _ := by
      unfold canonicalRoughParameter
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0]
      norm_num

lemma canonicalRoughParameter_error (L : ℝ) (hL : 0 ≤ L) :
    canonicalRoughParameter L ^ (-11 / 10 : ℝ) = L ^ (-10945 / 9999 : ℝ) := by
  unfold canonicalRoughParameter
  rw [← Real.rpow_mul hL]
  norm_num

lemma canonicalRoughParameter_tendsto : Tendsto canonicalRoughParameter atTop atTop :=
  tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9950 / 9999)

lemma tuple_expansion_small_power (L : ℝ) (hL : 1 ≤ L) (J : ℕ)
    (hJ : (J : ℝ) ≤ Real.log L / 200) :
    (2 : ℝ) ^ J ≤ L ^ (1 / 100 : ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hl : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlog2 : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos hLp]
  apply Real.exp_le_exp.mpr
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  nlinarith

lemma canonical_centering_rate_bound (L : ℝ) (hL : 1 ≤ L) (J : ℕ)
    (hJ : (J : ℝ) ≤ Real.log L / 200) :
    (2 : ℝ) ^ J * L * canonicalRoughParameter L ^ (-11 / 10 : ℝ) ≤
      L ^ (-2 / 25 : ℝ) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  rw [canonicalRoughParameter_error L hL0]
  calc
    _ ≤ L ^ (1 / 100 : ℝ) * L * L ^ (-10945 / 9999 : ℝ) := by
      gcongr
      exact tuple_expansion_small_power L hL J hJ
    _ = L ^ ((1 / 100 : ℝ) + 1 - 10945 / 9999) := by
      rw [sub_eq_add_neg, Real.rpow_add (zero_lt_one.trans_le hL),
        Real.rpow_add (zero_lt_one.trans_le hL), Real.rpow_one]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

end TwoPointCorrelations

end OAI
