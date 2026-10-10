import OAI.Combinatorics.EditApproximation.Binary.BinaryMedianKernel
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The literal scale list and sample counts, including scales below one.
Dyadic input exponents are carried by the computed parameter construction;
no real logarithm is evaluated by these routines. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem signedPowerTwoWithWork_value (e : ℤ) :
    (signedPowerTwoWithWork e).1.value = (2 : ℚ) ^ e := by
  unfold signedPowerTwoWithWork
  split_ifs with h
  · change (bitWordValue (powerTwoWord e.toNat) : ℚ) / 1 = (2 : ℚ) ^ e
    rw [div_one, powerTwoWord_value, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast,
      Int.toNat_of_nonneg h]
  · rw [inversePowerTwo_value, Int.toNat_of_nonneg
      (show 0 ≤ -e from neg_nonneg.mpr (le_of_lt (lt_of_not_ge h))), neg_neg]

theorem signedPowerTwoWithWork_width (e : ℤ) :
    (signedPowerTwoWithWork e).1.width ≤ e.natAbs + 1 := by
  unfold signedPowerTwoWithWork
  split_ifs with h
  · simp only [width, powerTwoWord_length, List.length_cons, List.length_nil]
    have hs := Int.toNat_add_toNat_neg_eq_natAbs e
    have he : e.toNat ≤ e.natAbs := by omega
    omega
  · rw [inversePowerTwo_width]
    have hs := Int.toNat_add_toNat_neg_eq_natAbs e
    have he : (-e).toNat ≤ e.natAbs := by omega
    omega



@[simp] theorem groupScalesWithWork_value (eM eb eF : ℕ) :
    ((groupScalesWithWork eM eb eF).1.map value) =
      groupDyadicScales (2 ^ eM) (2 ^ eb) ((2 : ℚ) ^ eF) := by
  have hlower : ((2 ^ eb : ℕ) : ℚ) / (2 ^ eM : ℕ) = (2 : ℚ) ^ ((eb : ℤ) - eM) := by
    rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0),
      zpow_natCast, zpow_natCast]
  have hupper : (64 : ℚ) * (2 : ℚ) ^ eF * (2 ^ eb : ℕ) =
      (2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, zpow_natCast, pow_add, pow_add]
    norm_num
  have hlog : Int.log 2 ((2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ)) = ((6 + eF + eb : ℕ) : ℤ) := by
    simpa only [Nat.cast_ofNat] using Int.log_zpow (R := ℚ) (by decide : 1 < 2) ((6 + eF + eb : ℕ) : ℤ)
  have hclog : Int.clog 2 ((2 : ℚ) ^ ((eb : ℤ) - eM)) = (eb : ℤ) - eM := by
    simpa only [Nat.cast_ofNat] using Int.clog_zpow (R := ℚ) (by decide : 1 < 2) ((eb : ℤ) - eM)
  simp only [groupScalesWithWork, arithmeticMapWithWork_value, List.map_map,
    Function.comp_def, signedPowerTwoWithWork_value, groupDyadicScales, hlower, hupper, hlog, hclog]

theorem groupScalesWithWork_length (eM eb eF : ℕ) :
    (groupScalesWithWork eM eb eF).1.length = 7 + eM + eF := by
  have h := congrArg List.length (groupScalesWithWork_value eM eb eF)
  simpa only [List.length_map, groupDyadicScales_length_dyadic] using h

/-- Exact versus sampled is decided from the actual binary sample count. -/


@[simp] theorem groupSampleCountWithWork_value (M Q b : ℕ) (h : BinaryFraction) :
    bitWordValue (groupSampleCountWithWork M Q b h).1 = groupSampleCount M Q b h.value := by
  simp only [groupSampleCountWithWork, wordMinWithWork_value, bitWordValue_bits,
    naturalCeilingWithWork_value, divWithWork_value, canonicalMulWithWork_value,
    nat_value, groupSampleCount]

end BinaryFraction
end EditApproximation

end OAI
