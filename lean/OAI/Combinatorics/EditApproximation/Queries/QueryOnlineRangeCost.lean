import OAI.Combinatorics.EditApproximation.Queries.QueryOnlineSources
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedOnlineWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryBandReadCosts

namespace OAI

/-! Online source ranges are computed before their random draws. This
charges the actual band, coordinate set, two powers, and triangular mass. -/

namespace EditApproximation.BinaryFraction

def queryOnlineRangeBitBudget (M P B R : ℕ) : ℕ :=
  let V := (40 * P + 2) ^ (2 * M)
  26 * B + 4 +
    (wideMaterializationBitBudget M P B + representativeCompleteBitBudget M V (4 * B + 20) + V + 1) *
      tableReadFactor R + onlineIndexBitBudget M V B + bitPowerBitBudget 80 (B + 4) +
      10000 * (80 * (B + 4) + 4) ^ 2 + 4

theorem queryOnlineRangeWithWork_bounds {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P exponent H B R : ℕ) (hP : 0 < P)
    (tau : BinaryFraction) (child : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (key : ℕ × TargetInterval target.length)
    (hB : 2 ≤ B) (hnx : Nat.size source.length ≤ B) (hny : Nat.size target.length ≤ B)
    (hM : Nat.size M ≤ B) (hb : Nat.size key.1 ≤ B) (hPb : Nat.size P ≤ B)
    (he : exponent + 1 ≤ B) (hH : Nat.size H ≤ B)
    (hd : Nat.size (M * (40 * P + 2) ^ 2) ≤ B)
    (htau : tau.width ≤ B) (hchild : ∀ i q, (child i q).1.width ≤ B)
    (hR : ∀ i q, (child i q).2 ≤ R) :
    Nat.size (queryOnlineRangeWithWork parent P exponent H tau child key).1 ≤ 240 * (B + 4) + 7 ∧
    (queryOnlineRangeWithWork parent P exponent H tau child key).2 ≤ queryOnlineRangeBitBudget M P B R := by
  let V := (40 * P + 2) ^ (2 * M)
  let band := preparedRepresentativeReadWithWork parent key.2 (parent.hi - parent.lo) key.1 P
    tau (inversePowerTwo exponent) child
  let setup := onlineIndexSetupWithWork H band.1
  let power := bitPowerWithWork setup.1.bits 80
  let mass := triangularMassWithWork (bitWordValue power.1)
  have hvalue := (preparedRepresentativeReadWithWork_eq_cost parent key.2 (parent.hi - parent.lo)
    key.1 P tau (inversePowerTwo exponent) child R hR).1
  have hsemantic : band.1 = representativeBandActions source target parent key.2 key.1 P tau.value
      (inversePowerTwo exponent).value (fun i q => (child i q).1.value) := by
    exact hvalue.trans (preparedRepresentativeWithWork_value source target parent key.2 key.1 P hP
      tau (inversePowerTwo exponent) (fun i q => (child i q).1))
  have hlen : band.1.length ≤ V := by
    rw [hsemantic]
    exact (representativeBandActions_length_le source target parent key.2 key.1 P tau.value
      (inversePowerTwo exponent).value (fun i q => (child i q).1.value)).trans
      (wideActionList_length_le M parent key.2 key.1 P hP)
  have hdim : (listedBandCoordinates band.1).length ≤ M * (40 * P + 2) ^ 2 := by
    rw [listedBandCoordinates_length, hsemantic]
    exact bandCoordinates_card_le parent key.2 hP _
      (fun action ha => representativeBandActions_wide source target parent key.2 key.1 P tau.value
        (inversePowerTwo exponent).value (fun i q => (child i q).1.value) action ha)
  have hwide : (wideActionGridWithWork M parent key.2 key.1 P).1.length ≤ V := by
    have hh := congrArg List.length (wideActionGridWithWork_value M parent key.2 key.1 P hP)
    simp only [List.length_map] at hh
    rw [hh]
    exact wideActionList_length_le M parent key.2 key.1 P hP
  have hplain := preparedRepresentativeWithWork_complete_cost parent key.2 key.1 P B hP tau
    (inversePowerTwo exponent) (fun i q => (child i q).1) hnx hny hM hb hPb htau
    (by rw [inversePowerTwo_width]; exact he) hchild
  have hmono := representativeCompleteBitBudget_mono_vertices M _ V (4 * B + 20) hwide
  have hband := preparedRepresentativeReadWithWork_factor parent key.2 (parent.hi - parent.lo)
    key.1 P tau (inversePowerTwo exponent) child R hR
  have hbandCost : band.2 ≤
      (wideMaterializationBitBudget M P B + representativeCompleteBitBudget M V (4 * B + 20) + V + 1) *
        tableReadFactor R := by
    apply hband.trans
    apply Nat.mul_le_mul_right
    omega
  have hsetup := onlineIndexSetupWithWork_bounds H B band.1 hB hH hM hny
    ((Nat.size_le_size hdim).trans hd)
  have hsetupWork : setup.2 ≤ onlineIndexBitBudget M band.1.length B := by
    simpa only [setup] using hsetup.2
  have hsetupCost : setup.2 ≤ onlineIndexBitBudget M V B :=
    hsetupWork.trans (onlineIndexBitBudget_mono_vertices M B band.1.length V hlen)
  have hsetupSize : setup.1.bits.length ≤ B + 4 := by
    simpa only [setup, Nat.size_eq_bits_len] using hsetup.1
  have hpower : power.2 ≤ bitPowerBitBudget 80 (B + 4) := by
    simpa only [power] using bitPowerWithWork_cost setup.1.bits 80 (B + 4) hsetupSize
  have hpowerLength : power.1.length ≤ 80 * (B + 4) + 1 := by
    simpa only [power] using bitPowerWithWork_length_le setup.1.bits 80 (B + 4) hsetupSize
  have hpowerSize : Nat.size (bitWordValue power.1) ≤ 80 * (B + 4) + 1 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length power.1)).trans hpowerLength
  have hmass := triangularMassWithWork_bounds (bitWordValue power.1) (80 * (B + 4) + 1) hpowerSize
  have hmassLength : mass.1.length ≤ 3 * (80 * (B + 4) + 1) + 4 := by
    simpa only [mass] using hmass.1
  have hmassCost : mass.2 ≤ 10000 * (80 * (B + 4) + 4) ^ 2 := by
    simpa only [mass, Nat.add_assoc, Nat.reduceAdd] using hmass.2
  have hwidth : (saturatingSubtractWithWork parent.hi parent.lo).2 ≤ 26 * B + 4 := by
    have hhi := (Nat.size_le_size parent.valid).trans hnx
    have hlo := (Nat.size_le_size (parent.ordered.trans parent.valid)).trans hnx
    have hh := saturatingSubtractWithWork_cost parent.hi parent.lo
    omega
  constructor
  · have hm : Nat.size (bitWordValue mass.1) ≤ 3 * (80 * (B + 4) + 1) + 4 :=
      (Nat.size_le.mpr (bitWordValue_lt_pow_length mass.1)).trans hmassLength
    have hsize : Nat.size (bitWordValue mass.1) ≤ 240 * (B + 4) + 7 :=
      hm.trans_eq (by ring)
    simpa only [queryOnlineRangeWithWork, saturatingSubtractWithWork_value,
      band, setup, power, mass] using hsize
  · have hcost : (saturatingSubtractWithWork parent.hi parent.lo).2 +
        band.2 + setup.2 + power.2 + mass.2 + 4 ≤ queryOnlineRangeBitBudget M P B R := by
      have hsum := Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hwidth hbandCost)
          hsetupCost) hpower) hmassCost) 4
      simpa only [queryOnlineRangeBitBudget, V] using hsum
    simpa only [queryOnlineRangeWithWork, saturatingSubtractWithWork_value,
      band, setup, power, mass] using hcost

end EditApproximation.BinaryFraction

end OAI
