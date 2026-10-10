import OAI.Combinatorics.EditApproximation.Binary.BinaryKeyedOnline
import OAI.Combinatorics.EditApproximation.Binary.BinaryCoordinateActionWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalGridWork

namespace OAI

/-! Actual coordinate enumeration, index construction and range reduction
preceding the online optimizer, counted in Boolean operations. -/

namespace EditApproximation
namespace BinaryFraction

def onlineIndexBitBudget (M vertices B : ℕ) : ℕ :=
  bandCoordinatesBitBudget M vertices B + 40 * (B + 4) +
    bitPowerBitBudget 80 (B + 4) + 3

theorem onlineIndexSetupWithWork_bounds {M n : ℕ} (H B : ℕ)
    (band : List (Fin M → TargetInterval n))
    (_hB : 2 ≤ B) (hH : Nat.size H ≤ B) (hM : Nat.size M ≤ B)
    (hn : Nat.size n ≤ B) (hd : Nat.size (listedBandCoordinates band).length ≤ B) :
    Nat.size (onlineIndexSetupWithWork H band).1 ≤ B + 4 ∧
      (onlineIndexSetupWithWork H band).2 ≤ onlineIndexBitBudget M band.length B := by
  let coordinates := bandCoordinatesWithWork band
  let total := binaryNaturalAddWithWork H coordinates.1.length
  let offset := binaryNaturalAddWithWork (bitWordValue total.1) 2
  have hcoord := bandCoordinatesWithWork_cost band B hM hn
  have hd' : Nat.size coordinates.1.length ≤ B := by
    simpa only [coordinates, bandCoordinatesWithWork_value] using hd
  have htotal : Nat.size (bitWordValue total.1) ≤ B + 2 := by
    rw [binaryNaturalAddWithWork_value]
    exact (binaryNaturalAdd_size_le _ _).trans (by omega)
  have hoffset : offset.1.length ≤ B + 4 := by
    have hh := bitAddWithWork_length (bitWordValue total.1).bits (2 : ℕ).bits false
    change offset.1.length ≤ _ at hh
    rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len] at hh
    have htwo : Nat.size 2 = 2 := by decide
    omega
  have hsize : Nat.size (bitWordValue offset.1) ≤ B + 4 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length offset.1)).trans hoffset
  have hsumc := binaryNaturalAddWithWork_cost H coordinates.1.length
  have hoffc := binaryNaturalAddWithWork_cost (bitWordValue total.1) 2
  have hpower := bitPowerWithWork_cost offset.1 80 (B + 4) hoffset
  have htwo : Nat.size 2 = 2 := by decide
  constructor
  · exact hsize
  · change coordinates.2 + total.2 + offset.2 + (bitPowerWithWork offset.1 80).2 + 3 ≤ _
    change coordinates.2 ≤ _ at hcoord
    change total.2 ≤ _ at hsumc
    change offset.2 ≤ _ at hoffc
    rw [htwo] at hoffc
    unfold onlineIndexBitBudget
    omega

def reduceOnlineBitBudget (B : ℕ) : ℕ :=
  10000 * (B + 3) ^ 2 + 200 * (4 * B + 6) ^ 2 + B + 2

theorem reduceOnlineIntegerWithWork_bounds (K integer B : ℕ) (hK : 0 < K)
    (hKB : Nat.size K ≤ B) (hi : Nat.size integer ≤ B) :
    Nat.size (reduceOnlineIntegerWithWork K hK integer).1.val ≤ 3 * B + 4 ∧
      (reduceOnlineIntegerWithWork K hK integer).2 ≤ reduceOnlineBitBudget B := by
  let mass := triangularMassWithWork K
  have hm := triangularMassWithWork_bounds K B hKB
  have hms : Nat.size (bitWordValue mass.1) ≤ 3 * B + 4 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length mass.1)).trans hm.1
  have hpos : 0 < bitWordValue mass.1 := by
    rw [triangularMassWithWork_value]
    exact optimizerTriangularMass_positive K hK
  have hsmall := (binaryNaturalDivModWithWork_spec integer (bitWordValue mass.1) hpos).2
  have hrem : Nat.size (bitWordValue (binaryNaturalDivModWithWork integer (bitWordValue mass.1)).2.1) ≤
      3 * B + 4 := by
    rw [hsmall]
    exact (Nat.size_le_size (Nat.mod_lt integer hpos).le).trans hms
  have hc := binaryNaturalDivModWithWork_cost integer (bitWordValue mass.1)
  constructor
  · exact hrem
  · change mass.2 + (binaryNaturalDivModWithWork integer (bitWordValue mass.1)).2.2 + Nat.size integer + 2 ≤ _
    have hmc : mass.2 ≤ 10000 * (B + 3) ^ 2 := hm.2
    unfold reduceOnlineBitBudget
    have hprod : (Nat.size integer + 1) * (Nat.size integer + Nat.size (bitWordValue mass.1) + 1) ≤
        (4 * B + 6) ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul (by omega) (by omega)
    have h30 := Nat.mul_le_mul_left 30 hprod
    rw [Nat.mul_assoc] at hc
    omega

end BinaryFraction
end EditApproximation

end OAI
