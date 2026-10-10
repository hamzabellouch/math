import OAI.Combinatorics.EditApproximation.Coarse.CoarseLevelMagnitude

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseBitParameters_grid (H N k B q L d : ℕ)
    (hH : 100 ≤ H) (hd : d ≤ H)
    (hN : Nat.size N ≤ 2 * H) (hk : Nat.size k ≤ 2 * H)
    (hB : Nat.size B ≤ 2 * H) (hq : Nat.size q ≤ 2 * H) (hL : Nat.size L ≤ 2 * H) :
    Nat.size (coarseCommonDenominator 1 q L B d) ≤ 10 * H ^ 2 ∧
    Nat.size (coarseLevelMagnitude N k B d + 2) + 2 * (10 * H ^ 2) + 1 ≤ H ^ 3 := by
  have hsum : Nat.size L + Nat.size B + Nat.size q ≤ 6 * H := by omega
  have hcoeff := Nat.mul_le_mul hd hsum
  have hden := coarseCommonDenominator_bits 1 q L B d
  rw [Nat.size_one] at hden
  have hbaseprod := natural_product_bit_length 2 B
  have hbasesum := natural_sum_bit_length (2 * B) 2
  rw [show Nat.size 2 = 2 by decide] at hbaseprod hbasesum
  have hbase : Nat.size (2 * B + 2) ≤ 2 * H + 5 := by omega
  have hsumNk := natural_sum_bit_length N k
  have hsumone := natural_sum_bit_length (N + k) 1
  rw [Nat.size_one] at hsumone
  have hnk : Nat.size (N + k + 1) ≤ 4 * H + 3 := by omega
  have hmag := coarseLevelMagnitude_bits N k B d
  have hmag2 := natural_sum_bit_length (coarseLevelMagnitude N k B d) 2
  rw [show Nat.size 2 = 2 by decide] at hmag2
  have hprod := Nat.mul_le_mul (show d + 1 ≤ H + 1 by omega) hbase
  have hsq : H ≤ H ^ 2 := Nat.le_pow (by decide)
  have hcube : 100 * H ^ 2 ≤ H ^ 3 := by
    have hh := Nat.mul_le_mul_right (H ^ 2) hH
    nlinarith only [hh]
  constructor
  · nlinarith only [hden, hq, hcoeff, hH, hsq]
  · nlinarith only [hmag, hmag2, hnk, hprod, hsq, hcube, hH]

end BinaryFraction
end EditApproximation

end OAI
