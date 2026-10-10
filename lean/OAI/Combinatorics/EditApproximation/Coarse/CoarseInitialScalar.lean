import OAI.Combinatorics.EditApproximation.Coarse.CoarseInitialCost

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Scalar envelope used only after summing the executed dyadic roots. -/
theorem coarseInitial_aggregate_scalar (H x a g roots work : ℕ) (hH : 100 ≤ H)
    (hg : g ≤ H + 1)
    (hr : roots ≤ H ^ 32 * (a + g))
    (hw : work ≤ roots + (3 * x + 1) * (8 * H ^ 3 + 4) +
      10000 * (g + 1) * (H ^ 4 + 2) ^ 2) :
    work ≤ H ^ 36 * (a + x + 1) := by
  have hpos : 0 < H := by omega
  have hpow (i j : ℕ) (hij : i ≤ j) : H ^ i ≤ H ^ j := Nat.pow_le_pow_right hpos hij
  have hone : 1 ≤ H := by omega
  have hthree : 3 ≤ H := by omega
  have hhundred : 10000 ≤ H ^ 2 := by nlinarith
  have hgp : g + 1 ≤ H ^ 2 := by nlinarith
  have hp3 : 1 ≤ H ^ 3 := one_le_pow₀ hone
  have hp4 : H ^ 4 + 2 ≤ H ^ 5 := by
    have hh := Nat.mul_le_mul_right (H ^ 4) (show 2 ≤ H by omega)
    have h4 : 2 ≤ H ^ 4 := (show 2 ≤ H by omega).trans (by simpa only [pow_one] using hpow 1 4 (by decide))
    nlinarith only [hh, h4]
  have hwrap : 10000 * (g + 1) * (H ^ 4 + 2) ^ 2 ≤ H ^ 14 := by
    calc
      _ ≤ H ^ 2 * H ^ 2 * (H ^ 5) ^ 2 := by gcongr
      _ = _ := by ring
  have hscale : 3 * (8 * H ^ 3 + 4) ≤ H ^ 5 := by
    have hh := Nat.mul_le_mul_right (H ^ 3) (show 36 ≤ H ^ 2 by nlinarith)
    nlinarith only [hh, hp3]
  have hscan : (3 * x + 1) * (8 * H ^ 3 + 4) ≤ (x + 1) * H ^ 5 := by
    calc
      _ ≤ (x + 1) * (3 * (8 * H ^ 3 + 4)) := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_left _ hscale
  have hroot : roots ≤ H ^ 34 * (a + 1) := by
    have hga : a + g ≤ H ^ 2 * (a + 1) := by
      have ha := Nat.mul_le_mul_right a (show 1 ≤ H ^ 2 from one_le_pow₀ hone)
      nlinarith only [ha, hgp]
    calc
      roots ≤ H ^ 32 * (a + g) := hr
      _ ≤ H ^ 32 * (H ^ 2 * (a + 1)) := Nat.mul_le_mul_left _ hga
      _ = _ := by ring
  have hscan' := hscan.trans (Nat.mul_le_mul_left (x + 1) (hpow 5 34 (by decide)))
  have hwrap' := hwrap.trans (hpow 14 34 (by decide))
  have hfinal : 3 * H ^ 34 ≤ H ^ 36 := by
    have hh := Nat.mul_le_mul_left (H ^ 34) (show 3 ≤ H ^ 2 by nlinarith)
    nlinarith only [hh]
  have hfinal' := Nat.mul_le_mul_right (a + x + 1) hfinal
  nlinarith only [hw, hroot, hscan', hwrap', hfinal', Nat.zero_le a, Nat.zero_le x]

end BinaryFraction
end EditApproximation

end OAI
