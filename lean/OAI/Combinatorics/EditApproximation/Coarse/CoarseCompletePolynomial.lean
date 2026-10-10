import OAI.Combinatorics.EditApproximation.Coarse.CoarseCompleteArrayWork
import OAI.Combinatorics.EditApproximation.Geometry.TreeParameters

namespace OAI

namespace EditApproximation
namespace BinaryFraction

theorem coarseCompleteNodes_polynomial (N B n : ℕ) (hB : 2 ≤ B)
    (hn : n ≤ N) (hBP : B ≤ (N + 2) ^ 4) :
    coarseCompleteNodes B (intervalTreeDepth B n) ≤ (N + 2) ^ 6 := by
  have hc := coarseCompleteNodes_le B (intervalTreeDepth B n) hB
  have hp := intervalTreeDepth_power_le B n hB
  have hm : B * max 1 n ≤ (N + 2) ^ 4 * (N + 2) :=
    Nat.mul_le_mul hBP (max_le (by omega) (by omega))
  calc
    _ ≤ 2 * (B * max 1 n) := by omega
    _ ≤ 2 * ((N + 2) ^ 4 * (N + 2)) := Nat.mul_le_mul_left 2 hm
    _ = 2 * (N + 2) ^ 5 := by ring
    _ ≤ (N + 2) ^ 6 := by
      have h := Nat.mul_le_mul_right ((N + 2) ^ 5) (show 2 ≤ N + 2 by omega)
      nlinarith only [h]

theorem coarseRootWidth_polynomial (N B k : ℕ) (hBP : B ≤ (N + 2) ^ 4)
    (hk : k ≤ 2 * (N + 2)) : B * (2 * k + 1) + 1 ≤ (N + 2) ^ 8 := by
  let X := N + 2
  have hx : 2 ≤ X := by dsimp only [X]; omega
  have hw : 2 * k + 1 ≤ 5 * X := by dsimp only [X]; omega
  have hm := Nat.mul_le_mul hBP hw
  change B * (2 * k + 1) ≤ X ^ 4 * (5 * X) at hm
  have hp : 1 ≤ X ^ 5 := one_le_pow₀ (by omega)
  have h8 : 6 * X ^ 5 ≤ X ^ 8 := by
    have hX3 : 6 ≤ X ^ 3 := by
      have h := Nat.pow_le_pow_left hx 3
      norm_num at h
      omega
    calc
      _ ≤ X ^ 3 * X ^ 5 := Nat.mul_le_mul_right _ hX3
      _ = _ := by rw [← pow_add]
  change B * (2 * k + 1) + 1 ≤ X ^ 8
  nlinarith only [hm, hp, h8]

theorem coarseActiveArrayWork_polynomial {α : Type*} (N B n k : ℕ) (Q lam allowance : ℚ)
    (hB : 2 ≤ B) (hn : n ≤ N) (hBP : B ≤ (N + 2) ^ 4) (hk : k ≤ 2 * (N + 2))
    (tree : CoarseSourceTree B α (intervalTreeDepth B n))
    (draws : CoarseThresholdDraws B (intervalTreeDepth B n)) :
    coarseActiveArrayWork k Q lam tree draws allowance ≤ (N + 2) ^ 14 := by
  have hc := coarseActiveArrayWork_le_complete k Q lam tree draws allowance
  have hn' := coarseCompleteNodes_polynomial N B n hB hn hBP
  have hw : B * (2 * k + 1) ≤ (N + 2) ^ 8 := by
    have h := coarseRootWidth_polynomial N B k hBP hk
    omega
  calc
    _ ≤ _ := hc
    _ ≤ (N + 2) ^ 8 * (N + 2) ^ 6 := Nat.mul_le_mul hw hn'
    _ = _ := by rw [← pow_add]

end BinaryFraction
end EditApproximation

end OAI
