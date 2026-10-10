import OAI.Combinatorics.EditApproximation.Queries.QueryGroupKeyCost

namespace OAI

namespace EditApproximation.BinaryFraction

def queryCellStatesWithWork (n P b exponent : ℕ) (cell : ℕ × ℕ) :
    List (TargetInterval n) × ℕ :=
  let spacing := seedGridSpacingWithWork b P
  let side := canonicalMulWithWork (inversePowerTwo exponent) (nat b)
  let states := cellStatesWithWork n (bitWordValue spacing.1) side.1 cell
  (states.1, spacing.2 + side.2 + states.2 + exponent + 3)

def queryCellStatesBitBudget (P exponent B : ℕ) : ℕ :=
  100 * (B + 5) ^ 2 + 2000 * (B + 4) ^ 2 +
    cellStatesBitBudget P P (16 * B + 200) + exponent + 3

theorem queryCellStatesWithWork_bounds (n P b exponent B : ℕ) (cell : ℕ × ℕ)
    (hP : 0 < P) (hPb : Nat.size P ≤ B) (hb : Nat.size b ≤ B + 1)
    (he : exponent + 1 ≤ B) (hn : Nat.size n ≤ B)
    (hc : Nat.size cell.1 ≤ 16 * B + 183 ∧ Nat.size cell.2 ≤ 16 * B + 183)
    (hbd : ∃ e : ℕ, b = 2 ^ e) (hPd : ∃ e : ℕ, P = 2 ^ e) :
    (queryCellStatesWithWork n P b exponent cell).1.length ≤ P ^ 2 ∧
    (queryCellStatesWithWork n P b exponent cell).2 ≤ queryCellStatesBitBudget P exponent B := by
  let spacing := seedGridSpacingWithWork b P
  let theta := inversePowerTwo exponent
  let side := canonicalMulWithWork theta (nat b)
  let states := cellStatesWithWork n (bitWordValue spacing.1) side.1 cell
  let C := 16 * B + 200
  have hsp := seedGridSpacingWithWork_bounds b P (B + 3) (by omega) (by omega)
  have hgs : Nat.size (bitWordValue spacing.1) ≤ B + 4 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length _)).trans hsp.1
  have ht : theta.width ≤ B + 3 := by dsimp only [theta]; rw [inversePowerTwo_width]; omega
  have hsw := canonicalMulWithWork_width theta (nat b) (B + 3) ht ((nat_width_le b).trans (by omega))
  have hsc := canonicalMulWithWork_cost theta (nat b) (B + 3) ht ((nat_width_le b).trans (by omega))
  have htheta : 0 ≤ theta.value ∧ theta.value ≤ 1 := by
    rw [inversePowerTwo_value]
    exact ⟨by positivity, zpow_le_one_of_nonpos₀ (by norm_num) (by omega)⟩
  have hv : side.1.value = theta.value * b := by rw [canonicalMulWithWork_value, nat_value]
  have hg : (0 : ℚ) < seedGridSpacing b P := by
    exact_mod_cast (show 0 < seedGridSpacing b P by unfold seedGridSpacing; omega)
  have hcover : (b : ℚ) ≤ P * (seedGridSpacing b P : ℚ) := by
    exact_mod_cast seedGridSpacing_covers_dyadic hbd hPd
  have hratio : theta.value * b / seedGridSpacing b P ≤ (P : ℚ) := by
    apply (div_le_iff₀ hg).2
    exact (mul_le_mul_of_nonneg_right htheta.2 (Nat.cast_nonneg b)).trans (by simpa only [one_mul] using hcover)
  have hlen (j : ℕ) : (cellGridPoints side.1.value (bitWordValue spacing.1) j).length ≤ P := by
    rw [hv, seedGridSpacingWithWork_value b P hP]
    exact cellGridPoints_length_le (mul_nonneg htheta.1 (Nat.cast_nonneg _)) hratio
  have hstate := cellStatesWithWork_cost n (bitWordValue spacing.1) C side.1 cell
    (by dsimp only [C]; omega) (by dsimp only [C]; omega)
    (by dsimp only [C]; change side.1.width ≤ _ at hsw; omega)
    (by dsimp only [C]; omega) (by dsimp only [C]; omega)
  have hstate' : states.2 ≤ cellStatesBitBudget P P C := hstate.trans (by
    unfold cellStatesBitBudget cellGridPointsBitBudget
    gcongr <;> apply hlen)
  constructor
  · have hlength := (cellStatesWithWork_length n (bitWordValue spacing.1) side.1 cell).trans
      (Nat.mul_le_mul (hlen cell.1) (hlen cell.2))
    simpa only [queryCellStatesWithWork, spacing, theta, side, states, pow_two] using hlength
  · change spacing.2 + side.2 + states.2 + exponent + 3 ≤ _
    exact Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add hsp.2 hsc) hstate') exponent) 3

end EditApproximation.BinaryFraction

end OAI
