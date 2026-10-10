import OAI.Combinatorics.EditApproximation.Binary.BinaryCellGridWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalGuardWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryWideChildWork

namespace OAI

/-! Complete work for a whole-cell representative scan, including both
endpoint grids and every initial-value eligibility test. -/

namespace EditApproximation
namespace BinaryFraction

private theorem flatMap_length_bound {α β : Type*} (f : α → List β)
    (xs : List α) (n : ℕ) (h : ∀ x ∈ xs, (f x).length ≤ n) :
    (xs.flatMap f).length ≤ xs.length * n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hh := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem cellStatesWithWork_length (n g : ℕ) (side : BinaryFraction) (cell : ℕ × ℕ) :
    (cellStatesWithWork n g side cell).1.length ≤
      (cellGridPoints side.value g cell.1).length *
        (cellGridPoints side.value g cell.2).length := by
  simp only [cellStatesWithWork, arithmeticFlatMapWithWork_value, filterMapWithWork_value,
    makeStateWithWork_value]
  have h := flatMap_length_bound
    (fun lo => ((cellGridPointsWithWork side g cell.2).1.filterMap (makeTargetState n lo)))
    (cellGridPointsWithWork side g cell.1).1 (cellGridPointsWithWork side g cell.2).1.length
    (fun _ _ => List.length_filterMap_le _ _)
  simpa only [cellGridPointsWithWork_value] using h

def cellCentersBitBudget (left right B : ℕ) : ℕ :=
  100 * (B + 2) ^ 2 + 2000 * (B + 1) ^ 2 +
    cellStatesBitBudget left right (4 * B + 40) +
    left * right * (localEligibilityBitBudget B + 3) + 3

theorem cellCentersWithWork_cost {n : ℕ} (P F b B : ℕ) (a theta : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction) (cell : ℕ × ℕ)
    (hB : 6 ≤ B) (hn : Nat.size n ≤ B) (hb : Nat.size b + 2 ≤ B)
    (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (ha : a.width ≤ B) (htheta : theta.width ≤ B)
    (hi : ∀ q, (initial q).width ≤ B)
    (hleft : Nat.size cell.1 ≤ B) (hright : Nat.size cell.2 ≤ B) :
    (cellCentersWithWork P F b a theta initial cell).2 ≤
      cellCentersBitBudget
        (cellGridPoints (theta.value * b) (bitWordValue (seedGridSpacingWithWork b P).1) cell.1).length
        (cellGridPoints (theta.value * b) (bitWordValue (seedGridSpacingWithWork b P).1) cell.2).length B := by
  let spacing := seedGridSpacingWithWork b P
  let side := canonicalMulWithWork theta (nat b)
  let states := cellStatesWithWork n (bitWordValue spacing.1) side.1 cell
  let C := 4 * B + 40
  have hspacing := seedGridSpacingWithWork_bounds b P B (by omega) hP
  have hgs : Nat.size (bitWordValue spacing.1) ≤ C :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length spacing.1)).trans (by
      have hh : spacing.1.length ≤ B + 1 := hspacing.1
      dsimp only [C]
      omega)
  have hsidew := canonicalMulWithWork_width theta (nat b) B htheta ((nat_width_le b).trans hb)
  have hsidec := canonicalMulWithWork_cost theta (nat b) B htheta ((nat_width_le b).trans hb)
  change side.1.width ≤ 4 * B + 2 at hsidew
  have hstates := cellStatesWithWork_cost n (bitWordValue spacing.1) C side.1 cell
    (by dsimp only [C]; omega) hgs (by dsimp only [C]; omega)
    (by dsimp only [C]; omega) (by dsimp only [C]; omega)
  have hcount := cellStatesWithWork_length n (bitWordValue spacing.1) side.1 cell
  have hselected := filterWithWork_cost
    (fun r => centerEligibilityWithWork b F a (initial r)) states.1
    (localEligibilityBitBudget B)
    (fun r _ => centerEligibilityWithWork_cost b F B a (initial r) hB hb hF ha (hi r))
  change states.1.length ≤ _ at hcount
  change states.2 ≤ _ at hstates
  change side.2 ≤ _ at hsidec
  change spacing.2 + side.2 + states.2 +
    (filterWithWork (fun r => centerEligibilityWithWork b F a (initial r)) states.1).2 + 3 ≤ _
  have hsc : spacing.2 ≤ 100 * (B + 2) ^ 2 := hspacing.2
  have hv : side.1.value = theta.value * b := by
    simp only [side, canonicalMulWithWork_value, nat_value]
  rw [hv] at hstates hcount
  unfold cellCentersBitBudget
  change _ ≤ 100 * (B + 2) ^ 2 + 2000 * (B + 1) ^ 2 +
    cellStatesBitBudget
      (cellGridPoints (theta.value * b) (bitWordValue spacing.1) cell.1).length
      (cellGridPoints (theta.value * b) (bitWordValue spacing.1) cell.2).length (4 * B + 40) +
    (cellGridPoints (theta.value * b) (bitWordValue spacing.1) cell.1).length *
      (cellGridPoints (theta.value * b) (bitWordValue spacing.1) cell.2).length *
        (localEligibilityBitBudget B + 3) + 3
  have hfilter := hselected.trans (Nat.mul_le_mul_right _ hcount)
  dsimp only [C] at hstates
  omega

theorem cellCentersBitBudget_mono_count (l l' r r' B : ℕ) (hl : l ≤ l') (hr : r ≤ r') :
    cellCentersBitBudget l r B ≤ cellCentersBitBudget l' r' B := by
  unfold cellCentersBitBudget cellStatesBitBudget cellGridPointsBitBudget
  gcongr

theorem cellCentersWithWork_uniform_cost {n : ℕ} (P F b B : ℕ) (a theta : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction) (cell : ℕ × ℕ)
    (hB : 6 ≤ B) (hn : Nat.size n ≤ B) (hb : Nat.size b + 2 ≤ B)
    (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B)
    (ha : a.width ≤ B) (htheta : theta.width ≤ B)
    (hi : ∀ q, (initial q).width ≤ B)
    (hleft : Nat.size cell.1 ≤ B) (hright : Nat.size cell.2 ≤ B)
    (hthetaValue : 0 ≤ theta.value ∧ theta.value ≤ 1)
    (hbdyadic : ∃ e : ℕ, b = 2 ^ e) (hPdyadic : ∃ e : ℕ, P = 2 ^ e) :
    (cellCentersWithWork P F b a theta initial cell).2 ≤ cellCentersBitBudget P P B := by
  have hPpos : 0 < P := by obtain ⟨e, rfl⟩ := hPdyadic; exact Nat.two_pow_pos e
  have hg : (0 : ℚ) < seedGridSpacing b P := by
    exact_mod_cast (show 0 < seedGridSpacing b P by unfold seedGridSpacing; omega)
  have hcover : (b : ℚ) ≤ P * (seedGridSpacing b P : ℚ) := by
    exact_mod_cast seedGridSpacing_covers_dyadic hbdyadic hPdyadic
  have hsize : theta.value * b / seedGridSpacing b P ≤ (P : ℚ) := by
    apply (div_le_iff₀ hg).2
    have hb : theta.value * b ≤ (b : ℚ) := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hthetaValue.2 (Nat.cast_nonneg (α := ℚ) b)
    exact hb.trans hcover
  have hlen (j : ℕ) : (cellGridPoints (theta.value * b) (seedGridSpacing b P) j).length ≤ P :=
    cellGridPoints_length_le (mul_nonneg hthetaValue.1 (Nat.cast_nonneg _)) hsize
  have hc := cellCentersWithWork_cost P F b B a theta initial cell hB hn hb hP hF ha htheta hi hleft hright
  rw [seedGridSpacingWithWork_value b P hPpos] at hc
  exact hc.trans (cellCentersBitBudget_mono_count _ _ _ _ B (hlen cell.1) (hlen cell.2))

end BinaryFraction
end EditApproximation

end OAI
