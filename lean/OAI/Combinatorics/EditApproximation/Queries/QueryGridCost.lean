import OAI.Combinatorics.EditApproximation.Queries.QueryInitialSupport
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalRepresentativeWork

namespace OAI

/-! A scale guard bounds the number of grid points even when the center
radius is as large as the input.  These bounds include construction of
all points, before subsequent eligibility filtering. -/

namespace EditApproximation

theorem queryGridSpacing_count (P b radius K : ℕ) (hP : 0 < P) (hr : radius ≤ K * b) :
    2 * radius / seedGridSpacing b P + 2 ≤ 4 * K * P + 2 := by
  have hg : 0 < seedGridSpacing b P := by unfold seedGridSpacing; omega
  have hq : b / P ≤ seedGridSpacing b P := le_max_right _ _
  have hdiv := Nat.lt_mul_div_succ b hP
  have hb : b ≤ 2 * P * seedGridSpacing b P := by nlinarith only [hq, hdiv, hg]
  have hn : 2 * radius ≤ 4 * K * P * seedGridSpacing b P := by
    nlinarith only [hr, Nat.mul_le_mul_left (2 * K) hb]
  have hfloor := Nat.div_mul_le_self (2 * radius) (seedGridSpacing b P)
  nlinarith only [hfloor, hn, hg]

def queryGridPointsWithWork {n : ℕ} (P b radius : ℕ) (q : TargetInterval n) :
    List (TargetInterval n) × ℕ :=
  let spacing := seedGridSpacingWithWork b P
  let points := gridStateBoxWithWork n (bitWordValue spacing.1) radius q.lo q.hi
  (points.1, spacing.2 + points.2 + 1)

def queryGridPointsBitBudget (P K B : ℕ) : ℕ :=
  100 * (B + 2) ^ 2 + gridStateBoxBitBudget (4 * K * P + 2) (B + 1) + 1

theorem queryGridPointsWithWork_bounds {n : ℕ} (P b radius K B : ℕ) (q : TargetInterval n)
    (hP : 0 < P) (hPb : Nat.size P ≤ B) (hb : Nat.size b ≤ B)
    (hr : Nat.size radius ≤ B) (hn : Nat.size n ≤ B) (hcount : radius ≤ K * b) :
    (queryGridPointsWithWork P b radius q).1.length ≤ (4 * K * P + 2) ^ 2 ∧
    (queryGridPointsWithWork P b radius q).2 ≤ queryGridPointsBitBudget P K B := by
  let spacing := seedGridSpacingWithWork b P
  have hs := seedGridSpacingWithWork_bounds b P B hb hPb
  have hp := seedGridSpacingWithWork_pos b P hP
  have hsp : Nat.size (bitWordValue spacing.1) ≤ B + 1 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length spacing.1)).trans hs.1
  have hc := queryGridSpacing_count P b radius K hP hcount
  have hv : bitWordValue spacing.1 = seedGridSpacing b P := seedGridSpacingWithWork_value b P hP
  have hgc := gridStateBoxWithWork_cost n (bitWordValue spacing.1) radius q.lo q.hi (B + 1)
    hp (by omega) hsp (by omega)
    ((Nat.size_le_size (q.ordered.trans q.valid)).trans (by omega))
    ((Nat.size_le_size q.valid).trans (by omega))
  rw [hv] at hgc
  have hgc' := hgc.trans (gridStateBoxBitBudget_mono_count _ _ (B + 1) hc)
  have hlength : (gridStateBoxWithWork n (bitWordValue spacing.1) radius q.lo q.hi).1.length ≤
      (4 * K * P + 2) ^ 2 := by
    rw [gridStateBoxWithWork_value _ _ _ _ _ hp, hv]
    exact (localTargetStates_length_le (by unfold seedGridSpacing; omega) q).trans
      (Nat.pow_le_pow_left hc 2)
  have hcost : spacing.2 +
      (gridStateBoxWithWork n (bitWordValue spacing.1) radius q.lo q.hi).2 + 1 ≤
      queryGridPointsBitBudget P K B := by
    rw [hv]
    exact Nat.add_le_add_right (Nat.add_le_add hs.2 hgc') 1
  simpa only [queryGridPointsWithWork, spacing] using And.intro hlength hcost

end EditApproximation

end OAI
