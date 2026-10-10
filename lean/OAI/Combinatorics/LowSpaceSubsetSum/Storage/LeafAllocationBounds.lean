import OAI.Combinatorics.LowSpaceSubsetSum.Storage.BackgroundAllocation
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationResourceBounds

namespace OAI

/-! # Quantitative leaf entropy after both integer allocations -/

namespace LowSpaceSubsetSum

/-- A Boolean selects the two complementary allocations without changing the
fixed remainder convention. -/
def allocateSide (right : Bool) (r a b : ℕ) : ℕ :=
  if right then allocateRight r a b else allocateLeft r a b

noncomputable def idealSide (right : Bool) (r A B : ℝ) : ℝ :=
  if right then r / 2 + (A - B) / 2 else r / 2 + (B - A) / 2

theorem allocateSide_error (side : Bool) (r a b : ℕ)
    (ha : a ≤ r + b) (hb : b ≤ r + a) {A B e : ℝ}
    (hA : |(a : ℝ) - A| ≤ e) (hB : |(b : ℝ) - B| ≤ e) :
    |(allocateSide side r a b : ℝ) - idealSide side r A B| < e + 1 := by
  cases side
  · exact allocateLeft_entropy_error r a b ha hA hB
  · exact allocateRight_entropy_error r a b ha hb hA hB

/-- The error of a two-level allocation followed by the leaf split is small
uniformly in the parent/child orientations. -/
theorem allocated_leaf_entropy_bound (parent child : Bool) (leaf : Fin 2)
    (r a0 b0 a1 b1 : ℕ) {A0 B0 A1 B1 e : ℝ}
    (h0a : a0 ≤ r + b0) (h0b : b0 ≤ r + a0)
    (h1a : a1 ≤ allocateSide parent r a0 b0 + b1)
    (h1b : b1 ≤ allocateSide parent r a0 b0 + a1)
    (hA0 : |(a0 : ℝ) - A0| ≤ e) (hB0 : |(b0 : ℝ) - B0| ≤ e)
    (hA1 : |(a1 : ℝ) - A1| ≤ e) (hB1 : |(b1 : ℝ) - B1| ≤ e)
    {top localPart : ℝ}
    (htop : top ≤ (if parent then B0 else A0) / 4 + 3)
    (hlocal : localPart ≤ (if child then B1 else A1) / 2 + 3) :
    top + localPart + (leafBackgroundSize
      (allocateSide child (allocateSide parent r a0 b0) a1 b1) leaf : ℝ) ≤
      (r : ℝ) / 8 + (A0 + B0) / 8 + (A1 + B1) / 4 + 3 / 4 * e + 29 / 4 := by
  have hP := abs_lt.mp (allocateSide_error parent r a0 b0 h0a h0b hA0 hB0)
  have hC := abs_lt.mp (allocateSide_error child (allocateSide parent r a0 b0)
    a1 b1 h1a h1b hA1 hB1)
  have hF := (abs_le.mp (leafBackgroundSize_error
    (allocateSide child (allocateSide parent r a0 b0) a1 b1) leaf)).2
  cases parent <;> cases child <;> simp only [idealSide, Bool.false_eq_true,
    ↓reduceIte] at hP hC htop hlocal <;> linarith

/-- Once the input scale dominates the domain size, the ten-power leaf cap
absorbs the explicit allocation and rounding errors. -/
theorem allocated_leaf_error_absorbed {u m : ℝ} (hu : 2 ≤ u) (hm : 0 ≤ m)
    (hmu : m + 1 ≤ u) :
    (3 / 4 : ℝ) * (Real.logb 2 (m + 1) + 1) + 29 / 4 ≤ Real.logb 2 (u ^ 10) := by
  have hu0 : 0 < u := by linarith
  have huLog : 1 ≤ Real.logb 2 u := by
    simpa using Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) hu
  have hmLog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by linarith : 0 < m + 1) hmu
  rw [Real.logb_pow]
  norm_num
  linarith

/-- A prescribed integer count within one of its ideal count changes its
weighted entropy by at most three. -/
theorem rounded_leaf_component {b : ℕ} {k p : ℝ} (hb : 24 ≤ b)
    (hp : p ∈ Set.Icc (1 / 6) (1 / 3)) (hk : |k - (b : ℝ) * p| ≤ 1) :
    (b : ℝ) * binaryEntropy (k / b) ≤ (b : ℝ) * binaryEntropy p + 3 := by
  have hbR : (24 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have herr := abs_le.mp hk
  have hfrac : k / b ∈ Set.Icc (1 / 8) (7 / 8) := by
    constructor
    · apply (le_div_iff₀ hb0).mpr
      nlinarith [mul_le_mul_of_nonneg_left hp.1 hb0.le]
    · apply (div_le_iff₀ hb0).mpr
      nlinarith [mul_le_mul_of_nonneg_left hp.2 hb0.le]
  have h := weighted_binaryEntropy_error hb0.le hfrac
    (show p ∈ Set.Icc (1 / 8) (7 / 8) by constructor <;> linarith [hp.1, hp.2])
    (b := (b : ℝ))
  have hcancel : (b : ℝ) * (k / b) = k := by field_simp
  rw [hcancel, sub_self, abs_zero, mul_zero, add_zero] at h
  have hupper := (abs_le.mp h).2
  linarith

end LowSpaceSubsetSum

end OAI
