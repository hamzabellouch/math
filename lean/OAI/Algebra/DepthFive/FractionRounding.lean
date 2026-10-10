import Mathlib

namespace OAI

noncomputable section
namespace Problem335

/-- Quantitative monotonicity of the fraction used in the rounded rank parameters. -/
theorem fraction_rounding_ratio_bounds {x v a : ℝ} (hx : 0 < x) (hv : 0 < v)
    (hxa : x ≤ a) (hax : a ≤ x + 1) :
    1 ≤ (a / (a + v)) / (x / (x + v)) ∧
      (a / (a + v)) / (x / (x + v)) ≤ 1 + 1 / x := by
  have ha : 0 < a := lt_of_lt_of_le hx hxa
  have hxv : 0 < x + v := add_pos hx hv
  have hav : 0 < a + v := add_pos ha hv
  have hratio : (a / (a + v)) / (x / (x + v)) =
      a * (x + v) / (x * (a + v)) := by field_simp
  rw [hratio]
  constructor
  · apply (le_div_iff₀ (mul_pos hx hav)).mpr
    nlinarith
  · apply (div_le_iff₀ (mul_pos hx hav)).mpr
    have hxne : x ≠ 0 := ne_of_gt hx
    field_simp
    nlinarith

/-- Rounding upward by at most one changes the logarithm by at most `1/x`. -/
theorem fraction_rounding_log_bounds {x v a : ℝ} (hx : 0 < x) (hv : 0 < v)
    (hxa : x ≤ a) (hax : a ≤ x + 1) :
    0 ≤ Real.log ((a / (a + v)) / (x / (x + v))) ∧
      Real.log ((a / (a + v)) / (x / (x + v))) ≤ 1 / x := by
  obtain ⟨hlo, hhi⟩ := fraction_rounding_ratio_bounds hx hv hxa hax
  constructor
  · exact Real.log_nonneg hlo
  · have hpos : 0 < (a / (a + v)) / (x / (x + v)) := lt_of_lt_of_le zero_lt_one hlo
    have hlog := Real.log_le_sub_one_of_pos hpos
    linarith

/-- Once the unrounded value is at least one, the logarithmic loss is `2/a`. -/
theorem fraction_rounding_log_le_two_div {x v a : ℝ} (hx : 1 ≤ x) (hv : 0 < v)
    (hxa : x ≤ a) (hax : a ≤ x + 1) :
    Real.log ((a / (a + v)) / (x / (x + v))) ≤ 2 / a := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hapos : 0 < a := hxpos.trans_le hxa
  apply (fraction_rounding_log_bounds hxpos hv hxa hax).2.trans
  apply (div_le_div_iff₀ hxpos hapos).mpr
  nlinarith

/-- Equivalent multiplicative exponential form of the rounding estimate. -/
theorem fraction_rounding_bounds {x v a : ℝ} (hx : 0 < x) (hv : 0 < v)
    (hxa : x ≤ a) (hax : a ≤ x + 1) :
    x / (x + v) ≤ a / (a + v) ∧
      a / (a + v) ≤ x / (x + v) * Real.exp (1 / x) := by
  have hbase : 0 < x / (x + v) := div_pos hx (add_pos hx hv)
  obtain ⟨hlo, hhi⟩ := fraction_rounding_ratio_bounds hx hv hxa hax
  constructor
  · exact (one_le_div hbase).mp hlo
  · have hexp : 1 + 1 / x ≤ Real.exp (1 / x) := by
      simpa [add_comm] using Real.add_one_le_exp (1 / x)
    have hratio := hhi.trans hexp
    exact (div_le_iff₀ hbase).mp hratio |>.trans_eq (mul_comm _ _)

/-- The ceiling specialization used for both parameters `a` and `b`. -/
theorem fraction_natCeil_log_bounds {x v : ℝ} (hx : 0 < x) (hv : 0 < v) :
    0 ≤ Real.log (((⌈x⌉₊ : ℝ) / ((⌈x⌉₊ : ℝ) + v)) / (x / (x + v))) ∧
      Real.log (((⌈x⌉₊ : ℝ) / ((⌈x⌉₊ : ℝ) + v)) / (x / (x + v))) ≤ 1 / x := by
  apply fraction_rounding_log_bounds hx hv
  · exact Nat.le_ceil x
  · exact le_of_lt (Nat.ceil_lt_add_one (le_of_lt hx))

/-- The first rank parameter has ideal fraction `1/s`; here `s = sqrt n`. -/
theorem fraction_natCeil_inverse_bounds {s v : ℝ} (hs : 1 < s) (hv : 0 < v) :
    let a : ℝ := ⌈v / (s - 1)⌉₊
    1 / s ≤ a / (a + v) ∧
      a / (a + v) ≤ 1 / s * Real.exp ((s - 1) / v) := by
  have hsm : 0 < s - 1 := sub_pos.mpr hs
  have hx : 0 < v / (s - 1) := div_pos hv hsm
  have hbase : (v / (s - 1)) / (v / (s - 1) + v) = 1 / s := by
    field_simp
    ring
  have hinv : 1 / (v / (s - 1)) = (s - 1) / v := by
    rw [one_div_div]
  have h := fraction_rounding_bounds hx hv (Nat.le_ceil _) (le_of_lt (Nat.ceil_lt_add_one hx.le))
  simpa only [hbase, hinv] using h

/-- The first rounded parameter has reciprocal at most its ideal reciprocal. -/
theorem fraction_natCeil_reciprocal_le {s v : ℝ} (hs : 1 < s) (hv : 0 < v) :
    let a : ℝ := ⌈v / (s - 1)⌉₊
    (a / (a + v))⁻¹ ≤ s := by
  dsimp
  have h := (fraction_natCeil_inverse_bounds hs hv).1
  have hspos : 0 < s := zero_lt_one.trans hs
  have hpos : 0 < (⌈v / (s - 1)⌉₊ : ℝ) / ((⌈v / (s - 1)⌉₊ : ℝ) + v) :=
    lt_of_lt_of_le (one_div_pos.mpr hspos) h
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hpos).mpr
  nlinarith [(div_le_iff₀ hspos).mp h]

/-- The second rank parameter is rounded from a prescribed target fraction `p`. -/
theorem fraction_natCeil_target_bounds {p v : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hv : 0 < v) :
    let b : ℝ := ⌈v * p / (1 - p)⌉₊
    p ≤ b / (b + v) ∧
      b / (b + v) ≤ p * Real.exp ((1 - p) / (v * p)) := by
  have hpm : 0 < 1 - p := sub_pos.mpr hp1
  have hx : 0 < v * p / (1 - p) := div_pos (mul_pos hv hp) hpm
  have hbase : (v * p / (1 - p)) / (v * p / (1 - p) + v) = p := by
    field_simp
    ring
  have hinv : 1 / (v * p / (1 - p)) = (1 - p) / (v * p) := by
    rw [one_div_div]
  have h := fraction_rounding_bounds hx hv (Nat.le_ceil _) (le_of_lt (Nat.ceil_lt_add_one hx.le))
  simpa only [hbase, hinv] using h

end Problem335

end

end OAI
