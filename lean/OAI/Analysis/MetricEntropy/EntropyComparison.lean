import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Real scalar entropy comparisons

The encoding term is controlled by choosing the field size after all other
parameters. The final lemmas transfer bounds for the finite approximation list
to bounds for covering numbers. Their hypotheses are scalar inequalities, so
natural cardinalities can be inserted by casting.
-/

namespace MetricEntropyDuality

/-- A sufficiently large field size makes the encoding contribution arbitrarily
small. This formulation also records its nonnegativity. -/
theorem encoding_ratio_bounds {r C D p : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (hD : 0 < D)
    (hp : Real.exp (r * C / D) < p) (hp1 : 1 < p) :
    0 ≤ 2 * C / (D * Real.log p) ∧ 2 * C / (D * Real.log p) < 2 / r := by
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hden : 0 < D * Real.log p := mul_pos hD hlogp
  constructor
  · exact div_nonneg (by positivity) hden.le
  · have hlog := Real.log_lt_log (Real.exp_pos (r * C / D)) hp
    rw [Real.log_exp] at hlog
    have hcross := (div_lt_iff₀ hD).mp hlog
    apply (div_lt_div_iff₀ hden hr).mpr
    nlinarith only [hcross]

theorem encoding_ratio_lt {r C D p : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (hD : 0 < D)
    (hp : Real.exp (r * C / D) < p) (hp1 : 1 < p) :
    2 * C / (D * Real.log p) < 2 / r :=
  (encoding_ratio_bounds hr hC hD hp hp1).2

theorem encoding_ratio_le {r C D p : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (hD : 0 < D)
    (hp : Real.exp (r * C / D) < p) (hp1 : 1 < p) :
    2 * C / (D * Real.log p) ≤ 2 / r :=
  (encoding_ratio_lt hr hC hD hp hp1).le

/-- The rank and field-size choices each contribute less than one quarter of
the reciprocal proposed comparison constant. -/
theorem entropy_budget_lt {b C D H R p : ℝ}
    (hb : 1 ≤ b) (hC : 0 ≤ C) (hD : 0 < D) (hH : 0 ≤ H)
    (hR : 8 * b * H < R)
    (hp : Real.exp (8 * b * C / D) < p) (hp1 : 1 < p) :
    2 * H / R + 2 * C / (D * Real.log p) < 1 / (2 * b) := by
  have hb0 : 0 < b := by linarith only [hb]
  have hR0 : 0 < R := lt_of_le_of_lt (by positivity) hR
  have hfirst : 2 * H / R < 1 / (4 * b) := by
    apply (div_lt_div_iff₀ hR0 (by positivity)).mpr
    nlinarith only [hR]
  have hsecond : 2 * C / (D * Real.log p) < 2 / (8 * b) :=
    encoding_ratio_lt (by positivity) hC hD hp hp1
  calc
    2 * H / R + 2 * C / (D * Real.log p) <
        1 / (4 * b) + 2 / (8 * b) := add_lt_add hfirst hsecond
    _ = 1 / (2 * b) := by field_simp; ring

/-- The entropy ratio is nonnegative when both covering counts have the usual
positive lower bounds. -/
theorem entropy_ratio_nonneg {N dual : ℝ} (hN : 1 < N) (hdual : 1 ≤ dual) :
    0 ≤ Real.log dual / Real.log N :=
  div_nonneg (Real.log_nonneg hdual) (Real.log_pos hN).le

/-- Increasing the denominator and decreasing the nonnegative numerator
preserves the upper entropy-ratio bound. -/
theorem entropy_ratio_bounds {N m dual Q : ℝ}
    (hm : 1 < m) (hNm : m ≤ N) (hdual : 1 ≤ dual) (hdualQ : dual ≤ Q ^ 2) :
    0 ≤ Real.log dual / Real.log N ∧
      Real.log dual / Real.log N ≤ Real.log (Q ^ 2) / Real.log m := by
  have hN : 1 < N := hm.trans_le hNm
  have hlogm : 0 < Real.log m := Real.log_pos hm
  have hlogNm : Real.log m ≤ Real.log N :=
    Real.log_le_log (by linarith only [hm]) hNm
  have hlogdual : 0 ≤ Real.log dual := Real.log_nonneg hdual
  have hlogdualQ : Real.log dual ≤ Real.log (Q ^ 2) :=
    Real.log_le_log (by linarith only [hdual]) hdualQ
  refine ⟨entropy_ratio_nonneg hN hdual, ?_⟩
  calc
    Real.log dual / Real.log N ≤ Real.log dual / Real.log m :=
      div_le_div_of_nonneg_left hlogdual hlogm hlogNm
    _ ≤ Real.log (Q ^ 2) / Real.log m :=
      div_le_div_of_nonneg_right hlogdualQ hlogm.le

/-- The strict finite entropy-ratio estimate contradicts the proposed covering
comparison after inserting the geometric lower and upper bounds. -/
theorem entropy_strict_comparison {N m dual Q b : ℝ}
    (hm : 1 < m) (hNm : m ≤ N) (hdual : 1 ≤ dual) (hdualQ : dual ≤ Q ^ 2)
    (hb : 1 ≤ b)
    (hratio : Real.log (Q ^ 2) / Real.log m < 1 / (2 * b)) :
    b * Real.log dual < Real.log N := by
  have hb0 : 0 < b := by linarith only [hb]
  have hlogm : 0 < Real.log m := Real.log_pos hm
  have hlogNm : Real.log m ≤ Real.log N :=
    Real.log_le_log (by linarith only [hm]) hNm
  have hlogdual : 0 ≤ Real.log dual := Real.log_nonneg hdual
  have hlogdualQ : Real.log dual ≤ Real.log (Q ^ 2) :=
    Real.log_le_log (by linarith only [hdual]) hdualQ
  have hscaled := mul_le_mul_of_nonneg_left hlogdualQ hb0.le
  have hscaled0 : 0 ≤ b * Real.log dual := mul_nonneg hb0.le hlogdual
  have hcross := (div_lt_div_iff₀ hlogm (by positivity : 0 < 2 * b)).mp hratio
  nlinarith only [hscaled, hscaled0, hcross, hlogNm]

end MetricEntropyDuality

end OAI
