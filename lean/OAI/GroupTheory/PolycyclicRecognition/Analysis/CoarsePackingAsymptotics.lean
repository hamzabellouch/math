import OAI.GroupTheory.PolycyclicRecognition.Analysis.VolumeExponents
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PolynomialPackingAlgebra
import Mathlib.Tactic

namespace OAI

/-! # Polynomial losses and logarithmic errors in path packing -/

namespace PolycyclicRecognition

open Filter
open scoped Topology ENNReal

/-- Every fixed affine function of the logarithmic path error is sublinear. -/
theorem eventually_logarithmic_error_le (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, a * (1 + Real.log (2 + r)) + b ≤ ε * r := by
  have hadd : Tendsto (fun r : ℝ => 2 + r) atTop atTop := by
    apply tendsto_atTop.mpr
    intro x
    filter_upwards [eventually_ge_atTop (x - 2)] with r hr
    linarith
  have hlog : Tendsto (fun r : ℝ => Real.log (2 + r) / r) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp hadd
    convert h using 1
    funext r
    simp only [Function.comp_apply, pow_one, one_mul]
    congr 1
    ring
  have hconst : Tendsto (fun r : ℝ => (a + b) / r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlim : Tendsto (fun r : ℝ => (a * (1 + Real.log (2 + r)) + b) / r)
      atTop (𝓝 0) := by
    have h := (hlog.const_mul a).add hconst
    convert h using 1
    · funext r; ring
    · simp
  filter_upwards [(tendsto_order.mp hlim).2 ε hε, eventually_gt_atTop (0 : ℝ)] with r hr hr0
  exact ((div_lt_iff₀ hr0).mp hr).le

/-- The path-word subdivision prefactor is bounded by one fixed quadratic. -/
theorem coarse_path_word_prefactor_le {A r : ℝ} (hA : 0 ≤ A) (hr : 1 ≤ r) :
    3 + (A * r + 1) * (A * (1 + Real.log (2 + r)) + 2) ≤
      (3 + (A + 1) * (3 * A + 2)) * (1 + r) ^ 2 := by
  have hr0 : 0 ≤ r := by linarith
  have hlog : 1 + Real.log (2 + r) ≤ 3 * r := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 2 + r)
    linarith
  have h1 : A * r + 1 ≤ (A + 1) * (1 + r) := by nlinarith
  have h2 : A * (1 + Real.log (2 + r)) + 2 ≤ (3 * A + 2) * (1 + r) := by
    have h := mul_le_mul_of_nonneg_left hlog hA
    nlinarith
  have hlog0 : 0 ≤ 1 + Real.log (2 + r) := by
    have hh := Real.log_nonneg (by linarith : 1 ≤ 2 + r)
    linarith
  have hm := mul_le_mul h1 h2 (by positivity : 0 ≤ A * (1 + Real.log (2 + r)) + 2)
    (by positivity : 0 ≤ (A + 1) * (1 + r))
  calc
    _ ≤ 3 + (A + 1) * (1 + r) * ((3 * A + 2) * (1 + r)) := add_le_add le_rfl hm
    _ ≤ _ := by nlinarith [sq_nonneg r]

/-- Positive exponential lower mass and a polynomial exponential upper
cardinality force the comparison of their exponents. -/
theorem exponent_le_of_separated_card_bounds {p q a D : ℝ}
    (ha : 0 < a) (hD : 0 < D) {Q : ℝ≥0∞} (hQ : Q < ⊤) (k : ℕ)
    (h : ∀ᶠ r : ℝ in atTop, ∃ N : ℕ,
      ENNReal.ofReal a * ENNReal.ofReal (Real.exp (r * p)) ≤ (N : ℝ≥0∞) * Q ∧
      (N : ℝ) ≤ D * (1 + r) ^ k * Real.exp (r * q)) : p ≤ q := by
  apply exponent_le_of_polynomial_exp_bound ha (show 0 < D * Q.toReal + 1 by positivity) k
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with r hr hr0
  obtain ⟨N, hlow, hupp⟩ := hr
  have hfinite : (N : ℝ≥0∞) * Q ≠ ⊤ := ENNReal.mul_ne_top (by simp) hQ.ne
  have hreal := ENNReal.toReal_mono hfinite hlow
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_natCast] at hreal
  calc
    a * Real.exp (r * p) ≤ (N : ℝ) * Q.toReal := hreal
    _ ≤ (D * (1 + r) ^ k * Real.exp (r * q)) * Q.toReal :=
      mul_le_mul_of_nonneg_right hupp ENNReal.toReal_nonneg
    _ = (D * Q.toReal) * (1 + r) ^ k * Real.exp (r * q) := by ring
    _ ≤ _ := by gcongr; linarith

/-- The same comparison with a positive finite lower mass coefficient. -/
theorem exponent_le_of_separated_mass_bounds {p q D : ℝ}
    {a Q : ℝ≥0∞} (ha : 0 < a) (hafin : a < ⊤) (hD : 0 < D) (hQ : Q < ⊤) (k : ℕ)
    (h : ∀ᶠ r : ℝ in atTop, ∃ N : ℕ,
      a * ENNReal.ofReal (Real.exp (r * p)) ≤ (N : ℝ≥0∞) * Q ∧
      (N : ℝ) ≤ D * (1 + r) ^ k * Real.exp (r * q)) : p ≤ q := by
  apply exponent_le_of_separated_card_bounds
    (ENNReal.toReal_pos ha.ne' hafin.ne) hD hQ k
  simpa only [ENNReal.ofReal_toReal hafin.ne] using h

end PolycyclicRecognition

end OAI
