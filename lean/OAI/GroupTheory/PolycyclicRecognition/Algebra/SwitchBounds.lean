import OAI.GroupTheory.PolycyclicRecognition.Algebra.LogDistortion

namespace OAI

/-! # Short switches at supporting heights

Logarithmic distortion turns a polynomial times a subexponential coordinate
bound into a sublinear metric displacement. The estimate is uniform in the
points before and after a switch.
-/

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- The polynomial correction contributes only a logarithmic error. -/
theorem log_polynomial_exp_le {C r δ : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hδ : 0 ≤ δ) (b : ℕ) :
    Real.log (2 + C * (1 + r) ^ b * Real.exp (r * δ)) ≤
      Real.log (2 + C) + (b : ℝ) * Real.log (1 + r) + r * δ := by
  have hp : 1 ≤ (1 + r) ^ b := one_le_pow₀ (by linarith)
  have he : 1 ≤ Real.exp (r * δ) := Real.one_le_exp (mul_nonneg hr hδ)
  have hpe : 1 ≤ (1 + r) ^ b * Real.exp (r * δ) := one_le_mul_of_one_le_of_one_le hp he
  have hbound : 2 + C * (1 + r) ^ b * Real.exp (r * δ) ≤
      (2 + C) * (1 + r) ^ b * Real.exp (r * δ) := by nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < 2 + C * (1 + r) ^ b * Real.exp (r * δ)) hbound
  rw [Real.log_mul (mul_ne_zero (by positivity) (by positivity)) (Real.exp_ne_zero _),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp] at hlog
  exact hlog

/-- Uniform coordinate bounds give the quantitative switch-length bound. -/
theorem switch_length_le
    {G V : Type*} [PseudoMetricSpace G] [One G] [NormedAddCommGroup V]
    (Exp : V → G) {D C r δ : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hr : 0 ≤ r) (hδ : 0 ≤ δ) (b : ℕ)
    (hdist : ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖))
    {v : V} (hv : ‖v‖ ≤ C * (1 + r) ^ b * Real.exp (r * δ)) :
    dist 1 (Exp v) ≤
      D * (Real.log (2 + C) + (b : ℝ) * Real.log (1 + r) + r * δ) := by
  apply (hdist v).trans
  apply mul_le_mul_of_nonneg_left _ hD
  exact (Real.log_le_log (by positivity) (by linarith)).trans (log_polynomial_exp_le hC hr hδ b)

/-- Coordinate size polynomial times `exp(o(r))` gives a switch of length
`o(r)`. This is an individual-displacement estimate, uniform over every
family sharing the displayed coordinate bound. -/
theorem switch_length_sublinear
    {G V : Type*} [PseudoMetricSpace G] [One G] [NormedAddCommGroup V]
    (Exp : V → G) {D C : ℝ} (hD : 0 ≤ D) (hC : 0 ≤ C) (b : ℕ)
    (hdist : ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖))
    (v : ℝ → V) (δ : ℝ → ℝ) (hδ : ∀ᶠ r in atTop, 0 ≤ δ r)
    (hδlim : Tendsto δ atTop (𝓝 0))
    (hv : ∀ᶠ r in atTop, ‖v r‖ ≤ C * (1 + r) ^ b * Real.exp (r * δ r)) :
    Tendsto (fun r => dist 1 (Exp (v r)) / r) atTop (𝓝 0) := by
  have hlog : Tendsto (fun r : ℝ => Real.log (1 + r) / r) atTop (𝓝 0) := by
    have hs : Tendsto (fun r : ℝ => 1 + r) atTop atTop := by
      apply tendsto_atTop.mpr
      intro z
      filter_upwards [eventually_ge_atTop (z - 1)] with r hr
      linarith
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hs
    convert hh using 1
    funext r
    congr 1 <;> ring
  have hc : Tendsto (fun r : ℝ => Real.log (2 + C) / r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hup : Tendsto (fun r => D * (Real.log (2 + C) / r +
      (b : ℝ) * (Real.log (1 + r) / r) + δ r)) atTop (𝓝 0) := by
    simpa using ((hc.add (hlog.const_mul (b : ℝ))).add hδlim).const_mul D
  apply squeeze_zero' _ _ hup
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact div_nonneg dist_nonneg hr.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ), hδ, hv] with r hr hδr hvr
    have hh := div_le_div_of_nonneg_right
      (switch_length_le Exp hD hC hr.le hδr b hdist hvr) hr.le
    convert hh using 1
    field_simp

end PolycyclicRecognition

end OAI
