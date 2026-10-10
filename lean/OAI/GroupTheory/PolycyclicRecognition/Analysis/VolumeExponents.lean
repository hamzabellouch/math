import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-!
# Extracting exponential volume rates

A polynomial loss in the cardinality of a separated set does not change
its exponential rate. This is the limiting step after applying the path
packing estimate to the good endpoint set selected by stationary averaging.
-/

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- An eventual exponential lower bound cannot exceed an exponential upper
bound with a fixed polynomial prefactor. -/
theorem exponent_le_of_polynomial_exp_bound
    {p q c C : ℝ} (hc : 0 < c) (hC : 0 < C) (k : ℕ)
    (hbound : ∀ᶠ r : ℝ in atTop,
      c * Real.exp (r * p) ≤ C * (1 + r) ^ k * Real.exp (r * q)) :
    p ≤ q := by
  have hlog : Tendsto (fun r : ℝ => Real.log (1 + r) / r) atTop (𝓝 0) := by
    have ha : Tendsto (fun r : ℝ => 1 + r) atTop atTop := by
      apply tendsto_atTop.mpr
      intro b
      filter_upwards [eventually_ge_atTop (b - 1)] with r hr
      linarith
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      ha
    convert h using 1
    funext r
    congr 1 <;> ring
  have hconst : Tendsto (fun r : ℝ => (Real.log C - Real.log c) / r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlim : Tendsto
      (fun r : ℝ => q + (Real.log C - Real.log c) / r + (k : ℝ) * (Real.log (1 + r) / r))
      atTop (𝓝 q) := by
    simpa using (tendsto_const_nhds.add hconst).add (tendsto_const_nhds.mul hlog)
  apply ge_of_tendsto hlim
  filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with r hr hr0
  have h1 : 0 < 1 + r := by linarith
  have h := Real.log_le_log (mul_pos hc (Real.exp_pos _)) hr
  rw [Real.log_mul hc.ne' (Real.exp_ne_zero _),
    Real.log_mul (mul_ne_zero hC.ne' (pow_ne_zero _ h1.ne')) (Real.exp_ne_zero _),
    Real.log_mul hC.ne' (pow_ne_zero _ h1.ne'), Real.log_pow,
    Real.log_exp, Real.log_exp] at h
  calc
    p ≤ (q * r + (Real.log C - Real.log c) + (k : ℝ) * Real.log (1 + r)) / r :=
      (le_div_iff₀ hr0).mpr (by nlinarith [h])
    _ = _ := by field_simp

end PolycyclicRecognition

end OAI
