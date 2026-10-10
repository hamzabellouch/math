import OAI.NumberTheory.TotientAsymptotic.Phase
import OAI.NumberTheory.TotientAsymptotic.CollisionCoordinateEndpoint
import OAI.NumberTheory.TotientAsymptotic.StrictContractionCost

namespace OAI

/-!
The geometric lower bound on a remaining prime coordinate bounds the
length of that suffix in terms of its own comparison scale.  This is a
local statement; it does not transfer normality from a larger scale.
-/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

def pptLocalDimensionConstant (c : ℝ) : ℝ := (2+|Real.log c|)/lam

lemma ppt_local_dimension_constant_pos (c : ℝ) :
    0 < pptLocalDimensionConstant c := by
  unfold pptLocalDimensionConstant
  exact div_pos (by positivity) lam_pos

/-- A geometric endpoint lower bound gives a logarithmic local length
bound, with a constant depending only on the fixed candidate family. -/
lemma ppt_local_dimension_bound {c t U : ℝ} {H : ℕ}
    (hc : 0 < c) (ht : Real.exp 1 ≤ t)
    (hlower : c*(rho^H)⁻¹ ≤ U) (hupper : U ≤ t+1) :
    (H : ℝ) ≤ pptLocalDimensionConstant c*Real.log t := by
  have ht1 : 1 ≤ t := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hlogt : 1 ≤ Real.log t := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) ht
  have hr : 0 < rho^H := pow_pos rho_pos H
  have hlog := Real.log_le_log (mul_pos hc (inv_pos.mpr hr)) (hlower.trans hupper)
  rw [Real.log_mul hc.ne' (inv_pos.mpr hr).ne', Real.log_inv, Real.log_pow] at hlog
  have hlam : Real.log rho = -lam := by
    simp only [lam, one_div, Real.log_inv, neg_neg]
  rw [hlam] at hlog
  have hlogupper : Real.log (t+1) ≤ Real.log t+1 := by
    have hh := Real.log_le_log (by positivity : 0 < t+1)
      (show t+1 ≤ 2*t by linarith only [ht1])
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht0.ne'] at hh
    have htwo : Real.log (2 : ℝ) ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hh ⊢
      exact hh
    linarith only [hh, htwo]
  have habs := mul_le_mul_of_nonneg_left hlogt (abs_nonneg (Real.log c))
  have hmain : (H : ℝ)*lam ≤ (2+|Real.log c|)*Real.log t := by
    nlinarith only [hlog, hlogupper, hlogt, neg_le_abs (Real.log c), habs]
  calc
    (H : ℝ) ≤ ((2+|Real.log c|)*Real.log t)/lam := (le_div_iff₀ lam_pos).mpr hmain
    _ = pptLocalDimensionConstant c*Real.log t := by
      unfold pptLocalDimensionConstant
      ring

/-- The endpoint form used for a largest prime in a local comparison
block.  The harmless `+1` comes from replacing `p-1` by `p`. -/
theorem ppt_local_prime_dimension {c : ℝ} (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop, ∀ (H p : ℕ),
      3 ≤ p → c*(rho^H)⁻¹ ≤ B p → (p-1 : ℕ) ≤ z →
      (H : ℝ) ≤ pptLocalDimensionConstant c*Real.log (B z) := by
  filter_upwards [B_tendsto.eventually (eventually_ge_atTop (Real.exp 1)),
    eventually_ge_atTop (Real.exp 1)] with z hB hz
  intro H p hp hlower hsize
  exact ppt_local_dimension_bound hc hB hlower (prime_coordinate_endpoint_bound hp hz hsize)

/-- Allow the distinguished head prime in addition to the geometric
tail length.  Every surviving sublist inherits the same local bound. -/
theorem ppt_local_prime_sublist_dimension {c : ℝ} (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop, ∀ (H p k : ℕ),
      3 ≤ p → c*(rho^H)⁻¹ ≤ B p → (p-1 : ℕ) ≤ z → k ≤ H+1 →
      (k : ℝ) ≤ (pptLocalDimensionConstant c+1)*Real.log (B z) := by
  filter_upwards [ppt_local_prime_dimension hc,
    B_tendsto.eventually (eventually_ge_atTop (Real.exp 1))] with z hz hB
  intro H p k hp hlower hsize hk
  have hdim := hz H p hp hlower hsize
  have hk' : (k : ℝ) ≤ (H : ℝ)+1 := by exact_mod_cast hk
  have hlog : 1 ≤ Real.log (B z) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hB
  nlinarith only [hdim, hk', hlog]

/-- A fixed inverse-cube row margin becomes the inverse-log-cube saving
needed by the analytic comparison estimate. -/
lemma ppt_local_row_saving {c t : ℝ} {H r : ℕ}
    (_ht : 0 < Real.log t) (hrH : r+1 ≤ H)
    (hdim : (H : ℝ) ≤ pptLocalDimensionConstant c*Real.log t) :
    1/(80*(pptLocalDimensionConstant c)^3)/(Real.log t)^3 ≤
      (1/(5*(r+1 : ℝ)^3))/16 := by
  have hr : (r+1 : ℝ) ≤ pptLocalDimensionConstant c*Real.log t := by
    have hh : (r+1 : ℝ) ≤ H := by exact_mod_cast hrH
    exact hh.trans hdim
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r+1) hr 3
  have hh : 1/(80*(pptLocalDimensionConstant c*Real.log t)^3) ≤
      1/(80*(r+1 : ℝ)^3) :=
    one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left hp (by norm_num))
  calc
    _ = 1/(80*(pptLocalDimensionConstant c*Real.log t)^3) := by
      rw [div_div, mul_pow]
      ring
    _ ≤ 1/(80*(r+1 : ℝ)^3) := hh
    _ = _ := by rw [div_div]; ring

/-- A bounded change of head coordinate consumes less than the allowed
quarter-row margin, uniformly for every logarithmic local dimension. -/
theorem ppt_local_head_error_absorbed {A E : ℝ} (_hA : 0 < A) (hE : 0 ≤ E) :
    ∀ᶠ t : ℝ in atTop, ∀ H r : ℕ,
      (H : ℝ) ≤ A*Real.log t → r+1 ≤ H →
      4*E ≤ (rowContractionError r/2)*t := by
  have hlim : Tendsto (fun t : ℝ => (Real.log t)^3/t) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have hscaled : Tendsto (fun t : ℝ => 40*E*A^3*((Real.log t)^3/t))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul (40*E*A^3)
  filter_upwards [hscaled.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (1 : ℝ)] with t hsmall ht
  intro H r hdim hrH
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hHR : (r+1 : ℝ) ≤ H := by exact_mod_cast hrH
  have hpH := pow_le_pow_left₀ (Nat.cast_nonneg H) hdim 3
  have hpr := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r+1) hHR 3
  have hbound : 40*E*(r+1 : ℝ)^3 ≤ t := by
    calc
      _ ≤ 40*E*(H : ℝ)^3 :=
        mul_le_mul_of_nonneg_left hpr (by positivity)
      _ ≤ 40*E*(A*Real.log t)^3 :=
        mul_le_mul_of_nonneg_left hpH (by positivity)
      _ = (40*E*A^3*((Real.log t)^3/t))*t := by
        rw [mul_assoc (40*E*A^3), div_mul_cancel₀ _ ht0.ne']
        ring
      _ ≤ t := by
        have hh := mul_le_mul_of_nonneg_right hsmall.le ht0.le
        simpa only [one_mul] using hh
  have hdiv : 4*E ≤ t/(10*(r+1 : ℝ)^3) := by
    apply (le_div_iff₀ (by positivity : 0 < 10*(r+1 : ℝ)^3)).mpr
    nlinarith only [hbound]
  calc
    4*E ≤ t/(10*(r+1 : ℝ)^3) := hdiv
    _ = (rowContractionError r/2)*t := by
      unfold rowContractionError
      rw [div_div]
      ring

end TotientAsymptotic

end

end OAI
