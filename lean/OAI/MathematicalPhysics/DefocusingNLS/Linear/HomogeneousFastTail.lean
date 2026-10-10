import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! # The fast radial exponent cannot satisfy the top-derivative condition

Only the elementary power comparison is used here.  Applying it to an
actual slow/fast decomposition still requires the normalized asymptotic
formula for that solution; no decomposition is postulated as an input.
-/

open MeasureTheory Set Filter Topology

namespace DefocusingNLS

/-- Any nonzero tail bounded below by r^beta with beta >= -6 fails the
12-dimensional radial square-integrability condition. -/
theorem radial_weighted_not_integrable_of_power_lower
    (f : ℝ → ℂ) (R beta c : ℝ) (hc : 0 < c) (hb : -6 ≤ beta)
    (hlower : ∀ᶠ r in atTop, c * r ^ beta ≤ ‖f r‖) :
    ¬ IntegrableOn (fun r => r ^ (11 : ℕ) * ‖f r‖ ^ 2) (Ioi R) := by
  intro hf
  obtain ⟨T, hT⟩ := eventually_atTop.1 hlower
  let A := max (max R T) 1
  have hAR : R ≤ A := (le_max_left R T).trans (le_max_left _ _)
  have hAT : T ≤ A := (le_max_right R T).trans (le_max_left _ _)
  have hA : 0 < A := zero_lt_one.trans_le (le_max_right _ _)
  have hsmall : IntegrableOn (fun r => c ^ 2 * r ^ (11 + 2 * beta)) (Ioi A) := by
    apply (hf.mono_set (Ioi_subset_Ioi hAR)).mono'
    · exact (measurable_const.mul (measurable_id.pow_const _)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hA.trans hr
    have hrT : T ≤ r := hAT.trans hr.le
    have hsq := pow_le_pow_left₀ (mul_nonneg hc.le (Real.rpow_nonneg hr0.le _))
      (hT r hrT) 2
    have hpow : c ^ 2 * r ^ (11 + 2 * beta) = r ^ (11 : ℕ) * (c * r ^ beta) ^ 2 := by
      have hbeta : r ^ (2 * beta) = (r ^ beta) ^ (2 : ℕ) := by
        rw [mul_comm (2 : ℝ) beta, Real.rpow_mul hr0.le]
        simp only [Real.rpow_ofNat]
      rw [Real.rpow_add hr0, hbeta]
      simp only [Real.rpow_ofNat, mul_pow]
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hpow]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hn : c ^ 2 ≠ 0 := pow_ne_zero _ hc.ne'
  have hpower : IntegrableOn (fun r : ℝ => r ^ (11 + 2 * beta)) (Ioi A) := by
    have h := hsmall.const_mul ((c ^ 2)⁻¹)
    simpa only [IntegrableOn, ← mul_assoc, inv_mul_cancel₀ hn, one_mul] using h
  exact (not_integrableOn_Ioi_rpow_of_neg_one_le (a := A) (by linarith)) hpower

/-- A nonzero normalized limiting amplitude is incompatible with the radial
L² condition whenever its power is at least the threshold -6. -/
theorem radial_weighted_limit_eq_zero
    (f : ℝ → ℂ) (R beta c : ℝ) (hb : -6 ≤ beta) (hc : 0 ≤ c)
    (hf : IntegrableOn (fun r => r ^ (11 : ℕ) * ‖f r‖ ^ 2) (Ioi R))
    (hlim : Tendsto (fun r => ‖f r‖ / r ^ beta) atTop (𝓝 c)) : c = 0 := by
  by_contra hn
  have hc0 : 0 < c := lt_of_le_of_ne hc (Ne.symm hn)
  have hpos := hlim.eventually (lt_mem_nhds (show c / 2 < c by linarith))
  have hlower : ∀ᶠ r in atTop, (c / 2) * r ^ beta ≤ ‖f r‖ := by
    filter_upwards [hpos, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    exact ((lt_div_iff₀ (Real.rpow_pos_of_pos hr0 _)).mp hr).le
  exact radial_weighted_not_integrable_of_power_lower f R beta (c / 2)
    (by positivity) hb hlower hf

/-- The exponent in the manuscript's fast kth derivative is above the
radial L² threshold throughout the counting half-plane. -/
theorem fast_derivative_exponent (a reLam : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (hLam : -(1 / 32 : ℝ) ≤ reLam) (hk : 7 ≤ k) :
    -6 < (k : ℝ) - 12 + 2 * (a + reLam) := by
  have hk' : (7 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

end DefocusingNLS

end OAI
