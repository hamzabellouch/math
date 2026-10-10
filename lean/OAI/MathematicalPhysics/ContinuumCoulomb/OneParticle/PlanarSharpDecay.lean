import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarModeDecay

namespace OAI

/-! A sharp exponential rate for the actual planar resolvent mode. Gaussian
exponential tilting gives a polynomial prefactor and decay `exp (-|r|)`, as
needed to bracket the contact hoppings at lengths `(1±ε)D`. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarHeatKernel_tilt {t : ℝ} (ht : 0 < t) (e b : PlanarPosition) :
    planarHeatKernel t b * Real.exp (inner ℝ e b) =
      Real.exp (t * ‖e‖ ^ 2) * planarHeatKernel t (b - (2 * t) • e) := by
  have he : -‖b‖ ^ 2 / (4 * t) + inner ℝ e b =
      t * ‖e‖ ^ 2 + -‖b - (2 * t) • e‖ ^ 2 / (4 * t) := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, real_inner_comm b e]
    field_simp
    ring
  unfold planarHeatKernel
  rw [mul_assoc, ← Real.exp_add, he, Real.exp_add]
  ring

theorem planarForcing_exponential_bound (e s : PlanarPosition) :
    planarForcing s ≤ Real.exp (‖e‖ - inner ℝ e s) := by
  by_cases hf : planarForcing s = 0
  · rw [hf]
    exact (Real.exp_pos _).le
  have hs : ‖s‖ ≤ 1 := le_of_lt (lt_of_not_ge
    (fun h => hf (planarForcing_zero_of_norm_ge_one h)))
  have hi : inner ℝ e s ≤ ‖e‖ := (real_inner_le_norm e s).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (norm_nonneg e))
  exact (planarForcing_le_one s).trans (Real.one_le_exp (by linarith))

theorem planarHeatForcing_tilt_bound {t : ℝ} (ht : 0 < t) (e r b : PlanarPosition) :
    planarHeatKernel t b * planarForcing (r - b) ≤
      (Real.exp (‖e‖ - inner ℝ e r) * Real.exp (t * ‖e‖ ^ 2)) *
        planarHeatKernel t (b - (2 * t) • e) := by
  calc
    _ ≤ planarHeatKernel t b * Real.exp (‖e‖ - inner ℝ e (r - b)) :=
      mul_le_mul_of_nonneg_left (planarForcing_exponential_bound e (r - b))
        (planarHeatKernel_positive ht b).le
    _ = Real.exp (‖e‖ - inner ℝ e r) *
        (planarHeatKernel t b * Real.exp (inner ℝ e b)) := by
      rw [inner_sub_right, show ‖e‖ - (inner ℝ e r - inner ℝ e b) =
        (‖e‖ - inner ℝ e r) + inner ℝ e b by ring, Real.exp_add]
      ring
    _ = _ := by rw [planarHeatKernel_tilt ht]; ring

theorem planarHeatAverage_tilt_bound {t : ℝ} (ht : 0 < t) (e r : PlanarPosition) :
    planarHeatAverage t r ≤
      Real.exp (‖e‖ - inner ℝ e r) * Real.exp (t * ‖e‖ ^ 2) := by
  have hi := ((planarHeatKernel_integrable ht).comp_sub_right ((2 * t) • e)).const_mul
    (Real.exp (‖e‖ - inner ℝ e r) * Real.exp (t * ‖e‖ ^ 2))
  have h := integral_mono (planarHeatAverage_integrand_integrable ht r) hi
    (planarHeatForcing_tilt_bound ht e r)
  simpa only [planarHeatAverage, integral_const_mul, integral_sub_right_eq_self,
    planarHeatKernel_integral ht, mul_one] using h

theorem planarResolventMode_tilt_bound (e r : PlanarPosition) (he : ‖e‖ < 1) :
    planarResolventMode r ≤ Real.exp (‖e‖ - inner ℝ e r) / (1 - ‖e‖ ^ 2) := by
  have hc : 0 < 1 - ‖e‖ ^ 2 := by nlinarith [norm_nonneg e]
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-(1 - ‖e‖ ^ 2) * t)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hc
  rw [planarResolventMode_heat_representation]
  have h := integral_mono_ae (planarResolventMode_heat_integrable r)
    (hi.const_mul (Real.exp (‖e‖ - inner ℝ e r))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      calc
        _ ≤ Real.exp (-t) * (Real.exp (‖e‖ - inner ℝ e r) * Real.exp (t * ‖e‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (planarHeatAverage_tilt_bound ht e r) (Real.exp_pos _).le
        _ = Real.exp (‖e‖ - inner ℝ e r) * Real.exp (-(1 - ‖e‖ ^ 2) * t) := by
          rw [show -(1 - ‖e‖ ^ 2) * t = -t + t * ‖e‖ ^ 2 by ring, Real.exp_add]
          ring)
  have heval : (∫ t : ℝ in Set.Ioi 0, Real.exp (-(1 - ‖e‖ ^ 2) * t)) =
      (1 - ‖e‖ ^ 2)⁻¹ := by
    rw [integral_exp_mul_Ioi (by linarith : -(1 - ‖e‖ ^ 2) < 0)]
    simp
    rw [show ‖e‖ ^ 2 - 1 = -(1 - ‖e‖ ^ 2) by ring, div_neg]
    simp only [neg_div, neg_neg, one_div]
  simpa only [integral_const_mul, heval, div_eq_mul_inv] using h

theorem planar_tilt_envelope_sharp_upper (r : PlanarPosition) (v : ℝ)
    (hv : ∀ e : PlanarPosition, ‖e‖ < 1 →
      v ≤ Real.exp (‖e‖ - inner ℝ e r) / (1 - ‖e‖ ^ 2)) (hr : 1 ≤ ‖r‖) :
    v ≤ ‖r‖ * Real.exp (2 - ‖r‖) := by
  have hR : 0 < ‖r‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hr
  let c : ℝ := (‖r‖ - 1) / ‖r‖ ^ 2
  let e : PlanarPosition := c • r
  have hc : 0 ≤ c := div_nonneg (by linarith) (sq_nonneg _)
  have hn : ‖e‖ = (‖r‖ - 1) / ‖r‖ := by
    rw [show e = c • r from rfl, norm_smul, Real.norm_of_nonneg hc]
    dsimp [c]
    field_simp
  have hi : inner ℝ e r = ‖r‖ - 1 := by
    rw [show e = c • r from rfl, real_inner_smul_left, real_inner_self_eq_norm_sq]
    dsimp [c]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hR.ne')
  have he : ‖e‖ < 1 := by
    rw [hn]
    exact (div_lt_one hR).2 (by linarith)
  have hdpos : 0 < 1 - ‖e‖ ^ 2 := by nlinarith [norm_nonneg e]
  have hden : 1 / ‖r‖ ≤ 1 - ‖e‖ ^ 2 := by
    have hsq : ‖e‖ ^ 2 ≤ ‖e‖ := by nlinarith [norm_nonneg e]
    have hid : 1 - ‖e‖ = 1 / ‖r‖ := by rw [hn]; field_simp; ring
    linarith
  have hinv : (1 - ‖e‖ ^ 2)⁻¹ ≤ ‖r‖ := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (one_div_pos.mpr hR) hden
    simpa only [one_div, inv_inv] using h
  have hexp : Real.exp (‖e‖ - inner ℝ e r) ≤ Real.exp (2 - ‖r‖) := by
    apply Real.exp_le_exp.mpr
    rw [hi]
    linarith
  calc
    _ ≤ Real.exp (‖e‖ - inner ℝ e r) / (1 - ‖e‖ ^ 2) :=
      hv e he
    _ ≤ Real.exp (2 - ‖r‖) * ‖r‖ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul hexp hinv (inv_nonneg.mpr hdpos.le) (Real.exp_pos _).le
    _ = _ := mul_comm _ _

theorem planarResolventMode_sharp_upper {r : PlanarPosition} (hr : 1 ≤ ‖r‖) :
    planarResolventMode r ≤ ‖r‖ * Real.exp (2 - ‖r‖) :=
  planar_tilt_envelope_sharp_upper r (planarResolventMode r)
    (fun e he => planarResolventMode_tilt_bound e r he) hr

end ContinuumCoulomb

end

end OAI
