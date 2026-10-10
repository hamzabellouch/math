import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

/-- The Gamma law is concentrated on strictly positive real weights. -/
theorem gamma_ae_pos (shape rate : ℝ) :
    ∀ᵐ x : ℝ ∂gammaMeasure shape rate, 0 < x := by
  change ∀ᵐ x : ℝ ∂volume.withDensity (gammaPDF shape rate), 0 < x
  rw [ae_withDensity_iff (by unfold gammaPDF; fun_prop)]
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  intro hd
  by_contra h
  exact hd (gammaPDF_of_neg (lt_of_le_of_ne (le_of_not_gt h) hx))

/-- Multiplication by `x` shifts the Gamma shape by one. Both sides vanish at the origin. -/
lemma gamma_first_weighted_density {shape rate : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (x : ℝ) :
    gammaPDF shape rate x * ENNReal.ofReal x =
      ENNReal.ofReal (shape / rate) * gammaPDF (shape + 1) rate x := by
  by_cases hx : 0 < x
  · rw [gammaPDF_of_nonneg hx.le, gammaPDF_of_nonneg hx.le,
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (div_pos hshape hrate).le]
    congr 1
    have hxp : x ^ (shape - 1) * x = x ^ shape := by
      calc
        x ^ (shape - 1) * x = x ^ (shape - 1) * x ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = x ^ shape := by
          rw [← Real.rpow_add hx]
          congr 1
          ring
    rw [Real.Gamma_add_one hshape.ne', Real.rpow_add hrate, Real.rpow_one]
    simp only [add_sub_cancel_right]
    calc
      rate ^ shape / Gamma shape * x ^ (shape - 1) * exp (-(rate * x)) * x =
          rate ^ shape / Gamma shape * (x ^ (shape - 1) * x) *
            exp (-(rate * x)) := by ring
      _ = rate ^ shape / Gamma shape * x ^ shape * exp (-(rate * x)) := by rw [hxp]
      _ = shape / rate *
          (rate ^ shape * rate / (shape * Gamma shape) * x ^ shape *
            exp (-(rate * x))) := by
        field_simp [hrate.ne', hshape.ne', (Real.Gamma_pos_of_pos hshape).ne']
  · rcases lt_or_eq_of_le (le_of_not_gt hx) with hn | rfl
    · simp [gammaPDF_of_neg hn, ENNReal.ofReal_eq_zero.mpr hn.le]
    · simp [gammaPDF, gammaPDFReal, Real.zero_rpow hshape.ne']

/-- The nonnegative first moment from the normalized density with shifted shape. -/
theorem gamma_lintegral_id {shape rate : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) :
    (∫⁻ x : ℝ, ENNReal.ofReal x ∂gammaMeasure shape rate) =
      ENNReal.ofReal (shape / rate) := by
  change (∫⁻ x : ℝ, ENNReal.ofReal x
    ∂volume.withDensity (gammaPDF shape rate)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (by unfold gammaPDF; fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply, gamma_first_weighted_density hshape hrate]
  rw [lintegral_const_mul _ (by unfold gammaPDF; fun_prop),
    lintegral_gammaPDF_eq_one (by linarith : 0 < shape + 1) hrate, mul_one]

/-- The Gamma law has an integrable identity function for positive shape and rate. -/
theorem gamma_integrable_id {shape rate : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) :
    Integrable (fun x : ℝ => x) (gammaMeasure shape rate) := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    ((gamma_ae_pos shape rate).mono fun _ hx => hx.le)).mp
  rw [gamma_lintegral_id hshape hrate]
  exact ENNReal.ofReal_ne_top

/-- The mean of the Gamma law with shape and rate parameters. -/
theorem gamma_integral_id {shape rate : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) :
    (∫ x : ℝ, x ∂gammaMeasure shape rate) = shape / rate := by
  rw [integral_eq_lintegral_of_nonneg_ae
    ((gamma_ae_pos shape rate).mono fun _ hx => hx.le) (by fun_prop),
    gamma_lintegral_id hshape hrate]
  exact ENNReal.toReal_ofReal (div_pos hshape hrate).le
end GammaFPP

end OAI
