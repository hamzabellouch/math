import OAI.Geometry.RCD.Transport.PositiveExponentialTilt
import OAI.Geometry.RCD.Coordinates.NormalizedPositiveWeights

namespace OAI

/-! # Logarithmic derivatives of positive kernel rows

Two uniformly positive bounded rows, tilted by the same bounded exponent,
have logarithmic derivatives differing by at most a strict fraction of
the oscillation of that exponent.
-/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)

def positiveKernelLogTilt (k r d : Y → ℝ) (t : ℝ) : ℝ :=
  Real.log (∫ x, Real.exp (t*d x)*(k x*r x) ∂μ)

def positiveKernelLogTiltDerivative (k r d : Y → ℝ) (t : ℝ) : ℝ :=
  (∫ x, d x*(k x*(Real.exp (t*d x)*r x)) ∂μ) /
    (∫ x, k x*(Real.exp (t*d x)*r x) ∂μ)

theorem positiveKernelLogTilt_hasDerivAt {k r d : Y → ℝ} {m M : ℝ}
    (hr : Integrable r μ) (hr0 : ∀ᵐ x ∂μ, 0 ≤ r x)
    (hmass : 0 < ∫ x, r x ∂μ) (hk : Measurable k) (hd : Measurable d)
    (hm : 0 < m) (hkb : ∀ x, m ≤ k x ∧ k x ≤ M)
    {D : ℝ≥0} (hdb : ∀ x, |d x| ≤ D) (t : ℝ) :
    HasDerivAt (positiveKernelLogTilt μ k r d)
      (positiveKernelLogTiltDerivative μ k r d t) t := by
  have hkn : ∀ᵐ x ∂μ, ‖k x‖ ≤ M := Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hm.le.trans (hkb x).1)]
    exact (hkb x).2
  have hkr : Integrable (fun x => k x*r x) μ := hr.bdd_mul hk.aestronglyMeasurable hkn
  have hkr0 : ∀ᵐ x ∂μ, 0 ≤ k x*r x :=
    hr0.mono fun x hx => mul_nonneg (hm.le.trans (hkb x).1) hx
  have hkrmass : 0 < ∫ x, k x*r x ∂μ := by
    have hb := integral_mono_ae (hr.const_mul m) hkr
      (hr0.mono fun x hx => mul_le_mul_of_nonneg_right (hkb x).1 hx)
    rw [integral_const_mul] at hb
    exact (mul_pos hm hmass).trans_le hb
  have ht := log_exponential_tilt_hasDerivAt μ hkr hd hdb t
    (exponential_tilt_mass_pos μ hkr hkr0 hkrmass hd hdb t)
  convert ht using 1
  · rfl
  · unfold positiveKernelLogTiltDerivative
    congr 1 <;> apply integral_congr_ae <;> exact Eventually.of_forall (fun x => by ring)

theorem positiveKernelLogTiltDerivative_difference {k v r d : Y → ℝ} {m M a b : ℝ}
    (hr : Integrable r μ) (hr0 : ∀ᵐ x ∂μ, 0 ≤ r x)
    (hmass : 0 < ∫ x, r x ∂μ) (hk : Measurable k) (hv : Measurable v)
    (hd : Measurable d) (hm : 0 < m)
    (hkb : ∀ x, m ≤ k x ∧ k x ≤ M) (hvb : ∀ x, m ≤ v x ∧ v x ≤ M)
    {D : ℝ≥0} (hdb : ∀ x, |d x| ≤ D)
    (hab : ∀ᵐ x ∂μ, a ≤ d x ∧ d x ≤ b) (t : ℝ) :
    |positiveKernelLogTiltDerivative μ k r d t -
      positiveKernelLogTiltDerivative μ v r d t| ≤ (1-m/M)*(b-a) := by
  have hrt := bounded_exp_mul_integrable μ hr hd hdb t
  have hrt0 : ∀ᵐ x ∂μ, 0 ≤ Real.exp (t*d x)*r x :=
    hr0.mono fun x hx => mul_nonneg (Real.exp_pos _).le hx
  have hdrt : Integrable (fun x => d x*(Real.exp (t*d x)*r x)) μ :=
    hrt.bdd_mul hd.aestronglyMeasurable
      (Eventually.of_forall fun x => (Real.norm_eq_abs (d x)).trans_le (hdb x))
  exact normalized_positive_weights_difference μ hrt hdrt hrt0
    (exponential_tilt_mass_pos μ hr hr0 hmass hd hdb t) hk hv hm hkb hvb hab

end RegularPointCoordinates

end

end OAI
