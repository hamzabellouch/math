import OAI.Geometry.EinsteinFour.ScalarLpVariation
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

namespace OAI

/-! The squared Lp norm at a normalized function has the expected first
variation, including for sign-changing or merely Lp representatives. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The ordinary real Lp norm as an integral of the actual representative. -/
theorem scalarLp_norm_eq_moment {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    (f : Lp ℝ (ENNReal.ofReal p) μ) :
    ‖f‖ = (∫ x, |f x| ^ p ∂μ) ^ p⁻¹ := by
  rw [Lp.norm_def, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
      ENNReal.ofReal_ne_top (Lp.aestronglyMeasurable f)]
  simp only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs]

theorem scalarLp_moment_eq_norm_rpow {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    (f : Lp ℝ (ENNReal.ofReal p) μ) :
    (∫ x, |f x| ^ p ∂μ) = ‖f‖ ^ p := by
  rw [scalarLp_norm_eq_moment hp f,
    Real.rpow_inv_rpow (integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _)) hp.ne']

theorem scalarLp_norm_sq_eq_moment {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 0 < p)
    (f : Lp ℝ (ENNReal.ofReal p) μ) :
    ‖f‖ ^ 2 = (∫ x, |f x| ^ p ∂μ) ^ (2 / p) := by
  rw [scalarLp_moment_eq_norm_rpow hp f, ← Real.rpow_mul (norm_nonneg f)]
  have he : p * (2 / p) = 2 := by field_simp [hp.ne']
  rw [he, Real.rpow_two]

private theorem scalarLp_add_smul_moment {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (f b : Lp ℝ (ENNReal.ofReal p) μ) (t : ℝ) :
    (∫ x, |(f + t • b) x| ^ p ∂μ) = ∫ x, |f x + t * b x| ^ p ∂μ := by
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add f (t • b), Lp.coeFn_smul t b] with x hsum hsmul
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hsum hsmul
  rw [hsum, hsmul]

variable [IsFiniteMeasure μ]

/-- At Lp norm one, the squared norm differentiates to twice the nonlinear
pairing against a bounded measurable direction. -/
theorem scalarLpNormSq_hasDerivAt {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 < p) (f b : Lp ℝ (ENNReal.ofReal p) μ) (hf : ‖f‖ = 1)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ x ∂μ, |b x| ≤ B) :
    HasDerivAt (fun t : ℝ => ‖f + t • b‖ ^ 2)
      (2 * ∫ x, |f x| ^ (p - 2) * f x * b x ∂μ) 0 := by
  have hp0 : 0 < p := by linarith
  have hd := scalarLpMoment_hasDerivAt_lp hp f (Lp.aestronglyMeasurable b) hB hb
  have hz : (∫ x, |f x + (0 : ℝ) * b x| ^ p ∂μ) = 1 := by
    simp only [zero_mul, add_zero]
    rw [scalarLp_moment_eq_norm_rpow hp0 f, hf, Real.one_rpow]
  have hpow := hd.rpow_const (p := 2 / p) (Or.inl (by rw [hz]; norm_num))
  have heq : (fun t : ℝ => ‖f + t • b‖ ^ 2) =
      fun t => (∫ x, |f x + t * b x| ^ p ∂μ) ^ (2 / p) := by
    funext t
    rw [scalarLp_norm_sq_eq_moment hp0, scalarLp_add_smul_moment]
  rw [← heq] at hpow
  convert hpow using 1
  rw [hz, Real.one_rpow, mul_one]
  field_simp [hp0.ne']

/-- A continuous representative of the direction is sufficient; no regularity
or pointwise sign is required of the normalized Lp function. -/
theorem scalarLpNormSq_hasDerivAt_continuous [TopologicalSpace X]
    [OpensMeasurableSpace X] [CompactSpace X] {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p)
    (f b : Lp ℝ (ENNReal.ofReal p) μ) (hf : ‖f‖ = 1)
    (v : C(X, ℝ)) (hb : (b : X → ℝ) =ᵐ[μ] v) :
    HasDerivAt (fun t : ℝ => ‖f + t • b‖ ^ 2)
      (2 * ∫ x, |f x| ^ (p - 2) * f x * v x ∂μ) 0 := by
  have hbound : ∀ᵐ x ∂μ, |b x| ≤ ‖v‖ := by
    filter_upwards [hb] with x hx
    rw [hx]
    exact v.norm_coe_le_norm x
  have hd := scalarLpNormSq_hasDerivAt hp f b hf (norm_nonneg v) hbound
  have hi : (∫ x, |f x| ^ (p - 2) * f x * b x ∂μ) =
      ∫ x, |f x| ^ (p - 2) * f x * v x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hb] with x hx
    rw [hx]
  rwa [hi] at hd

end
end PositiveEinsteinFour.Geometry

end OAI
