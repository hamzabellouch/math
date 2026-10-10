import OAI.Geometry.RCD.Heat.GaussianHeatInput
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! # Gaussian decay of the heat kernel away from its pole -/

open Set Metric MeasureTheory Filter
open scoped Topology

noncomputable section

namespace RegularPointCoordinates

/-- The envelope after a polynomial lower bound for small ball volume. -/
def gaussianOffDiagonalEnvelope (s a b t : ℝ) : ℝ :=
  (t⁻¹) ^ s * Real.exp (-a * t⁻¹ + b * t)

theorem gaussianOffDiagonalEnvelope_nonneg (s a b t : ℝ) (ht : 0 ≤ t) :
    0 ≤ gaussianOffDiagonalEnvelope s a b t :=
  mul_nonneg (Real.rpow_nonneg (inv_nonneg.mpr ht) _) (Real.exp_pos _).le

/-- Every polynomial volume loss is dominated by a positive off-diagonal
Gaussian exponent at small time. -/
theorem gaussianOffDiagonalEnvelope_tendsto (s b : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (gaussianOffDiagonalEnvelope s a b) (𝓝[>] 0) (𝓝 0) := by
  have htail := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s a ha).comp
    tendsto_inv_nhdsGT_zero
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hexp : Tendsto (fun t : ℝ => Real.exp (b * t)) (𝓝[>] 0) (𝓝 (Real.exp (b * 0))) :=
    Real.continuous_exp.continuousAt.tendsto.comp (ht.const_mul b)
  unfold gaussianOffDiagonalEnvelope
  simpa only [mul_zero, zero_mul, Real.exp_zero, Real.exp_add,
    mul_assoc, Function.comp_apply] using htail.mul hexp

/-- The same error still vanishes after any fixed polynomial loss from
an interscale change of normalization. -/
theorem gaussianOffDiagonalEnvelope_weighted_tendsto (s b q : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => (t⁻¹) ^ q * gaussianOffDiagonalEnvelope s a b t)
      (𝓝[>] 0) (𝓝 0) := by
  apply (gaussianOffDiagonalEnvelope_tendsto (q + s) b ha).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change (t⁻¹) ^ (q + s) * Real.exp (-a * t⁻¹ + b * t) =
    (t⁻¹) ^ q * ((t⁻¹) ^ s * Real.exp (-a * t⁻¹ + b * t))
  rw [Real.rpow_add (inv_pos.mpr ht), mul_assoc]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (k : ℝ → X → X → ℝ)

/-- The exact Gaussian upper bound and a lower volume power produce a
uniform off-diagonal envelope. The volume hypothesis is in the inverse
power form needed here; it is kept separate from the published bound. -/
theorem gaussian_upper_of_inverse_power_volume
    {t s d C₁ C₂ V ε : ℝ} (ht : 0 < t) (hd : 0 ≤ d)
    (hC : 0 < C₁) (hV : 0 < V) (hden : 0 < 4 + ε) (x y : X)
    (hupper : k t x y ≤ (C₁ / μ.real (ball y (Real.sqrt t))) *
      Real.exp (-(dist x y) ^ 2 / ((4 + ε) * t) + C₂ * t))
    (hvol : V / (t⁻¹) ^ s ≤ μ.real (ball y (Real.sqrt t)))
    (hsep : d ≤ dist x y) :
    k t x y ≤ (C₁ / V) * gaussianOffDiagonalEnvelope s (d ^ 2 / (4 + ε)) C₂ t := by
  have hpow : 0 < (t⁻¹) ^ s := Real.rpow_pos_of_pos (inv_pos.mpr ht) _
  have hvolpos : 0 < μ.real (ball y (Real.sqrt t)) :=
    (div_pos hV hpow).trans_le hvol
  have hratio : C₁ / μ.real (ball y (Real.sqrt t)) ≤ (C₁ / V) * (t⁻¹) ^ s := by
    apply (div_le_iff₀ hvolpos).2
    have hmul := (div_le_iff₀ hpow).mp hvol
    calc
      C₁ = (C₁ / V) * V := by field_simp
      _ ≤ (C₁ / V) * (μ.real (ball y (Real.sqrt t)) * (t⁻¹) ^ s) :=
        mul_le_mul_of_nonneg_left hmul (div_pos hC hV).le
      _ = _ := by ring
  have hdist : d ^ 2 ≤ (dist x y) ^ 2 := by nlinarith [dist_nonneg (x := x) (y := y)]
  have hfrac := div_le_div_of_nonneg_right hdist (mul_pos hden ht).le
  have hform : -(d ^ 2 / ((4 + ε) * t)) + C₂ * t =
      -(d ^ 2 / (4 + ε)) * t⁻¹ + C₂ * t := by
    field_simp
  have hexp : Real.exp (-(dist x y) ^ 2 / ((4 + ε) * t) + C₂ * t) ≤
      Real.exp (-(d ^ 2 / (4 + ε)) * t⁻¹ + C₂ * t) := by
    rw [← hform]
    exact Real.exp_le_exp.mpr (by simpa only [neg_div, add_comm] using add_le_add_right (neg_le_neg hfrac) (C₂ * t))
  calc
    k t x y ≤ _ := hupper
    _ ≤ ((C₁ / V) * (t⁻¹) ^ s) *
        Real.exp (-(d ^ 2 / (4 + ε)) * t⁻¹ + C₂ * t) :=
      mul_le_mul hratio hexp (Real.exp_pos _).le
        (mul_nonneg (div_pos hC hV).le hpow.le)
    _ = _ := by rw [gaussianOffDiagonalEnvelope]; ring

end RegularPointCoordinates

end

end OAI
