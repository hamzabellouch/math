import OAI.MathematicalPhysics.Boltzmann.Branching.AxisMismatch

namespace OAI

/-! # Restricted affine slice changes of variables -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.GeometricSlice

namespace BoltzmannNonuniqueness.AffineSlices

theorem lintegral_affine (f : ℝ → ℝ≥0∞) (hf : Measurable f) (A : ℝ) {B : ℝ}
    (hB : B ≠ 0) :
    (∫⁻ x : ℝ, f (A - B * x)) = ENNReal.ofReal (|B|⁻¹) * ∫⁻ y : ℝ, f y := by
  have hg : Measurable (fun y : ℝ => f (A + y)) := hf.comp (measurable_const.add measurable_id)
  calc
    _ = ∫⁻ x : ℝ, (fun y => f (A + y)) (-B * x) := by
      apply lintegral_congr
      intro x
      congr 1
      ring
    _ = ∫⁻ y : ℝ, f (A + y) ∂Measure.map (fun x : ℝ => -B * x) volume :=
      (lintegral_map hg (measurable_const.mul measurable_id)).symm
    _ = ENNReal.ofReal (|B|⁻¹) * ∫⁻ y : ℝ, f (A + y) := by
      rw [Real.map_volume_mul_left (neg_ne_zero.mpr hB), lintegral_smul_measure]
      simp only [abs_inv, abs_neg, smul_eq_mul]
    _ = _ := by rw [lintegral_add_left_eq_self f A]

theorem lintegral_affine_interval (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (A C D : ℝ) {B : ℝ} (hB : B ≠ 0) :
    (∫⁻ x : ℝ, if |A - B * x - C| ≤ D then f (A - B * x) else 0) =
      ENNReal.ofReal (|B|⁻¹) * ∫⁻ y in Icc (C - D) (C + D), f y := by
  have he (y : ℝ) : (if |y - C| ≤ D then f y else 0) =
      (Icc (C - D) (C + D)).indicator f y := by
    have hh : |y - C| ≤ D ↔ y ∈ Icc (C - D) (C + D) := by
      rw [abs_le]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    simp only [hh, indicator_apply]
  simp_rw [he]
  rw [lintegral_affine _ (hf.indicator measurableSet_Icc) A hB,
    lintegral_indicator measurableSet_Icc]

def intervalConstant (q D : ℝ) : ℝ := 2 * (2 * D) ^ (2 - q) / (2 - q)

theorem intervalConstant_nonneg {q D : ℝ} (hq : q < 2) (hD : 0 ≤ D) :
    0 ≤ intervalConstant q D := by unfold intervalConstant; positivity

theorem extendedPower_interval_bound {q D : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hD : 0 ≤ D) (C : ℝ) :
    (∫⁻ u in Icc (C - D) (C + D), extendedPower q u) ≤ ENNReal.ofReal (intervalConstant q D) := by
  have he : (fun u : ℝ => extendedPower q u) =ᵐ[volume]
      (fun u => ENNReal.ofReal (|u| ^ (1 - q))) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with u hu
    simp only [extendedPower, ite_eq_right hu]
  rw [← restrict_Ioc_eq_restrict_Icc,
    lintegral_congr_ae (ae_restrict_of_ae he)]
  have hi := AxialSlices.intervalIntegrable_abs_rpow (show -1 < 1 - q by linarith) (C - D) (C + D)
  rw [← ofReal_integral_eq_lintegral_ofReal hi.1
      (ae_of_all _ (fun u => Real.rpow_nonneg (abs_nonneg _) _)),
    ← intervalIntegral.integral_of_le (show C - D ≤ C + D by linarith)]
  apply ENNReal.ofReal_le_ofReal
  have hb := AxialSlices.integral_abs_sub_rpow_le (show -1 < 1 - q by linarith)
    (show 1 - q ≤ 0 by linarith) (show C - D ≤ C + D by linarith) (t := 0)
  simpa only [sub_zero, show C + D - (C - D) = 2 * D by ring,
    show 1 - q + 1 = 2 - q by ring, intervalConstant] using hb

def rectangleConstant (q D S : ℝ) : ℝ :=
  4 * D * S + AxialSlices.lineConstant q * intervalConstant q D

theorem rectangleConstant_nonneg {q D S : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 ≤ D) (hS : 0 ≤ S) :
    0 ≤ rectangleConstant q D S := by
  have := AxialSlices.lineConstant_pos hq₁
  have := intervalConstant_nonneg hq₂ hD
  unfold rectangleConstant
  positivity

theorem affine_rectangle_bound {q D S : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (A C : ℝ) {B : ℝ} (hB : B ≠ 0) :
    (∫⁻ x : ℝ, if |A - B * x - C| ≤ D then
      ENNReal.ofReal (2 * S) + ENNReal.ofReal (AxialSlices.lineConstant q) *
        extendedPower q (A - B * x) else 0) ≤
      ENNReal.ofReal (|B|⁻¹ * rectangleConstant q D S) := by
  have hm : Measurable (fun u => ENNReal.ofReal (2 * S) +
      ENNReal.ofReal (AxialSlices.lineConstant q) * extendedPower q u) :=
    measurable_const.add (measurable_const.mul (measurable_extendedPower q))
  rw [lintegral_affine_interval _ hm A C D hB,
    lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
  have hc := (AxialSlices.lineConstant_pos hq₁).le
  calc
    _ ≤ ENNReal.ofReal (|B|⁻¹) *
        (ENNReal.ofReal (2 * S) * ENNReal.ofReal (C + D - (C - D)) +
          ENNReal.ofReal (AxialSlices.lineConstant q) * ENNReal.ofReal (intervalConstant q D)) :=
      mul_le_mul' le_rfl (add_le_add le_rfl (mul_le_mul' le_rfl
        (extendedPower_interval_bound hq₁ hq₂ hD C)))
    _ = _ := by
      rw [show C + D - (C - D) = 2 * D by ring,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * S), ← ENNReal.ofReal_mul hc,
        ← ENNReal.ofReal_add (by positivity) (mul_nonneg hc (intervalConstant_nonneg hq₂ hD)),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ |B|⁻¹)]
      apply congrArg ENNReal.ofReal
      unfold rectangleConstant
      ring

end BoltzmannNonuniqueness.AffineSlices

end

end OAI
