import OAI.MathematicalPhysics.Boltzmann.Branching.AxisInput

namespace OAI

/-! # Slice bounds with a nonzero axial mismatch -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.TransverseAverage

namespace BoltzmannNonuniqueness.MismatchSlices

theorem lintegral_extendedPower_slope {q a b A B : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a ≤ b) (hA : A ≠ 0) (hB : B ≠ 0) :
    (∫⁻ x in Ioc a b, extendedPower q (A - B * x)) ≤
      ENNReal.ofReal (|B| ^ (1 - q) * (2 * (b - a) ^ (2 - q) / (2 - q))) := by
  have hi := AxialSlices.intervalIntegrable_abs_affine_rpow
    (show -1 < 1 - q by linarith) A B a b
  rw [lintegral_congr_ae (ae_restrict_of_ae (extendedPower_ae_eq hA B q)),
    ← ofReal_integral_eq_lintegral_ofReal hi.1
      (ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg _) _)),
    ← intervalIntegral.integral_of_le hab]
  apply ENNReal.ofReal_le_ofReal
  simpa only [show 1 - q + 1 = 2 - q by ring] using
    AxialSlices.integral_abs_affine_rpow_le (show -1 < 1 - q by linarith)
      (show 1 - q ≤ 0 by linarith) hab hB

theorem rectangleLineMass_slope_bound {q a b A B R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a ≤ b) (hR : 0 ≤ R)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (e : Transverse) (he : ‖e‖ = 1) (m : ℝ) :
    rectangleLineMass q e A B m R a b ≤
      ENNReal.ofReal (2 * R * (b - a) + AxialSlices.lineConstant q *
        (|B| ^ (1 - q) * (2 * (b - a) ^ (2 - q) / (2 - q)))) := by
  have hc := (AxialSlices.lineConstant_pos hq₁).le
  have hs := lintegral_extendedPower_slope hq₁ hq₂ hab hA hB
  unfold rectangleLineMass
  calc
    _ ≤ ∫⁻ z in Ioc a b, ENNReal.ofReal (2 * R) +
        ENNReal.ofReal (AxialSlices.lineConstant q) * extendedPower q (A - B * z) :=
      lintegral_mono (fun z => lintegral_lineWeight_le_extended hq₁ hR e he _ m)
    _ = ENNReal.ofReal (2 * R) * ENNReal.ofReal (b - a) +
        ENNReal.ofReal (AxialSlices.lineConstant q) *
          ∫⁻ z in Ioc a b, extendedPower q (A - B * z) := by
      rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
    _ ≤ ENNReal.ofReal (2 * R) * ENNReal.ofReal (b - a) +
        ENNReal.ofReal (AxialSlices.lineConstant q) *
          ENNReal.ofReal (|B| ^ (1 - q) * (2 * (b - a) ^ (2 - q) / (2 - q))) :=
      add_le_add le_rfl (mul_le_mul' le_rfl hs)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * R),
        ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add (by positivity) (by positivity)]

theorem inverse_power_le {q b : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 < b) :
    b ^ (q - 2) ≤ 1 + b⁻¹ := by
  by_cases hb₁ : b ≤ 1
  · have hp : b ^ (q - 1) ≤ 1 := Real.rpow_le_one hb.le hb₁ (by linarith)
    have he : b ^ (q - 2) = b ^ (q - 1) * b⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hb]
      congr 1
      ring
    rw [he]
    have h := mul_le_mul_of_nonneg_right hp (inv_nonneg.mpr hb.le)
    linarith
  · exact (Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge hb₁) (by linarith)).trans
      (le_add_of_nonneg_right (inv_nonneg.mpr hb.le))

theorem inverse_slope_bound {q a b δ : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hb : 0 < b) (hδ : 0 < δ) (ha : δ ≤ |a|) :
    b⁻¹ * |a / b| ^ (1 - q) ≤ δ ^ (1 - q) * (1 + b⁻¹) := by
  have hapos : 0 < |a| := hδ.trans_le ha
  have hpow : |a| ^ (1 - q) ≤ δ ^ (1 - q) :=
    Real.rpow_le_rpow_of_nonpos hδ ha (by linarith)
  have he : b⁻¹ * |a / b| ^ (1 - q) = |a| ^ (1 - q) * b ^ (q - 2) := by
    rw [abs_div, abs_of_pos hb, Real.div_rpow hapos.le hb.le, div_eq_mul_inv,
      ← Real.rpow_neg hb.le, ← Real.rpow_neg_one]
    calc
      _ = |a| ^ (1 - q) * (b ^ (-1 : ℝ) * b ^ (-(1 - q))) := by ring
      _ = _ := by rw [← Real.rpow_add hb, show (-1 : ℝ) + -(1 - q) = q - 2 by ring]
  rw [he]
  exact mul_le_mul hpow (inverse_power_le hq₁ hq₂ hb)
    (Real.rpow_nonneg hb.le _) (Real.rpow_nonneg hδ.le _)

def slopeCoefficient (q R : ℝ) : ℝ :=
  AxialSlices.lineConstant q * (2 * (2 * R) ^ (2 - q) / (2 - q))

def mismatchCoefficient (q R δ : ℝ) : ℝ :=
  4 * R ^ 2 + slopeCoefficient q R * δ ^ (1 - q)

theorem slopeCoefficient_nonneg {q R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hR : 0 ≤ R) :
    0 ≤ slopeCoefficient q R := by
  have := AxialSlices.lineConstant_pos hq₁
  unfold slopeCoefficient
  positivity

theorem mismatchCoefficient_nonneg {q R δ : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hR : 0 ≤ R) (hδ : 0 ≤ δ) :
    0 ≤ mismatchCoefficient q R δ := by
  have := slopeCoefficient_nonneg hq₁ hq₂ hR
  unfold mismatchCoefficient
  positivity

theorem normalizedBallSlice_mismatch {q R δ : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hR : 0 < R) (hδ : 0 < δ)
    (v p : Transverse) (t α : ℝ) (hreg : RegularTransverse v p)
    (hm : δ ≤ |t - α|) :
    normalizedBallSlice q v t p α R (-R) R ≤
      ENNReal.ofReal ((mismatchCoefficient q R δ / transverseWeight q v) *
        (1 + ‖v - p‖⁻¹)) := by
  have hn : 0 < ‖v - p‖ := norm_pos_iff.mpr hreg.1
  have hB : (t - α) / ‖v - p‖ ≠ 0 := div_ne_zero (by
    intro he
    rw [he, abs_zero] at hm
    linarith) hn.ne'
  have hs := rectangleLineMass_slope_bound hq₁ hq₂ (by linarith : -R ≤ R)
    hR.le hreg.2 hB (direction (v - p)) (norm_direction hreg.1)
    (inner ℝ (TransverseLine.quarterTurn (direction (v - p))) v)
  have hmass := (ballLineMass_le_rectangle hR.le q (direction (v - p)) v
    (norm_direction hreg.1) (sliceOffset v p) ((t - α) / ‖v - p‖) (-R) R).trans hs
  have hW := transverseWeight_pos q v
  rw [normalizedBallSlice, ite_eq_left hreg]
  apply (mul_le_mul' le_rfl hmass).trans
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (transverseWeight q v * ‖v - p‖))]
  apply ENNReal.ofReal_le_ofReal
  have hc := slopeCoefficient_nonneg hq₁ hq₂ hR.le
  have hi := inverse_slope_bound hq₁ hq₂ hn hδ hm
  have he : 2 * R * (R - -R) + AxialSlices.lineConstant q *
      (|(t - α) / ‖v - p‖| ^ (1 - q) * (2 * (R - -R) ^ (2 - q) / (2 - q))) =
      4 * R ^ 2 + slopeCoefficient q R * |(t - α) / ‖v - p‖| ^ (1 - q) := by
    rw [show R - -R = 2 * R by ring]
    unfold slopeCoefficient
    ring
  rw [he]
  have hi' := mul_le_mul_of_nonneg_left hi hc
  have hr : 4 * R ^ 2 * ‖v - p‖⁻¹ ≤ 4 * R ^ 2 * (1 + ‖v - p‖⁻¹) := by
    nlinarith [sq_nonneg R]
  have hsum : (4 * R ^ 2 + slopeCoefficient q R * |(t - α) / ‖v - p‖| ^ (1 - q)) *
      ‖v - p‖⁻¹ ≤ mismatchCoefficient q R δ * (1 + ‖v - p‖⁻¹) := by
    unfold mismatchCoefficient
    nlinarith [hi', hr]
  have hdiv := div_le_div_of_nonneg_right hsum hW.le
  convert hdiv using 1 <;> ring

end BoltzmannNonuniqueness.MismatchSlices

end

end OAI
