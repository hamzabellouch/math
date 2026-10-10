import OAI.MathematicalPhysics.Boltzmann.Branching.SlopedChart

namespace OAI

/-! # Vanishing transverse tails as the sheet width tends to zero -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetTails
open BoltzmannNonuniqueness.GaussianDiskMixture

namespace BoltzmannNonuniqueness.WidthTails

theorem exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ x⁻¹ := by
  have he : x ≤ Real.exp x := (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp x)
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hx).mpr
  have h := mul_le_mul_of_nonneg_left he (Real.exp_pos (-x)).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  exact h

theorem gaussian_tilt_width_bound {d U : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 8)
    (hU : 0 < U) (p : Transverse) (hp : U ≤ ‖p‖) :
    Real.exp (2 * ‖p‖ ^ 2) * gaussianDensity d p ≤
      (8 * d ^ 2 / U ^ 2) * gaussianDensity (2 * d) p := by
  have hd₂ : d ^ 2 ≤ 1 / 64 := by nlinarith
  have hcoef : 1 / (2 * d ^ 2) ≤ 3 / (4 * d ^ 2) - 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * d ^ 2)).mpr
    field_simp
    nlinarith
  have he : Real.exp (-(3 / (4 * d ^ 2) - 2) * ‖p‖ ^ 2) ≤
      Real.exp (-(U ^ 2 / (2 * d ^ 2))) := by
    apply Real.exp_le_exp.mpr
    have hn : U ^ 2 ≤ ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
    have hc := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖p‖)
    have hh := div_le_div_of_nonneg_right hn (by positivity : 0 ≤ 2 * d ^ 2)
    have hc' : ‖p‖ ^ 2 / (2 * d ^ 2) ≤ (3 / (4 * d ^ 2) - 2) * ‖p‖ ^ 2 := by
      convert hc using 1
      ring
    nlinarith [hc']
  have ht := exp_neg_le_inv (by positivity : 0 < U ^ 2 / (2 * d ^ 2))
  rw [gaussian_tilt_identity hd p]
  have h := mul_le_mul_of_nonneg_left (he.trans ht) (by norm_num : (0 : ℝ) ≤ 4)
  apply (mul_le_mul_of_nonneg_right h (gaussianDensity_nonneg _ _)).trans_eq
  congr 1
  field_simp
  norm_num

theorem transverse_tail_bound {d U : ℝ} (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    (hU : 0 < U) :
    (transverseTilt d).restrict {p : Transverse | U < ‖p‖} ≤
      ENNReal.ofReal (8 * d ^ 2 / U ^ 2) • transverseLaw (2 * d) := by
  obtain rfl | hdpos := hd.eq_or_lt
  · rw [transverseTilt_zero]
    have hz : (Measure.dirac (0 : Transverse)).restrict {p : Transverse | U < ‖p‖} = 0 := by
      apply Measure.restrict_eq_zero.mpr
      simp only [Measure.dirac_apply, indicator_of_notMem (show (0 : Transverse) ∉
        {p : Transverse | U < ‖p‖} by simpa using not_lt.mpr hU.le)]
    rw [hz]
    exact bot_le
  · rw [transverseTilt_gaussian hdpos]
    have hs : MeasurableSet {p : Transverse | U < ‖p‖} :=
      measurableSet_lt measurable_const measurable_norm
    rw [restrict_withDensity hs, ← withDensity_indicator hs]
    have h2d : 2 * d ≠ 0 := by positivity
    simp only [transverseLaw, ite_eq_right (c := 2 * d = 0) h2d, gaussianLaw]
    rw [← withDensity_smul _ (measurable_gaussianDensity (2 * d) |>.ennreal_ofReal)]
    apply withDensity_mono
    filter_upwards [] with p
    by_cases hp : U < ‖p‖
    · simp only [indicator_of_mem (show p ∈ {p : Transverse | U < ‖p‖} from hp),
        Pi.smul_apply, smul_eq_mul]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * d ^ 2 / U ^ 2)]
      exact ENNReal.ofReal_le_ofReal (gaussian_tilt_width_bound hdpos hdmax hU p hp.le)
    · simp only [indicator_of_notMem (show p ∉ {p : Transverse | U < ‖p‖} from hp)]
      exact bot_le

def incomingTail (U : ℝ) : Set Velocity := {p | U < ‖transverse p‖}

theorem measurableSet_incomingTail (U : ℝ) : MeasurableSet (incomingTail U) :=
  measurableSet_lt measurable_const ChartKernel.measurable_transverse.norm

theorem tiltedSheet_transverse_tail {d U L : ℝ} (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    (hU : 0 < U) {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (hρ : AxialMoment ρ L) :
    (tiltedSheet d ρ).restrict (incomingTail U) ≤
      ENNReal.ofReal ((8 * d ^ 2 / U ^ 2) * L) • sheetLaw (2 * d) (axialProbability ρ hρ) := by
  have := transverseTilt_finite hd hdmax
  have := axialTilt_finite hρ
  have hp : SheetMeasures.join ⁻¹' incomingTail U =
      {p : Transverse | U < ‖p‖} ×ˢ (univ : Set ℝ) := by
    ext p
    change (U < ‖transverse (PlaneChart.join p.1 p.2)‖) ↔ _
    simp only [PlaneChart.transverse_join, mem_prod, mem_ofPred_eq, mem_univ, and_true]
  rw [tiltedSheet_eq, Measure.restrict_map SheetMeasures.join.measurable (measurableSet_incomingTail U),
    hp, ← Measure.restrict_prod_eq_prod_univ]
  have h := Measure.map_mono (Measure.prod_mono (transverse_tail_bound hd hdmax hU)
    (axialTilt_le_probability hρ)) SheetMeasures.join.measurable
  simpa only [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_smul _ SheetMeasures.join.measurable.aemeasurable,
    mul_comm (ENNReal.ofReal L) (ENNReal.ofReal (8 * d ^ 2 / U ^ 2)),
    ← ENNReal.ofReal_mul (show 0 ≤ 8 * d ^ 2 / U ^ 2 by positivity), sheetLaw] using h

end BoltzmannNonuniqueness.WidthTails

end

end OAI
