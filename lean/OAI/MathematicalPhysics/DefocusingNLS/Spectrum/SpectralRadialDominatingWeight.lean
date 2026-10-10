import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialPrimitiveEvaluation

namespace OAI

/-! An integrable bound for the squared positive-radius evaluation norm. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectral_radial_inverse_tenth_integrable (R : ℝ) :
    Integrable (fun r : ℝ => (r^10)⁻¹) (radialPressureMeasure R) := by
  unfold radialPressureMeasure
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hi : Integrable (fun r : ℝ => r) (volume.restrict (Icc 0 R)) :=
    continuous_id.continuousOn.integrableOn_compact isCompact_Icc
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  rw [ENNReal.toReal_ofReal (by positivity),max_eq_left hr.1]
  change r=r^11*(r^10)⁻¹
  by_cases h : r=0
  · simp [h]
  · field_simp

noncomputable def spectralRadialEvaluationWeight (R : ℝ) (hR : 0 < R) (r : ℝ) : ℝ :=
  2*‖spectralRadialTrace R hR‖^2+(r^10)⁻¹/5

theorem spectralRadialEvaluationWeight_integrable (R : ℝ) (hR : 0 < R) :
    Integrable (spectralRadialEvaluationWeight R hR) (radialPressureMeasure R) :=
  (integrable_const _).add ((spectral_radial_inverse_tenth_integrable R).div_const 5)

theorem spectralRadialPointValue_sq_bound (R : ℝ) (hR : 0 < R) (r : ℝ)
    (hr : 0 < r) (hrR : r ≤ R) (u : SpectralRadialEnergy R) :
    ‖spectralRadialPointValue R hR r hr u‖^2 ≤ spectralRadialEvaluationWeight R hR r*‖u‖^2 := by
  have hd := spectralRadialPointValue_difference_bound R hR r hr hrR u
  have he := spectralRadialEnergy_norm_sq R u
  have hD : ‖spectralRadialDerivative R u‖^2 ≤ ‖u‖^2 := by
    nlinarith [sq_nonneg ‖spectralRadialValue R u‖]
  have ha : 0 ≤ (r^10)⁻¹/10 := by positivity
  have hd' : ‖spectralRadialPointValue R hR r hr u-spectralRadialTrace R hR u‖^2 ≤
      ((r^10)⁻¹/10)*‖u‖^2 := hd.trans (mul_le_mul_of_nonneg_left hD ha)
  have ht := (spectralRadialTrace R hR).le_opNorm u
  have ht' : ‖spectralRadialTrace R hR u‖^2 ≤ ‖spectralRadialTrace R hR‖^2*‖u‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) ht 2
  have htri : ‖spectralRadialPointValue R hR r hr u‖ ≤
      ‖spectralRadialPointValue R hR r hr u-spectralRadialTrace R hR u‖+
        ‖spectralRadialTrace R hR u‖ := norm_le_norm_sub_add _ _
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  unfold spectralRadialEvaluationWeight
  nlinarith [sq_nonneg (‖spectralRadialPointValue R hR r hr u-spectralRadialTrace R hR u‖-
    ‖spectralRadialTrace R hR u‖)]

theorem spectralRadialSmooth_sq_bound (R : ℝ) (hR : 0 < R) (r : ℝ)
    (hr : 0 < r) (hrR : r ≤ R) (f : 𝓢(ℝ,ℂ)) :
    ‖f r‖^2 ≤ spectralRadialEvaluationWeight R hR r*‖spectralRadialSmoothEmbedding R f‖^2 := by
  rw [← spectralRadialPointValue_smooth R hR r hr hrR f]
  exact spectralRadialPointValue_sq_bound R hR r hr hrR _

end DefocusingNLS

end OAI
