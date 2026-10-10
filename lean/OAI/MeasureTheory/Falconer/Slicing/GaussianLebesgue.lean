import OAI.MeasureTheory.Falconer.Slicing.GaussianProjection
import OAI.MeasureTheory.Falconer.Slicing.GaussianConvolution

namespace OAI

/-! # A Lebesgue density for the standard Gaussian used in the band estimates -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal FourierTransform
variable {d : ℕ}

noncomputable def gaussianLebesgue (d : ℕ) : Measure (Space d) :=
  (volume : Measure (Space d)).withDensity (fun x => ENNReal.ofReal (Real.exp (-(1/2:ℝ)*‖x‖^2)))

instance gaussianLebesgue_finite : IsFiniteMeasure (gaussianLebesgue d) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal
    (PlanarFalconer.gaussian_lebesgue_integrable (by norm_num : (0:ℝ) < 1/2))
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le))]
  exact ENNReal.ofReal_ne_top

theorem gaussianLebesgue_sourceFourier (v : Space d) :
    PlanarFalconer.sourceFourier (gaussianLebesgue d) v =
      (((2*Real.pi)^((d:ℝ)/2)*Real.exp (-(2*Real.pi^2)*‖v‖^2):ℝ):ℂ) := by
  have he : PlanarFalconer.sourceFourier (gaussianLebesgue d) v =
      𝓕 (fun x : Space d => (Real.exp (-(1/2:ℝ)*‖x‖^2):ℂ)) v := by
    rw [sourceFourier_phase,gaussianLebesgue,
      integral_withDensity_eq_integral_toReal_smul (by fun_prop)
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le,Complex.real_smul]
    simp only [euclideanFourierPhase,smul_eq_mul]
    rw [mul_comm]
    congr 2
    ring_nf
  rw [he,PlanarFalconer.source_gaussian_fourier (by norm_num : (0:ℝ) < 1/2)]
  simp only [Space,finrank_euclideanSpace,Fintype.card_fin]
  congr 1
  congr 1 <;> ring_nf

noncomputable def gaussianVolumeNormalization (d : ℕ) : ℝ := ((2*Real.pi)^((d:ℝ)/2))⁻¹

noncomputable def normalizedGaussianLebesgue (d : ℕ) : Measure (Space d) :=
  ENNReal.ofReal (gaussianVolumeNormalization d) • gaussianLebesgue d

instance normalizedGaussianLebesgue_finite : IsFiniteMeasure (normalizedGaussianLebesgue d) := by
  refine ⟨?_⟩
  change ENNReal.ofReal (gaussianVolumeNormalization d)*gaussianLebesgue d univ < ∞
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem normalizedGaussianLebesgue_sourceFourier (v : Space d) :
    PlanarFalconer.sourceFourier (normalizedGaussianLebesgue d) v =
      (Real.exp (-(2*Real.pi^2)*‖v‖^2):ℂ) := by
  have hpos : 0 < (2*Real.pi)^((d:ℝ)/2) := by positivity
  rw [PlanarFalconer.sourceFourier,charFun_apply,normalizedGaussianLebesgue,integral_smul_measure]
  change (ENNReal.ofReal (gaussianVolumeNormalization d)).toReal •
    PlanarFalconer.sourceFourier (gaussianLebesgue d) v = _
  rw [ENNReal.toReal_ofReal (by unfold gaussianVolumeNormalization; positivity),
    gaussianLebesgue_sourceFourier,Complex.real_smul]
  unfold gaussianVolumeNormalization
  push_cast
  rw [← mul_assoc,inv_mul_cancel₀ (by exact_mod_cast hpos.ne'),one_mul]

end Falconer

end OAI
