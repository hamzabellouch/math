import OAI.MeasureTheory.Falconer.Slicing.GaussianLebesgue

namespace OAI

/-! # Exact Gaussian density and its dimensional Lebesgue upper bound -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d : ℕ}

theorem gaussian_frequency_scale (t : Space d) :
    2*Real.pi^2*‖((-(2*Real.pi))⁻¹) • t‖^2 = ‖t‖^2/2 := by
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  field_simp

theorem normalizedGaussianLebesgue_eq_standard :
    normalizedGaussianLebesgue d = stdGaussian (Space d) := by
  apply Measure.ext_of_charFun
  ext t
  let v : Space d := ((-(2*Real.pi))⁻¹) • t
  have he : (-(2*Real.pi)) • v = t := by
    dsimp [v]
    rw [smul_smul,mul_inv_cancel₀
      (neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)),one_smul]
  have hh := normalizedGaussianLebesgue_sourceFourier v
  change charFun (normalizedGaussianLebesgue d) ((-(2*Real.pi)) • v) = _ at hh
  rw [he] at hh
  rw [hh,charFun_stdGaussian]
  dsimp [v]
  have hs := gaussian_frequency_scale t
  rw [show -(2*Real.pi^2)*‖((-(2*Real.pi))⁻¹) • t‖^2 = -‖t‖^2/2 by linarith]
  simp only [Complex.ofReal_exp,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_pow,
    Complex.ofReal_ofNat]

theorem gaussianLebesgue_le_volume : gaussianLebesgue d ≤ (volume : Measure (Space d)) := by
  calc
    _ ≤ (volume : Measure (Space d)).withDensity (fun _ => (1:ℝ≥0∞)) := by
      apply withDensity_mono
      filter_upwards with x
      have he : Real.exp (-(1/2:ℝ)*‖x‖^2) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x‖])
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal he
    _ = _ := by rw [withDensity_const,one_smul]

theorem standard_gaussian_le_volume : stdGaussian (Space d) ≤
    ENNReal.ofReal (gaussianVolumeNormalization d) • (volume : Measure (Space d)) := by
  rw [← normalizedGaussianLebesgue_eq_standard]
  unfold normalizedGaussianLebesgue
  gcongr
  exact gaussianLebesgue_le_volume

end Falconer

end OAI
