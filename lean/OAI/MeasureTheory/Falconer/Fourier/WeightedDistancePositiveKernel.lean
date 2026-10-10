import OAI.MeasureTheory.Falconer.Estimates.WeightedDistanceNestedDomination
import OAI.MeasureTheory.Falconer.Fourier.PositiveDistanceSpatialKernel

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem normalized_weight_kernel_factor (d : PositiveDistanceData) :
    ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-d.a)) *
      ENNReal.ofReal (d.levelMass^(-2:ℤ)) * ENNReal.ofReal (d.levelMass^(-2:ℤ)) *
      ENNReal.ofReal (d.levelMass^4*(2:ℝ)^(-((d.t:ℝ)-d.a))) = 1 := by
  have he : (2:ℝ)^((d.t:ℝ)-d.a) * d.levelMass^(-2:ℤ) * d.levelMass^(-2:ℤ) *
      (d.levelMass^4*(2:ℝ)^(-((d.t:ℝ)-d.a))) = 1 := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    norm_num only [zpow_neg,zpow_ofNat]
    have hm := d.levelMass_pos.ne'
    have hp : (2:ℝ)^((d.t:ℝ)-d.a) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
    field_simp
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),he,ENNReal.ofReal_one]

theorem normalized_dominated_distance_kernel (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ ≤ ENNReal.ofReal (d.levelMass^(-2:ℤ)) • d.distance) :
    ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-d.a)) *
      (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+(2:ℝ)^d.t*|z.1-z.2|)^2) ∂μ.prod μ) ≤
        binKernelConstant * d.coincidence := by
  let F : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (1/(1+(2:ℝ)^d.t*|z.1-z.2|)^2)
  have hp := Measure.prod_mono hμ hμ
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul] at hp
  have h := lintegral_mono' hp (fun z => le_refl (F z))
  rw [lintegral_smul_measure] at h
  have hb := d.common_profile_distance_kernel_max d rfl rfl
  simp only [max_self] at hb
  simp_rw [d.width_kernel] at hb
  have h₁ := mul_le_mul_right h (ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-d.a)))
  have h₂ := mul_le_mul_right hb (ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-d.a)) *
    ENNReal.ofReal (d.levelMass^(-2:ℤ)) * ENNReal.ofReal (d.levelMass^(-2:ℤ)))
  have hh : ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-d.a)) * (∫⁻ z, F z ∂μ.prod μ) ≤
      (ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-d.a)) * ENNReal.ofReal (d.levelMass^(-2:ℤ)) *
        ENNReal.ofReal (d.levelMass^(-2:ℤ))) *
      (binKernelConstant * ENNReal.ofReal (d.levelMass^4*(2:ℝ)^(-((d.t:ℝ)-d.a))) * d.coincidence) := by
    apply le_trans ?_ h₂
    simpa only [smul_eq_mul,mul_assoc,F] using h₁
  have he (a b c k l D : ℝ≥0∞) : (a*b*c)*(k*l*D) = (a*b*c*l)*(k*D) := by ring
  rw [he,d.normalized_weight_kernel_factor,one_mul] at hh
  exact hh

end PositiveDistanceData

end PlanarFalconer

end OAI
