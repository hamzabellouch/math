import OAI.Combinatorics.BalancedRyser.Profiles.ProfileGridProducts
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileParameterLaw

namespace OAI

open scoped ENNReal Topology
open MeasureTheory Set Filter

namespace Balanced.ProfileParameterGrids

theorem integral_parameterLaw {γ : ℝ} (hγ : 1 ≤ γ)
    (f : BoundedContinuousFunction ℝ ℝ) :
    (∫ z, f z ∂ProfileParameterLaw.parameterLaw γ) =
      ∫ z in (0 : ℝ)..1, f z * (γ * z ^ (γ - 1)) := by
  have hm : Measurable (fun z : ℝ => ENNReal.ofReal (γ * z ^ (γ - 1))) :=
    (measurable_const.mul (ProfileParameterLaw.measurable_real_rpow_const _)).ennreal_ofReal
  rw [ProfileParameterLaw.parameterLaw,
    integral_withDensity_eq_integral_toReal_smul hm
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hnn : ∀ᵐ z : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      0 ≤ γ * z ^ (γ - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact mul_nonneg (zero_le_one.trans hγ) (Real.rpow_nonneg hz.1.le _)
  have heq : (∫ z in Ioo (0 : ℝ) 1, (ENNReal.ofReal (γ * z ^ (γ - 1))).toReal • f z) =
      ∫ z in Ioo (0 : ℝ) 1, f z * (γ * z ^ (γ - 1)) := by
    apply integral_congr_ae
    filter_upwards [hnn] with z hz
    rw [ENNReal.toReal_ofReal hz, smul_eq_mul, mul_comm]
  rw [heq, ← integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le zero_le_one]

theorem powerUniform_eq_parameterLaw {γ : ℝ} (hγ : 1 ≤ γ) :
    (powerUniform γ (zero_le_one.trans hγ) : Measure ℝ) =
      ProfileParameterLaw.parameterLaw γ := by
  let := ProfileParameterLaw.parameterLaw_isProbabilityMeasure
    (lt_of_lt_of_le zero_lt_one hγ)
  let ν : FiniteMeasure ℝ := ⟨ProfileParameterLaw.parameterLaw γ, inferInstance⟩
  have heq : (powerUniform γ (zero_le_one.trans hγ)).toFiniteMeasure = ν := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro f
    change (∫ z, f z ∂(powerUniform γ (zero_le_one.trans hγ) : Measure ℝ)) =
      ∫ z, f z ∂ProfileParameterLaw.parameterLaw γ
    rw [integral_powerUniform hγ f, integral_parameterLaw hγ f]
  exact congrArg FiniteMeasure.toMeasure heq

theorem unitUniform_eq_parameterLaw_one :
    (unitUniform : Measure ℝ) = ProfileParameterLaw.parameterLaw 1 := by
  rw [ProfileParameterLaw.parameterLaw_one]
  change volume.restrict (Icc (0 : ℝ) 1) = volume.restrict (Ioo (0 : ℝ) 1)
  exact Measure.restrict_congr_set Ioo_ae_eq_Icc.symm

end Balanced.ProfileParameterGrids

end OAI
