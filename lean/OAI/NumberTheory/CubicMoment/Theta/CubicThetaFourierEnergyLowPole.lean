import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierEnergyIntegrable
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEnergyPoleValue

namespace OAI

/-! Cutting the arithmetic energy Mellin integral at height one preserves its pole. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

def cubicThetaFourierEnergyHighMass (σ : ℝ) : ℝ :=
  ∫ v in Ioi (1:ℝ),v^(2*σ-1)*cubicThetaArithmeticFourierEnergy v

def cubicThetaFourierEnergyLowMass (σ : ℝ) : ℝ :=
  ∫ v in Ioc (0:ℝ) 1,v^(2*σ-1)*cubicThetaArithmeticFourierEnergy v

lemma cubicThetaFourierEnergyHighMass_tendsto :
    Tendsto cubicThetaFourierEnergyHighMass (𝓝[>] 0)
      (𝓝 (cubicThetaFourierEnergyHighMass 0)) := by
  have hmajor := (cubicThetaArithmeticFourierEnergy_mellin_integrable (σ:=1) (by norm_num)).mono_set
    (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun v : ℝ => v^(2*(1:ℝ)-1)*cubicThetaArithmeticFourierEnergy v) ?_ ?_ hmajor ?_
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact ((cubicThetaArithmeticFourierEnergy_mellin_integrable hσ).mono_set
      (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))).aestronglyMeasurable
  · have hs0 : ∀ᶠ σ : ℝ in 𝓝 0,σ<1 := Iio_mem_nhds (by norm_num : (0:ℝ)<1)
    have hs : ∀ᶠ σ : ℝ in 𝓝[>] 0,σ<1 := hs0.filter_mono nhdsWithin_le_nhds
    filter_upwards [hs] with σ hσ
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    change 1<v at hv
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (cubicThetaArithmeticFourierEnergy_nonneg v))]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hv.le (by linarith))
      (cubicThetaArithmeticFourierEnergy_nonneg v)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    change 1<v at hv
    have hc : ContinuousAt (fun σ : ℝ => v^(2*σ-1)) 0 :=
      (Real.continuousAt_const_rpow (by linarith : v≠0)).comp (by fun_prop)
    exact (hc.mul continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds

lemma cubicThetaFourierEnergyLowMass_eq {σ : ℝ} (hσ : 0<σ) :
    cubicThetaFourierEnergyLowMass σ=
      (∫ v in Ioi (0:ℝ),v^(2*σ-1)*cubicThetaArithmeticFourierEnergy v)-
        cubicThetaFourierEnergyHighMass σ := by
  have hi := cubicThetaArithmeticFourierEnergy_mellin_integrable hσ
  have he : (∫ v in Ioi (0:ℝ),v^(2*σ-1)*cubicThetaArithmeticFourierEnergy v)=
      cubicThetaFourierEnergyLowMass σ+cubicThetaFourierEnergyHighMass σ := by
    rw [←Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1),
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hi.mono_set Ioc_subset_Ioi_self)
        (hi.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1)))]
    rfl
  linarith

theorem cubicThetaFourierEnergyLowMass_residue :
    Tendsto (fun σ : ℝ => (σ:ℂ)*(cubicThetaFourierEnergyLowMass σ:ℂ))
      (𝓝[>] 0) (𝓝 (243/8)) := by
  have hσ : Tendsto (fun σ : ℝ => (σ:ℂ)) (𝓝[>] 0) (𝓝 (0:ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hH := (Complex.continuous_ofReal.tendsto _).comp cubicThetaFourierEnergyHighMass_tendsto
  have hz := hσ.mul hH
  simp only [zero_mul] at hz
  have h := cubicThetaArithmeticFourierEnergy_residue_explicit.sub hz
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  dsimp only [Function.comp_apply]
  rw [cubicThetaFourierEnergyLowMass_eq hσ]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
