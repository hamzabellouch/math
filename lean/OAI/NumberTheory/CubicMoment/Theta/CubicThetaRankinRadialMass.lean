import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarRankinRadial
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierEnergyLowPole

namespace OAI

/-! Splitting the constant mode from the exact radial Rankin integral. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaRankin_constant_integral {σ : ℝ} (hσ : 0<σ) :
    (∫ v in Ioc (0:ℝ) 1,cubicThetaConstant^2*v^(2*σ+1/3))=
      cubicThetaConstant^2/(2*σ+4/3) := by
  rw [integral_const_mul,←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    integral_rpow (Or.inl (by linarith : -1<2*σ+1/3))]
  rw [Real.one_rpow,Real.zero_rpow (by linarith : 2*σ+1/3+1≠0)]
  ring

lemma cubicThetaRankin_constant_term {σ v : ℝ} (hv : 0<v) :
    v^(2*σ-1)*(cubicThetaConstant*v^(2/3:ℝ))^2=
      cubicThetaConstant^2*v^(2*σ+1/3) := by
  have hp : (v^(2/3:ℝ))^2=v^(4/3:ℝ) := by
    rw [←Real.rpow_mul_natCast hv.le]
    norm_num
  rw [mul_pow,hp]
  calc
    _ = cubicThetaConstant^2*(v^(2*σ-1)*v^(4/3:ℝ)) := by ring
    _ = _ := by rw [←Real.rpow_add hv]; congr 1; congr 1; ring

lemma cubicThetaRankinRadialEnergy_integral {σ : ℝ} (hσ : 0<σ) :
    (∫ v in Ioc (0:ℝ) 1,cubicThetaRankinRadialEnergy σ v)=
      ((cubicThetaConstant^2/(2*σ+4/3):ℝ):ℂ)+
        (‖cubicThetaArithmeticBaseScalar‖^2:ℝ)*
          (cubicThetaFourierEnergyLowMass σ:ℂ) := by
  have hconst : IntegrableOn (fun v : ℝ => cubicThetaConstant^2*v^(2*σ+1/3)) (Ioc 0 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1<2*σ+1/3))).const_mul _
  have henergy := ((cubicThetaArithmeticFourierEnergy_mellin_integrable hσ).mono_set
    (show Ioc (0:ℝ) 1⊆Ioi 0 from Ioc_subset_Ioi_self)).const_mul
      (‖cubicThetaArithmeticBaseScalar‖^2)
  have he : (∫ v in Ioc (0:ℝ) 1,cubicThetaRankinRadialEnergy σ v)=
      ((∫ v in Ioc (0:ℝ) 1,cubicThetaConstant^2*v^(2*σ+1/3)+
        ‖cubicThetaArithmeticBaseScalar‖^2*(v^(2*σ-1)*cubicThetaArithmeticFourierEnergy v):ℝ):ℂ) := by
    rw [←integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    unfold cubicThetaRankinRadialEnergy
    have hc := cubicThetaRankin_constant_term (σ:=σ) hv.1
    push_cast
    have hcc := congrArg Complex.ofReal hc
    push_cast at hcc
    linear_combination hcc
  rw [he,integral_add hconst henergy,cubicThetaRankin_constant_integral hσ,integral_const_mul]
  push_cast
  rfl

theorem cubicThetaRankinRadialEnergy_residue :
    Tendsto (fun σ : ℝ => (σ:ℂ)*∫ v in Ioc (0:ℝ) 1,cubicThetaRankinRadialEnergy σ v)
      (𝓝[>] 0) (𝓝 ((‖cubicThetaArithmeticBaseScalar‖^2:ℝ)*(243/8:ℂ))) := by
  have hσ : Tendsto (fun σ : ℝ => (σ:ℂ)) (𝓝[>] 0) (𝓝 (0:ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hc : ContinuousAt (fun σ : ℝ => ((cubicThetaConstant^2/(2*σ+4/3):ℝ):ℂ)) 0 := by
    fun_prop (disch := norm_num)
  have hz := hσ.mul (hc.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [zero_mul] at hz
  have h := hz.add (cubicThetaFourierEnergyLowMass_residue.const_mul
    ((‖cubicThetaArithmeticBaseScalar‖^2:ℝ):ℂ))
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [cubicThetaRankinRadialEnergy_integral hσ]
  ring

end CubicFirstMoment

end

end OAI
