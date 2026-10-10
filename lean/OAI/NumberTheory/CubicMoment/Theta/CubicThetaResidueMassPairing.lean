import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueKernelPairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueNormalization

namespace OAI

/-! The actual residue's global mass is fixed by its high-cusp constant
observation. This uses the weak eigenvalue equation, not a norm assumption. -/
noncomputable section
open scoped InnerProduct
namespace CubicFirstMoment

lemma cubicThetaResidue_energy_pairing (v : cubicThetaGlobalEnergySpace) :
    inner ℂ v (cubicThetaArithmeticResidueEnergy (4/3)) =
      (17/9:ℂ)*inner ℂ (cubicThetaGlobalInclusion v)
        (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))) := by
  have hw := cubicThetaArithmeticResidueEnergy_weak (4/3) v
  rw [cubicThetaGlobalEnergy_inner]
  norm_num at hw
  linear_combination hw

lemma cubicThetaResidue_mass_pairing (v : cubicThetaGlobalEnergySpace)
    (hv : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ)) v=0) :
    inner ℂ (cubicThetaGlobalInclusion v)
        (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))) =
      (3/2:ℂ)*inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaHighWindowL2 (4/3)) := by
  have hp := cubicThetaResidue_kernel_pairing v hv
  rw [cubicThetaResidue_energy_pairing,cubicThetaKernel_window_balance v hv] at hp
  norm_num [cubicThetaGlobalSpectralParameter] at hp
  linear_combination (9/17:ℂ)*hp

lemma cubicThetaArithmeticResidue_mass_sq :
    (‖cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))‖^2:ℂ) =
      (3/2:ℂ)*star ((3*Real.pi:ℂ)*cubicThetaScatteringResidue*
        cubicThetaZeroRadialTest (cubicThetaHighWindowWeight (4/3)) (4/3)) := by
  have hk : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ))
      (cubicThetaArithmeticResidueEnergy (4/3))=0 := by
    convert cubicThetaArithmeticResidueEnergy_kernel (4/3) using 1
    norm_num
  have hp := cubicThetaResidue_mass_pairing (cubicThetaArithmeticResidueEnergy (4/3)) hk
  rw [inner_self_eq_norm_sq_to_K,←inner_conj_symm,cubicThetaHighWindowPairing_energy,
    cubicThetaResidue_zero_observation _
      (fun _ hv => cubicThetaHighWindowForcing_low (4/3) hv)] at hp
  exact hp

lemma cubicThetaNormalizedArithmeticResidue_mass_sq :
    (‖cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue‖^2:ℂ) =
      (3/2:ℂ)*cubicThetaResidueScale*
        star (((9*Real.sqrt 3/2:ℝ):ℂ)*(cubicThetaConstant:ℂ)*
          cubicThetaZeroRadialTest (cubicThetaHighWindowWeight (4/3)) (4/3)) := by
  rw [cubicThetaNormalizedArithmeticResidue,map_smul,norm_smul]
  push_cast
  rw [mul_pow,cubicThetaArithmeticResidue_mass_sq]
  have hn : (‖cubicThetaResidueScale‖:ℂ)^2=
      star cubicThetaResidueScale*cubicThetaResidueScale := by
    simpa only [Complex.star_def] using
      (Complex.conj_mul' cubicThetaResidueScale).symm
  rw [hn]
  have h := cubicThetaResidueScale_constant
  push_cast at h
  rw [←h]
  simp only [star_mul]
  ring

end CubicFirstMoment

end

end OAI
