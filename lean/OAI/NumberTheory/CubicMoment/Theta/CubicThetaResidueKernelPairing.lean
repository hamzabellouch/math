import OAI.NumberTheory.CubicMoment.Theta.CubicThetaWindowWeak

namespace OAI

/-! The actual residue pairs with any vector in the theta eigenspace
through the incoming forcing. Its compact-window equation reduces that
pairing to the constant cusp observation. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaResidue_kernel_pairing (v : cubicThetaGlobalEnergySpace)
    (hv : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ)) v=0) :
    inner ℂ v (cubicThetaArithmeticResidueEnergy (4/3))=
      (cubicThetaGlobalSpectralParameter (4/3:ℂ)/((2*(4/3:ℝ)-2:ℝ):ℂ))*
        inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaForcingL2 (4/3)) := by
  let K := (cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ))).ker
  have hPv : K.starProjection v=v := K.starProjection_eq_self_iff.mpr hv
  have hR : cubicThetaArithmeticResidueEnergy (4/3)=
      (17/6:ℂ) • K.starProjection (cubicThetaGlobalInclusion.adjoint (cubicThetaForcingL2 (4/3))) := by
    unfold cubicThetaArithmeticResidueEnergy K cubicThetaExceptionalProjection
    norm_num [cubicThetaGlobalSpectralParameter]
  have hc : cubicThetaGlobalSpectralParameter (4/3:ℂ)/((2*(4/3:ℝ)-2:ℝ):ℂ)=(17/6:ℂ) := by
    norm_num [cubicThetaGlobalSpectralParameter]
  rw [hR,inner_smul_right (𝕜:=ℂ) (E:=cubicThetaGlobalEnergySpace),hc]
  congr 1
  let f := cubicThetaGlobalInclusion.adjoint (cubicThetaForcingL2 (4/3))
  have he : inner ℂ (K.starProjection v) f = inner ℂ v f :=
    congrArg (fun w : cubicThetaGlobalEnergySpace => inner ℂ w f) hPv
  exact (K.inner_starProjection_left_eq_right v f).symm.trans
    (he.trans (cubicThetaGlobalInclusion.adjoint_inner_right v (cubicThetaForcingL2 (4/3))))

lemma cubicThetaKernel_window_balance (v : cubicThetaGlobalEnergySpace)
    (hv : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ)) v=0) :
    inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaForcingL2 (4/3))=
      inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaHighWindowL2 (4/3)) := by
  have hR := cubicThetaEnergyPencil_inner (cubicThetaGlobalSpectralParameter (4/3:ℂ))
    (cubicThetaGlobalEnergyTest (cubicThetaIncomingWindowTest (4/3))) v
  rw [hv,inner_zero_right,cubicThetaGlobalInclusion_test,cubicThetaGlobalEnergyGradient_test] at hR
  have hR' := congrArg (starRingEnd ℂ) hR
  simp only [map_add,map_mul,map_sub,map_zero,map_one,map_ofNat,inner_conj_symm,
    cubicThetaGlobalSpectralParameter] at hR'
  norm_num [starRingEnd_apply] at hR'
  have hW := cubicThetaWindow_global_weak (4/3) v
  have hz : inner ℂ (cubicThetaGlobalEnergyGradient v)
      (cubicThetaGlobalGradient (cubicThetaIncomingWindowTest (4/3)))+
      (4/3:ℂ)*((4/3:ℂ)-2)*inner ℂ (cubicThetaGlobalInclusion v)
        (cubicThetaGlobalMass (cubicThetaIncomingWindowTest (4/3)))=0 := by
    norm_num at hR' ⊢
    linear_combination -hR'
  rw [hz,inner_sub_right] at hW
  exact (sub_eq_zero.mp hW.symm).symm

theorem cubicThetaResidue_orthogonal_of_zero_cusp_mean (v : cubicThetaGlobalEnergySpace)
    (hv : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ)) v=0)
    (hmean : inner ℂ (cubicThetaCuspFourierTest 0 (cubicThetaHighWindowWeight (4/3)))
      (cubicThetaCuspRestriction v)=0) :
    inner ℂ v (cubicThetaArithmeticResidueEnergy (4/3))=0 := by
  rw [cubicThetaResidue_kernel_pairing v hv,cubicThetaKernel_window_balance v hv,
    ←inner_conj_symm,cubicThetaHighWindowPairing_energy,hmean,map_zero,mul_zero]

end CubicFirstMoment

end

end OAI
