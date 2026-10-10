import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedWindowContinuation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueKernelPairing

namespace OAI

/-! The equality of the physical cusp residues, together with the
spectral projection identity, forces inversion invariance of the full residue. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaArithmeticResidueEnergy_inversion :
    cubicThetaInversionEnergy (cubicThetaArithmeticResidueEnergy (4/3))=
      cubicThetaArithmeticResidueEnergy (4/3) := by
  let R := cubicThetaArithmeticResidueEnergy (4/3)
  have hR : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ)) R=0 := by
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using
      cubicThetaArithmeticResidueEnergy_kernel (4/3)
  have hU := cubicThetaInversionEnergy_kernel _ R hR
  have hD : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ))
      (R-cubicThetaInversionEnergy R)=0 := by rw [map_sub,hR,hU,sub_self]
  have hmean : inner ℂ (cubicThetaCuspFourierTest 0 (cubicThetaHighWindowWeight (4/3)))
      (cubicThetaCuspRestriction (R-cubicThetaInversionEnergy R))=0 := by
    rw [map_sub,inner_sub_right,←cubicThetaHighWindowPairing_energy,
      ←cubicThetaHighWindowPairing_energy]
    exact sub_eq_zero.mpr cubicThetaResidue_inverted_window_pairing.symm
  have ho := cubicThetaResidue_orthogonal_of_zero_cusp_mean _ hD hmean
  change inner ℂ (R-cubicThetaInversionEnergy R) R=0 at ho
  rw [inner_sub_left] at ho
  have hc : inner ℂ (cubicThetaInversionEnergy R) R=inner ℂ R R :=
    (sub_eq_zero.mp ho).symm
  have hc' : inner ℂ R (cubicThetaInversionEnergy R)=inner ℂ R R := by
    exact (inner_conj_symm (𝕜:=ℂ) R (cubicThetaInversionEnergy R)).symm.trans
      ((congrArg (starRingEnd ℂ) hc).trans (inner_self_conj (𝕜:=ℂ) R))
  have hz : inner ℂ (R-cubicThetaInversionEnergy R) (R-cubicThetaInversionEnergy R)=0 := by
    rw [inner_sub_left,inner_sub_right,inner_sub_right,hc,hc',
      cubicThetaInversionEnergy.inner_map_map]
    ring
  exact (sub_eq_zero.mp ((inner_self_eq_zero (𝕜:=ℂ)).mp hz)).symm

end CubicFirstMoment

end

end OAI
