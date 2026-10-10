import OAI.NumberTheory.CubicMoment.Theta.CubicThetaResidueMassPairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaWindowFluxIntegral

namespace OAI

/-! Exact global L2 norms of the actual and constant-normalized residues. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaArithmeticResidue_norm_sq :
    (‖cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))‖^2:ℂ)=
      star ((3*Real.pi:ℂ)*cubicThetaScatteringResidue) := by
  rw [cubicThetaArithmeticResidue_mass_sq,cubicThetaHighWindow_zero_radial]
  simp only [star_mul,star_div₀,star_ofNat,Complex.star_def,Complex.conj_ofReal]
  ring

lemma cubicThetaNormalizedArithmeticResidue_norm_sq :
    (‖cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue‖^2:ℂ)=
      cubicThetaResidueScale*((9*Real.sqrt 3/2:ℝ):ℂ)*(cubicThetaConstant:ℂ) := by
  rw [cubicThetaNormalizedArithmeticResidue_mass_sq,cubicThetaHighWindow_zero_radial]
  simp only [star_mul,star_div₀,star_ofNat,Complex.star_def,Complex.conj_ofReal]
  ring

theorem cubicThetaNormalizedArithmeticResidue_norm_identity :
    (‖cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue‖^2:ℂ)*
      ((Real.pi:ℂ)^2/(54*principalIdealZeta 2))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(cubicThetaConstant:ℂ)^2 := by
  rw [cubicThetaNormalizedArithmeticResidue_norm_sq,cubicThetaResidueScale]
  have hπ : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hZ := cubicTheta_principalZeta_two_ne_zero
  field_simp

end CubicFirstMoment

end

end OAI
